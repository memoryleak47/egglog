Rewrites an egglog program to use a slotted-egraph encoding so the e-graph
identifies terms that are equal up to renaming of free variables/slots,
without the user having to thread renames through their rules by hand.

The pass is implemented in [`src/slotted_encoding.rs`](crate::slotted_encoding) and is
enabled by constructing the e-graph with
[`EGraph::with_slotted_encoding`](crate::EGraph::with_slotted_encoding) (or
the `--slotted` CLI flag). It mirrors the structure of the proof/term
encoding pass: per-program preamble emitted on the first `(sort _)`,
per-constructor machinery emitted alongside each constructor declaration,
per-rule rewriting on each user `(rule ...)`, and a maintenance
`(run-schedule (saturate slotted))` appended after every non-declarative
top-level command.

# Background

Slotted e-graphs (Schneider et al., PLDI 2025) make α-equivalence a
data-structure invariant: e-classes carry an explicit set of free **slots**,
e-node children are stored as `(eclass-id, renaming)` pairs, and two terms
that differ only by a renaming end up in the same e-class. The reference
implementation lives at https://github.com/memoryleak47/slotted-egraphs and
the paper PDF at https://steuwer.info/files/publications/2025/PLDI-Slotted-E-Graphs.pdf.

The hand-written reference for this pass is
[`tests/slotted-egraph-encoding-10.egg`](https://github.com/egraphs-good/egglog) — a
sparse-map dialect of the paper's idea expressed directly in egglog with no
native support beyond `Map i64 i64` plus the `compose`, `inverse`,
`find-mapping`, `map-get` primitives:

```text
(sort Renaming (Map i64 i64))
(constructor Var (i64) U)              ; atomic-id leaf
(constructor App (String U Renaming U Renaming) U)   ; one Renaming per U child
(relation RenamesToLeader (U U Renaming))            ; R * e2 = e1
```

with hand-written rules for transitivity, alpha-equivalence finding, and
per-position child rewrites.

The auto-encoder generates that boilerplate from "ordinary" user-facing
constructors and rules.

# Vocabulary mapping (paper ↔ encoding-10)

| Paper concept                              | Encoding-10 form                                                |
|--------------------------------------------|-----------------------------------------------------------------|
| Slot `$x` (free variable name)             | An `i64` value appearing as a key/value in some `Renaming` map  |
| E-class `c` with slot set `S`              | A `U`-sorted e-class, slots inferred from incident renamings    |
| Renamed-id child `m * c`                   | `(c : U, m : Renaming)` adjacent positional pair                |
| Shape (canonical normal form)              | *not materialized*; orbit variants coexist in the same e-class  |
| Symmetry group of an e-class               | `RenamesToLeader_U self self R` entries                         |
| α-equivalence between e-classes            | `RenamesToLeader_U e2 e1 R` (with non-trivial `R`)              |
| Drop-redundant slot                        | Out of scope for the first milestone                            |
| Binder (`Lam(Bind<RenamedId>)`)            | Out of scope for the first milestone                            |

# Triggering the pass

Constructed via
[`EGraph::with_slotted_encoding`](crate::EGraph::with_slotted_encoding) (or
the `--slotted` CLI flag). The pass runs after type checking and before the
term/proof encoding, so all later instrumentation sees the desugared sorts.

Like the term encoding, the slotted encoding emits new sorts, relations,
rulesets, and rewriting alongside every user-facing command, and emits
`(run-schedule (saturate slotted))` between top-level commands so the
slotted invariants stay current without the user having to call `(run)`
explicitly before a `check`.

# What gets added once per program

A single `Renaming` sort and a single `slotted` ruleset, on the first
`(sort _)` declaration encountered:

```text
(sort Renaming (Map i64 i64))
(ruleset slotted)
```

The four primitives (`compose`, `inverse`, `find-mapping`, `map-get`)
already exist in [`src/sort/map.rs`](crate::sort::map); the pass relies on
them.

# What gets added per user `U`-sort

For every user-defined eq-sort (every `(sort U)` whose constructors return
`U`), the pass emits a per-sort `RenamesToLeader_<U>` relation plus the
transitivity rule:

```text
(relation RenamesToLeader_U (U U Renaming))    ; R * e2 = e1, e1 < e2 by id

(rule ((RenamesToLeader_U e1 e2 R)
       (RenamesToLeader_U e2 e3 R2))
      ((RenamesToLeader_U e1 e3 (compose R2 R)))
      :ruleset slotted)
```

# What gets added per constructor

There are two flavours of constructor we care about:

1. **Atomic-id leaves.** A constructor with one or more non-`U` arguments
   and no `U` arguments. Each `i64`-typed argument is treated as a slot
   reference. Concrete example: `Var`.
2. **Compound nodes.** A constructor with one or more `U`-typed arguments.
   Each `U` argument grows an adjacent `Renaming` argument that names that
   child's slots inside the parent's slot space. Concrete example: `App`.

Pure-data constructors (no `U` arg, no `i64` slot arg — e.g. `(constructor
True () Bool)`) are left untouched.

The transformations below use `App` and `Var` as the running example, but
they generalize to arbitrary arities by zipping over each `U`-typed
position.

## Atomic-id leaves

The constructor signature stays the same. The pass adds only the **pair
rule**, which records — but does not unify — the renaming relationship
between any two distinct leaf instances:

```text
(rule ((= e1 (Var id1))
       (= e2 (Var id2))
       (!= id1 id2)
       (= e2 (ordering-max e1 e2)))
      ((RenamesToLeader_U e2 e1
                          (map-insert (map-empty) id2 id1)))
      :ruleset slotted)
```

There is *no* leaf-side migration rule. Leaving leaf classes distinct is
load-bearing: the per-pair `RenamesToLeader_U` entries are what
**child-rewrite** in compound migrations needs to fire on, and merging
leaf classes here would degenerate those entries to self-loops before any
surrounding compound was even constructed.

This means `(check (= (Var a) (Var b)))` for distinct `a`, `b` will fail —
the two leaves stay in different e-classes. Equality probes between leaf
e-classes should go through let-bindings or via the
`RenamesToLeader_U` relation directly.

## Compound nodes

The constructor signature is rewritten to interleave `Renaming` after every
`U`-typed input:

```text
;; before
(constructor App (String U U) U)
;; after
(constructor App (String U Renaming U Renaming) U)
```

For each rewritten constructor with `n` `U`-typed positions `c_1, ..., c_n`
(carrying renamings `r_1, ..., r_n`), the pass emits three rules:

```text
;; α-equivalence finder
(rule ((= e1 (App f c_1 a_1 ... c_n a_n))
       (= e2 (App f c_1 b_1 ... c_n b_n))
       (= rename (find-mapping a_1 ... a_n b_1 ... b_n))
       (= e2 (ordering-max e1 e2)))
      ((RenamesToLeader_U e2 e1 rename))
      :ruleset slotted)

;; migration: push R through every edge rename of e2 and delete the
;; pre-migration e-node so the e-class converges to a canonical form.
(rule ((RenamesToLeader_U e2 e1 R)
       (= e2 (App f c_1 r_1 ... c_n r_n))
       (!= e1 e2))
      ((union e2 (App f c_1 (compose R r_1) ... c_n (compose R r_n)))
       (delete (App f c_1 r_1 ... c_n r_n)))
      :ruleset slotted)

;; per-position child rewrite (one rule per i ∈ 1..n).
;; Note: no `delete` here — we want the rewritten variant to coexist
;; with the original so congruence can do the merging through it.
(rule ((RenamesToLeader_U c_i c_i' R)
       (= node (App f ... c_i r_i ...))
       (!= c_i c_i'))
      ((union node (App f ... c_i' (compose r_i (inverse R)) ...)))
      :ruleset slotted)
```

The three derivations (`compose R r`, `compose r (inverse R)`, and
`find-mapping`) all use the strict partial-map semantics implemented in
[`src/sort/map.rs`](crate::sort::map): missing keys mean "no mapping," not
identity. The `(!= c_i c_i')` and `(!= e1 e2)` guards keep the migration
from looping on self-`RenamesToLeader_U` entries.

# Maintenance schedule between commands

Mirroring the proof/term encoding, the pass appends

```text
(run-schedule (saturate slotted))
```

after every top-level command except `Function` (let/relation/constructor
declarations), `NormRule`, `Sort`, and ruleset declarations. This keeps
slotted invariants saturated whenever new e-graph data is introduced
(let-binding `set`s, standalone expressions, etc.), so a user can write
`(check (= $a $b))` straight after a `(let ...)` without needing to `(run)`
first.

Additionally, **user `RunSchedule` commands are instrumented** to fire
`(saturate slotted)` after each iteration: each `Run` node inside the
schedule tree gets wrapped as `(seq run (saturate slotted))`. So during a
long user `(run N)`, slotted machinery is applied to whatever the user's
own rules produce per iteration, not just at the end.

# What gets rewritten in user expressions

Top-level user expressions (let-binding values, standalone expressions,
check arguments, action expressions in `CoreAction` commands) get
**slot-inferred edge renames**. The convention is **identity-at-literal**:
each U-child's edge rename has keys *and* values both equal to the child's
own slot list. So `(App "f" (Var 20) (Var 1))` is emitted as

```text
(App "f" (Var 20) (map-insert (map-empty) 20 20)
         (Var 1)  (map-insert (map-empty) 1  1))
```

The compound's outer slot list is the deduped union of its U-children's
slot lists in encounter order. Same-variable references at different
child positions naturally reuse the same slot id (so `(App "f" $v1 $v1)`
ends up as `(App "f" $v1 {n:n} $v1 {n:n})` for whatever `n` is `$v1`'s
slot). Each let-binding's outer slot list is recorded so subsequent
expressions referencing it can use those slots as keys when building
their own edge renames.

Identity-at-literal matches the convention encoding-10 uses by hand and
matches the action-side synthesis below — top-level and rules emit the
*same* encoded form for the *same* user term. Slot ids are arbitrary;
no canonical `[0..k-1]` space is enforced.

# What gets rewritten in user rules

A user rule body is a conjunction of atoms; user actions are sequences of
unions/inserts/deletes. The pass walks each, treating every reference to a
rewritten `U`-sorted child position as if it had an implicit `Renaming`
attached.

Mechanically:

1. **Body**: every `U`-typed positional argument of a rewritten
   constructor in a body atom gains a fresh edge-rename pattern variable.
   As we descend into compound calls, we accumulate the *path* of edge
   renames from the outermost atom to the current position via `compose`.
   Each user variable at a U-child position records the path it was
   reached by.
2. **Equality constraints**: when a variable is reached via multiple
   paths in the body (multiple body atoms, or multiple positions within an
   atom), the paths must all describe the same effective slot view, so we
   emit `(= path_i path_j)` constraints between consecutive pairs.
3. **Action**: each user-variable U-child reuses the variable's first
   body path as its edge rename. For variables that *only* appear as a
   constructor head in the body (e.g. `(= e (App "f" a b))`), no path is
   collected, but the body-bound child renames `r_a, r_b, ...` are. The
   pass synthesizes the identity rename over the union of their value
   sets via `(map-union (compose r_a (inverse r_a)) (compose r_b (inverse r_b)) ...)`
   and uses that as the edge rename in actions. Variables with neither a
   path nor head matches fall back to `(map-empty)`.

This is operationally similar to what the wrapper-style prototype
(`b38a2f71:src/slotted_encoding.rs` in the git history) did, but expressed
as edge renamings on the constructor itself.

# Where up-to-renaming surfaces

The encoding lets `(check (= a b))` succeed for terms that are α-equivalent
in the slotted sense, *provided* both sides go through let-bindings or
sufficiently-shared structure that the migration/child-rewrite/congruence
chain unifies their e-classes. A future task (#13 in the in-tree task
list) sketched a separate `(check-eq-with-rename $a $b)` primitive that
would query `RenamesToLeader_U` directly for cases where structural
unification doesn't hold (or for two arbitrary leaf e-classes); that's not
in the current implementation.

# Worked examples

A larger collection lives in
[`src/slotted_encoding_examples.md`](crate::slotted_encoding_examples) —
ten before/after pairs covering constructor renaming, commutativity, path
equality, head-as-child synthesis, shared-variable cases, and the two
"intended" examples for #16 (literal leaf in action, nested fresh
compound). The four below are a quick on-ramp; for the full set, see that
file. Each example's "before" is what the user types; the "after" is what
the pass emits, modulo fresh-variable names.

## Example A — Constructor declaration with `U` children

Before:
```text
(constructor App (String U U) U)
```
After (machinery only — pair/migration/child-rewrite rules above are
emitted alongside):
```text
(constructor App (String U Renaming U Renaming) U)
```

## Example B — Atomic-id leaf

Before:
```text
(constructor Var (i64) U)
```
After:
```text
(constructor Var (i64) U)              ; signature unchanged
;; + the pair rule from the leaf section
```

## Example C — Top-level expressions get inferred renames

Before (slotted-test-1.egg):
```text
(let $v1 (Var 20))
(let $v2 (Var 1))
(let $a1 (App "f" $v1 $v2))
(let $a2 (App "f" $v2 $v1))
(check (= $a1 $a2))
```
After: each `let` is followed by an automatic
`(run-schedule (saturate slotted))`, and every constructor application has
its identity-at-literal edge renames inserted:
```text
(let $a1 (App "f"
              $v1 (map-insert (map-empty) 20 20)
              $v2 (map-insert (map-empty) 1  1)))
(let $a2 (App "f"
              $v2 (map-insert (map-empty) 1  1)
              $v1 (map-insert (map-empty) 20 20)))
;; (check passes after the maintenance schedule fires the leaf pair rule
;; and child-rewrite rules; child-rewrite produces matching edge-rename
;; orbits, the App α-finder ties them together via find-mapping, and
;; migration unions $a1 and $a2.)
```

## Example D — User commutativity rule (slotted-test-3.egg)

Before:
```text
(rule ((= e (App "f" a b)))
      ((union e (App "f" b a))))
```
After: each U-child position in the body gets a fresh edge-rename pattern
variable; the action reuses each user variable's body-bound rename in its
new position:
```text
(rule ((= e (App "f" a r1 b r2)))
      ((union e (App "f" b r2 a r1))))
```

## Example E — Path tracking with shared variable (slotted-test-5.egg)

Before:
```text
(rule ((= e (App "f" (App "g" a b) b)))
      ((union e (App "matched" b b))))
```
The body has `b` at two positions: nested inside `(App "g" ...)` and as a
direct child of `(App "f" ...)`. Their composed paths must agree.

After:
```text
(rule ((= e (App "f" (App "g" a r1 b r2) r b r3))
       (= (compose r r2) r3))
      ((union e (App "matched" b (compose r r2) b (compose r r2)))))
```

The rule fires only when the inner-path `compose r r2` (from the outer App
into the inner App into `b`) equals the outer-path `r3` (from the outer
App directly to `b`).

# Limitations

(none currently — see *Open questions* for things worth tightening.)

# Out of scope (later milestones)

- **Binders.** A future iteration adds an annotation (e.g.
  `(constructor Lam (Bind<U>) U)` or a `:slotted-binder` attribute) that
  declares a constructor introduces a fresh slot. The encoding for
  binders would also emit redundant-slot-elimination rules.
- **Shape canonicalization.** The pass currently keeps every orbit variant
  of an e-node co-resident in the same e-class. The paper canonicalizes
  to one shape; doing so in egglog would require choosing a canonical
  representative (e.g., `ordering-min` over the orbit).
- **Redundant slots.** Detection and dropping requires reasoning about
  symmetry orbits across unions; this is the hardest part of the paper.
- **Performance / orbit explosion.** Worth benchmarking once the basic
  encoding is in place.
- **`check-eq-with-rename` primitive.** A `RenamesToLeader_U`-based
  equality probe to complement structural `check`. Especially useful for
  leaf e-classes (which the pass intentionally keeps distinct).

# Open questions

1. **(decided)** One `RenamesToLeader_<sort>` relation per `U`-sort.
2. **(decided)** Identity-at-literal, not canonical `[0..k-1]`. Slot ids are
   arbitrary; the convention is that every U-child's edge rename has equal
   keys and values, equal to the child's own slot list. Under this
   convention, shared-variable identity is preserved through arbitrary
   nesting in user expressions and rules — exercised in
   `tests/slotted/slotted-test-shared.egg`.
3. **Tightening (open)**: when a variable is matched as both a constructor
   head *and* a U-child in a rule body, currently the path takes
   precedence silently — no body fact ties the path's slot view to the
   head-implied slot space. Should we emit
   `(= path synthesized_head_identity)` to force them to agree?
   Same question for a variable matched as a head in multiple body atoms:
   should the head-rename sets across atoms be constrained equal?
