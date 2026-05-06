Rewrites an egglog program to use a slotted-egraph encoding so the e-graph
identifies terms that are equal up to renaming of free variables/slots,
without the user having to thread renames through their rules by hand.

This is a *draft* plan: the file describes the intended pipeline and the
examples it should produce. The current `src/slotted_encoding.rs` only
implements an early prototype (a `Rename` wrapper-style encoding gated on
rule names containing `"user"`); the plan below replaces it with the
edge-renaming style of `tests/slotted-egraph-encoding-10.egg`.

# Background

Slotted e-graphs (Schneider et al., PLDI 2025) make α-equivalence a
data-structure invariant: e-classes carry an explicit set of free **slots**,
e-node children are stored as `(eclass-id, renaming)` pairs, and two terms
that differ only by a renaming end up in the same e-class. The reference
implementation lives at https://github.com/memoryleak47/slotted-egraphs and
the paper PDF at https://steuwer.info/files/publications/2025/PLDI-Slotted-E-Graphs.pdf.

Encoding-10 is a sparse-map dialect of the same idea, expressed entirely in
egglog with no native support beyond `Map i64 i64` plus the `compose`,
`inverse`, `find-mapping`, `map-get` primitives:

```text
(sort Renaming (Map i64 i64))
(constructor Var (i64) U)              ; atomic id leaf
(constructor App (String U Renaming U Renaming) U)   ; one Renaming per U child
(relation RenamesToLeader (U U Renaming))            ; R * e2 = e1
```

with hand-written rules for transitivity, alpha-equivalence finding,
migration of e2-nodes into e1's representation, and per-position child
rewrites.

The plan is to auto-generate that boilerplate from "ordinary" user-facing
constructors and rules, the same way the proof/term encoding pass auto-
generates UF/view tables and rebuild rules per sort.

# Vocabulary mapping (paper ↔ encoding-10)

| Paper concept                              | Encoding-10 form                                                |
|--------------------------------------------|-----------------------------------------------------------------|
| Slot `$x` (free variable name)             | An `i64` value appearing as a key/value in some `Renaming` map  |
| E-class `c` with slot set `S`              | An `U`-sorted e-class, slots inferred from incident renamings   |
| Renamed-id child `m * c`                   | `(c : U, m : Renaming)` adjacent positional pair                |
| Shape (canonical normal form)              | *not materialized*; orbit variants coexist in the same e-class  |
| Symmetry group of an e-class               | `RenamesToLeader self self R` entries                           |
| α-equivalence between e-classes            | `RenamesToLeader e2 e1 R` (with non-trivial `R`)                |
| Drop-redundant slot                        | Out of scope for the first milestone                            |
| Binder (`Lam(Bind<RenamedId>)`)            | Out of scope for the first milestone                            |

# Triggering the pass

Constructed via
[`EGraph::with_slotted_encoding`](crate::EGraph::with_slotted_encoding) (or
the existing `--with-slotted-encoding` CLI flag). The pass runs after type
checking and before the term/proof encoding, so all later instrumentation
sees the desugared sorts.

Like the term encoding, the slotted encoding emits new sorts, relations,
and rulesets up front, then rewrites each constructor declaration and each
user rule in place.

# What gets added once per program

Independent of how many sorts the user declares:

```text
(sort Renaming (Map i64 i64))
```

The four primitives (`compose`, `inverse`, `find-mapping`, `map-get`)
already exist in `src/sort/map.rs`; the pass relies on them.

# What gets added per user `U`-sort

For every user sort `U` (every `(sort U)` whose constructors take or return
`U`):

```text
(relation RenamesToLeader_U (U U Renaming))    ; R * e2 = e1, e1 < e2 by id

;; transitivity
(rule ((RenamesToLeader_U e1 e2 R)
       (RenamesToLeader_U e2 e3 R2))
      ((RenamesToLeader_U e1 e3 (compose R2 R))))
```

Migration of `e2` is split per-constructor below — the relation only
records the *fact* that two e-classes are related by a rename.

# What gets added per constructor

There are two flavours of constructor we care about:

1. **Atomic-id leaves.** A constructor with one or more non-`U` arguments
   and no `U` arguments. Each `i64`-typed argument is treated as a slot
   reference (the constructor's "free variables"). Concrete example: `Var`.
2. **Compound nodes.** A constructor with one or more `U`-typed arguments.
   Each `U` argument grows an adjacent `Renaming` argument that names that
   child's slots inside the parent's slot space. Concrete example: `App`.

Pure-data constructors (no `U` arg, no `i64` slot arg — e.g. `(constructor
True () Bool)`) are left untouched.

The transformations below use `App` and `Var` as the running example, but
they generalize to arbitrary arities by zipping over each `U`-typed
position.

## Atomic-id leaves

The constructor signature stays the same. The pass adds:

```text
;; pair rule: any two distinct (Var id) e-classes are α-related by the
;; substitution that swaps one id for the other.
(rule ((= e1 (Var id1))
       (= e2 (Var id2))
       (!= id1 id2)
       (= e2 (ordering-max e1 e2)))
      ((RenamesToLeader_U e2 e1
                          (map-insert (map-empty) id2 id1))))

;; migration: rewrite (Var id) into (Var (map-get R id)) when R points it
;; at a leader.
(rule ((RenamesToLeader_U e2 e1 R)
       (= e2 (Var id))
       (= new_id (map-get R id))
       (!= e1 e2))
      ((union e2 (Var new_id))
       (delete (Var id))))
```

Multiple `i64` arguments would all be slot references; the pair rule
generalizes by combining them into a single `Renaming` value (one entry per
slot position).

## Compound nodes

Constructor signature is rewritten to interleave `Renaming` after every
`U`-typed input:

```text
;; before
(constructor App (String U U) U)
;; after
(constructor App (String U Renaming U Renaming) U)
```

For each rewritten constructor with `n` `U`-typed positions `c_1, ..., c_n`
(carrying renamings `r_1, ..., r_n`), the pass emits:

```text
;; α-equivalence finder
(rule ((= e1 (App f c_1 a_1 ... c_n a_n))
       (= e2 (App f c_1 b_1 ... c_n b_n))
       (= rename (find-mapping a_1 ... a_n b_1 ... b_n))
       (= e2 (ordering-max e1 e2)))
      ((RenamesToLeader_U e2 e1 rename)))

;; migration: push R through every edge rename of e2.
(rule ((RenamesToLeader_U e2 e1 R)
       (= e2 (App f c_1 r_1 ... c_n r_n))
       (!= e1 e2))
      ((union e2 (App f c_1 (compose R r_1) ... c_n (compose R r_n)))
       (delete (App f c_1 r_1 ... c_n r_n))))

;; per-position child rewrite (one rule per i ∈ 1..n)
(rule ((RenamesToLeader_U c_i c_i' R)
       (= node (App f ... c_i r_i ...))
       (!= c_i c_i'))
      ((delete (App f ... c_i r_i ...))
       (union node (App f ... c_i' (compose r_i (inverse R)) ...))))
```

The three derivations (`compose R r`, `compose r (inverse R)`, and
`find-mapping`) all use the same explicit partial-map semantics implemented
in `src/sort/map.rs`: missing keys mean “no mapping”, not identity. The
`(!= c_i c_i')` and `(!= e1 e2)` guards keep the migration from looping on
self-RenamesToLeader entries.

# What gets rewritten in user rules

A user rule body is a conjunction of atoms; user actions are sequences of
unions/inserts/deletes. The pass walks each, treating every reference to a
rewritten `U`-sorted child position as if it had an implicit `Renaming`
attached.

Mechanically:

1. Each `U`-typed positional argument in a body atom grows a fresh
   `Renaming` variable matched alongside it.
2. Each `U`-typed positional argument in an action grows a `Renaming`
   expression — composed from the renamings the rule already bound (so the
   variable's "slot space" agrees with the surrounding context).
3. When the same egglog variable `x` appears in multiple atoms, the
   renamings recovered from each occurrence must agree as `Renaming`
   values; the pass adds `(= rx_at_atom1 rx_at_atom2)` constraints to the
   body.

This is operationally similar to what the prototype `slotted_encoding.rs`
does today via the `Rename` wrapper, but expressed as edge renamings on
the constructor itself.

# Where up-to-renaming surfaces

The encoding keeps two notions of equality cleanly separated at the user
surface:

| Form | Means |
|------|-------|
| `(check (= a b))` | structural — `a` and `b` are in the *same* e-class |
| `(check-eq-with-rename $a $b)` | slotted — `$a` and `$b` are connected by `RenamesToLeader_U` |

`check-eq-with-rename` is a new top-level command added by this pass. It
takes exactly two **global identifiers** (i.e. names introduced by `let`
or `function`-with-no-args). The global-only restriction keeps the
operation safe: it just looks up two known e-class ids and probes a
relation, with no risk of implicitly inserting fresh terms.

It desugars to a single `RenamesToLeader_U` query (no `or`-style
disjunction needed; egglog doesn't have one):

```text
;; user writes
(check-eq-with-rename $a $b)
;; pass emits
(check (RenamesToLeader_U $a $b R))   ; R is a free pattern variable
```

The transitivity rule emitted in the per-sort preamble closes
`RenamesToLeader_U` under chaining, so a single hop is enough.

Implications for the surface:

- `(check (= (Var 13) (Var 14)))` — strictly structural. Whether this
  succeeds depends on the migration choice in *Open questions* below.
  When migration is unifying, this is `true`; when it isn't, this is
  `false`.
- `(check-eq-with-rename $g13 $g14)` (where `$g13`, `$g14` are globals
  bound to `(Var 13)` and `(Var 14)`) — always `true` once the leaf
  pair rule has fired, regardless of the migration choice.

# Worked examples

The examples below are written in encoding-10 form. The "before" column is
what the user types; the "after" column is what the slotted-encoding pass
should emit (modulo names of fresh renaming variables).

## Example A — Constructor declaration with `U` children

Before:
```text
(constructor App (String U U) U)
```
After (machinery only — the pair/migration/child-rewrite rules above are
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
;; + the pair rule and migration rule from the leaf section
```

## Example C — Trivial commutativity-style rule

Before:
```text
(rule ((= e (App "f" a b)))
      ((union e (App "f" b a))))
```
After: every `U`-child reference gains a renaming, and the renamings just
travel along with the child reordering.
```text
(rule ((= e (App "f" a r_a b r_b)))
      ((union e (App "f" b r_b a r_a))))
```

## Example D — Re-use of a child variable

Before (the same `x` appears twice as an `App` child):
```text
(rule ((= e (App "g" x x)))
      ((union e x)))
```
After: each occurrence of `x` carries its own renaming, and we constrain
them to agree (so `x` really means "the same slot view in both positions"):
```text
(rule ((= e (App "g" x r1 x r2))
       (= r1 r2))
      ((union e x)))
```
The action's `union e x` uses `x` directly; if instead the action embedded
`x` inside another `U`-constructor, its renaming would be `r1` (= `r2`)
threaded into the right edge.

## Example E — A rule whose action introduces a new constructor

Before:
```text
(rule ((= e (App "f" a b)))
      ((union e (App "h" a b))))
```
After: re-use the same renamings on both sides so the rewrite preserves
each child's slot view.
```text
(rule ((= e (App "f" a r_a b r_b)))
      ((union e (App "h" a r_a b r_b))))
```

## Example F — `Var` α-equivalence (built-in, no user rule)

Without writing any rule, the user's program containing
```text
(let $v1 (Var 20))
(let $v2 (Var 1))
```
ends up unifying `$v1` and `$v2` after one `(run …)`, because the
auto-emitted leaf pair rule and migration rule from the *Atomic-id leaves*
section conspire to do so. This matches the behavior of encoding-10 today.

## Example G — `App` α-equivalence (built-in, no user rule)

Likewise, with
```text
(let $a1 (App "f"
              $v1 (map-insert (map-empty) 20 0)
              $v2 (map-insert (map-empty) 1 1)))
(let $a2 (App "f"
              $v2 (map-insert (map-empty) 1 0)
              $v1 (map-insert (map-empty) 20 1)))
```
the auto-emitted α-equivalence finder and migration rules unify `$a1` and
`$a2` by matching explicit child-slot maps and deriving the outer-slot
rename between them — see `src/sort/map.rs`.

# Implementation milestones

1. **Replace the prototype.** Delete the `Rename`-wrapper logic in the
   current `slotted_encoding.rs`. Drop the `rule.name.contains("user")`
   trigger.
2. **Per-program preamble.** Emit the `Renaming` sort and per-sort
   `RenamesToLeader_U` relation + transitivity rule as the first commands
   in the rewritten program.
3. **Constructor rewrite.** Walk every `(constructor C (T1...) U)` in the
   resolved program; rewrite the signature in place; emit the pair-or-α-
   finder rule, migration rule, and per-position child-rewrite rules.
4. **User rule rewrite.** Walk every user rule, threading fresh renaming
   variables through body atoms and actions per the rewrite rules above.
5. **Check rewrite.** `check` and `extract` need to look up canonicalized
   forms; in the simplest version, leave them alone and rely on the orbit
   eventually containing the queried form.
6. **Tests.** Lift `tests/slotted-egraph-encoding-10.egg` into a "before"
   form (no Renaming arguments anywhere in the user surface), run it
   through the pass, and snapshot-test that the emitted program is
   semantically equivalent to today's hand-written version.

The first three milestones are the minimum viable encoding; 4 is the part
the prototype was already attempting; 5 and 6 finish the loop.

# Out of scope (later milestones)

- **Binders.** A future iteration adds an annotation (e.g.
  `(constructor Lam (Bind<U>) U)` or a `:slotted-binder` attribute) that
  declares a constructor introduces a fresh slot. The encoding for
  binders also emits redundant-slot-elimination rules.
- **Shape canonicalization.** Today encoding-10 keeps every orbit variant
  of an e-node co-resident in the same e-class. The paper canonicalizes
  to one shape. Doing so in egglog requires choosing a canonical
  representative; an obvious approach is "lexicographic min over the
  orbit" using `ordering-min`.
- **Redundant slots.** Detection and dropping requires reasoning about
  symmetry orbits across unions; this is the hardest part of the paper.
- **Performance / orbit explosion.** Worth benchmarking once the basic
  encoding is in place.

# Open questions

1. One `RenamesToLeader_<sort>` relation per `U`-sort, or one global one?
   The per-sort version makes type-checking trivial; a global version
   would need a single supertype of all `U`-sorts.
2. **Should migration unify e-classes, or just record the relation?**
   Unifying migration (encoding-10 today) means the migration rule's `union e2 (rewritten)` collapses α-equivalent e-classes into one, so `(check (= a b))` and `(check-eq-with-rename $a $b)` succeed in the same situations. Non-unifying migration drops that `union` and only emits the `RenamesToLeader_U` entry, so α-equivalent classes stay distinct and the structural `check` and slotted `check-eq-with-rename` give genuinely different answers. That is closer to the paper's model and resolves the `(Var 13) ≡ (Var 14)` surprise. The encoding plan should pick one; non-unifying is the cleaner story once `check-eq-with-rename` exists, since users have an explicit slot-aware probe and don't need `check` to do double duty.
3. How does a user write a rule that *does* mention slots explicitly
   (e.g. an η-style rule with a freshness side condition)? Probably an
   escape hatch where the user can directly write encoded rules.
4. Should the migration rule's `delete` happen unconditionally, or only
   when the rule's `union` would otherwise leave the e-class with an
   empty representative? The current encoding-10 pattern (`union e2
   (rewritten); delete (original)`) is fine because the union ensures a
   representation survives, but the audit for that property is left as
   future work.
5. Does `check-eq-with-rename` need a corresponding `extract-with-rename`?
   `extract` already picks one orbit variant; if migration is non-
   unifying, the user might want to ask "give me any term in the
   `RenamesToLeader_U`-orbit of `$a`." Probably yes, but a separate
   milestone.
