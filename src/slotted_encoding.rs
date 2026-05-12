#![doc = include_str!("slotted_encoding.md")]

use egglog_ast::generic_ast::GenericExpr;
use egglog_ast::generic_ast::Literal;
use egglog_ast::span::Span;

use crate::{
    EGraph,
    ast::{Command, Expr, GenericNCommand, ResolvedNCommand},
    util::{FreshGen, HashMap, HashSet},
};

/// Persistent state for the slotted encoding pass. Lives on `EGraph` so it
/// accumulates across the per-source-command invocations of the pass.
#[derive(Clone, Default)]
pub(crate) struct SlottedState {
    /// User-defined eq-sorts that get the slotted treatment.
    pub u_sorts: HashSet<String>,
    /// Constructors whose signatures we rewrote: name -> per-argument mask
    /// where `true` means the argument is U-typed and now has a `Renaming`
    /// inserted after it.
    pub rewritten_ctors: HashMap<String, Vec<bool>>,
    /// Atomic-id leaf constructors (no U inputs, single i64 input). Used to
    /// recover the leaf's outer slot from the literal i64 argument.
    pub leaf_ctors: HashSet<String>,
    /// Outer-slot list for each let-binding (a no-arg function whose value
    /// expression we've slot-inferred). Stored in encounter-canonical form
    /// (sequential 0..n-1 for compound bound terms; `[id]` for atomic-id
    /// leaves).
    pub let_outer_slots: HashMap<String, Vec<i64>>,
    /// Whether the global `Renaming` sort has been emitted yet.
    pub renaming_sort_emitted: bool,
}

/// Auto-encoding pass that rewrites a user program into slotted-egraph form
/// per `slotted_encoding.md`.
///
/// Inputs are `ResolvedNCommand`s (post-typecheck). Output is `Vec<Command>`
/// (untyped); the caller re-resolves and re-typechecks each emitted command.
pub(crate) struct SlottedInstrumentor<'a> {
    pub(crate) egraph: &'a mut EGraph,
}

impl<'a> SlottedInstrumentor<'a> {
    pub(crate) fn add_slotted_encoding(
        egraph: &'a mut EGraph,
        program: Vec<ResolvedNCommand>,
    ) -> Vec<Command> {
        let mut s = Self { egraph };
        let mut out = Vec::new();
        for cmd in program {
            // Decide whether to append a slotted-maintenance run after this
            // command. We skip Function (let/relation/constructor decls
            // desugared), NormRule, and Sort: these change schema only and
            // can't trigger any new slotted machinery firings on their own.
            let needs_maintenance = !matches!(
                &cmd,
                GenericNCommand::Function(..)
                    | GenericNCommand::NormRule { .. }
                    | GenericNCommand::Sort { .. }
                    | GenericNCommand::AddRuleset(..)
                    | GenericNCommand::UnstableCombinedRuleset(..)
            );
            out.extend(s.handle_command(cmd));
            if needs_maintenance && s.egraph.slotted_state.renaming_sort_emitted {
                out.extend(s.parse_program(
                    "(run-schedule (saturate slotted))",
                ));
            }
        }
        if std::env::var("SLOTTED_DEBUG").is_ok() {
            eprintln!("---- slotted-encoded program ----");
            for c in &out {
                eprintln!("{}", c);
            }
            eprintln!("---- end ----");
        }
        out
    }

    /// Parse an egglog source snippet into commands using the e-graph's parser.
    fn parse_program(&mut self, input: &str) -> Vec<Command> {
        self.egraph.parser.ensure_no_reserved_symbols = false;
        let res = self.egraph.parser.get_program_from_string(None, input);
        self.egraph.parser.ensure_no_reserved_symbols = true;
        res.unwrap()
    }

    /// True if `sort` is one of the user-declared U-sorts we're slotting.
    fn is_u_sort(&self, sort: &str) -> bool {
        self.egraph.slotted_state.u_sorts.contains(sort)
    }

    fn handle_command(&mut self, cmd: ResolvedNCommand) -> Vec<Command> {
        match cmd {
            // User-defined eq-sort (no presort) — emit per-sort preamble.
            GenericNCommand::Sort {
                ref name,
                presort_and_args: None,
                ..
            } => {
                let mut out = vec![cmd.clone().to_command().make_unresolved()];
                let sort_name = name.clone();
                self.egraph.slotted_state.u_sorts.insert(sort_name.clone());
                out.extend(self.emit_sort_preamble(&sort_name));
                out
            }

            // Constructor declaration. If it produces a U value we may
            // rewrite its signature and emit machinery.
            GenericNCommand::Function(ref f)
                if f.subtype == crate::ast::FunctionSubtype::Constructor
                    && self.is_u_sort(&f.schema.output) =>
            {
                let name = f.name.clone();
                let inputs = f.schema.input.clone();
                let output = f.schema.output.clone();
                let u_mask: Vec<bool> = inputs.iter().map(|t| self.is_u_sort(t)).collect();
                let has_u_input = u_mask.iter().any(|b| *b);

                self.egraph
                    .slotted_state
                    .rewritten_ctors
                    .insert(name.clone(), u_mask.clone());

                if has_u_input {
                    // Compound node: emit a rewritten signature and the
                    // alpha-finder + migration + child-rewrite machinery.
                    self.emit_compound_constructor(&name, &inputs, &output, &u_mask)
                } else {
                    // Atomic-id leaf: keep the original signature; emit
                    // pair-rule + migration if it has at least one i64 arg.
                    let mut out = vec![cmd.clone().to_command().make_unresolved()];
                    if inputs.len() == 1 && inputs[0] == "i64" {
                        self.egraph.slotted_state.leaf_ctors.insert(name.clone());
                        out.extend(self.emit_leaf_machinery(&name, &inputs, &output));
                    }
                    out
                }
            }

            // Everything else: re-walk expressions to insert empty renames at
            // rewritten-constructor child positions.
            other => {
                let raw = other.to_command().make_unresolved();
                vec![self.rewrite_command(raw)]
            }
        }
    }

    /// Emit `Renaming` sort (once) plus the per-U-sort `RenamesToLeader_<S>`
    /// relation and transitivity rule. Also emits the global `slotted`
    /// ruleset on the first call.
    fn emit_sort_preamble(&mut self, sort: &str) -> Vec<Command> {
        let mut out = Vec::new();
        if !self.egraph.slotted_state.renaming_sort_emitted {
            out.extend(self.parse_program(
                "(sort Renaming (Map i64 i64))
                 (ruleset slotted)",
            ));
            self.egraph.slotted_state.renaming_sort_emitted = true;
        }
        let snippet = format!(
            "(relation RenamesToLeader_{0} ({0} {0} Renaming))
             (rule ((RenamesToLeader_{0} e1 e2 R)
                    (RenamesToLeader_{0} e2 e3 R2))
                   ((RenamesToLeader_{0} e1 e3 (compose R2 R)))
                   :ruleset slotted)",
            sort
        );
        out.extend(self.parse_program(&snippet));
        out
    }

    /// Emit the machinery for a constructor with at least one U-typed input.
    fn emit_compound_constructor(
        &mut self,
        name: &str,
        inputs: &[String],
        output: &str,
        u_mask: &[bool],
    ) -> Vec<Command> {
        // 1) New signature: insert Renaming after every U-typed input.
        let mut new_inputs: Vec<String> = Vec::new();
        for (ty, &is_u) in inputs.iter().zip(u_mask.iter()) {
            new_inputs.push(ty.clone());
            if is_u {
                new_inputs.push("Renaming".to_string());
            }
        }
        let sig_snippet = format!(
            "(constructor {} ({}) {})",
            name,
            new_inputs.join(" "),
            output
        );

        // 2) Build per-position fresh names for the alpha-finder + migration.
        // We have N total inputs; each contributes either (one slot) for non-U
        // or (eclass slot, renaming slot) for U.
        let mut e1_args = Vec::new();
        let mut e2_args = Vec::new();
        let mut mig_args = Vec::new();
        let mut e1_renamings = Vec::new();
        let mut e2_renamings = Vec::new();
        let mut mig_renamings: Vec<(String, usize)> = Vec::new();
        let mut u_positions: Vec<usize> = Vec::new();
        for (i, &is_u) in u_mask.iter().enumerate() {
            if is_u {
                let cv = format!("c{i}");
                let r1 = format!("a{i}");
                let r2 = format!("b{i}");
                let mr = format!("r{i}");
                e1_args.push(cv.clone());
                e1_args.push(r1.clone());
                e2_args.push(cv.clone());
                e2_args.push(r2.clone());
                mig_args.push(cv.clone());
                mig_args.push(mr.clone());
                e1_renamings.push(r1);
                e2_renamings.push(r2);
                mig_renamings.push((mr, i));
                u_positions.push(i);
            } else {
                let nv = format!("x{i}");
                e1_args.push(nv.clone());
                e2_args.push(nv.clone());
                mig_args.push(nv);
            }
        }

        // 3) Alpha-finder: find pairs of `name` e-nodes that share their non-U
        // children, then run find-mapping on the U-children's renamings.
        let find_mapping_args = e1_renamings
            .iter()
            .chain(e2_renamings.iter())
            .cloned()
            .collect::<Vec<_>>()
            .join(" ");
        let alpha_rule = format!(
            "(rule ((= e1 ({name} {e1}))
                    (= e2 ({name} {e2}))
                    (= rename (find-mapping {fm}))
                    (= e2 (ordering-max e1 e2)))
                   ((RenamesToLeader_{output} e2 e1 rename))
                   :ruleset slotted)",
            name = name,
            e1 = e1_args.join(" "),
            e2 = e2_args.join(" "),
            fm = find_mapping_args,
            output = output,
        );

        // 4) Migration: when RenamesToLeader_<output> e2 e1 R holds and e2 is
        // an instance of `name`, push R through every U-child rename.
        // Build migrated arg list: same as mig_args, but each rN replaced with (compose R rN).
        let mig_args_str = mig_args.join(" ");
        let mig_args_composed: Vec<String> = mig_args
            .iter()
            .map(|raw| {
                if mig_renamings.iter().any(|(rn, _)| rn == raw) {
                    format!("(compose R {raw})")
                } else {
                    raw.clone()
                }
            })
            .collect();
        let migration_rule = format!(
            "(rule ((RenamesToLeader_{output} e2 e1 R)
                    (= e2 ({name} {orig}))
                    (!= e1 e2))
                   ((union e2 ({name} {composed}))
                    (delete ({name} {orig})))
                   :ruleset slotted)",
            output = output,
            name = name,
            orig = mig_args_str,
            composed = mig_args_composed.join(" "),
        );

        // 5) Child-rewrite rules: one per U-position. When a child c has a
        // RenamesToLeader entry pointing to leader c', rewrite this App to
        // use c' instead, composing R^-1 into that position's edge rename.
        // Without these rules, find-mapping bails on key-set mismatches
        // between alpha-equivalent Apps (different child variables → different
        // rename keys).
        let mut child_rules = Vec::new();
        for &pos in &u_positions {
            let cv = format!("c{pos}");
            let rv = format!("r{pos}");
            let lhs_args: Vec<String> = mig_args
                .iter()
                .map(|s| {
                    if s == &cv {
                        "c".to_string()
                    } else if s == &rv {
                        "r".to_string()
                    } else {
                        s.clone()
                    }
                })
                .collect();
            let rhs_args: Vec<String> = mig_args
                .iter()
                .map(|s| {
                    if s == &cv {
                        "c'".to_string()
                    } else if s == &rv {
                        "(compose r (inverse R))".to_string()
                    } else {
                        s.clone()
                    }
                })
                .collect();
            let rule = format!(
                "(rule ((RenamesToLeader_{output} c c' R)
                        (= node ({name} {lhs}))
                        (!= c c'))
                       ((union node ({name} {rhs})))
                       :ruleset slotted)",
                output = output,
                name = name,
                lhs = lhs_args.join(" "),
                rhs = rhs_args.join(" "),
            );
            child_rules.push(rule);
        }

        let everything = format!(
            "{sig}\n{alpha}\n{migration}\n{children}",
            sig = sig_snippet,
            alpha = alpha_rule,
            migration = migration_rule,
            children = child_rules.join("\n"),
        );
        self.parse_program(&everything)
    }

    /// Emit the pair rule and migration rule for an atomic-id leaf
    /// (a constructor like `Var` whose only inputs are non-U slot ids).
    fn emit_leaf_machinery(
        &mut self,
        name: &str,
        inputs: &[String],
        output: &str,
    ) -> Vec<Command> {
        // Restricted to single-i64 leaves for the first cut. Multi-arg leaves
        // would generalize by combining the args into one Renaming map.
        if inputs.len() != 1 || inputs[0] != "i64" {
            return vec![];
        }
        // Leaf machinery: just the pair rule. With maintenance running
        // between user commands, we want each leaf class to keep its
        // identity so that child-rewrite has persistent `c != c'`
        // RenamesToLeader entries to fire on. Merging leaf classes in a
        // dedicated migration would consume those entries before any
        // surrounding compound was even emitted. Users probing
        // `(check (= ({name} a) ({name} b)))` should go through
        // let-bindings or `RenamesToLeader_{output}` directly.
        let snippet = format!(
            "(rule ((= e1 ({name} id1))
                    (= e2 ({name} id2))
                    (!= id1 id2)
                    (= e2 (ordering-max e1 e2)))
                   ((RenamesToLeader_{output} e2 e1
                       (map-insert (map-empty) id2 id1)))
                   :ruleset slotted)",
            name = name,
            output = output,
        );
        self.parse_program(&snippet)
    }

    /// Walk a (now-unresolved) `Command` and rewrite every call to a
    /// rewritten constructor by threading edge renames inferred from the
    /// expression's outer-slot structure.
    fn rewrite_command(&mut self, cmd: Command) -> Command {
        use crate::ast::GenericCommand::*;
        match cmd {
            Action(action) => Action(self.rewrite_action(action)),
            Check(span, facts) => Check(
                span,
                facts.into_iter().map(|f| self.rewrite_fact(f)).collect(),
            ),
            Extract(span, e1, e2) => {
                Extract(span, self.rewrite_expr(e1), self.rewrite_expr(e2))
            }
            Fail(span, inner) => Fail(span, Box::new(self.rewrite_command(*inner))),
            Output { span, file, exprs } => Output {
                span,
                file,
                exprs: exprs.into_iter().map(|e| self.rewrite_expr(e)).collect(),
            },
            Rule { rule } => Rule {
                rule: self.rewrite_user_rule(rule),
            },
            RunSchedule(schedule) => {
                // Mirror proof_encoding: wrap each `(run ...)` inside the
                // schedule tree so that `(saturate slotted)` runs after
                // every iteration. This keeps the slotted ruleset current
                // with state produced inside long user runs, not just
                // between top-level commands.
                RunSchedule(self.instrument_schedule(schedule))
            }
            other => other,
        }
    }

    fn instrument_schedule(
        &mut self,
        schedule: crate::ast::Schedule,
    ) -> crate::ast::Schedule {
        use crate::ast::GenericSchedule::*;
        match schedule {
            Run(span, config) => {
                let saturate = self.saturate_slotted(span.clone());
                Sequence(span.clone(), vec![Run(span, config), saturate])
            }
            Saturate(span, inner) => {
                Saturate(span, Box::new(self.instrument_schedule(*inner)))
            }
            Repeat(span, n, inner) => {
                Repeat(span, n, Box::new(self.instrument_schedule(*inner)))
            }
            Sequence(span, items) => Sequence(
                span,
                items
                    .into_iter()
                    .map(|s| self.instrument_schedule(s))
                    .collect(),
            ),
        }
    }

    /// Returns a `(saturate slotted)` schedule fragment.
    fn saturate_slotted(&mut self, span: Span) -> crate::ast::Schedule {
        use crate::ast::GenericSchedule::*;
        Saturate(
            span.clone(),
            Box::new(Run(
                span,
                crate::ast::GenericRunConfig {
                    ruleset: "slotted".to_string(),
                    until: None,
                },
            )),
        )
    }

    fn rewrite_fact(&mut self, fact: crate::ast::Fact) -> crate::ast::Fact {
        use crate::ast::GenericFact::*;
        match fact {
            Eq(span, lhs, rhs) => Eq(span, self.rewrite_expr(lhs), self.rewrite_expr(rhs)),
            Fact(e) => Fact(self.rewrite_expr(e)),
        }
    }

    fn rewrite_action(&mut self, action: crate::ast::Action) -> crate::ast::Action {
        use egglog_ast::generic_ast::GenericAction::*;
        match action {
            Union(span, lhs, rhs) => {
                Union(span, self.rewrite_expr(lhs), self.rewrite_expr(rhs))
            }
            Let(span, v, e) => {
                let (rewritten, slots) = self.rewrite_expr_with_slots(e);
                if !slots.is_empty() {
                    self.egraph
                        .slotted_state
                        .let_outer_slots
                        .insert(v.clone(), slots);
                }
                Let(span, v, rewritten)
            }
            Set(span, head, args, val) => {
                let (rewritten_val, slots) = self.rewrite_expr_with_slots(val);
                // `(set (head) val)` with no args is the desugared form of a
                // top-level `(let head ...)`. Record head's outer slots so
                // later expressions referencing `(head)` can use them.
                if args.is_empty() && !slots.is_empty() {
                    self.egraph
                        .slotted_state
                        .let_outer_slots
                        .insert(head.clone(), slots);
                }
                Set(
                    span,
                    head,
                    args.into_iter().map(|a| self.rewrite_expr(a)).collect(),
                    rewritten_val,
                )
            }
            Change(span, change, head, args) => Change(
                span,
                change,
                head,
                args.into_iter().map(|a| self.rewrite_expr(a)).collect(),
            ),
            Expr(span, e) => Expr(span, self.rewrite_expr(e)),
            Panic(span, msg) => Panic(span, msg),
        }
    }

    fn rewrite_expr(&self, expr: Expr) -> Expr {
        let (rewritten, _slots) = self.rewrite_expr_with_slots(expr);
        rewritten
    }

    /// Rewrite a user-written rule for the slotted encoding.
    ///
    /// **Body**: every U-typed child of a rewritten constructor gets a fresh
    /// edge-rename pattern variable. As we descend into compound calls, we
    /// accumulate the *path* of edge renames from outermost atom to current
    /// position via `compose`. Each user variable at a U-child position
    /// records the path it was reached by.
    ///
    /// **Equality constraints**: when a variable is reached via multiple
    /// paths in the body (multiple body atoms or multiple positions within an
    /// atom), the paths must all describe the same effective slot view. We
    /// emit `(= path_i path_j)` constraints between pairs.
    ///
    /// **Action**: when an action constructs a term, each user-variable
    /// U-child reuses the variable's first body path as its edge rename.
    /// Variables that don't appear as U-children in the body (e.g.,
    /// matched as a constructor head only) fall back to `(map-empty)`.
    fn rewrite_user_rule(
        &mut self,
        rule: crate::ast::GenericRule<String, String>,
    ) -> crate::ast::GenericRule<String, String> {
        let mut var_paths: HashMap<String, Vec<Expr>> = HashMap::default();
        // Variables matched as constructor heads in the body. Each head match
        // contributes its body-bound child rename names; the variable's
        // *slot space* is the union of values across these renames, and its
        // identity rename is identity over that slot space.
        let mut head_renames: HashMap<String, Vec<String>> = HashMap::default();
        let mut new_body: Vec<crate::ast::Fact> = rule
            .body
            .into_iter()
            .map(|f| self.rewrite_body_fact(f, &mut var_paths, &mut head_renames))
            .collect();
        // Add equality constraints between pairs of paths for variables
        // observed at multiple positions.
        for paths in var_paths.values() {
            for window in paths.windows(2) {
                new_body.push(crate::ast::GenericFact::Eq(
                    rule.span.clone(),
                    window[0].clone(),
                    window[1].clone(),
                ));
            }
        }
        // For action use: pick each variable's first observed path. For
        // variables that have *only* head matches (no path), synthesize the
        // identity rename over the union of body-bound rename value-sets.
        let mut var_to_path: HashMap<String, Expr> = var_paths
            .into_iter()
            .filter_map(|(v, mut paths)| paths.drain(..).next().map(|p| (v, p)))
            .collect();
        for (var, renames) in &head_renames {
            if var_to_path.contains_key(var) {
                continue;
            }
            if let Some(id_expr) = synthesize_identity(rule.span.clone(), renames) {
                var_to_path.insert(var.clone(), id_expr);
            }
        }
        let new_head: Vec<crate::ast::Action> = rule
            .head
            .0
            .into_iter()
            .map(|a| self.rewrite_action_with_paths(a, &var_to_path))
            .collect();
        crate::ast::GenericRule {
            span: rule.span,
            head: crate::ast::GenericActions(new_head),
            body: new_body,
            name: rule.name,
            ruleset: rule.ruleset,
        }
    }

    fn fresh_rename_var(&mut self) -> String {
        self.egraph.parser.symbol_gen.fresh("r_slotted")
    }
}

/// Build the path that descends into a child: if `outer` is `None`, the
/// child's path is just `inner`; otherwise it's `(compose outer inner)`.
fn compose_path(span: Span, outer: Option<Expr>, inner: Expr) -> Expr {
    match outer {
        None => inner,
        Some(o) => GenericExpr::Call(span, "compose".to_string(), vec![o, inner]),
    }
}

/// Synthesize an identity rename over the union of the value-sets of the
/// given body-bound rename variables. For one rename `r`, that's
/// `(compose r (inverse r))` (identity over `values(r)`); for several, we
/// fold via `(map-union ...)`.
///
/// Returns `None` if the rename list is empty (caller falls back to
/// `(map-empty)`).
fn synthesize_identity(span: Span, renames: &[String]) -> Option<Expr> {
    let mut iter = renames.iter();
    let first = iter.next()?;
    let mut acc = id_on_values(span.clone(), first);
    for r in iter {
        acc = GenericExpr::Call(
            span.clone(),
            "map-union".to_string(),
            vec![acc, id_on_values(span.clone(), r)],
        );
    }
    Some(acc)
}

/// `compose r (inverse r)` — identity over `values(r)`.
fn id_on_values(span: Span, rename_var: &str) -> Expr {
    let r = GenericExpr::Var(span.clone(), rename_var.to_string());
    let inv_r = GenericExpr::Call(span.clone(), "inverse".to_string(), vec![r.clone()]);
    GenericExpr::Call(span, "compose".to_string(), vec![r, inv_r])
}

/// `(map-insert (map-empty) k k)` — identity at a single literal slot.
fn identity_at(span: Span, k: i64) -> Expr {
    GenericExpr::Call(
        span.clone(),
        "map-insert".to_string(),
        vec![
            GenericExpr::Call(span.clone(), "map-empty".to_string(), Vec::new()),
            GenericExpr::Lit(span.clone(), Literal::Int(k)),
            GenericExpr::Lit(span, Literal::Int(k)),
        ],
    )
}

/// Like `synthesize_identity` but takes a slice of arbitrary edge-rename
/// `Expr`s instead of body-bound rename variable names. Returns identity
/// over the union of each edge's value-set, built as
/// `(map-union (compose e1 (inverse e1)) (compose e2 (inverse e2)) ...)`.
/// Returns `None` if the slice is empty.
fn synthesize_identity_from_exprs(span: Span, edges: &[Expr]) -> Option<Expr> {
    let mut iter = edges.iter();
    let first = iter.next()?;
    let mut acc = id_on_values_expr(span.clone(), first.clone());
    for e in iter {
        acc = GenericExpr::Call(
            span.clone(),
            "map-union".to_string(),
            vec![acc, id_on_values_expr(span.clone(), e.clone())],
        );
    }
    Some(acc)
}

/// `compose e (inverse e)` — identity over `values(e)`, generalized over
/// arbitrary `Expr` (not just a variable name like [`id_on_values`]).
fn id_on_values_expr(span: Span, edge: Expr) -> Expr {
    let inv = GenericExpr::Call(span.clone(), "inverse".to_string(), vec![edge.clone()]);
    GenericExpr::Call(span, "compose".to_string(), vec![edge, inv])
}

impl<'a> SlottedInstrumentor<'a> {

    fn rewrite_body_fact(
        &mut self,
        fact: crate::ast::Fact,
        var_paths: &mut HashMap<String, Vec<Expr>>,
        head_renames: &mut HashMap<String, Vec<String>>,
    ) -> crate::ast::Fact {
        use crate::ast::GenericFact::*;
        match fact {
            Eq(span, lhs, rhs) => {
                // Detect head matches: `(= var Call)` or `(= Call var)`,
                // where `Call` is a rewritten constructor. The Var is then
                // matched as the head e-class of that Call, and its slot
                // space is determined by the Call's child renames.
                let head_for_rhs = match (&lhs, &rhs) {
                    (GenericExpr::Var(_, name), GenericExpr::Call(_, ch, _))
                        if self
                            .egraph
                            .slotted_state
                            .rewritten_ctors
                            .contains_key(ch) =>
                    {
                        Some(name.clone())
                    }
                    _ => None,
                };
                let head_for_lhs = match (&lhs, &rhs) {
                    (GenericExpr::Call(_, ch, _), GenericExpr::Var(_, name))
                        if self
                            .egraph
                            .slotted_state
                            .rewritten_ctors
                            .contains_key(ch) =>
                    {
                        Some(name.clone())
                    }
                    _ => None,
                };
                Eq(
                    span,
                    self.rewrite_body_expr(
                        lhs,
                        None,
                        head_for_lhs.as_deref(),
                        var_paths,
                        head_renames,
                    ),
                    self.rewrite_body_expr(
                        rhs,
                        None,
                        head_for_rhs.as_deref(),
                        var_paths,
                        head_renames,
                    ),
                )
            }
            Fact(e) => Fact(self.rewrite_body_expr(e, None, None, var_paths, head_renames)),
        }
    }

    /// Walk a body expression, inserting fresh edge-rename pattern variables
    /// at U-child positions of rewritten constructors. `current_path` is the
    /// composed edge rename from the outermost atom to the current position
    /// (or `None` if we're still at the top level).
    ///
    /// At each user variable, the *current_path* is the variable's effective
    /// edge-rename for this occurrence. Recorded into `var_paths`.
    fn rewrite_body_expr(
        &mut self,
        expr: Expr,
        current_path: Option<Expr>,
        head_var: Option<&str>,
        var_paths: &mut HashMap<String, Vec<Expr>>,
        head_renames: &mut HashMap<String, Vec<String>>,
    ) -> Expr {
        match expr {
            GenericExpr::Var(span, v) => {
                if let Some(path) = current_path {
                    var_paths.entry(v.clone()).or_default().push(path);
                }
                GenericExpr::Var(span, v)
            }
            GenericExpr::Lit(span, lit) => GenericExpr::Lit(span, lit),
            GenericExpr::Call(span, head, args) => {
                if let Some(mask) = self
                    .egraph
                    .slotted_state
                    .rewritten_ctors
                    .get(&head)
                    .cloned()
                {
                    let mut new_args: Vec<Expr> = Vec::with_capacity(args.len() * 2);
                    let mut this_call_renames: Vec<String> = Vec::new();
                    for (arg, &is_u) in args.into_iter().zip(mask.iter()) {
                        if is_u {
                            // Generate a fresh edge-rename pattern variable
                            // for this U-child position.
                            let fresh = self.fresh_rename_var();
                            this_call_renames.push(fresh.clone());
                            let fresh_var = GenericExpr::Var(span.clone(), fresh);
                            // Build the path that descends into this child.
                            let child_path = compose_path(
                                span.clone(),
                                current_path.clone(),
                                fresh_var.clone(),
                            );
                            // Children are not heads of this call; clear head_var.
                            let new_arg = self.rewrite_body_expr(
                                arg,
                                Some(child_path),
                                None,
                                var_paths,
                                head_renames,
                            );
                            new_args.push(new_arg);
                            new_args.push(fresh_var);
                        } else {
                            // Non-U-typed child: recurse without changing the
                            // path (since the rename concept doesn't apply).
                            let new_arg = self.rewrite_body_expr(
                                arg,
                                current_path.clone(),
                                None,
                                var_paths,
                                head_renames,
                            );
                            new_args.push(new_arg);
                        }
                    }
                    // Record this call's child rename names against the head
                    // variable, if there was one.
                    if let Some(hv) = head_var {
                        head_renames
                            .entry(hv.to_string())
                            .or_default()
                            .extend(this_call_renames);
                    }
                    GenericExpr::Call(span, head, new_args)
                } else {
                    let new_args: Vec<Expr> = args
                        .into_iter()
                        .map(|a| {
                            self.rewrite_body_expr(
                                a,
                                current_path.clone(),
                                None,
                                var_paths,
                                head_renames,
                            )
                        })
                        .collect();
                    GenericExpr::Call(span, head, new_args)
                }
            }
        }
    }

    fn rewrite_action_with_paths(
        &mut self,
        action: crate::ast::Action,
        var_to_path: &HashMap<String, Expr>,
    ) -> crate::ast::Action {
        use egglog_ast::generic_ast::GenericAction::*;
        match action {
            Union(span, lhs, rhs) => Union(
                span,
                self.rewrite_action_expr(lhs, var_to_path),
                self.rewrite_action_expr(rhs, var_to_path),
            ),
            Let(span, v, e) => Let(span, v, self.rewrite_action_expr(e, var_to_path)),
            Set(span, head, args, val) => Set(
                span,
                head,
                args.into_iter()
                    .map(|a| self.rewrite_action_expr(a, var_to_path))
                    .collect(),
                self.rewrite_action_expr(val, var_to_path),
            ),
            Change(span, change, head, args) => Change(
                span,
                change,
                head,
                args.into_iter()
                    .map(|a| self.rewrite_action_expr(a, var_to_path))
                    .collect(),
            ),
            Expr(span, e) => Expr(span, self.rewrite_action_expr(e, var_to_path)),
            Panic(span, msg) => Panic(span, msg),
        }
    }

    fn rewrite_action_expr(
        &self,
        expr: Expr,
        var_to_path: &HashMap<String, Expr>,
    ) -> Expr {
        let (rewritten, _outgoing) = self.rewrite_action_expr_with_outgoing(expr, var_to_path);
        rewritten
    }

    /// Rewrite an action expression and return both:
    /// - the rewritten `Expr`, and
    /// - an `Option<Expr>` for the term's *outgoing rename*: a Map
    ///   expression that, at runtime, evaluates to the rename used at this
    ///   term's edge position when it sits as a U-child of some parent.
    ///
    /// Synthesis follows the runtime, no-canonical-assumption shape laid
    /// out in `slotted_encoding_examples.md`:
    ///
    /// - **User variable with a body path**: outgoing = the path.
    /// - **Literal atomic-id leaf** like `(Var k)` with `k: Lit::Int`:
    ///   outgoing = `(map-insert (map-empty) k k)` — identity at slot `k`.
    /// - **Nested rewritten compound**: outgoing = identity over the union
    ///   of values across the inner edges, computed via `map-union` of
    ///   `compose-inverse` chains over each U-child's own outgoing rename.
    /// - Anything else: `None` (no outgoing). Caller falls back to
    ///   `(map-empty)` when an edge rename is needed.
    fn rewrite_action_expr_with_outgoing(
        &self,
        expr: Expr,
        var_to_path: &HashMap<String, Expr>,
    ) -> (Expr, Option<Expr>) {
        match expr {
            GenericExpr::Var(span, v) => {
                let outgoing = var_to_path.get(&v).cloned();
                (GenericExpr::Var(span, v), outgoing)
            }
            GenericExpr::Lit(span, lit) => (GenericExpr::Lit(span, lit), None),
            GenericExpr::Call(span, head, args) => {
                // Atomic-id leaf with a literal i64 arg: outgoing rename is
                // identity at the literal slot.
                if self.egraph.slotted_state.leaf_ctors.contains(&head) {
                    if let Some(GenericExpr::Lit(_, Literal::Int(n))) = args.first() {
                        let outgoing = identity_at(span.clone(), *n);
                        return (
                            GenericExpr::Call(span, head, args),
                            Some(outgoing),
                        );
                    }
                }

                if let Some(mask) = self
                    .egraph
                    .slotted_state
                    .rewritten_ctors
                    .get(&head)
                    .cloned()
                {
                    let mut new_args: Vec<Expr> = Vec::with_capacity(args.len() * 2);
                    let mut child_outgoings: Vec<Expr> = Vec::new();
                    for (arg, &is_u) in args.into_iter().zip(mask.iter()) {
                        let (rewritten_arg, child_outgoing) =
                            self.rewrite_action_expr_with_outgoing(arg, var_to_path);
                        if is_u {
                            // Edge rename at this position = child's
                            // outgoing rename. If the child has none (e.g.
                            // unrecognised non-leaf call), fall back to an
                            // empty map.
                            let edge = child_outgoing.clone().unwrap_or_else(|| {
                                GenericExpr::Call(
                                    span.clone(),
                                    "map-empty".to_string(),
                                    Vec::new(),
                                )
                            });
                            new_args.push(rewritten_arg);
                            new_args.push(edge);
                            if let Some(out) = child_outgoing {
                                child_outgoings.push(out);
                            }
                        } else {
                            new_args.push(rewritten_arg);
                        }
                    }
                    // The compound's own outgoing rename = identity over
                    // the union of values across all its U-edge renames.
                    let outgoing = synthesize_identity_from_exprs(span.clone(), &child_outgoings);
                    (GenericExpr::Call(span, head, new_args), outgoing)
                } else {
                    let new_args: Vec<Expr> = args
                        .into_iter()
                        .map(|a| self.rewrite_action_expr(a, var_to_path))
                        .collect();
                    (GenericExpr::Call(span, head, new_args), None)
                }
            }
        }
    }

    /// Rewrite an expression, inserting edge renames that reflect inferred
    /// slot identities, and return the expression's outer-slot list.
    ///
    /// The inferred outer-slot list for an atomic-id leaf with literal arg
    /// `n` is `[n]`. For a let-binding reference, it's the stored list. For a
    /// compound application, it's `[0, 1, ..., k-1]` where k is the number of
    /// distinct outer slots its U-typed children reference (canonicalized).
    fn rewrite_expr_with_slots(&self, expr: Expr) -> (Expr, Vec<i64>) {
        match expr {
            GenericExpr::Var(span, v) => (GenericExpr::Var(span, v), Vec::new()),
            GenericExpr::Lit(span, lit) => (GenericExpr::Lit(span, lit), Vec::new()),
            GenericExpr::Call(span, head, args) => {
                // Atomic-id leaf with a literal i64 arg: outer slot = [arg].
                if self.egraph.slotted_state.leaf_ctors.contains(&head) {
                    let leaf_slot = match args.first() {
                        Some(GenericExpr::Lit(_, Literal::Int(n))) => Some(*n),
                        _ => None,
                    };
                    if let Some(n) = leaf_slot {
                        return (GenericExpr::Call(span, head, args), vec![n]);
                    }
                }

                // No-arg call to a let binding we've slot-inferred before.
                if args.is_empty() {
                    if let Some(slots) =
                        self.egraph.slotted_state.let_outer_slots.get(&head)
                    {
                        return (
                            GenericExpr::Call(span, head, Vec::new()),
                            slots.clone(),
                        );
                    }
                }

                // Compound constructor we rewrote: do slot inference.
                if let Some(mask) =
                    self.egraph.slotted_state.rewritten_ctors.get(&head).cloned()
                {
                    return self.rewrite_compound_call(span, head, args, &mask);
                }

                // Otherwise pass through.
                let rewritten_args: Vec<Expr> = args
                    .into_iter()
                    .map(|a| self.rewrite_expr_with_slots(a).0)
                    .collect();
                (GenericExpr::Call(span, head, rewritten_args), Vec::new())
            }
        }
    }

    /// Rewrite a call to a compound (rewritten) constructor.
    ///
    /// Each U-typed child gets an **identity-at-its-slots** edge rename:
    /// for child slot list `[s_1, ..., s_k]`, the edge rename is
    /// `(map-insert ... (map-empty) s_i s_i)`. The compound's own outer
    /// slot list is the deduped union of its U-children's slot lists.
    ///
    /// This identity-at-literal convention matches the action-side
    /// synthesis used in `rewrite_action_expr_with_outgoing` (literal
    /// leaves emit `(map-insert (map-empty) k k)`, nested compounds emit
    /// the `map-union (compose r (inverse r)) ...` chain). Top-level and
    /// action-side stay consistent so the same user term encodes to the
    /// same e-class regardless of where it appears.
    fn rewrite_compound_call(
        &self,
        span: Span,
        head: String,
        args: Vec<Expr>,
        mask: &[bool],
    ) -> (Expr, Vec<i64>) {
        // First pass: rewrite children, collecting their outer slots.
        let mut child_results: Vec<(Expr, Vec<i64>)> = Vec::with_capacity(args.len());
        for arg in args {
            child_results.push(self.rewrite_expr_with_slots(arg));
        }

        // The compound's own outer slot list = deduped union of U-children's
        // slot lists in encounter order.
        let mut seen: HashSet<i64> = HashSet::default();
        let mut outer_slots: Vec<i64> = Vec::new();
        for ((_child_expr, child_slots), &is_u) in
            child_results.iter().zip(mask.iter())
        {
            if !is_u {
                continue;
            }
            for &s in child_slots {
                if seen.insert(s) {
                    outer_slots.push(s);
                }
            }
        }

        // Build the rewritten arg list, inserting an identity-at-slots edge
        // rename after each U-typed child.
        let mut new_args: Vec<Expr> = Vec::with_capacity(child_results.len() * 2);
        for ((child_expr, child_slots), &is_u) in
            child_results.into_iter().zip(mask.iter())
        {
            new_args.push(child_expr);
            if !is_u {
                continue;
            }
            let mut rename_expr = GenericExpr::Call(
                span.clone(),
                "map-empty".to_string(),
                Vec::new(),
            );
            for s in &child_slots {
                rename_expr = GenericExpr::Call(
                    span.clone(),
                    "map-insert".to_string(),
                    vec![
                        rename_expr,
                        GenericExpr::Lit(span.clone(), Literal::Int(*s)),
                        GenericExpr::Lit(span.clone(), Literal::Int(*s)),
                    ],
                );
            }
            new_args.push(rename_expr);
        }

        (
            GenericExpr::Call(span, head, new_args),
            outer_slots,
        )
    }
}
