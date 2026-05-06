#![doc = include_str!("slotted_encoding.md")]

use egglog_ast::generic_ast::GenericExpr;

use crate::{
    EGraph,
    ast::{Command, Expr, GenericNCommand, ResolvedNCommand},
    util::{HashMap, HashSet},
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
            // Decide whether the input command warrants a maintenance run
            // afterwards. Mirroring proof_encoding.rs:1313–1324, we skip
            // Function (lets/relations etc.), NormRule, and Sort — those
            // change schema only, not e-graph data.
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
                    if inputs.iter().any(|t| t == "i64") {
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
                   ((union e2 ({name} {composed})))
                   :ruleset slotted)",
            output = output,
            name = name,
            orig = mig_args_str,
            composed = mig_args_composed.join(" "),
        );

        // Child-rewrite rules are intentionally omitted from the first cut.
        // They introduce orbit-variant App e-nodes whenever a U-child has a
        // self-loop RenamesToLeader entry (e.g., right after Var migration
        // makes (Var 20) and (Var 1) share a class), and the variants don't
        // always merge back via the simpler `find-mapping`-based migration.
        // For slotted-test-1, congruence after Var migration is enough to
        // unify alpha-equivalent Apps directly. We can re-add them once the
        // migration pipeline reliably collapses the orbit.

        let everything = format!(
            "{sig}\n{alpha}\n{migration}",
            sig = sig_snippet,
            alpha = alpha_rule,
            migration = migration_rule,
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
        // Note: no `delete` in the migration. Deleting the source e-node
        // would make later `(check (= (... id) (... id')))` queries fail
        // because one of the constructor applications would no longer exist
        // in the e-graph. Redundancy pruning belongs to a later milestone.
        let snippet = format!(
            "(rule ((= e1 ({name} id1))
                    (= e2 ({name} id2))
                    (!= id1 id2)
                    (= e2 (ordering-max e1 e2)))
                   ((RenamesToLeader_{output} e2 e1
                       (map-insert (map-empty) id2 id1)))
                   :ruleset slotted)
             (rule ((RenamesToLeader_{output} e2 e1 R)
                    (= e2 ({name} id))
                    (= new_id (map-get R id))
                    (!= e1 e2))
                   ((union e2 ({name} new_id)))
                   :ruleset slotted)",
            name = name,
            output = output,
        );
        self.parse_program(&snippet)
    }

    /// Walk a (now-unresolved) `Command` and rewrite every call to a
    /// rewritten constructor by inserting `(map-empty)` after each U-typed
    /// argument.
    fn rewrite_command(&self, cmd: Command) -> Command {
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
                rule: crate::ast::GenericRule {
                    span: rule.span,
                    head: crate::ast::GenericActions(
                        rule.head
                            .0
                            .into_iter()
                            .map(|a| self.rewrite_action(a))
                            .collect(),
                    ),
                    body: rule
                        .body
                        .into_iter()
                        .map(|f| self.rewrite_fact(f))
                        .collect(),
                    name: rule.name,
                    ruleset: rule.ruleset,
                },
            },
            other => other,
        }
    }

    fn rewrite_fact(&self, fact: crate::ast::Fact) -> crate::ast::Fact {
        use crate::ast::GenericFact::*;
        match fact {
            Eq(span, lhs, rhs) => Eq(span, self.rewrite_expr(lhs), self.rewrite_expr(rhs)),
            Fact(e) => Fact(self.rewrite_expr(e)),
        }
    }

    fn rewrite_action(&self, action: crate::ast::Action) -> crate::ast::Action {
        use egglog_ast::generic_ast::GenericAction::*;
        match action {
            Union(span, lhs, rhs) => {
                Union(span, self.rewrite_expr(lhs), self.rewrite_expr(rhs))
            }
            Let(span, v, e) => Let(span, v, self.rewrite_expr(e)),
            Set(span, head, args, val) => Set(
                span,
                head,
                args.into_iter().map(|a| self.rewrite_expr(a)).collect(),
                self.rewrite_expr(val),
            ),
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
        match expr {
            GenericExpr::Var(span, v) => GenericExpr::Var(span, v),
            GenericExpr::Lit(span, lit) => GenericExpr::Lit(span, lit),
            GenericExpr::Call(span, head, args) => {
                let rewritten_args: Vec<Expr> = args
                    .into_iter()
                    .map(|a| self.rewrite_expr(a))
                    .collect();
                if let Some(mask) = self.egraph.slotted_state.rewritten_ctors.get(&head) {
                    // Insert (map-empty) after each U-typed argument position.
                    let mut new_args: Vec<Expr> = Vec::with_capacity(rewritten_args.len() * 2);
                    for (a, &is_u) in rewritten_args.into_iter().zip(mask.iter()) {
                        new_args.push(a);
                        if is_u {
                            new_args.push(GenericExpr::Call(
                                span.clone(),
                                "map-empty".to_string(),
                                vec![],
                            ));
                        }
                    }
                    GenericExpr::Call(span, head, new_args)
                } else {
                    GenericExpr::Call(span, head, rewritten_args)
                }
            }
        }
    }
}
