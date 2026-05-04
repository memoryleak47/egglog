use egglog_bridge::UnionAction;
use std::any::TypeId;
use std::iter::zip;
use crate::constraint::AllEqualTypeConstraint;

use super::*;

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct VecContainer {
    pub do_rebuild: bool,
    pub data: Vec<Value>,
}

impl ContainerValue for VecContainer {
    fn rebuild_contents(&mut self, rebuilder: &dyn Rebuilder) -> bool {
        if self.do_rebuild {
            rebuilder.rebuild_slice(&mut self.data)
        } else {
            false
        }
    }
    fn iter(&self) -> impl Iterator<Item = Value> + '_ {
        self.data.iter().copied()
    }
}

#[derive(Clone, Debug)]
pub struct VecSort {
    name: String,
    element: ArcSort,
}

impl VecSort {
    pub fn element(&self) -> ArcSort {
        self.element.clone()
    }
}

impl Presort for VecSort {
    fn presort_name() -> &'static str {
        "Vec"
    }

    fn reserved_primitives() -> Vec<&'static str> {
        vec![
            "vec-of",
            "vec-append",
            "vec-empty",
            "vec-push",
            "vec-pop",
            "vec-not-contains",
            "vec-contains",
            "vec-length",
            "vec-get",
            "vec-set",
            "vec-remove",
            "vec-union",
            "vec-range",
            "unstable-vec-map",
        ]
    }

    fn make_sort(
        typeinfo: &mut TypeInfo,
        name: String,
        args: &[Expr],
    ) -> Result<ArcSort, TypeError> {
        if let [Expr::Var(span, e)] = args {
            let e = typeinfo
                .get_sort_by_name(e)
                .ok_or(TypeError::UndefinedSort(e.clone(), span.clone()))?;

            let out = Self {
                name,
                element: e.clone(),
            };
            Ok(out.to_arcsort())
        } else {
            panic!("Vec sort must have sort as argument. Got {args:?}")
        }
    }
}

impl ContainerSort for VecSort {
    type Container = VecContainer;

    fn name(&self) -> &str {
        &self.name
    }

    fn inner_sorts(&self) -> Vec<ArcSort> {
        vec![self.element.clone()]
    }

    fn is_eq_container_sort(&self) -> bool {
        self.element.is_eq_sort() || self.element.is_eq_container_sort()
    }

    fn inner_values(
        &self,
        container_values: &ContainerValues,
        value: Value,
    ) -> Vec<(ArcSort, Value)> {
        let val = container_values
            .get_val::<VecContainer>(value)
            .unwrap()
            .clone();
        val.data
            .iter()
            .map(|e| (self.element.clone(), *e))
            .collect()
    }

    fn register_primitives(&self, eg: &mut EGraph) {
        let arc: Arc<dyn Sort> = self.clone().to_arcsort();

        add_primitive!(eg, "vec-empty"  = {self.clone(): VecSort} |                                | -> @VecContainer (arc) { VecContainer {
            do_rebuild: self.ctx.is_eq_container_sort(),
            data: Vec::new()
        } });
        add_primitive!(eg, "vec-of"     = {self.clone(): VecSort} [xs: # (self.element())          ] -> @VecContainer (arc) { VecContainer {
            do_rebuild: self.ctx.is_eq_container_sort(),
            data: xs                     .collect()
        } });
        add_primitive!(eg, "vec-append" = {self.clone(): VecSort} [xs: @VecContainer (arc)] -> @VecContainer (arc) { VecContainer {
            do_rebuild: self.ctx.is_eq_container_sort(),
            data: xs.flat_map(|x| x.data).collect()
        } });

        add_primitive!(eg, "vec-push" = |mut xs: @VecContainer (arc), x: # (self.element())| -> @VecContainer (arc) {{ xs.data.push(x); xs }});
        add_primitive!(eg, "vec-pop"  = |mut xs: @VecContainer (arc)                       | -> @VecContainer (arc) {{ xs.data.pop();   xs }});

        add_primitive!(eg, "vec-length"       = |xs: @VecContainer (arc)| -> i64 { xs.data.len() as i64 });
        add_primitive!(eg, "vec-contains"     = |xs: @VecContainer (arc), x: # (self.element())| -?> () { ( xs.data.contains(&x)).then_some(()) });
        add_primitive!(eg, "vec-not-contains" = |xs: @VecContainer (arc), x: # (self.element())| -?> () { (!xs.data.contains(&x)).then_some(()) });

        add_primitive!(eg, "vec-get"    = |    xs: @VecContainer (arc), i: i64                       | -?> # (self.element()) { xs.data.get(i as usize).copied() });
        add_primitive!(eg, "vec-set"    = |mut xs: @VecContainer (arc), i: i64, x: # (self.element())| -> @VecContainer (arc) {{ xs.data[i as usize] = x;    xs }});
        add_primitive!(eg, "vec-remove" = |mut xs: @VecContainer (arc), i: i64                       | -> @VecContainer (arc) {{ xs.data.remove(i as usize); xs }});
        if self.element.is_eq_sort() {
            eg.add_primitive(Union {
                name: "vec-union".into(),
                vec: arc.clone(),
                action: eg.new_union_action(),
            });
        }
        // vec-range
        if self.element.name() == "i64" {
            add_primitive!(eg, "vec-range" = {self.clone(): VecSort} |end: i64| -> @VecContainer (arc) { VecContainer {
                do_rebuild: self.ctx.is_eq_container_sort(),
                data: {
                    let end: usize = end.try_into().unwrap_or(0);
                    (0..end)
                        .map(|i| exec_state.base_values().get::<i64>(i as i64))
                        .collect()
                }
            } });
        }
        let all_vec_sorts = eg
            .type_info
            .get_arcsorts_by(|f| f.value_type() == Some(TypeId::of::<VecContainer>()));
        for fn_sort in eg.type_info.get_sorts::<FunctionSort>() {
            for vec_sort in &all_vec_sorts {
                try_registering_vec_map(eg, fn_sort.clone(), vec_sort.clone(), arc.clone());
                if vec_sort.name() != arc.name() {
                    try_registering_vec_map(eg, fn_sort.clone(), arc.clone(), vec_sort.clone());
                }
            }
        }

        eg.add_primitive(Shape {});
        eg.add_primitive(FindMapping {});
        eg.add_primitive(ApplyMapping {});
    }

    fn reconstruct_termdag(
        &self,
        _container_values: &ContainerValues,
        _value: Value,
        termdag: &mut TermDag,
        element_terms: Vec<TermId>,
    ) -> TermId {
        if element_terms.is_empty() {
            termdag.app("vec-empty".into(), vec![])
        } else {
            termdag.app("vec-of".into(), element_terms)
        }
    }

    fn serialized_name(&self, _container_values: &ContainerValues, _: Value) -> String {
        "vec-of".to_owned()
    }
}

/**
 * Register a vec map primitive if the function matches the input and output vec.
 */
pub(crate) fn try_registering_vec_map(
    eg: &mut EGraph,
    fn_: Arc<FunctionSort>,
    input_vec: ArcSort,
    output_vec: ArcSort,
) {
    if fn_.inputs().len() != 1
        || fn_.inputs()[0].name() != input_vec.inner_sorts()[0].name()
        || fn_.output().name() != output_vec.inner_sorts()[0].name()
    {
        return;
    }
    eg.add_primitive(VecMap {
        name: "unstable-vec-map".into(),
        vec: input_vec,
        output_vec,
        fn_: fn_.clone(),
    });
}

pub(crate) fn register_vec_primitives_for_function(eg: &mut EGraph, fn_: Arc<FunctionSort>) {
    let all_vec_sorts = eg
        .type_info
        .get_arcsorts_by(|f| f.value_type() == Some(TypeId::of::<VecContainer>()));
    for input_vec in &all_vec_sorts {
        for output_vec in &all_vec_sorts {
            try_registering_vec_map(eg, fn_.clone(), input_vec.clone(), output_vec.clone());
        }
    }
}

// (unstable-vec-map (Vec[X], [X] -> Y) -> Vec[Y])
// will map the function over all elements in the vec and drop elements where it is undefined.
#[derive(Clone)]
struct VecMap {
    name: String,
    vec: ArcSort,
    output_vec: ArcSort,
    fn_: Arc<FunctionSort>,
}

impl Primitive for VecMap {
    fn name(&self) -> &str {
        &self.name
    }

    fn get_type_constraints(&self, span: &Span) -> Box<dyn TypeConstraint> {
        SimpleTypeConstraint::new(
            self.name(),
            vec![self.fn_.clone(), self.vec.clone(), self.output_vec.clone()],
            span.clone(),
        )
        .into_box()
    }

    fn apply(&self, exec_state: &mut ExecutionState, args: &[Value]) -> Option<Value> {
        let fc = exec_state
            .container_values()
            .get_val::<FunctionContainer>(args[0])
            .unwrap()
            .clone();
        let vec = exec_state
            .container_values()
            .get_val::<VecContainer>(args[1])
            .unwrap()
            .clone();
        let mut new_data = Vec::with_capacity(vec.data.len());
        for v in vec.data {
            if let Some(mapped) = fc.apply(exec_state, &[v]) {
                new_data.push(mapped);
            }
        }
        let vec = VecContainer {
            do_rebuild: self.output_vec.is_eq_container_sort(),
            data: new_data,
        };
        Some(
            exec_state
                .clone()
                .container_values()
                .register_val(vec, exec_state),
        )
    }
}

// (vec-union Vec[A] Vec[A]) -> Vec[A]
// where A: Eq
// Unions items from two vecs, asserting they are the same length.
#[derive(Clone)]
struct Union {
    name: String,
    vec: ArcSort,
    action: UnionAction,
}

impl Primitive for Union {
    fn name(&self) -> &str {
        &self.name
    }

    fn get_type_constraints(&self, span: &Span) -> Box<dyn TypeConstraint> {
        SimpleTypeConstraint::new(
            self.name(),
            vec![self.vec.clone(), self.vec.clone(), self.vec.clone()],
            span.clone(),
        )
        .into_box()
    }

    fn apply(&self, exec_state: &mut ExecutionState, args: &[Value]) -> Option<Value> {
        let left = exec_state
            .container_values()
            .get_val::<VecContainer>(args[0])?
            .clone()
            .data;
        let right = exec_state
            .container_values()
            .get_val::<VecContainer>(args[1])?
            .clone()
            .data;
        if left.len() != right.len() {
            return None;
        }
        for (l, r) in zip(left, right) {
            self.action.union(exec_state, l, r);
        }
        Some(args[0])
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_vec_make_expr() {
        let mut egraph = EGraph::default();
        let outputs = egraph
            .parse_and_run_program(
                None,
                r#"
            (sort IVec (Vec i64))
            (let v0 (vec-empty))
            (let v1 (vec-of 1 2 3 4))
            (extract v0)
            (extract v1)
            "#,
            )
            .unwrap();

        // Check extracted expr is parsed as an original expr
        egraph
            .parse_and_run_program(
                None,
                &format!(
                    r#"
                (check (= v0 {}))
                (check (= v1 {}))
                "#,
                    outputs[0], outputs[1],
                ),
            )
            .unwrap();
    }
}

#[derive(Clone, Debug)]
struct Shape {}

/// Computes the "shape" of children renaming maps.
/// The shape is a renaming of a map so that the values start from zero and increase by one when a new unique value is seen.
/// This first input says "pass b to the first eclass and pass a to the second eclass"
/// Example input 1: (vec![b], vec![a])
/// Output: vec![0, 1]
/// The second input says "pass y to the first eclass and z to the second eclass"
/// Example input 2: (vec![y], vec![z])
/// Output: vec![0, 1]
/// The shapes are the same.
///
///
/// Another example:
/// Input 1: (vec![b, a, b], vec![a, a])
/// Output: vec![0, 1, 0, 1, 1]
/// Input 2: (vec![y, z, y], vec![z, z])
/// Output: vec![0, 1, 0, 1, 1]
impl Primitive for Shape {
    fn name(&self) -> &str {
        "shape"
    }

    fn get_type_constraints(&self, span: &Span) -> Box<dyn crate::constraint::TypeConstraint> {
        // must be vecs of integer sort
        Box::new(AllEqualTypeConstraint::new("shape", span.clone()))
    }

    fn apply(&self, exec_state: &mut ExecutionState<'_>, args: &[Value]) -> Option<Value> {
        let mut maps = vec![];
        for arg in args {
            let m = exec_state
                .container_values()
                .get_val::<VecContainer>(*arg)
                .unwrap();
            maps.push(m);
        }
        let mut counter = 0;
        let mut mapping = HashMap::default();
        let mut shape = vec![];
        for m1 in maps.iter() {
            for i in 0..m1.data.len() {
                let v = m1.data.get(i).unwrap();
                let mapped = if mapping.contains_key(v) {
                    *mapping.get(v).unwrap()
                } else {
                    let new_val = exec_state.base_values().get::<i64>(counter);
                    counter += 1;
                    mapping.insert(*v, new_val);
                    new_val
                };
                shape.push(mapped);
            }
        }

        let result = VecContainer {
            do_rebuild: false,
            data: shape,
        };
        Some(
            exec_state
                .container_values()
                .register_val(result, exec_state),
        )
    }
}

#[derive(Clone, Debug)]
struct FindMapping {}

/// Helper for two nodes that are the same up to renaming on their children.
///
/// Given two parallel sequences of renaming maps, returns a mapping `r` such
/// that applying `r` to each map in the *second* sequence yields the
/// corresponding map in the *first* sequence — i.e. for every `i`,
/// `(apply-mapping second[i] r) == first[i]`.
///
/// Arguments are passed as a flat list `[first..., second...]` of equal-length
/// halves. For each paired entry across the two halves, the elements are walked
/// in parallel and `r[v_second] = v_first` is recorded. The result is returned
/// as a `Vec i64` indexed by `v_second`.
///
/// # Bails (returns `None`) when the inputs don't share a shape
///
/// A consistent `r` only exists when `first` and `second` have the same
/// aliasing pattern (same `shape` — see the `shape` primitive). The check is
/// done inline during the walk:
///
/// - **Second-side aliasing not in first.** Two positions in `second` hold the
///   same value `e2` but the matching positions in `first` hold different
///   values. There is no `r` with `r[e2]` equal to two things at once.
/// - **First-side aliasing not in second.** Two positions in `first` hold the
///   same value `e1` but the matching positions in `second` differ — `r` would
///   have to collapse two distinct slots into one, so it isn't a bijection and
///   the inverse rename wouldn't exist.
/// - **Length mismatch** between paired vecs.
/// - **`second` not in canonical-shape form.** The result is constructed as
///   `result_vec[v_second] = v_first`, so `second`'s values must densely cover
///   `0..=max`. A gap would leave an entry of `result_vec` uninitialized and
///   silently wrong, so this is treated as a misuse and bails.
///
/// # Example
///
/// Inputs (split into two halves):
/// ```text
/// first  = [[0, 1, 0], [1, 2]]
/// second = [[1, 2, 1], [2, 0]]
/// ```
/// Walking the pairs builds `{1 -> 0, 2 -> 1, 0 -> 2}`, so the output is:
/// ```text
/// [2, 0, 1]   // index 0 -> 2, index 1 -> 0, index 2 -> 1
/// ```
/// Verification:
/// - `apply-mapping [1,2,1] [2,0,1] = [0,1,0]` ✓
/// - `apply-mapping [2,0]   [2,0,1] = [1,2]`   ✓
///
/// # Typical use
///
/// When two e-nodes have identical structure but differ only in their child
/// renamings, calling this with the renamings of the first node followed by
/// the renamings of the second yields the rename that translates the second
/// node's slots into the first's. Because the shape check is now built in,
/// callers no longer need a separate `(= (shape ...) (shape ...))` guard in
/// the rule body — a `find-mapping` call on mismatched shapes simply fails to
/// match.
impl Primitive for FindMapping {
    fn name(&self) -> &str {
        "find-mapping"
    }

    fn get_type_constraints(&self, span: &Span) -> Box<dyn crate::constraint::TypeConstraint> {
        // must be vecs of integer sort
        Box::new(AllEqualTypeConstraint::new("shape", span.clone()))
    }

    fn apply(&self, exec_state: &mut ExecutionState<'_>, args: &[Value]) -> Option<Value> {
        let first_half = &args[0..args.len() / 2];
        let second_half = &args[args.len() / 2..];

        // mapping: e2 -> e1; inverse: e1 -> e2.
        // Both must be functions (no conflicts) for the two halves to share a
        // shape. Any conflict means the renaming we'd return wouldn't be a
        // well-defined bijection — bail.
        let mut mapping = HashMap::default();
        let mut inverse = HashMap::default();
        let mut min = i64::MAX;
        let mut max = i64::MIN;
        for (m1, m2) in first_half.iter().zip(second_half.iter()) {
            let vec1 = exec_state
                .container_values()
                .get_val::<VecContainer>(*m1)
                .unwrap();
            let vec2 = exec_state
                .container_values()
                .get_val::<VecContainer>(*m2)
                .unwrap();

            if vec1.data.len() != vec2.data.len() {
                return None;
            }

            for (e1, e2) in vec1.data.iter().zip(vec2.data.iter()) {
                let e1 = exec_state.base_values().unwrap::<i64>(*e1);
                let e2 = exec_state.base_values().unwrap::<i64>(*e2);
                if let Some(prev) = mapping.insert(e2, e1) {
                    if prev != e1 {
                        return None;
                    }
                }
                if let Some(prev) = inverse.insert(e1, e2) {
                    if prev != e2 {
                        return None;
                    }
                }
                if e2 < min {
                    min = e2;
                }
                if e2 > max {
                    max = e2;
                }
            }
        }

        if mapping.is_empty() {
            // No pairs to constrain; return an empty rename.
            let result = VecContainer {
                do_rebuild: false,
                data: vec![],
            };
            return Some(
                exec_state
                    .container_values()
                    .register_val(result, exec_state),
            );
        }

        // For the second half to be a canonicalized renaming (matching shape),
        // its values must densely cover 0..=max.
        if min != 0 || (max as usize + 1) != mapping.len() {
            return None;
        }

        let mut result_vec = vec![0; (max + 1) as usize];
        for (k, v) in mapping.iter() {
            result_vec[*k as usize] = *v;
        }
        let result = VecContainer {
            do_rebuild: false,
            data: result_vec
                .iter()
                .map(|i| exec_state.base_values().get::<i64>(*i))
                .collect(),
        };
        Some(
            exec_state
                .container_values()
                .register_val(result, exec_state),
        )
    }
}

#[derive(Clone, Debug)]
struct ApplyMapping {}

/// Applies a renaming mapping to a renaming map.
/// The first input is the renaming map to apply to.
/// The second input is the mapping to apply.
/// The output is the renamed renaming map.
impl Primitive for ApplyMapping {
    fn name(&self) -> &str {
        "apply-mapping"
    }

    fn get_type_constraints(&self, span: &Span) -> Box<dyn crate::constraint::TypeConstraint> {
        // must be vecs of integer sort
        Box::new(AllEqualTypeConstraint::new("apply-mapping", span.clone()))
    }

    fn apply(&self, exec_state: &mut ExecutionState<'_>, args: &[Value]) -> Option<Value> {
        let map = exec_state
            .container_values()
            .get_val::<VecContainer>(args[0])
            .unwrap();
        let mapping = exec_state
            .container_values()
            .get_val::<VecContainer>(args[1])
            .unwrap();

        let mut result_vec = vec![];
        for v in map.data.iter() {
            let v = exec_state.base_values().unwrap::<i64>(*v);
            let mapped_v = exec_state
                .base_values()
                .unwrap::<i64>(mapping.data[v as usize]);
            result_vec.push(exec_state.base_values().get::<i64>(mapped_v));
        }

        let result = VecContainer {
            do_rebuild: false,
            data: result_vec,
        };
        Some(
            exec_state
                .container_values()
                .register_val(result, exec_state),
        )
    }
}
