use crate::constraint::{AllEqualTypeConstraint, NoTypeConstraint};

use super::*;
use std::collections::{BTreeMap, BTreeSet};

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct MapContainer {
    do_rebuild_keys: bool,
    do_rebuild_vals: bool,
    pub data: BTreeMap<Value, Value>,
}

impl ContainerValue for MapContainer {
    fn rebuild_contents(&mut self, rebuilder: &dyn Rebuilder) -> bool {
        let mut changed = false;
        if self.do_rebuild_keys {
            self.data = self
                .data
                .iter()
                .map(|(old, v)| {
                    let new = rebuilder.rebuild_val(*old);
                    changed |= *old != new;
                    (new, *v)
                })
                .collect();
        }
        if self.do_rebuild_vals {
            for old in self.data.values_mut() {
                let new = rebuilder.rebuild_val(*old);
                changed |= *old != new;
                *old = new;
            }
        }
        changed
    }
    fn iter(&self) -> impl Iterator<Item = Value> + '_ {
        self.data.iter().flat_map(|(k, v)| [k, v]).copied()
    }
}

/// A map from a key type to a value type supporting these primitives:
/// - `map-empty`
/// - `map-insert`
/// - `map-get`
/// - `map-contains`
/// - `map-not-contains`
/// - `map-remove`
/// - `map-length`
#[derive(Clone, Debug)]
pub struct MapSort {
    name: String,
    key: ArcSort,
    value: ArcSort,
}

impl MapSort {
    pub fn key(&self) -> ArcSort {
        self.key.clone()
    }

    pub fn value(&self) -> ArcSort {
        self.value.clone()
    }
}

impl Presort for MapSort {
    fn presort_name() -> &'static str {
        "Map"
    }

    fn reserved_primitives() -> Vec<&'static str> {
        vec![
            "map-empty",
            "map-insert",
            "map-get",
            "map-not-contains",
            "map-contains",
            "map-remove",
            "map-length",
        ]
    }

    fn make_sort(
        typeinfo: &mut TypeInfo,
        name: String,
        args: &[Expr],
    ) -> Result<ArcSort, TypeError> {
        if let [Expr::Var(k_span, k), Expr::Var(v_span, v)] = args {
            let k = typeinfo
                .get_sort_by_name(k)
                .ok_or(TypeError::UndefinedSort(k.clone(), k_span.clone()))?;
            let v = typeinfo
                .get_sort_by_name(v)
                .ok_or(TypeError::UndefinedSort(v.clone(), v_span.clone()))?;

            let out = Self {
                name,
                key: k.clone(),
                value: v.clone(),
            };
            Ok(out.to_arcsort())
        } else {
            panic!()
        }
    }
}

impl ContainerSort for MapSort {
    type Container = MapContainer;

    fn name(&self) -> &str {
        &self.name
    }

    fn inner_sorts(&self) -> Vec<ArcSort> {
        vec![self.key.clone(), self.value.clone()]
    }

    fn is_eq_container_sort(&self) -> bool {
        self.key.is_eq_sort()
            || self.value.is_eq_sort()
            || self.key.is_eq_container_sort()
            || self.value.is_eq_container_sort()
    }

    fn inner_values(
        &self,
        container_values: &ContainerValues,
        value: Value,
    ) -> Vec<(ArcSort, Value)> {
        let val = container_values
            .get_val::<MapContainer>(value)
            .unwrap()
            .clone();
        val.data
            .iter()
            .flat_map(|(k, v)| [(self.key.clone(), *k), (self.value.clone(), *v)])
            .collect()
    }

    fn register_primitives(&self, eg: &mut EGraph) {
        let arc = self.clone().to_arcsort();

        // Takes two name maps that map child keys to input names and canonicalizes them, producing a "shape"
        add_primitive!(eg, "map-empty" = {self.clone(): MapSort} || -> @MapContainer (arc) { MapContainer {
            do_rebuild_keys: self.ctx.key.is_eq_sort() || self.ctx.key.is_eq_container_sort(),
            do_rebuild_vals: self.ctx.value.is_eq_sort() || self.ctx.value.is_eq_container_sort(),
            data: BTreeMap::new()
        } });

        add_primitive!(eg, "map-get"    = |    xs: @MapContainer (arc), x: # (self.key())                     | -?> # (self.value()) { xs.data.get(&x).copied() });
        add_primitive!(eg, "map-insert" = |mut xs: @MapContainer (arc), x: # (self.key()), y: # (self.value())| -> @MapContainer (arc) {{ xs.data.insert(x, y); xs }});
        add_primitive!(eg, "map-remove" = |mut xs: @MapContainer (arc), x: # (self.key())                     | -> @MapContainer (arc) {{ xs.data.remove(&x);   xs }});

        add_primitive!(eg, "map-length"       = |xs: @MapContainer (arc)| -> i64 { xs.data.len() as i64 });
        add_primitive!(eg, "map-contains"     = |xs: @MapContainer (arc), x: # (self.key())| -?> () { ( xs.data.contains_key(&x)).then_some(()) });
        add_primitive!(eg, "map-not-contains" = |xs: @MapContainer (arc), x: # (self.key())| -?> () { (!xs.data.contains_key(&x)).then_some(()) });

        add_primitive!(eg, "map-inverse" = |xs: @MapContainer (arc)| -> @MapContainer (arc) {{
            let mut new_map = BTreeMap::new();
            for (k, v) in xs.data.iter() {
                new_map.insert(*v, *k);
            }
            MapContainer {
                do_rebuild_keys: xs.do_rebuild_vals,
                do_rebuild_vals: xs.do_rebuild_keys,
                data: new_map
            }
        }});

        // (map-union m1 m2) returns the union of two maps. If a key is
        // present in both with different values, returns None. The slotted
        // encoder uses this to synthesize identity renames over the union
        // of multiple body-bound renames' slot spaces.
        add_primitive!(eg, "map-union" = |xs: @MapContainer (arc), ys: @MapContainer (arc)| -?> @MapContainer (arc) {{
            let mut new_map = xs.data.clone();
            for (k, v) in ys.data.iter() {
                if let Some(existing) = new_map.get(k) {
                    if existing != v { return None; }
                }
                new_map.insert(*k, *v);
            }
            Some(MapContainer {
                do_rebuild_keys: xs.do_rebuild_keys,
                do_rebuild_vals: xs.do_rebuild_vals,
                data: new_map
            })
        }});

        // add shape primitive
        eg.add_primitive(Shape {});
        eg.add_primitive(Inverse {});
        eg.add_primitive(Compose {});

        // `find-mapping` is the slotted-egraph "rename between two nodes that
        // share a shape" helper. It only makes sense over `Map i64 i64`
        // (slot-id → slot-id renamings), and we pin its type constraint to
        // this specific Map sort so it doesn't clash with the Vec-based
        // `find-mapping` registered for `Vec i64`.
        if self.key.name() == "i64" && self.value.name() == "i64" {
            eg.add_primitive(FindMapping { sort: arc.clone() });
        }
    }

    fn reconstruct_termdag(
        &self,
        _container_values: &ContainerValues,
        _value: Value,
        termdag: &mut TermDag,
        element_terms: Vec<TermId>,
    ) -> TermId {
        let mut term = termdag.app("map-empty".into(), vec![]);

        for x in element_terms.chunks(2) {
            term = termdag.app("map-insert".into(), vec![term, x[0], x[1]])
        }

        term
    }

    fn serialized_name(&self, _container_values: &ContainerValues, _: Value) -> String {
        self.name().to_owned()
    }
}

#[derive(Clone, Debug)]
struct Shape {}

impl Primitive for Shape {
    fn name(&self) -> &str {
        "shape2"
    }

    fn get_type_constraints(&self, _span: &Span) -> Box<dyn crate::constraint::TypeConstraint> {
        // todo no type contraints
        Box::new(NoTypeConstraint::new())
    }

    fn apply(&self, exec_state: &mut ExecutionState, args: &[Value]) -> Option<Value> {
        // maps from original slots to shape slots.
        let mut out: BTreeMap<Value, Value> = BTreeMap::new();

        for arg in args {
            let m = exec_state
                .container_values()
                .get_val::<MapContainer>(*arg)?;
            let mut kv_pairs: Vec<(Value, Value)> = m.clone().data.into_iter().collect();
            kv_pairs.sort_by_key(|(k, _)| exec_state.base_values().unwrap::<i64>(*k));

            for (_, v) in kv_pairs {
                if !out.contains_key(&v) {
                    let new_v = exec_state.base_values().get::<i64>(out.len() as i64);
                    out.insert(v, new_v);
                }
            }
        }

        let out = exec_state.container_values().register_val(
            MapContainer {
                do_rebuild_keys: false,
                do_rebuild_vals: false,
                data: out,
            },
            exec_state,
        );
        Some(out)
    }
}

#[derive(Clone, Debug)]
struct Inverse {}

// This computes (inverse m).
impl Primitive for Inverse {
    fn name(&self) -> &str {
        "inverse"
    }

    fn get_type_constraints(&self, span: &Span) -> Box<dyn crate::constraint::TypeConstraint> {
        // must be vecs of integer sort
        Box::new(AllEqualTypeConstraint::new("inverse", span.clone()))
    }

    fn apply(&self, exec_state: &mut ExecutionState, args: &[Value]) -> Option<Value> {
        let m = exec_state
            .container_values()
            .get_val::<MapContainer>(args[0])?
            .clone();
        let res = inverse(&m.data);
        let map_value = exec_state.container_values().register_val(
            MapContainer {
                do_rebuild_keys: false,
                do_rebuild_vals: false,
                data: res,
            },
            exec_state,
        );

        Some(map_value)
    }
}

#[derive(Clone, Debug)]
struct Compose {}

// '(compose m1 m2) * a' is conceptually the same as 'm1 * m2 * a'
impl Primitive for Compose {
    fn name(&self) -> &str {
        "compose"
    }

    fn get_type_constraints(&self, span: &Span) -> Box<dyn crate::constraint::TypeConstraint> {
        // must be vecs of integer sort
        Box::new(AllEqualTypeConstraint::new("compose", span.clone()))
    }

    fn apply(&self, exec_state: &mut ExecutionState, args: &[Value]) -> Option<Value> {
        let m1 = exec_state
            .container_values()
            .get_val::<MapContainer>(args[0])?
            .clone();
        let m2 = exec_state
            .container_values()
            .get_val::<MapContainer>(args[1])?
            .clone();
        let res = compose(&m1.data, &m2.data);
        let map_value = exec_state.container_values().register_val(
            MapContainer {
                do_rebuild_keys: false,
                do_rebuild_vals: false,
                data: res,
            },
            exec_state,
        );

        Some(map_value)
    }
}

/// Helper for two nodes that are the same up to renaming on their children.
///
/// Given two parallel sequences of renaming maps `[first..., second...]`
/// (passed flat, with equal-length halves), returns a renaming `R` such that
/// for every `i`, applying `R` to `second[i]` yields `first[i]`.
///
/// Renamings are treated as **explicit partial maps**. Missing keys carry no
/// meaning, so each paired `(first[i], second[i])` must mention the same key
/// set explicitly. For every shared key `k`, we derive the constraint
/// `R(second[i][k]) = first[i][k]`.
///
/// Bails (returns `None`) when the per-pair constraints are inconsistent:
/// - paired maps have different explicit key sets,
/// - the same `v_second` is forced to two different `v_first` values
///   (R wouldn't be a function), or
/// - the same `v_first` is forced from two different `v_second` values
///   (R wouldn't be injective).
fn find_mapping_data<'a>(
    pairs: impl IntoIterator<Item = (&'a BTreeMap<Value, Value>, &'a BTreeMap<Value, Value>)>,
) -> Option<BTreeMap<Value, Value>> {
    // mapping: v_second -> v_first (the renaming we're returning).
    // inverse: v_first -> v_second (only used to detect non-bijective collapses).
    let mut mapping: BTreeMap<Value, Value> = BTreeMap::new();
    let mut inverse: BTreeMap<Value, Value> = BTreeMap::new();

    for (map1, map2) in pairs {
        let keys1: BTreeSet<Value> = map1.keys().copied().collect();
        let keys2: BTreeSet<Value> = map2.keys().copied().collect();
        if keys1 != keys2 {
            return None;
        }

        let keys = keys1;
        for k in keys {
            let v_first = map1.get(&k).copied()?;
            let v_second = map2.get(&k).copied()?;

            if let Some(prev) = mapping.insert(v_second, v_first) {
                if prev != v_first {
                    return None;
                }
            }
            if let Some(prev) = inverse.insert(v_first, v_second) {
                if prev != v_second {
                    return None;
                }
            }
        }
    }

    Some(mapping)
}

#[derive(Clone, Debug)]
struct FindMapping {
    sort: ArcSort,
}

impl Primitive for FindMapping {
    fn name(&self) -> &str {
        "find-mapping"
    }

    fn get_type_constraints(&self, span: &Span) -> Box<dyn crate::constraint::TypeConstraint> {
        // Pin every arg (and the output) to this specific Map sort, so we
        // don't clash with other `find-mapping` registrations on different
        // container kinds.
        Box::new(
            AllEqualTypeConstraint::new("find-mapping", span.clone())
                .with_all_arguments_sort(self.sort.clone()),
        )
    }

    fn apply(&self, exec_state: &mut ExecutionState, args: &[Value]) -> Option<Value> {
        let first_half = &args[0..args.len() / 2];
        let second_half = &args[args.len() / 2..];
        let pairs = first_half
            .iter()
            .zip(second_half.iter())
            .map(|(m1, m2)| {
                let map1 = exec_state
                    .container_values()
                    .get_val::<MapContainer>(*m1)?
                    .clone();
                let map2 = exec_state
                    .container_values()
                    .get_val::<MapContainer>(*m2)?
                    .clone();
                Some((map1.data, map2.data))
            })
            .collect::<Option<Vec<_>>>()?;
        let data = find_mapping_data(pairs.iter().map(|(map1, map2)| (map1, map2)))?;

        let result = MapContainer {
            do_rebuild_keys: false,
            do_rebuild_vals: false,
            data,
        };
        Some(
            exec_state
                .container_values()
                .register_val(result, exec_state),
        )
    }
}

// (compose m1 m2) is ordinary partial-map composition: for each explicit
// entry k -> v in m2, we emit k -> m1[v] if and only if m1 has an explicit
// entry for v. Missing keys carry no identity behavior and therefore produce
// no composed entry.
fn compose(m1: &BTreeMap<Value, Value>, m2: &BTreeMap<Value, Value>) -> BTreeMap<Value, Value> {
    let mut res = BTreeMap::new();
    for (k, inter) in m2 {
        if let Some(final_v) = m1.get(inter) {
            res.insert(*k, *final_v);
        }
    }
    res
}

// Inverse of the explicit entries in the input map.
fn inverse(m1: &BTreeMap<Value, Value>) -> BTreeMap<Value, Value> {
    let mut res = BTreeMap::new();
    for (k, v) in m1.iter() {
        res.insert(*v, *k);
    }
    res
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::numeric_id::NumericId;

    fn value(n: usize) -> Value {
        Value::from_usize(n)
    }

    fn map(entries: &[(usize, usize)]) -> BTreeMap<Value, Value> {
        entries
            .iter()
            .map(|(key, mapped_value)| (value(*key), value(*mapped_value)))
            .collect()
    }

    #[test]
    fn test_find_mapping_data_canonicalizes_identity_entries() {
        let first = map(&[(0, 1)]);
        let second = map(&[(0, 2)]);

        let result = find_mapping_data([(&first, &second)]).unwrap();

        assert_eq!(result, map(&[(2, 1)]));
    }

    #[test]
    fn test_find_mapping_data_0_1() {
        let first = map(&[(8, 1)]);
        let second = map(&[(8, 0)]);

        let result = find_mapping_data([(&first, &second)]).unwrap();

        assert_eq!(result, map(&[(0, 1)]));
    }

    #[test]
    fn test_does_not_find_mapping_differ_shape() {
        let first = map(&[(8, 1), (9, 1)]);
        let second = map(&[(8, 2), (9, 1)]);

        assert_eq!(find_mapping_data([(&first, &second)]), None);
    }

    #[test]
    fn test_does_not_find_mapping_same_shape() {
        let first = map(&[(8, 1), (9, 1)]);
        let second = map(&[(8, 2), (9, 2)]);

        assert_eq!(find_mapping_data([(&first, &second)]).unwrap(), map(&[(2, 1)]));
    }

    #[test]
    fn test_does_find_mapping_good() {
        let first = map(&[(0, 1)]);
        let second = map(&[(0, 2)]);

        assert_eq!(find_mapping_data([(&first, &second)]), Some(map(&[(2, 1)])));
    }

    // f(x, x), f(x, y)
    #[test]
    fn test_differ_shape() {
        let first = map(&[(0, 0)]);
        let first2 = map(&[(0, 0)]);
        let second = map(&[(0, 0)]);
        let second2 = map(&[(0, 1)]);
        assert_eq!(
            find_mapping_data([(&first, &second), (&first2, &second2)]),
            None
        );
    }

    #[test]
    fn test_compose_only_uses_explicit_entries() {
        let m1 = map(&[(1, 9)]);
        let m2 = map(&[(0, 1), (2, 3)]);

        assert_eq!(compose(&m1, &m2), map(&[(0, 9)]));
    }

    #[test]
    fn test_inverse_preserves_explicit_identity_entries() {
        let m = map(&[(0, 0), (1, 2)]);

        assert_eq!(inverse(&m), map(&[(0, 0), (2, 1)]));
    }
}
