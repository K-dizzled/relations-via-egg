use egg::*;
use std::collections::{HashMap, HashSet};
use itertools::Itertools;

// This implementation is taken from
// https://github.com/remysucre/eggegg

pub fn intersect<L, A>(g1: &EGraph<L, A>, g2: &EGraph<L, A>, analysis: A) -> EGraph<L, A>
where
    L: Language,
    A: Analysis<L>,
{
    let mut g = EGraph::new(analysis);
    let mut e1_e: HashMap<Id, HashSet<Id>> = HashMap::new();
    let mut e_e2: HashMap<Id, Id> = HashMap::new();
    let empty_set = HashSet::new();
    loop {
        let mut g_changed = false;
        for class in g1.classes() {
            for node in &class.nodes {
                for mut n_new in flatmap_children(node, |id| {
                    e1_e.get(&id).unwrap_or(&empty_set).iter().copied()
                }) {
                    if let Some(c2) = g2.lookup(n_new.clone().map_children(|id| e_e2[&id])) {
                        let c_new = g.lookup(&mut n_new).unwrap_or_else(|| {
                            g_changed = true;
                            g.add(n_new.clone())
                        });
                        e_e2.insert(c_new, c2);
                        e1_e.entry(class.id).or_insert(HashSet::new()).insert(c_new);
                        for c in e1_e[&class.id].iter() {
                            if g2.find(e_e2[&c]) == g2.find(c2) {
                                let unioned = g.union(c_new, *c);
                                g_changed = g_changed || unioned;
                                g.rebuild();
                            }
                        }
                    }
                }
            }
        }
        if !g_changed {
            break;
        }
    }
    g
}

// compute the set of new nodes op(c1',...,cn') from op(c1,...,cn)
// let op(c1,...,cn) = node;
// vec![op(c1',...,cn') where c1' in f(c1),...,cn' in f(cn)]
fn flatmap_children<L, F, I>(node: &L, f: F) -> Vec<L>
where
    L: Language,
    I: Clone + Iterator<Item = Id>,
    F: Fn(Id) -> I,
{
    if node.children().is_empty() {
        vec![node.clone()]
    } else {
        let childrens = node
            .children()
            .iter()
            .map(|id| f(*id))
            .multi_cartesian_product();
        childrens
            .map(|children| {
                let mut new_node = node.clone();
                for i in 0..children.len() {
                    new_node.children_mut()[i] = children[i];
                }
                new_node
            })
            .collect()
    }
}