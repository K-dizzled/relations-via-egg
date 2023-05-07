use egg::{Explanation, FlatTerm, Id, Language, Pattern, RecExpr, Rewrite, Runner, Searcher, Subst, Symbol};
use std::collections::{LinkedList};
use crate::goal_preprocess::{GoalSExpr, recexpr_to_goal_expr, RelLanguage};
use crate::make_rules::RewriteRules;

/// Direction of Rewrite in the
/// proof
#[derive(Debug, ocaml::IntoValue, Copy, Clone, PartialEq)]
pub enum Direction {
    Forward,
    Backward,
}

impl Direction {
    fn neg(&self) -> Direction {
        match self {
            Direction::Forward => Direction::Backward,
            Direction::Backward => Direction::Forward,
        }
    }
}

/// A single rewrite in the proof
#[derive(Debug, ocaml::IntoValue)]
pub struct Rule {
    pub direction: Direction,
    pub theorem: String,
    pub rewrite_with: LinkedList<(String, GoalSExpr)>,
    pub rewrite_at: usize,
}

/// A sequence of rewrites
#[derive(Debug, ocaml::IntoValue)]
pub struct ProofSeq {
    pub rules: LinkedList<Rule>,
}

impl ProofSeq {
    pub fn from(rules: LinkedList<Rule>) -> ProofSeq {
        ProofSeq { rules }
    }
}

// Apply one rewrite without touching the e-graph
pub fn check_one_rewrite<L>(
    current_id: Id,
    egraph: &egg::EGraph<L, ()>,
    rewrite: &Rewrite<L, ()>,
    e_class_id: Id,
    subst: &Subst,
    next: &RecExpr<L>,
) -> bool
where
    L: Language,
    L: std::fmt::Display,
    L: egg::FromOp,
{
    let mut e_graph_copy = egraph.clone();

    rewrite.applier.apply_one(
        &mut e_graph_copy,
        e_class_id,
        subst,
        Some(rewrite.searcher.get_pattern_ast()
            .expect("Explanations must be enabled for the egraph")
        ),
        rewrite.name.clone(),
    );

    if let Some(id) = e_graph_copy.lookup_expr(&next) {
        if id == current_id {
            return true;
        }
    }

    false
}

// Takes two flat terms and a rewrite that
// was applied to get from the first to the second
// and returns a substitutions of the pattern variables from the
// lhs of the rewrite pattern
pub fn get_pattern_subst<L>(
    current: &mut RecExpr<L>,
    next: &mut RecExpr<L>,
    rewrite: &Rewrite<L, ()>,
    rewrite_direction: Direction,
) -> Option<LinkedList<(String, RecExpr<L>)>>
where
    L: Language,
    L: std::fmt::Display,
    L: egg::FromOp,
{
    if rewrite_direction == Direction::Backward {
        return get_pattern_subst(next, current, rewrite, rewrite_direction.neg());
    }

    // Create an empty egraph so that no
    // other information distracts us
    let empty_ruleset: Vec<Rewrite<L, ()>> = vec![];
    let runner_empty: Runner<L, ()> = Runner::default()
        .with_explanations_enabled()
        .with_expr(current)
        .run(&empty_ruleset);

    let rewrite_pattern_ast = rewrite.searcher.get_pattern_ast().unwrap();
    let rewrite_pattern = Pattern::new(rewrite_pattern_ast.clone());

    // Now egraph contains only one expression, moreover, all
    // nodes are self contained in their own e-classes
    //
    // We search the whole egraph for the rewrite pattern
    let matches = rewrite_pattern.search(&runner_empty.egraph);

    // Iterate over all places of the expression where we can apply
    // the rewrite
    for rewrite_match in matches {
        // Rewrite match is a particular place where we can
        // apply the rewrite. With a e-class id contained in it
        // rewrite_match.substs are substitutions for the pattern variables
        // in the rewrite pattern. We should have only on e-node in each e-class
        let subst = rewrite_match.substs
            .first()
            .expect("Unexpected behaviour, \
            no substitutions for rewrite. Report an issue.");
        if rewrite_match.substs.len() != 1 {
            panic!("Unexpected behaviour, multiple e-classes in a fresh egraph. Report an issue.")
        }

        // Check if expression B can be obtained from A by applying the rewrite
        let is_needed_rewrite = check_one_rewrite(
            runner_empty.egraph.lookup_expr(&current).unwrap(),
            &runner_empty.egraph,
            &rewrite,
            rewrite_match.eclass,
            subst,
            next,
        );

        // If so, iterate over pattern variables of the substitution
        // and return them as a list of pairs (var_name, var_value)
        if is_needed_rewrite {
            let mut substitutions: LinkedList<(String, RecExpr<L>)> = LinkedList::new();
            for var_name in rewrite.searcher.vars() {
                let subst_id = subst[var_name];
                let var_str: String = format!("{}", var_name);

                let subst_expr = runner_empty.egraph.id_to_expr(subst_id);

                substitutions.push_back((var_str, subst_expr));
            }
            return Some(substitutions);
        }
    }

    None
}

pub fn parse_proof(expl: &mut Explanation<RelLanguage>, r_rules: &RewriteRules) -> LinkedList<Rule> {
    let flat_expl = expl.make_flat_explanation();
    return if let Some(mut prev) = flat_expl.first() {
        let mut rules: LinkedList<Rule> = LinkedList::new();
        for ft in flat_expl.iter().skip(1) {
            let mut prev_expr = prev.get_recexpr();
            let mut cur_expr = ft.get_recexpr();

            let rule = ft_to_rule(ft, &mut prev_expr, &mut cur_expr, &r_rules);
            if rule.is_some() {
                rules.push_back(rule.unwrap());
            }
            prev = ft;
        }

        rules
    } else {
        LinkedList::new()
    }
}

/// The FlatTerm is basically an S-expr with some extra
/// information about the rule that was applied to get
/// the term. Recursively search for the rewrites
pub fn ft_to_rule(
    ft: &FlatTerm<RelLanguage>,
    prev_expr: &mut RecExpr<RelLanguage>,
    cur_expr: &mut RecExpr<RelLanguage>,
    rules: &RewriteRules,
) -> Option<Rule> {
    fn rule_from_rule_name(
        rule_name: &Symbol,
        direction: Direction,
        rewrite_from: &mut RecExpr<RelLanguage>,
        rewrite_to: &mut RecExpr<RelLanguage>,
        rewrite_sys: &RewriteRules,
    ) -> Option<Rule> {
        let rule_name = (*rule_name).to_string();
        if rule_name.ends_with("-rev") {
            let rule_name_wo_dir = rule_name.split("-rev").next().unwrap();
            let rewrite_with = get_pattern_subst(
                rewrite_from,
                rewrite_to,
                rewrite_sys.get_rule_by_name(rule_name_wo_dir).unwrap(),
                direction.neg()
            ).unwrap().iter().map(|(n, x)| (n.clone(), recexpr_to_goal_expr(x).unwrap())).collect();
            return Some(Rule {
                direction: direction.neg(),
                theorem: rule_name_wo_dir.to_string(),
                rewrite_with,
                rewrite_at: 1,
            });
        }

        let rewrite_with = get_pattern_subst(
            rewrite_from, rewrite_to,
            rewrite_sys.get_rule_by_name(rule_name.as_str()).unwrap(),
            direction.clone()
        ).unwrap().iter().map(|(n, x)| (n.clone(), recexpr_to_goal_expr(x).unwrap())).collect();
        return Some(Rule {
            direction,
            theorem: (*rule_name).to_string(),
            rewrite_with,
            rewrite_at: 1,
        });
    }

    if let Some(rule_name) = &ft.forward_rule {
        return rule_from_rule_name(
            rule_name, Direction::Forward, prev_expr, cur_expr, rules
        );
    }

    if let Some(rule_name) = &ft.backward_rule {
        return rule_from_rule_name(
            rule_name, Direction::Backward, prev_expr, cur_expr, rules
        );
    }

    for child in &ft.children {
        if let Some(rule) = ft_to_rule(child, prev_expr, cur_expr, rules) {
            return Some(rule);
        }
    }

    None
}

#[cfg(test)]
mod tests {
    use crate::*;
    use itertools::izip;

    #[test]
    fn test_get_subst() {
        let lhss: Vec<&str> = vec![
            "(;; (+ (? (? r))) (+ (? r)))",
            "(;; (+ (? r)) (+ (? (? r))))",
            "(;; (+ (? r)) (+ (? r)))",
            "(;; (+ (? r)) (+ (? r)))",
            "(+ (? (? r)))",
            "(+ (? (? r)))",
        ];

        let rhss: Vec<&str> = vec![
            "(;; (* (? r)) (+ (? r)))",
            "(;; (* r) (+ (? (? r))))",
            "(;; (* r) (+ (? r)))",
            "(;; (+ (? r)) (* r))",
            "(+ (? (? (? r))))",
            "(+ (? (? (? r))))"
        ];

        let rewrites: Vec<Rewrite<RelLanguage, ()>> = vec![
            rewrite!("ct_of_cr"; "(+ (? ?r))" => "(* ?r)"),
            rewrite!("ct_of_cr"; "(+ (? ?r))" => "(* ?r)"),
            rewrite!("ct_of_cr"; "(+ (? ?r))" => "(* ?r)"),
            rewrite!("ct_of_cr"; "(+ (? ?r))" => "(* ?r)"),
            rewrite!("cr_of_cr"; "(? (? ?r))" => "(? ?r)"),
            rewrite!("cr_of_cr"; "(? (? ?r))" => "(? ?r)"),
        ];

        let answers = vec![
            Some(LinkedList::from([("?r".to_string(), "(? r)".to_string())])),
            Some(LinkedList::from([("?r".to_string(), "r".to_string())])),
            Some(LinkedList::from([("?r".to_string(), "r".to_string())])),
            Some(LinkedList::from([("?r".to_string(), "r".to_string())])),
            None,
            Some(LinkedList::from([("?r".to_string(), "r".to_string())])),
        ];

        let is_forward = vec![true, true, true, true, true, false];

        // (+ (? (Rewrite<= cr_of_cr (? (? r)))))
        // (Rewrite=> ct_of_cr (* (? (? r))))
        // (* (Rewrite=> cr_of_cr (? r)))

        for (lhs, rhs, rewrite, answer, is_fwd) in izip!(lhss, rhss, rewrites, answers, is_forward) {
            let mut left: RecExpr<RelLanguage> = lhs.parse().unwrap();
            let mut right: RecExpr<RelLanguage> = rhs.parse().unwrap();
            let subst = get_pattern_subst(
                &mut left, &mut right, &rewrite, is_fwd
            );
            assert_eq!(subst, answer);
        }
    }
}

