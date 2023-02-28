use crate::{axioms::*, rewrite_in_runtime, RelLanguage};
use egg::Rewrite;
use lazy_static::lazy_static;
use std::io::Result;
use std::result::Result as StdResult;

// Added "<=" rewrite pattern for more convenient
// testing
#[macro_export]
macro_rules! rewrite {
    (
        $name:expr;
        $lhs:tt <= $rhs:tt
        $(if $cond:expr)*
    )  => {{
        let name_rev = String::from($name.clone()) + "-rev";
        egg::rewrite!(name_rev;  $rhs => $lhs $(if $cond)*)
    }};
    (
        $name:expr;
        $lhs:tt => $rhs:tt
        $(if $cond:expr)*
    )  => {{ egg::rewrite!($name;  $lhs => $rhs $(if $cond)*) }};
    (
        $name:expr;
        $lhs:tt <=> $rhs:tt
        $(if $cond:expr)*
    )  => {{ egg::rewrite!($name;  $lhs <=> $rhs $(if $cond)*) }};
}

pub type RelRules = Vec<Rewrite<RelLanguage, ()>>;

pub struct RewriteRules {
    pub rules: RelRules,
}

impl RewriteRules {
    pub fn new() -> Self {
        Self { rules: vec![] }
    }

    pub fn push(&mut self, rule: Rewrite<RelLanguage, ()>) {
        self.rules.push(rule);
    }

    pub fn neat_push(&mut self, rule: StdResult<Rewrite<RelLanguage, ()>, String>) {
        if let Ok(rule) = rule {
            self.rules.push(rule);
        }
    }

    pub fn default() -> Self {
        let mut rules = Self::new();
        for (name, lhs, rhs, dir) in RULES.iter() {
            match dir {
                RuleDir::Forward => {
                    rules.push(rewrite_in_runtime(name, lhs, rhs).unwrap());
                }
                RuleDir::Backward => {
                    rules.push(rewrite_in_runtime(&format!("{}-rev", name), rhs, lhs).unwrap());
                }
                RuleDir::Bidirectional => {
                    rules.push(rewrite_in_runtime(name, lhs, rhs).unwrap());
                    rules.push(rewrite_in_runtime(&format!("{}-rev", name), rhs, lhs).unwrap());
                }
            }
        }

        rules
    }

    pub fn all_bidirectional() -> Self {
        let mut rules = Self::new();
        for (name, lhs, rhs, _) in RULES.iter() {
            rules.neat_push(rewrite_in_runtime(name, lhs, rhs));
            rules.neat_push(rewrite_in_runtime(&format!("{}-rev", name), rhs, lhs));
        }

        rules
    }

    pub fn extend_with_wf(&mut self, path: &'static str) -> Result<()> {
        let axioms = load_axioms(path);
        let axioms_rules = extract_rules_from_axioms(&axioms)?;
        self.rules.extend(axioms_rules);
        Ok(())
    }
}

#[derive(Debug, ocaml::IntoValue)]
pub enum RuleDir {
    Forward,
    Backward,
    Bidirectional,
}

lazy_static! {
    /// Extract hahn COQ library theorems to rewrite
    /// rules and afterwards build graph using them
    static ref RULES: Vec<(&'static str, &'static str, &'static str, RuleDir)> = {
        Vec::from([
            ("ct_end", "(+ ?a)", "(;; (* ?a) ?a)", RuleDir::Bidirectional),
            ("ct_begin", "(+ ?a)", "(;; ?a (* ?a))", RuleDir::Bidirectional),
            ("rt_begin", "(* ?r)", "(|| (complete_set) (;; ?r (* ?r)))", RuleDir::Backward),
            ("rt_end", "(* ?r)", "(|| (complete_set) (;; (* ?r) ?r))", RuleDir::Backward),
            ("rt_cr", "(;; (* ?a) (? ?a))", "(* ?a)", RuleDir::Forward),
            ("seq_false_l", "(;; bot ?a)", "bot", RuleDir::Forward),
            ("seq_false_r", "(;; ?a bot)", "bot", RuleDir::Forward),
            ("interC", "(&& ?r1 ?r2)", "(&& ?r2 ?r1)", RuleDir::Forward),
            ("interK", "(&& ?r ?r)", "?r", RuleDir::Forward),
            ("inter_false_r", "(&& ?r bot)", "bot", RuleDir::Forward),
            ("inter_false_l", "(&& bot ?r)", "bot", RuleDir::Forward),
            ("inter_union_r", "(&& ?r (|| ?r1 ?r2))", "(|| (&& ?r ?r1) (&& ?r ?r2))", RuleDir::Backward),
            ("inter_union_l", "(&& (|| ?r1 ?r2) ?r)", "(|| (&& ?r1 ?r) (&& ?r2 ?r))", RuleDir::Backward),
            ("minus_false_r", "(setminus ?r bot)", "?r", RuleDir::Forward),
            ("minus_false_l", "(setminus bot ?r)", "bot", RuleDir::Forward),
            ("minusK", "(setminus ?r ?r)", "bot", RuleDir::Forward),
            ("crE", "(? ?r)", "(|| (complete_set) ?r)", RuleDir::Backward),
            ("rtE", "(* ?r)", "(|| (complete_set) (+ ?r))", RuleDir::Backward),
            ("csE", "(clos_sym ?r)", "(|| ?r (-1 ?r))", RuleDir::Backward),
            ("crsE", "(clos_refl_sym ?r)", "(|| (|| (complete_set) ?r) (-1 ?r))", RuleDir::Backward),
            ("crsEE", "(clos_refl_sym ?r)", "(|| (complete_set) (clos_sym ?r))", RuleDir::Backward),
            ("ct_rt", "(;; (+ ?a) (* ?a))", "(+ ?a)", RuleDir::Forward),
            ("rt_ct", "(;; (* ?a) (+ ?a))", "(+ ?a)", RuleDir::Forward),
            ("cr_ct", "(;; (? ?r) (+ ?r))", "(+ ?r)", RuleDir::Forward),
            ("ct_cr", "(;; (+ ?r) (? ?r))", "(+ ?r)", RuleDir::Forward),
            ("rt_rt", "(;; (* ?r) (* ?r))", "(* ?r)", RuleDir::Forward),
            ("cr_of_ct", "(? (+ ?r))", "(* ?r)", RuleDir::Forward),
            ("cr_of_cr", "(? (? ?r))", "(? ?r)", RuleDir::Forward),
            ("cr_of_rt", "(? (* ?r))", "(* ?r)", RuleDir::Forward),
            ("ct_of_ct", "(+ (+ ?r))", "(+ ?r)", RuleDir::Forward),
            ("ct_of_union_ct_l", "(+ (|| (+ ?r) ?r'))", "(+ (|| ?r ?r'))", RuleDir::Forward),
            ("ct_of_union_ct_r", "(+ (|| ?r (+ ?r')))", "(+ (|| ?r ?r'))", RuleDir::Forward),
            ("ct_of_cr", "(+ (? ?r))", "(* ?r)", RuleDir::Forward),
            ("ct_of_rt", "(+ (* ?r))", "(* ?r)", RuleDir::Forward),
            ("rt_of_ct", "(* (+ ?r))", "(* ?r)", RuleDir::Forward),
            ("rt_of_cr", "(* (? ?r))", "(* ?r)", RuleDir::Forward),
            ("rt_of_rt", "(* (* ?r))", "(* ?r)", RuleDir::Forward),
            ("cr_union_l", "(? (|| ?r ?r'))", "(|| (? ?r) ?r')", RuleDir::Forward),
            ("cr_union_r", "(? (|| ?r ?r'))", "(|| ?r (? ?r'))", RuleDir::Forward),
            ("cs_union", "(clos_sym (|| ?r ?r'))", "(|| (clos_sym ?r) (clos_sym ?r'))", RuleDir::Forward),
            ("crs_union", "(clos_refl_sym (|| ?r ?r'))", "(|| (clos_refl_sym ?r) (clos_refl_sym ?r'))", RuleDir::Forward),
            ("seq_id_l", "(;; complete_set ?a)", "?a", RuleDir::Forward),
            ("seq_id_r", "(;; ?a complete_set)", "?a", RuleDir::Forward),
            ("unionC", "(|| ?r1 ?r2)", "(|| ?r2 ?r1)", RuleDir::Forward),
            ("unionK", "(|| ?r ?r)", "?r", RuleDir::Forward),
            ("union_false_r", "(|| ?r bot)", "?r", RuleDir::Forward),
            ("union_false_l", "(|| bot ?r)", "?r", RuleDir::Forward),
            ("cr_seq", "(;; (? ?r) ?r')", "(|| ?r' (;; ?r ?r'))", RuleDir::Backward),
            ("ct_seq_swap", "(;; (+ (;; ?r ?r')) ?r)", "(;; ?r (+ (;; ?r' ?r)))", RuleDir::Forward),
        ])
    };
}

#[cfg(test)]
mod tests {
    use crate::*;

    #[test]
    fn test_default_rules() {
        let rules = RewriteRules::default();
        assert_eq!(rules.rules.len(), 51);
    }

    #[test]
    fn test_bidi() {
        let rules = RewriteRules::all_bidirectional();
        assert_eq!(rules.rules.len(), 92);
    }

    #[test]
    fn test_build_egraph_default() {
        let expr = "(;; (+ ?a) (* ?a))".parse().unwrap();
        let rules = RewriteRules::default();
        let _runner = Runner::default()
            .with_explanations_enabled()
            .with_expr(&expr)
            .run(&rules.rules);
    }

    #[test]
    fn test_build_egraph_bidi() {
        let expr = "(;; (+ ?a) (* ?a))".parse().unwrap();
        let rules = RewriteRules::all_bidirectional();
        let _runner = Runner::default()
            .with_explanations_enabled()
            .with_expr(&expr)
            .run(&rules.rules);
    }
}
