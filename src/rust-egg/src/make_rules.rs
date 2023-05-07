use std::collections::HashMap;
use crate::{axioms::*, rewrite_in_runtime, RelLanguage};
use egg::{Rewrite, AstSize, RecExpr, CostFunction};
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
pub type RuleRepr = Vec<(&'static str, &'static str, &'static str, RuleDir)>;

pub struct RewriteRules {
    pub rules: RelRules,
    pub rules_dict: HashMap<String, Rewrite<RelLanguage, ()>>
}

impl RewriteRules {
    pub fn new() -> Self {
        Self { rules: vec![], rules_dict: HashMap::new() }
    }

    pub fn get_rule_by_name(&self, name: &str) -> Option<&Rewrite<RelLanguage, ()>> {
        self.rules_dict.get(name)
    }

    pub fn push(&mut self, rule: Rewrite<RelLanguage, ()>) {
        self.rules_dict.insert(rule.name.as_str().to_string(), rule.clone());
        self.rules.push(rule);
    }

    pub fn neat_push(&mut self, rule: StdResult<Rewrite<RelLanguage, ()>, String>) {
        if let Ok(rule) = rule {
            self.rules_dict.insert(rule.name.as_str().to_string(), rule.clone());
            self.rules.push(rule);
        }
    }

    pub fn default(from: &RuleRepr) -> Self {
        let mut rules = Self::new();
        for (name, lhs, rhs, dir) in from.iter() {
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

    pub fn all_bidirectional(from: &RuleRepr) -> Self {
        let mut rules = Self::new();
        for (name, lhs, rhs, _) in from.iter() {
            rules.neat_push(rewrite_in_runtime(name, lhs, rhs));
            rules.neat_push(rewrite_in_runtime(&format!("{}-rev", name), rhs, lhs));
        }

        rules
    }

    pub fn all_decreasing(from: &RuleRepr) -> Self {
        let mut rules = Self::new();
        for (name, lhs, rhs, _) in from.iter() {
            let left: RecExpr<RelLanguage> = lhs.parse().unwrap();
            let right: RecExpr<RelLanguage> = rhs.parse().unwrap();

            if AstSize.cost_rec(&left) > AstSize.cost_rec(&right) {
                rules.neat_push(rewrite_in_runtime(name, lhs, rhs));
            } else {
                rules.neat_push(rewrite_in_runtime(&format!("{}-rev", name), rhs, lhs));
            }
        }

        rules
    }
 
    pub fn extend_with_wf(&mut self, path: &'static str) -> Result<()> {
        let axioms = load_axioms(path);
        let axioms_rules = extract_rules_from_axioms(&axioms)?;
        axioms_rules.iter().for_each(|rule| {
            self.rules_dict.insert(rule.name.as_str().to_string(), rule.clone());
        });
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

#[cfg(test)]
mod tests {
    use crate::*;

    #[test]
    fn test_default_rules() {
        let rules = RewriteRules::default(&RULES);
        assert_eq!(rules.rules.len(), 53);
    }

    #[test]
    fn test_bidi() {
        let rules = RewriteRules::all_bidirectional(&RULES);
        assert_eq!(rules.rules.len(), 96);
    }

    #[test]
    fn test_build_egraph_default() {
        let expr = "(;; (+ ?a) (* ?a))".parse().unwrap();
        let rules = RewriteRules::default(&RULES);
        let _runner = Runner::default()
            .with_explanations_enabled()
            .with_expr(&expr)
            .run(&rules.rules);
    }

    #[test]
    fn test_build_egraph_bidi() {
        let expr = "(;; (+ ?a) (* ?a))".parse().unwrap();
        let rules = RewriteRules::all_bidirectional(&RULES);
        let _runner = Runner::default()
            .with_explanations_enabled()
            .with_expr(&expr)
            .run(&rules.rules);
    }

    #[test]
    fn test_cost_fn() {
        let rules: RuleRepr = vec![
            ("a", "(;; ?a ?b)", "(;; ?b ?a)", RuleDir::Forward),
            ("b", "(&& ?a ?b)", "(|| ?b ?a)", RuleDir::Backward),
            ("c", "(? (? ?a))", "(? ?a)", RuleDir::Forward),
            ("c1", "(* (* ?a))", "(* ?a)", RuleDir::Forward),
            ("c", "(+ (+ ?a))", "(+ ?a)", RuleDir::Forward),
            ("union_false_r", "(|| ?r bot)", "?r", RuleDir::Forward),
            ("union_false_l", "(|| bot ?r)", "?r", RuleDir::Forward),
        ];

        let rules = RewriteRules::all_decreasing(&rules);
        assert_eq!(rules.rules.len(), 7);

        assert!(AstSize.cost_rec(&"(;; ?a ?b)".parse::<egg::RecExpr<RelLanguage>>().unwrap())
            > AstSize.cost_rec(&"?b".parse::<egg::RecExpr<RelLanguage>>().unwrap()));
        assert!(AstSize.cost_rec(&"(;; ?a ?b)".parse::<egg::RecExpr<RelLanguage>>().unwrap())
            > AstSize.cost_rec(&"?a".parse::<egg::RecExpr<RelLanguage>>().unwrap()));
        assert!(AstSize.cost_rec(&"(? ?b)".parse::<egg::RecExpr<RelLanguage>>().unwrap())
            > AstSize.cost_rec(&"(?b)".parse::<egg::RecExpr<RelLanguage>>().unwrap()));
    }
}
