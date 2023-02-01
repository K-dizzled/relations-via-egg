use std::collections::LinkedList;
use egg::{Explanation, FlatTerm, Language};

/// Direction of Rewrite in the 
/// proof
#[derive(Debug, ocaml::IntoValue)]
pub enum Direction {
    Forward,
    Backward,
}

/// A single rewrite in the proof
#[derive(Debug, ocaml::IntoValue)]
pub struct Rule {
    pub direction: Direction,
    pub theorem: String,
}

/// A sequence of rewrites
#[derive(Debug, ocaml::IntoValue)]
pub struct ProofSeq {
    pub rules: LinkedList<Rule>,
}

impl ProofSeq {
    pub fn from(rules: LinkedList<Rule>) -> ProofSeq {
        ProofSeq {
            rules,
        }
    }
}

pub fn parse_proof<L>(expl: &mut Explanation<L>) -> LinkedList<Rule> where 
    L: Language, 
    L: std::fmt::Display,
    L: egg::FromOp,
{
    expl.make_flat_explanation()
        .iter()
        .map(|ft| ft_to_rule(ft))
        .filter(|rule| rule.is_some())
        .map(|rule| rule.unwrap())
        .collect()
}

/// The FlatTerm is basically an S-expr with some extra
/// information about the rule that was applied to get
/// the term. Recursively search for the rewrites
pub fn ft_to_rule<L>(ft: &FlatTerm<L>) -> Option<Rule> where 
    L: Language, 
    L: std::fmt::Display,
    L: egg::FromOp,
{
    if let Some(rule_name) = &ft.forward_rule {
        let rule_name = (*rule_name).to_string();
        if rule_name.ends_with("-rev") {
            let rule_name_wo_dir = rule_name.split("-rev").next().unwrap();
            return Some(Rule {
                direction: Direction::Backward,
                theorem: rule_name_wo_dir.to_string(),
            });
        }

        return Some(Rule {
            direction: Direction::Forward,
            theorem: (*rule_name).to_string(),
        });
    }

    for child in &ft.children {
        if let Some(rule) = ft_to_rule(child) {
            return Some(rule);
        }
    }

    None
}