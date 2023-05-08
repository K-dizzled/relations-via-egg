use lazy_static::lazy_static;
use crate::{
    make_rules::RuleRepr,
    make_rules::RuleDir,
};

lazy_static! {
    pub static ref WF_FILE: &'static str = "axioms.json";
    /// Extract hahn COQ library theorems to rewrite
    /// rules and afterwards build graph using them
    pub static ref RULES: RuleRepr = {
        Vec::from([
            ("ct_end", "(+ ?r)", "(;; (* ?r) ?r)", RuleDir::Bidirectional, vec!["?r"]),
            ("ct_begin", "(+ ?r)", "(;; ?r (* ?r))", RuleDir::Bidirectional, vec!["?r"]),
            ("rt_begin", "(* ?r)", "(|| (complete_set) (;; ?r (* ?r)))", RuleDir::Backward, vec!["?r"]),
            ("rt_end", "(* ?r)", "(|| (complete_set) (;; (* ?r) ?r))", RuleDir::Backward, vec!["?r"]),
            ("rt_cr", "(;; (* ?r) (? ?r))", "(* ?r)", RuleDir::Forward, vec!["?r"]),
            ("seq_false_l", "(;; bot ?r)", "bot", RuleDir::Forward, vec!["?r"]),
            ("seq_false_r", "(;; ?r bot)", "bot", RuleDir::Forward, vec!["?r"]),
            ("interC", "(&& ?r1 ?r2)", "(&& ?r2 ?r1)", RuleDir::Forward, vec!["?r1", "?r2"]),
            ("interK", "(&& ?r ?r)", "?r", RuleDir::Forward, vec!["?r"]),
            ("inter_false_r", "(&& ?r bot)", "bot", RuleDir::Forward, vec!["?r"]),
            ("inter_false_l", "(&& bot ?r)", "bot", RuleDir::Forward, vec!["?r"]),
            ("inter_union_r", "(&& ?r (|| ?r1 ?r2))", "(|| (&& ?r ?r1) (&& ?r ?r2))", RuleDir::Backward, vec!["?r", "?r1", "?r2"]),
            ("inter_union_l", "(&& (|| ?r1 ?r2) ?r)", "(|| (&& ?r1 ?r) (&& ?r2 ?r))", RuleDir::Backward, vec!["?r", "?r1", "?r2"]),
            ("minus_false_r", "(setminus ?r bot)", "?r", RuleDir::Forward, vec!["?r"]),
            ("minus_false_l", "(setminus bot ?r)", "bot", RuleDir::Forward, vec!["?r"]),
            ("minusK", "(setminus ?r ?r)", "bot", RuleDir::Forward, vec!["?r"]),
            ("crE", "(? ?r)", "(|| (complete_set) ?r)", RuleDir::Backward, vec!["?r"]),
            ("rtE", "(* ?r)", "(|| (complete_set) (+ ?r))", RuleDir::Backward, vec!["?r"]),
            ("csE", "(clos_sym ?r)", "(|| ?r (-1 ?r))", RuleDir::Backward, vec!["?r"]),
            ("crsE", "(clos_refl_sym ?r)", "(|| (|| (complete_set) ?r) (-1 ?r))", RuleDir::Backward, vec!["?r"]),
            ("crsEE", "(clos_refl_sym ?r)", "(|| (complete_set) (clos_sym ?r))", RuleDir::Backward, vec!["?r"]),
            ("ct_rt", "(;; (+ ?r) (* ?r))", "(+ ?r)", RuleDir::Forward, vec!["?r"]),
            ("rt_ct", "(;; (* ?r) (+ ?r))", "(+ ?r)", RuleDir::Forward, vec!["?r"]),
            ("cr_ct", "(;; (? ?r) (+ ?r))", "(+ ?r)", RuleDir::Forward, vec!["?r"]),
            ("ct_cr", "(;; (+ ?r) (? ?r))", "(+ ?r)", RuleDir::Forward, vec!["?r"]),
            ("rt_rt", "(;; (* ?r) (* ?r))", "(* ?r)", RuleDir::Forward, vec!["?r"]),
            ("cr_of_ct", "(? (+ ?r))", "(* ?r)", RuleDir::Forward, vec!["?r"]),
            ("cr_of_cr", "(? (? ?r))", "(? ?r)", RuleDir::Forward, vec!["?r"]),
            ("cr_of_rt", "(? (* ?r))", "(* ?r)", RuleDir::Forward, vec!["?r"]),
            ("ct_of_ct", "(+ (+ ?r))", "(+ ?r)", RuleDir::Forward, vec!["?r"]),
            ("ct_of_union_ct_l", "(+ (|| (+ ?r) ?r'))", "(+ (|| ?r ?r'))", RuleDir::Forward, vec!["?r", "?r'"]),
            ("ct_of_union_ct_r", "(+ (|| ?r (+ ?r')))", "(+ (|| ?r ?r'))", RuleDir::Forward, vec!["?r", "?r'"]),
            ("ct_of_cr", "(+ (? ?r))", "(* ?r)", RuleDir::Forward, vec!["?r"]),
            ("ct_of_rt", "(+ (* ?r))", "(* ?r)", RuleDir::Forward, vec!["?r"]),
            ("rt_of_ct", "(* (+ ?r))", "(* ?r)", RuleDir::Forward, vec!["?r"]),
            ("rt_of_cr", "(* (? ?r))", "(* ?r)", RuleDir::Forward, vec!["?r"]),
            ("rt_of_rt", "(* (* ?r))", "(* ?r)", RuleDir::Forward, vec!["?r"]),
            ("cr_union_l", "(? (|| ?r ?r'))", "(|| (? ?r) ?r')", RuleDir::Forward, vec!["?r", "?r'"]),
            ("cr_union_r", "(? (|| ?r ?r'))", "(|| ?r (? ?r'))", RuleDir::Forward, vec!["?r", "?r'"]),
            ("cs_union", "(clos_sym (|| ?r ?r'))", "(|| (clos_sym ?r) (clos_sym ?r'))", RuleDir::Forward, vec!["?r", "?r'"]),
            ("crs_union", "(clos_refl_sym (|| ?r ?r'))", "(|| (clos_refl_sym ?r) (clos_refl_sym ?r'))", RuleDir::Forward, vec!["?r", "?r'"]),
            ("seq_id_l", "(;; complete_set ?r)", "?r", RuleDir::Forward, vec!["?r"]),
            ("seq_id_r", "(;; ?r complete_set)", "?r", RuleDir::Forward, vec!["?r"]),
            ("unionC", "(|| ?r1 ?r2)", "(|| ?r2 ?r1)", RuleDir::Forward, vec!["?r"]),
            ("unionK", "(|| ?r ?r)", "?r", RuleDir::Forward, vec!["?r"]),
            ("union_false_r", "(|| ?r bot)", "?r", RuleDir::Forward, vec!["?r"]),
            ("union_false_l", "(|| bot ?r)", "?r", RuleDir::Forward, vec!["?r"]),
            ("cr_seq", "(;; (? ?r) ?r')", "(|| ?r' (;; ?r ?r'))", RuleDir::Backward, vec!["?r", "?r'"]),
            ("ct_seq_swap", "(;; (+ (;; ?r ?r')) ?r)", "(;; ?r (+ (;; ?r' ?r)))", RuleDir::Forward, vec!["?r", "?r'"]),
            ("seq_union_l", "(;; (|| ?r1 ?r2) ?r)", "(|| (;; ?r1 ?r) (;; ?r2 ?r))", RuleDir::Forward, vec!["?r1", "?r2", "?r"]),
            ("seq_union_r", "(;; ?r (|| ?r1 ?r2))", "(|| (;; ?r ?r1) (;; ?r ?r2))", RuleDir::Forward, vec!["?r", "?r1", "?r2"])
        ])
    };
}