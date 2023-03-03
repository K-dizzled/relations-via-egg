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