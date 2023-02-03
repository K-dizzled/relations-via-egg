use egg::{rewrite, Rewrite};
use crate::RelLanguage;

pub type RelRules = Vec<Rewrite<RelLanguage, ()>>;
/// Extract hahn COQ library theorems to rewrite
/// rules and afterwards build graph using them
pub fn make_rules() -> RelRules {
    let mut rules =
        vec![ 
            rewrite!("ct_end"  ; "(+ ?a)" <=> "(;; (* ?a) ?a)"),
            rewrite!("ct_begin"; "(+ ?a)" <=> "(;; ?a (* ?a))"),
        ].concat();

    rules.extend(
        vec![
            rewrite!("rt_cr"  ; "(;; (* ?a) (? ?a))" => "(* ?a)"),
            rewrite!("seq_false_l"; "(;; bot ?a)" => "bot"),
            rewrite!("seq_false_r"; "(;; ?a bot)" => "bot"),
            rewrite!("interC"; "(&& ?r1 ?r2)" => "(&& ?r2 ?r1)"),
            rewrite!("interA"; "(&& (&& ?r1 ?r2) ?r3)" => "(&& ?r1 (&& ?r2 ?r3))"),
            rewrite!("interAC"; "(&& ?r (&& ?r' ?r''))" => "(&& ?r' (&& ?r ?r''))"),
            rewrite!("interK"; "(&& ?r ?r)" => "?r"),
            rewrite!("inter_false_r"; "(&& ?r bot)" => "bot"),
            rewrite!("inter_false_l"; "(&& bot ?r)" => "bot"),
            rewrite!("inter_union_r"; "(&& ?r (|| ?r1 ?r2))" => "(|| (&& ?r ?r1) (&& ?r ?r2))"),
            rewrite!("inter_union_l"; "(&& (|| ?r1 ?r2) ?r)" => "(|| (&& ?r1 ?r) (&& ?r2 ?r))"),
            rewrite!("inter_inclusion"; "(&& ?r ?i)" => "?r"),
            rewrite!("minus_false_r"; "(setminus ?r bot)" => "?r"),
            rewrite!("minus_false_l"; "(setminus bot ?r)" => "bot"),
            rewrite!("minusK"; "(setminus ?r ?r)" => "bot"),
            rewrite!("crE"; "(? ?r)" => "(|| (complete_set) ?r)"),
            rewrite!("rtE"; "(* ?r)" => "(|| (complete_set) (+ ?r))"),
            rewrite!("csE"; "(clos_sym ?r)" => "(|| ?r (-1 ?r))"),
            rewrite!("crsE"; "(clos_refl_sym ?r)" => "(|| (|| (complete_set) ?r) (-1 ?r))"),
            rewrite!("crsEE"; "(clos_refl_sym ?r)" => "(|| (complete_set) (clos_sym ?r))"),
            rewrite!("rt_begin"; "(* ?r)" => "(|| (complete_set) (;; ?r (* ?r)))"),
            rewrite!("rt_end"; "(* ?r)" => "(|| (complete_set) (;; (* ?r) ?r))"),
            rewrite!("ct_ct"; "(;; (+ ?a) (+ ?a))" => "(+ ?a)"),
            rewrite!("ct_rt"; "(;; (+ ?a) (* ?a))" => "(+ ?a)"),
            rewrite!("rt_ct"; "(;; (* ?a) (+ ?a))" => "(+ ?a)"),
            rewrite!("cr_ct"; "(;; (? ?r) (+ ?r))" => "(+ ?r)"),
            rewrite!("ct_cr"; "(;; (+ ?r) (? ?r))" => "(+ ?r)"),
            rewrite!("rt_rt"; "(;; (* ?r) (* ?r))" => "(* ?r)"),
            rewrite!("cr_of_ct"; "(? (+ ?r))" => "(* ?r)"),
            rewrite!("cr_of_cr"; "(? (? ?r))" => "(? ?r)"),
            rewrite!("cr_of_rt"; "(? (* ?r))" => "(* ?r)"),
            rewrite!("ct_of_ct"; "(+ (+ ?r))" => "(+ ?r)"),
            rewrite!("ct_of_union_ct_l"; "(+ (|| (+ ?r) ?r'))" => "(+ (|| ?r ?r'))"),
            rewrite!("ct_of_union_ct_r"; "(+ (|| ?r (+ ?r')))" => "(+ (|| ?r ?r'))"),
            rewrite!("ct_of_cr"; "(+ (? ?r))" => "(* ?r)"),
            rewrite!("ct_of_rt"; "(+ (* ?r))" => "(* ?r)"),
            rewrite!("rt_of_ct"; "(* (+ ?r))" => "(* ?r)"),
            rewrite!("rt_of_cr"; "(* (? ?r))" => "(* ?r)"),
            rewrite!("rt_of_rt"; "(* (* ?r))" => "(* ?r)"),
            rewrite!("cr_union_l"; "(? (|| ?r ?r'))" => "(|| (? ?r) ?r')"),
            rewrite!("cr_union_r"; "(? (|| ?r ?r'))" => "(|| ?r (? ?r'))"),
            rewrite!("cs_union"; "(clos_sym (|| ?r ?r'))" => "(|| (clos_sym ?r) (clos_sym ?r'))"),
            rewrite!("crs_union"; "(clos_refl_sym (|| ?r ?r'))" => "(|| (clos_refl_sym ?r) (clos_refl_sym ?r'))"),
            rewrite!("cs_inter"; "(clos_sym (&& ?r ?r'))" => "(&& (clos_sym ?r) (clos_sym ?r'))"),
            rewrite!("crs_inter"; "(clos_refl_sym (&& ?r ?r'))" => "(&& (clos_refl_sym ?r) (clos_refl_sym ?r'))"),
            rewrite!("seq_id_l"   ; "(;; complete_set ?a)" => "?a"),
            rewrite!("seq_id_r"   ; "(;; ?a complete_set)" => "?a"),
        ]);

    rules
}