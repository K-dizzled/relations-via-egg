use egg::*;

use crate::goal_preprocess::*;
use crate::proof_sequence::*;

#[ocaml::func]
pub fn rust_simplify_expr(expr: GoalSExpr) -> Result<ProofSeq, ocaml::Error> {
    let rl = expr_to_rellang(&expr);

    if let Err(error) = rl {
        let message = error.into();
        return Err(ocaml::Error::Message(message));
    }
    
    Ok(get_simplification_proof(&rl.unwrap()))
}

/// Extract hahn COQ library theorems to rewrite
/// rules and afterwards build graph using them
fn make_rules() -> Vec<Rewrite<RelLanguage, ()>> {
    let mut rules =
        vec![ 
            rewrite!("ct_end"  ; "(+ ?a)" <=> "(;; (* ?a) ?a)"),
            rewrite!("ct_begin"; "(+ ?a)" <=> "(;; ?a (* ?a))"),
        ].concat();

    rules.extend(
        vec![
            // rewrite!("seqA"    ; "(;; (;; ?a ?b) ?c)" => "(;; (;; ?a ?b) ?c)"),
            rewrite!("rt_cr"  ; "(;; (* ?a) (? ?a))" => "(* ?a)"),

            rewrite!("seq_id_l"   ; "(;; top ?a)" => "?a"),
            rewrite!("seq_id_r"   ; "(;; ?a top)" => "?a"),
            rewrite!("seq_false_l"; "(;; bot ?a)" => "bot"),
            rewrite!("seq_false_r"; "(;; ?a bot)" => "bot"),
            rewrite!("seq_ct"; "(;; (+ ?a) (+ ?a))" => "(+ ?a)"),
            rewrite!("ct_rt"; "(;; (+ ?a) (* ?a))" => "(+ ?a)"),
            rewrite!("rt_ct"; "(;; (* ?a) (+ ?a))" => "(+ ?a)"),
        ]);

    rules
}

/// Build a E-graph for expression, get the best 
/// element, then extract the sequence of rules
/// to explain equivalence. 
fn get_simplification_proof(expr: &RecExpr<RelLanguage>) -> ProofSeq {
    let mut runner = Runner::default()
        .with_explanations_enabled()
        .with_expr(&expr)
        .run(&make_rules());

    let root = runner.roots[0];

    let extractor = Extractor::new(&runner.egraph, AstSize);
    let (best_cost, best) = extractor.find_best(root);

    println!("Simplified {} to {} with cost {}", expr, best, best_cost);
    
    let mut explanation = runner.explain_equivalence(&expr, &best);
    let proof = parse_proof(&mut explanation);

    ProofSeq::from(proof)
}

/// Generate proof of equivalence between two expressions.
/// Build a E-graph for the lhs and then search it for
/// the rhs. Unused for now.
#[allow(dead_code)]
#[ocaml::func]
pub fn rust_prove_eq(expr1: GoalSExpr, expr2: GoalSExpr) -> String {
    let rl1 = expr_to_rellang(&expr1).unwrap();
    let rl2 = expr_to_rellang(&expr2).unwrap();

    let mut runner = Runner::default()
        .with_explanations_enabled()
        .with_expr(&rl1)
        .run(&make_rules());

    let explanation = runner.explain_equivalence(&rl1, &rl2)
                            .get_flat_string();

    println!("{}", explanation);

    explanation
}

pub mod goal_preprocess;
pub mod proof_sequence;