use egg::*;

use crate::{
    goal_preprocess::*,
    proof_sequence::*,
    axioms::*,
    make_rules::*,
};

use std::collections::LinkedList;

#[ocaml::func]
pub fn rust_configure_egg(axioms: LinkedList<(GoalSExpr, String)>) -> Result<(), ocaml::Error> {    
    let ax = Axioms(axioms);
    let res = save_axioms("axioms.json", ax);
    if let Err(_error) = res {
        return Err(ocaml::Error::Message("Unable to save Record"));
    }

    Ok(())
}

#[ocaml::func]
pub fn rust_simplify_expr(expr: GoalSExpr) -> Result<ProofSeq, ocaml::Error> {
    let rl = expr_to_rellang(&expr);

    if let Err(error) = rl {
        let message = error.into();
        return Err(ocaml::Error::Message(message));
    }
    
    Ok(get_simplification_proof(&rl.unwrap()))
}

/// Generate proof of equivalence between two expressions.
/// Build a E-graph for the lhs and then search it for
/// the rhs.
#[ocaml::func]
pub fn rust_prove_eq(expr1: GoalSExpr, expr2: GoalSExpr) -> Result<ProofSeq, ocaml::Error> {
    let rl1 = expr_to_rellang(&expr1);
    let rl2 = expr_to_rellang(&expr2);

    if rl1.is_err() || rl2.is_err() {
        let message = ExprParseError::SexpParsingError.into();
        return Err(ocaml::Error::Message(message));
    }
    let rl1 = rl1.unwrap(); let rl2 = rl2.unwrap();

    let mut rules = make_rules();

    let new_rules = extend_rules_w_axioms(&mut rules);
    if let Err(_error) = new_rules {
        return Err(ocaml::Error::Message("Unable to load axioms"));
    }

    let mut runner = Runner::default()
        .with_explanations_enabled()
        .with_expr(&rl1)
        .run(&rules);

    let mut explanation = runner.explain_equivalence(&rl1, &rl2);
    let proof = parse_proof(&mut explanation);

    Ok(ProofSeq::from(proof))
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
    let (_best_cost, best) = extractor.find_best(root);
    
    let mut explanation = runner.explain_equivalence(&expr, &best);
    let proof = parse_proof(&mut explanation);

    ProofSeq::from(proof)
}

pub mod goal_preprocess;
pub mod proof_sequence;
pub mod axioms;
pub mod make_rules;