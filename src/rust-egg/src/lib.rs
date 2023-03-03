use egg::*;

use crate::{
    axioms::*, egraph_intersect::intersect, goal_preprocess::*, make_rules::*, proof_sequence::*,
    proof_strategy::*, config::*,
};

use std::collections::LinkedList;

#[ocaml::func]
pub fn rust_configure_egg(axioms: LinkedList<(GoalSExpr, String)>) -> Result<(), ocaml::Error> {
    let ax = Axioms(axioms);
    let res = save_axioms(&*WF_FILE, ax);
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
pub fn rust_prove_eq(
    expr1: GoalSExpr,
    expr2: GoalSExpr,
    debug: bool,
) -> Result<ProofSeq, ocaml::Error> {
    let rl1 = expr_to_rellang(&expr1);
    let rl2 = expr_to_rellang(&expr2);

    if rl1.is_err() || rl2.is_err() {
        let message = ExprParseError::SexpParsingError.into();
        return Err(ocaml::Error::Message(message));
    }
    let rl1 = rl1.unwrap(); let rl2 = rl2.unwrap();

    let proof_strategy = ProofStrategySearchBoth {};
    let proof = proof_strategy.prove_eq(&rl1, &rl2, &RULES, debug);
    if let Err(error) = proof {
        let message = error.into();
        return Err(ocaml::Error::Message(message));
    }

    Ok(proof.unwrap())
}

/// Build a E-graph for expression, get the best
/// element, then extract the sequence of rules
/// to explain equivalence.
fn get_simplification_proof(expr: &RecExpr<RelLanguage>) -> ProofSeq {
    let rules = RewriteRules::default(&RULES);
    let mut runner = Runner::default()
        .with_explanations_enabled()
        .with_expr(&expr)
        .run(&rules.rules);

    let root = runner.roots[0];

    let extractor = Extractor::new(&runner.egraph, AstSize);
    let (_best_cost, best) = extractor.find_best(root);

    let mut explanation = runner.explain_equivalence(&expr, &best);
    let proof = parse_proof(&mut explanation);

    ProofSeq::from(proof)
}

pub mod axioms;
pub mod egraph_intersect;
pub mod goal_preprocess;
pub mod make_rules;
pub mod proof_sequence;
pub mod proof_strategy;
pub mod config;
