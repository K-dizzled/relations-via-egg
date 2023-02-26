use crate::{
    RelLanguage,
    RelRules,
    ProofSeq,
    parse_proof,
};
use egg::*;
use std::path::Path;

#[derive(Debug)]
pub enum ProofError {
    FailedToProve,
}

impl Into<&str> for ProofError {
    fn into(self) -> &'static str {
        match self {
            ProofError::FailedToProve => "Failed to prove the equality.",
        }
    }
}

pub trait ProofStrategy {
    fn prove_eq(
        &self, 
        expr1: &RecExpr<RelLanguage>, 
        expr2: &RecExpr<RelLanguage>, 
        rules: &RelRules,
        debug: bool,
    ) -> Result<ProofSeq, ProofError>;
}

// Build an e-graph for the lhs and then search it for the rhs.
pub struct ProofStrategySBiA {}

// Build an e-graph for the lhs and the rhs and
// search if the other side of the eq
// is contained in the e-graph.
pub struct ProofStrategySearchBoth {}

// Build two e-graphs for the lhs and the rhs and
// then find their union.
pub struct ProofStrategySearchUnion {}

fn debug_graph_pdf(egraph: &EGraph<RelLanguage, ()>, expr_str: &str, debug: bool) {
    if debug {
        std::fs::create_dir_all("egraphs").unwrap();
        let filename = "egraphs/".to_string() + &expr_str + ".pdf";
        let names = [filename, "last_expr.pdf".to_string()];

        for name in names.iter() {
            // That's needed to add a '-q 1' flag to the dot call.
            // Otherwise, graphviz is constantly printing
            // warnings to stdout.
            egraph.dot().run_dot(
                &[<str as AsRef<Path>>::as_ref("-Tpdf"),
                    "-q 1".as_ref(),
                    "-o".as_ref(),
                    name.as_ref()
                ]
            ).unwrap();
        }
    }
}


impl ProofStrategy for ProofStrategySBiA {
    fn prove_eq(
        &self, 
        expr1: &RecExpr<RelLanguage>, 
        expr2: &RecExpr<RelLanguage>, 
        rules: &RelRules,
        debug: bool,
    ) -> Result<ProofSeq, ProofError> {
        let mut runner = Runner::default()
            .with_explanations_enabled()
            .with_expr(&expr1)
            .run(rules);

        debug_graph_pdf(&runner.egraph, &expr1.to_string(), debug);

        let equivs = runner.egraph.equivs(&expr1, expr2);
        if equivs.is_empty() {
            return Err(ProofError::FailedToProve);
        }

        let mut explanation = runner.explain_equivalence(&expr1, &expr2);
        let proof = parse_proof(&mut explanation);

        Ok(ProofSeq::from(proof))
    }
}

impl ProofStrategy for ProofStrategySearchBoth {
    fn prove_eq(
        &self,
        expr1: &RecExpr<RelLanguage>,
        expr2: &RecExpr<RelLanguage>,
        rules: &RelRules,
        debug: bool,
    ) -> Result<ProofSeq, ProofError> {
        let mut runner1 = Runner::default()
            .with_explanations_enabled()
            .with_expr(&expr1)
            .run(rules);

        let equivs = runner1.egraph.equivs(&expr1, expr2);
        if equivs.is_empty() {
            let mut runner2 = Runner::default()
                .with_explanations_enabled()
                .with_expr(&expr2)
                .run(rules);

            let equivs2 = runner2.egraph.equivs(&expr2, expr1);
            if equivs2.is_empty() {
                return Err(ProofError::FailedToProve);
            }

            debug_graph_pdf(&runner2.egraph, &expr1.to_string(), debug);
            let mut explanation = runner2.explain_equivalence(&expr2, &expr1);
            let proof = parse_proof(&mut explanation);

            return Ok(ProofSeq::from(proof));
        }

        debug_graph_pdf(&runner1.egraph, &expr1.to_string(), debug);
        let mut explanation = runner1.explain_equivalence(&expr1, &expr2);
        let proof = parse_proof(&mut explanation);

        Ok(ProofSeq::from(proof))
    }
}