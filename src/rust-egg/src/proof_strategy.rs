use crate::{
    intersect,
    parse_proof,
    ProofSeq,
    RelLanguage,
    RuleRepr,
    WF_FILE,
};
use egg::*;
use std::path::Path;
use crate::make_rules::RewriteRules;

#[derive(Debug)]
pub enum ProofError {
    FailedToProve,
    UnableToLoadAxioms,
}

impl Into<&str> for ProofError {
    fn into(self) -> &'static str {
        match self {
            ProofError::FailedToProve => "Failed to prove the equality.",
            ProofError::UnableToLoadAxioms => "Unable to load axioms.",
        }
    }
}

pub trait ProofStrategy {
    fn prove_eq(
        &self,
        expr1: &RecExpr<RelLanguage>,
        expr2: &RecExpr<RelLanguage>,
        rules: &RuleRepr,
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
// then find their intersection.
pub struct ProofStrategySearchIntersect {}

// Add all rules to the e-graph as bidirectional rules.
// Build an e-graph for the lhs and search it for the rhs.
pub struct ProofStrategyAllBidi {}

pub fn debug_graph_pdf(egraph: &EGraph<RelLanguage, ()>, expr_str: &str, debug: bool) {
    if debug {
        std::fs::create_dir_all("egraphs").unwrap();
        let filename = "egraphs/".to_string() + &expr_str + ".pdf";
        let names = [filename, "last_expr.pdf".to_string()];

        for name in names.iter() {
            // That's needed to add a '-q 1' flag to the dot call.
            // Otherwise, graphviz is constantly printing
            // warnings to stdout.
            egraph
                .dot()
                .run_dot(&[
                    <str as AsRef<Path>>::as_ref("-Tpdf"),
                    "-q 1".as_ref(),
                    "-o".as_ref(),
                    name.as_ref(),
                ])
                .unwrap();
        }
    }
}

fn debug_msg(msg: &str, debug: bool) {
    if debug {
        println!("{}", msg);
    }
}

impl ProofStrategy for ProofStrategySBiA {
    fn prove_eq(
        &self,
        expr1: &RecExpr<RelLanguage>,
        expr2: &RecExpr<RelLanguage>,
        rules: &RuleRepr,
        debug: bool,
    ) -> Result<ProofSeq, ProofError> {
        let mut rules = RewriteRules::default(&rules);
        let res = rules.extend_with_wf(&WF_FILE);
        if let Err(_error) = res { return Err(ProofError::UnableToLoadAxioms); }

        let mut runner = Runner::default()
            .with_explanations_enabled()
            .with_expr(&expr1)
            .run(&rules.rules);

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
        rules: &RuleRepr,
        debug: bool,
    ) -> Result<ProofSeq, ProofError> {
        let mut rules = RewriteRules::default(&rules);
        let res = rules.extend_with_wf(&WF_FILE);
        if let Err(_error) = res { return Err(ProofError::UnableToLoadAxioms); }

        let mut runner1 = Runner::default()
            .with_explanations_enabled()
            .with_expr(&expr1)
            .run(&rules.rules);

        let equivs = runner1.egraph.equivs(&expr1, expr2);
        if equivs.is_empty() {
            let mut runner2 = Runner::default()
                .with_explanations_enabled()
                .with_expr(&expr2)
                .run(&rules.rules);

            let equivs2 = runner2.egraph.equivs(&expr2, expr1);
            if equivs2.is_empty() {
                return Err(ProofError::FailedToProve);
            }

            debug_graph_pdf(&runner2.egraph, &expr1.to_string(), debug);
            let mut explanation = runner2.explain_equivalence(&expr2, &expr1);
            debug_msg(
                format!("Explanation: {:?}", explanation.to_string()).as_str(),
                debug,
            );
            let proof = parse_proof(&mut explanation);

            return Ok(ProofSeq::from(proof));
        }

        debug_graph_pdf(&runner1.egraph, &expr1.to_string(), debug);
        let mut explanation = runner1.explain_equivalence(&expr1, &expr2);
        debug_msg(
            format!("Explanation: {:?}", explanation.to_string()).as_str(),
            debug,
        );
        let proof = parse_proof(&mut explanation);

        Ok(ProofSeq::from(proof))
    }
}

impl ProofStrategy for ProofStrategySearchIntersect {
    #[allow(unused)]
    fn prove_eq(
        &self,
        expr1: &RecExpr<RelLanguage>,
        expr2: &RecExpr<RelLanguage>,
        rules: &RuleRepr,
        debug: bool,
    ) -> Result<ProofSeq, ProofError> {
        let mut rules = RewriteRules::default(&rules);
        let res = rules.extend_with_wf(&WF_FILE);
        if let Err(_error) = res { return Err(ProofError::UnableToLoadAxioms); }

        let runner1 = Runner::default()
            .with_explanations_enabled()
            .with_expr(&expr1)
            .run(&rules.rules);

        let runner2 = Runner::default()
            .with_explanations_enabled()
            .with_expr(&expr2)
            .run(&rules.rules);

        let intersection = intersect(&runner1.egraph, &runner2.egraph, ());
        if intersection.is_empty() {
            return Err(ProofError::FailedToProve);
        }

        // take best cost from the intersection and show eq
        // from the lhs to the intersection and from the intersection to the rhs.
        let mut runner = Runner::default()
            .with_explanations_enabled()
            .with_egraph(intersection);

        let root = runner.roots[0];

        let extractor = Extractor::new(&runner.egraph, AstSize);
        let (_best_cost, best) = extractor.find_best(root);

        let mut explanation_left_to_mid = runner.explain_equivalence(&expr1, &best);
        let mut proof = parse_proof(&mut explanation_left_to_mid);

        let mut explanation_mid_to_right = runner.explain_equivalence(&best, &expr2);
        let mut proof2 = parse_proof(&mut explanation_mid_to_right);

        proof.append(&mut proof2);

        Ok(ProofSeq::from(proof))
    }
}

impl ProofStrategy for ProofStrategyAllBidi {
    #[allow(unused)]
    fn prove_eq(
        &self,
        expr1: &RecExpr<RelLanguage>,
        expr2: &RecExpr<RelLanguage>,
        rules: &RuleRepr,
        debug: bool,
    ) -> Result<ProofSeq, ProofError> {
        let mut rules = RewriteRules::all_bidirectional(&rules);
        let res = rules.extend_with_wf(&WF_FILE);
        if let Err(_error) = res { return Err(ProofError::UnableToLoadAxioms); }

        let mut runner = Runner::default()
            .with_explanations_enabled()
            .with_node_limit(1000)
            .with_expr(&expr1)
            .run(&rules.rules);

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

#[cfg(test)]
mod tests {
    use crate::*;

    #[test]
    fn test_prove_eq() {
        let exprs = vec![
            ("(* (* r))", "(* r)"),
            ("(;; (;; (* r) (? r)) (? r))", "(* r)"),
            ("(;; (;; (;; (* r) (? r)) (? r)) (? r))", "(* r)"),
            ("(+ r)", "(;; r (* r))"),
            ("(;; (? r) (+ r))", "(+ r)"),
            ("(+ (+ r))", "(+ r)"),
            ("(+ (+ (|| r (+ r))))", "(+ (|| r (+ r)))"),
        ];

        let mut exprs_vec = vec![];
        for (expr1, expr2) in exprs.iter() {
            let expr1 = expr1.parse().unwrap();
            let expr2 = expr2.parse().unwrap();
            exprs_vec.push((expr1, expr2));
        }

        let strategies: Vec<Box<dyn ProofStrategy>> = vec![
            Box::new(ProofStrategySearchBoth {}),
            Box::new(ProofStrategyAllBidi {}),
        ];

        for strategy in strategies {
            for (expr1, expr2) in exprs_vec.iter() {
                let proof = strategy.prove_eq(expr1, expr2, &RULES, false);
                assert!(proof.is_ok());
            }
        }
    }
}
