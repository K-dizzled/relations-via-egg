use std::collections::LinkedList;
use egg::*;
use crate::ExprParseError::BadOp;

#[derive(ocaml::FromValue)]
enum GoalSExpr {
    Symbol(String),
    Application(String, LinkedList<GoalSExpr>),
}

#[ocaml::func]
pub fn rust_simplify_expr(expr: GoalSExpr) -> ProofSeq {
    let rl = expr_to_rellang(&expr).unwrap();
    simplify(&rl)
}

#[allow(dead_code)]
fn rust_expr_to_string(expr: GoalSExpr) -> String {
    match expr {
        GoalSExpr::Symbol(s) => s,
        GoalSExpr::Application(s, args) => {
            let mut args_str = String::new();
            for arg in args {
                args_str.push_str(&rust_expr_to_string(arg));
                args_str.push(' ');
            }
            format!("({}: {})", s, args_str)
        }
    }
}

#[derive(Debug)]
pub enum ExprParseError {
    BadOp(FromOpError),
}

fn expr_to_rellang(sexp: &GoalSExpr) -> Result<RecExpr<RelLanguage>, ExprParseError> {
    fn parse_sexp_into(sexp: &GoalSExpr, expr: &mut RecExpr<RelLanguage>) -> Result<Id, ExprParseError> {
        match sexp {
            // Dont know what's top & bot in terms
            // of Relations in COQ, not parsing them for now
            GoalSExpr::Symbol(s) => {
                let node = RelLanguage::Symbol(Symbol::from(s.to_string()));
                Ok(expr.add(node))
            },
            GoalSExpr::Application(f, args) => {
                let arg_ids: Result<Vec<Id>, _> =
                    args.iter().map(|s| parse_sexp_into(s, expr)).collect();

                let op = match f.to_string().as_str() {
                    "seq" => ";;",
                    "clos_refl_trans" => "*",
                    "clos_refl" => "?",
                    "clos_trans" => "+",
                    _ => f,
                };

                let node = RelLanguage::from_op(op, arg_ids?).map_err(BadOp)?;
                Ok(expr.add(node))
            },
        }
    }

    let mut expr = RecExpr::default();
    parse_sexp_into(sexp, &mut expr)?;
    Ok(expr)
}

define_language! {
    enum RelLanguage {
        "top" = Top,
        "bot" = Bot,

        ";;" = Seq([Id; 2]),

        "+" = CT(Id),
        "?" = RT(Id),
        "*" = CRT(Id),

        Symbol(Symbol),
    }
}

fn make_rules() -> Vec<Rewrite<RelLanguage, ()>> {
    let mut rules =
        vec![ rewrite!("ct_end"  ; "(+ ?a)" <=> "(;; (* ?a) ?a)"),
              rewrite!("ct_begin"; "(+ ?a)" <=> "(;; ?a (* ?a))"),
        ].concat();

    rules.extend(
        vec![
            rewrite!("seqA"    ; "(;; ?a (;; ?b ?c))" => "(;; (;; ?a ?b) ?c)"),
            rewrite!("rt_cr"  ; "(;; (* ?a) (? ?a))" => "(* ?a)"),
            //rewrite!("rt_begin"; "(;; (? ?a) (* ?a))" => "(* ?a)"),

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

fn simplify(expr: &RecExpr<RelLanguage>) -> ProofSeq {
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

#[derive(Debug, ocaml::IntoValue)]
pub enum Direction {
    Forward,
    Backward,
}

#[derive(Debug, ocaml::IntoValue)]
pub struct Rule {
    direction: Direction,
    theorem: String,
}

#[derive(Debug, ocaml::IntoValue)]
pub struct ProofSeq {
    rules: LinkedList<Rule>,
}

impl ProofSeq {
    fn from(rules: LinkedList<Rule>) -> ProofSeq {
        ProofSeq {
            rules,
        }
    }
}

fn parse_proof<L>(expl: &mut Explanation<L>) -> LinkedList<Rule> where 
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

fn ft_to_rule<L>(ft: &FlatTerm<L>) -> Option<Rule> where 
    L: Language, 
    L: std::fmt::Display,
    L: egg::FromOp,
{
    if let Some(rule_name) = &ft.backward_rule {
        return Some(Rule {
            direction: Direction::Backward,
            theorem: (*rule_name).to_string(),
        });
    }
    if let Some(rule_name) = &ft.forward_rule {
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
