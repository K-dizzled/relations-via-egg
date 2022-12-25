use std::collections::LinkedList;
use egg::*;
use crate::ExprParseError::BadOp;

#[derive(ocaml::FromValue)]
enum GoalSExpr {
    Symbol(String),
    Application(String, LinkedList<GoalSExpr>),
}

#[ocaml::func]
pub fn rust_simplify_expr(expr: GoalSExpr) -> String {
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
            rewrite!("rt_end"  ; "(;; (* ?a) (? ?a))" => "(* ?a)"),
            rewrite!("rt_begin"; "(;; (? ?a) (* ?a))" => "(* ?a)"),

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

/// parse an expression, simplify it using egg, and pretty print it back out
fn simplify(expr: &RecExpr<RelLanguage>) -> String {
    // simplify the expression using a Runner, which creates an e-graph with
    // the given expression and runs the given rules over it
    let runner = Runner::default().with_expr(&expr)
        .run(&make_rules());

    // the Runner knows which e-class the expression given with `with_expr` is in
    let root = runner.roots[0];

    // use an Extractor to pick the best element of the root eclass
    let extractor = Extractor::new(&runner.egraph, AstSize);
    let (best_cost, best) = extractor.find_best(root);
    println!("Simplified {} to {} with cost {}", expr, best, best_cost);
    best.to_string()
}

