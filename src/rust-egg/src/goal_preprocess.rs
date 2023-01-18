use egg::{RecExpr, Symbol, Id, FromOpError, define_language, FromOp};
use std::collections::{LinkedList, HashMap};
use crate::ExprParseError::BadOp;
use lazy_static::lazy_static;
use ocaml::Value;

/// Goal is received from OCaml
/// as a simple s-expression
/// consisting of applications.
#[derive(ocaml::FromValue)]
pub enum GoalSExpr {
    Symbol(String),
    Application(String, LinkedList<GoalSExpr>),
    Lambda(Box<GoalSExpr>, Box<GoalSExpr>),
}

unsafe impl ocaml::FromValue<'_> for Box<GoalSExpr> {
    fn from_value(v: Value) -> Self {
        Box::new(ocaml::FromValue::from_value(v))
    }
}

define_language! {
    /// Define a language of relations
    /// 1. Top, bot
    /// 2. Composition of relations, transitive closure, 
    /// reflexive closure, reflexive transitive closure
    /// 3. Union, intersection, setminus
    /// 4. Symbols
    pub enum RelLanguage {
        "top" = Top,
        "bot" = Bot,

        ";;" = Seq([Id; 2]),
        "+" = CT(Id),
        "?" = RT(Id),
        "*" = CRT(Id),

        "||" = Union([Id; 2]),
        "&&" = Inter([Id; 2]),
        "setminus" = SetMinus([Id; 2]),

        Symbol(Symbol),
    }
}

lazy_static! {
    /// A map from Coq.Relations operator names 
    /// to their representations in RelLanguage
    static ref OPERATORS: HashMap<&'static str, &'static str> = {
        let mut map = HashMap::new();
        map.insert("seq", ";;");
        map.insert("clos_refl_trans", "*");
        map.insert("clos_refl", "?");
        map.insert("clos_trans", "+");
        map.insert("union", "||");
        map.insert("minus_rel", "setminus");
        map.insert("inter_rel", "&&");
        map
    };

    static ref COQ_TRUE: String = "Coq.Init.Logic.True".to_string();
    static ref COQ_FALSE: String = "Coq.Init.Logic.False".to_string();
}

/// Expression thrown in case of
/// invalid arguments amount or
/// invalid operator name given 
#[derive(Debug)]
pub enum ExprParseError {
    BadOp(FromOpError),
    UnexpectedLambdaUse,
}

impl Into<&str> for ExprParseError {
    fn into(self) -> &'static str {
        match self {
            ExprParseError::BadOp(_) => "Error parsing expr. Invalid operator used.",
            ExprParseError::UnexpectedLambdaUse => "Lambda used in an unexpected place.",
        }
    }
}

/// Parse S-expression from OCaml into 
/// a RecExpr that is used by Egg
pub fn expr_to_rellang(sexp: &GoalSExpr) -> Result<RecExpr<RelLanguage>, ExprParseError> {
    fn is_subterm_lambda_to(sexp: &GoalSExpr, to: &str) -> bool {
        if let GoalSExpr::Lambda(_, body) = sexp {
            if let GoalSExpr::Symbol(s) = body.as_ref() {
                return s == to;
            }
        }
        false
    }

    fn is_subterm_bot(sexp: &GoalSExpr) -> bool {
        if let GoalSExpr::Lambda(_, body) = sexp {
            return is_subterm_lambda_to(body.as_ref(), COQ_FALSE.as_str());
        }
        false
    }

    fn is_application_top(op: &str, args: &LinkedList<GoalSExpr>) -> bool {
        if op == "eqv_rel" && args.len() == 1 {
            return is_subterm_lambda_to(args.front().unwrap(), COQ_TRUE.as_str());
        }
        false
    }

    fn parse_sexp_into(sexp: &GoalSExpr, expr: &mut RecExpr<RelLanguage>) -> Result<Id, ExprParseError> {
        match sexp {
            GoalSExpr::Symbol(s) => {
                let node = RelLanguage::Symbol(Symbol::from(s.to_string()));
                Ok(expr.add(node))
            },

            GoalSExpr::Application(f, args) => {
                let op = match OPERATORS.get(f.as_str()) {
                    Some(op) => op,
                    None => f.as_str(),
                };

                // Check if Top was passed (i. e. (fun _ => True))
                if is_application_top(op, args) {
                    return Ok(expr.add(RelLanguage::Top));
                }

                let arg_ids: Result<Vec<Id>, _> =
                    args.iter().map(|s| parse_sexp_into(s, expr)).collect();

                let node = RelLanguage::from_op(op, arg_ids?).map_err(BadOp)?;
                Ok(expr.add(node))
            },

            GoalSExpr::Lambda(_, _) => {
                // Only check if lambda is a Bot const
                // (i.e. a (fun _ _ => False)), otherwise throw an error
                return if is_subterm_bot(sexp) {
                    Ok(expr.add(RelLanguage::Bot))
                } else {
                    Err(ExprParseError::UnexpectedLambdaUse)
                }
            }
        }
    }

    let mut expr = RecExpr::default();
    parse_sexp_into(sexp, &mut expr)?;
    Ok(expr)
}

#[allow(dead_code)]
fn expr_to_string(expr: GoalSExpr) -> String {
    match expr {
        GoalSExpr::Symbol(s) => s,
        GoalSExpr::Application(s, args) => {
            let mut args_str = String::new();
            for arg in args {
                args_str.push_str(&expr_to_string(arg));
                args_str.push(' ');
            }
            format!("({}: {})", s, args_str)
        }
        GoalSExpr::Lambda(tp, body) => {
            format!("(fun _ : {} => {})", expr_to_string(*tp), expr_to_string(*body))
        }
    }
}