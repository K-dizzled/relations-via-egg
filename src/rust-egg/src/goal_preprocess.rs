use crate::ExprParseError::BadOp;
use egg::{define_language, FromOp, FromOpError, Id, RecExpr, Symbol};
use lazy_static::lazy_static;
use ocaml::{Runtime, Value};
use serde::{Deserialize, Serialize};
use std::collections::{HashMap, LinkedList};
use egg::Language;

/// Goal is received from OCaml
/// as a simple s-expression
/// consisting of applications.
#[derive(ocaml::FromValue, Serialize, Deserialize, PartialEq, Debug, ocaml::IntoValue)]
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

unsafe impl ocaml::IntoValue for Box<GoalSExpr> {
    fn into_value(self, rt: &Runtime) -> Value {
        ocaml::IntoValue::into_value(*self, rt)
    }
}

define_language! {
    /// Define a language of relations
    /// 1. Top, bot
    /// 2. A compete set, i. e. (fun x => True)
    /// 3. Composition of relations, transitive closure,
    /// reflexive closure, reflexive transitive closure
    /// 4. Union, intersection, setminus
    /// 5. Symbols
    pub enum RelLanguage {
        "top" = Top,
        "bot" = Bot,

        "complete_set" = CompleteSet,

        ";;" = Seq([Id; 2]),
        "+" = CT(Id),
        "?" = RT(Id),
        "*" = CRT(Id),
        "eqv_rel" = Eqv(Id),
        "clos_sym" = CS(Id),
        "-1" = Transpose(Id),
        "clos_refl_sym" = CRS(Id),

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
        map.insert("eqv_rel", "eqv_rel");
        map.insert("clos_sym", "clos_sym");
        map.insert("transp", "-1");
        map.insert("clos_refl_sym", "clos_refl_sym");
        map
    };

    static ref OPERATORS_REVERSE: HashMap<&'static str, &'static str> = {
        let mut map = HashMap::new();
        map.insert(";;", "seq");
        map.insert("*", "clos_refl_trans");
        map.insert("?", "clos_refl");
        map.insert("+", "clos_trans");
        map.insert("||", "union");
        map.insert("setminus", "minus_rel");
        map.insert("&&", "inter_rel");
        map.insert("eqv_rel", "eqv_rel");
        map.insert("clos_sym", "clos_sym");
        map.insert("-1", "transp");
        map.insert("clos_refl_sym", "clos_refl_sym");
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
    WFParsingError,
    SexpParsingError,
    RecExprParsingError,
}

impl Into<&str> for ExprParseError {
    fn into(self) -> &'static str {
        match self {
            ExprParseError::BadOp(_) => "Error parsing expr. Invalid operator used.",
            ExprParseError::UnexpectedLambdaUse => "Lambda used in an unexpected place.",
            ExprParseError::WFParsingError => "Error parsing wf.",
            ExprParseError::SexpParsingError => "Error parsing s-expression.",
            ExprParseError::RecExprParsingError => "Error parsing rec-expression into goal expr.",
        }
    }
}

pub fn recexpr_to_goal_expr(expr: &RecExpr<RelLanguage>) -> Result<GoalSExpr, ExprParseError> {
    fn to_sexp_rec(
        i: usize,
        nodes: &[RelLanguage]
    ) -> Result<GoalSExpr, ExprParseError> {
        let node = &nodes[i];
        if node.is_leaf() {
            Ok(GoalSExpr::Symbol(node.to_string()))
        } else {
            let op = OPERATORS_REVERSE.get(node.to_string().as_str())
                .ok_or(ExprParseError::RecExprParsingError)?
                .to_string();

            let mut vec: LinkedList<GoalSExpr> = LinkedList::new();

            for child_id in node.children().iter().map(|i| usize::from(*i)) {
                let child = &nodes[child_id];
                if child.is_leaf() {
                    vec.push_back(GoalSExpr::Symbol(child.to_string()));
                } else {
                    let child = to_sexp_rec(child_id, nodes)?;
                    vec.push_back(child);
                }
            }
            Ok(GoalSExpr::Application(op, vec))
        }
    }

    let nodes = expr.as_ref();
    let last = nodes.len() - 1;
    return to_sexp_rec(last, nodes);
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

    fn is_subterm_bot_top(sexp: &GoalSExpr) -> Option<bool> {
        if let GoalSExpr::Lambda(_, body) = sexp {
            if is_subterm_lambda_to(body.as_ref(), COQ_TRUE.as_str()) {
                return Some(true);
            } else if is_subterm_lambda_to(body.as_ref(), COQ_FALSE.as_str()) {
                return Some(false);
            }
        }
        None
    }

    fn is_application_compset(op: &str, args: &LinkedList<GoalSExpr>) -> bool {
        if op == "eqv_rel" && args.len() == 1 {
            return is_subterm_lambda_to(args.front().unwrap(), COQ_TRUE.as_str());
        }
        false
    }

    fn parse_sexp_into(
        sexp: &GoalSExpr,
        expr: &mut RecExpr<RelLanguage>,
    ) -> Result<Id, ExprParseError> {
        match sexp {
            GoalSExpr::Symbol(s) => {
                let node = RelLanguage::Symbol(Symbol::from(s.to_string()));
                Ok(expr.add(node))
            }

            GoalSExpr::Application(f, args) => {
                let op = match OPERATORS.get(f.as_str()) {
                    Some(op) => op,
                    None => f.as_str(),
                };

                // Check if Complete Set was passed (i. e. eqv_rel (fun _ => True))
                if is_application_compset(op, args) {
                    return Ok(expr.add(RelLanguage::CompleteSet));
                }

                let arg_ids: Result<Vec<Id>, _> =
                    args.iter().map(|s| parse_sexp_into(s, expr)).collect();

                let node = RelLanguage::from_op(op, arg_ids?).map_err(BadOp)?;
                Ok(expr.add(node))
            }

            GoalSExpr::Lambda(_, _) => {
                // Only check if lambda is a Bot or Top const
                // (i.e. a (fun _ _ => False)) / (i.e. a (fun _ _ => True))
                // otherwise return an error
                match is_subterm_bot_top(sexp) {
                    Some(true) => Ok(expr.add(RelLanguage::Top)),
                    Some(false) => Ok(expr.add(RelLanguage::Bot)),
                    None => Err(ExprParseError::UnexpectedLambdaUse),
                }
            }
        }
    }

    let mut expr = RecExpr::default();
    parse_sexp_into(sexp, &mut expr)?;
    Ok(expr)
}

#[allow(dead_code)]
pub fn expr_to_string(expr: &GoalSExpr) -> String {
    match expr {
        GoalSExpr::Symbol(s) => s.to_string(),
        GoalSExpr::Application(s, args) => {
            let mut args_str = String::new();
            for arg in args {
                args_str.push_str(&expr_to_string(arg));
                args_str.push(' ');
            }
            format!("({}: {})", s, args_str)
        }
        GoalSExpr::Lambda(tp, body) => {
            format!(
                "(fun _ : {} => {})",
                expr_to_string(tp.as_ref()),
                expr_to_string(body.as_ref())
            )
        }
    }
}
