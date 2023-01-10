use egg::{RecExpr, Symbol, Id, FromOpError, define_language, FromOp};
use std::collections::{LinkedList, HashMap};
use crate::ExprParseError::BadOp;
use lazy_static::lazy_static;

/// Goal is recieved from OCaml 
/// as a simple s-expression
/// consisting of applications.
#[derive(ocaml::FromValue)]
pub enum GoalSExpr {
    Symbol(String),
    Application(String, LinkedList<GoalSExpr>),
}

define_language! {
    /// Define a language of relations, containing
    /// symbols, top, bot, a composition of relations, 
    /// a reflexive closure, a transitive closure,
    /// and a reflexive transitive closure. 
    pub enum RelLanguage {
        "top" = Top,
        "bot" = Bot,

        ";;" = Seq([Id; 2]),

        "+" = CT(Id),
        "?" = RT(Id),
        "*" = CRT(Id),

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
        map
    };
}

/// Expression thrown in case of
/// invalid arguments amount or
/// invalid operator name given 
#[derive(Debug)]
pub enum ExprParseError {
    BadOp(FromOpError),
}

/// Parse S-expression from OCaml into 
/// a RecExpr that is used by Egg
pub fn expr_to_rellang(sexp: &GoalSExpr) -> Result<RecExpr<RelLanguage>, ExprParseError> {
    fn parse_sexp_into(sexp: &GoalSExpr, expr: &mut RecExpr<RelLanguage>) -> Result<Id, ExprParseError> {
        match sexp {
            // Dont know what's top & bot in terms
            // of Relations in COQ, not parsing them for now
            // UPD: Bot is a map to False, Top is a map to True. 
            // TODO: Fix that
            GoalSExpr::Symbol(s) => {
                let node = RelLanguage::Symbol(Symbol::from(s.to_string()));
                Ok(expr.add(node))
            },

            GoalSExpr::Application(f, args) => {
                let arg_ids: Result<Vec<Id>, _> =
                    args.iter().map(|s| parse_sexp_into(s, expr)).collect();

                let op = match OPERATORS.get(f.as_str()) {
                    Some(op) => op,
                    None => f.as_str(),
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
    }
}