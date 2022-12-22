use std::collections::LinkedList;

#[derive(ocaml::FromValue)]
enum GoalSExpr {
    Symbol(String),
    Application(String, LinkedList<GoalSExpr>),
}

#[ocaml::func]
pub fn rust_simplify_expr(expr: GoalSExpr) -> String {
    rust_expr_to_string(expr)
}

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