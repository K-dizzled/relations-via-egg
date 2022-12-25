module Rust : sig
    val simplify_expr : Parse_goal.goal_s_expr -> string

    val prove_eq : Parse_goal.goal_s_expr -> Parse_goal.goal_s_expr -> string
end