module Rust : sig
    val simplify_expr : Parse_goal.goal_s_expr -> Parse_goal.proof_seq

    val prove_eq : Parse_goal.goal_s_expr -> Parse_goal.goal_s_expr -> bool -> Parse_goal.proof_seq

    val configure_egg : (Parse_goal.goal_s_expr * string) list -> unit
end