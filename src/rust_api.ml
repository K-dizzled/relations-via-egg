module Rust = struct
  external simplify_expr : Parse_goal.goal_s_expr -> Parse_goal.proof_seq = "rust_simplify_expr"

  external prove_eq : Parse_goal.goal_s_expr -> Parse_goal.goal_s_expr -> bool -> Parse_goal.proof_seq = "rust_prove_eq"

  external configure_egg : (Parse_goal.goal_s_expr * string) list -> unit = "rust_configure_egg"
end