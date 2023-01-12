open Rust_api
open Pp

let extract_goal_eq_sides (goal : Proofview.Goal.t) =
  let env = Proofview.Goal.env goal in
  let sigma = Proofview.Goal.sigma goal in
  let concl = Proofview.Goal.concl goal in

  let expr = try Parse_goal.goal_to_s env concl sigma with 
  Parse_goal.Goal_parse_exp msg -> CErrors.user_err (str msg) in
  let lhs, rhs = try Parse_goal.split_goal expr with 
  Parse_goal.Goal_parse_exp msg -> CErrors.user_err (str msg) in
  lhs, rhs

let multiple_rewrites_tac (sequence : Parse_goal.proof_seq) =
  let proof_seq = List.fold_left (fun tac (rule : Parse_goal.rule) -> 
    let thr = rule.theorem in 
    let dir = rule.direction in 

    let rewrite_tac = try Cegg_rewrite.rewrite thr dir with
    Cegg_rewrite.Rewriting_exp msg -> CErrors.user_err (str msg) in

    let tac = Proofview.tclTHEN tac rewrite_tac in
    tac
  ) (Tacticals.tclIDTAC) sequence.seq in
  proof_seq 

let simplify_lhs () = 
  Proofview.Goal.enter (fun goal -> 
    let lhs, _ = extract_goal_eq_sides goal in
    let proof_seq = Rust.simplify_expr lhs in

    let tac = multiple_rewrites_tac proof_seq in 
    
    (* Apply reflexivity at the end if 
       it succeeds, otherwise just simplify  *)
    let tac_with_reflexivity = Proofview.tclTHEN tac (Tactics.reflexivity) in 
    let tac = Proofview.tclOR tac_with_reflexivity (fun _ -> tac) in

    tac
  )