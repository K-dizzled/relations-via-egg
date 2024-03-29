open Rust_api
open Pp

module Control = struct
  let debug = false
  let debug_feedback = false
  let debug_egraphs = false
  let time = true
end

module Debug = Helper.Debug (Control)
open Debug

let time_tac msg tac =
  if Control.time then Proofview.tclTIME (Some msg) tac else tac

let warn msg = CWarnings.create ~name:"Coq-Egg" ~category:"No impact tactic call"
                            (fun _ -> strbrk msg) ()

let is_none x = 
  match x with
  | None -> true
  | Some _ -> false

let extract_goal_eq_sides (goal : Proofview.Goal.t) =
  let env = Proofview.Goal.env goal in
  let sigma = Proofview.Goal.sigma goal in
  let concl = Proofview.Goal.concl goal in

  let expr, type_param = 
    try 
      Parse_goal.goal_to_sexp env concl sigma 
    with Parse_goal.Goal_parse_exp msg -> 
      CErrors.user_err (str msg) in

  if is_none type_param then 
    CErrors.user_err (str "Error occured inferring type parameter. Submit an issue.") 
  else
    let type_param = EConstr.to_constr sigma (Option.get type_param)
  in
  
  let _ = debug ("Goal: " ^ (C_utilities.term_to_str env concl sigma)) in
  let _ = debug ("Goal before parsing: " ^ (C_utilities.term_kind_to_str env concl sigma)) in
  let _ = debug ("Goal after parsing: " ^ (Parse_goal.s_expr_to_string expr)) in 
  
  let lhs, rhs = 
    try 
      Parse_goal.split_goal expr 
    with Parse_goal.Goal_parse_exp msg -> 
      CErrors.user_err (str msg) in
  (lhs, rhs, type_param)

let multiple_rewrites_tac (sequence : Parse_goal.proof_seq) (type_param : Constr.t) =
  let proof_seq = List.fold_left (fun tac (rule : Parse_goal.rule) -> 
    let thr = rule.theorem in 
    let dir = rule.direction in 
    let with_exprs = rule.rewrite_with in
    let at_occur = rule.rewrite_at in
    let with_constr = 
      List.map (fun (name, subst) -> Parse_record.sexp_to_constr subst type_param) with_exprs in
    let with_constr_array = Array.of_list with_constr in
    let _ = debug ("rewrite " ^ (Parse_goal.rule_to_string rule)) in 

    let rewrite_tac = 
      try 
        Cegg_rewrite.rewrite_with thr dir with_constr_array at_occur type_param
      with Cegg_rewrite.Rewriting_exp msg -> 
        CErrors.user_err (str msg) in

    let tac = Proofview.tclTHEN tac rewrite_tac in
    let tac_with_auto = Proofview.tclTHEN tac (Auto.default_auto) in
    tac_with_auto
  ) (Tacticals.tclIDTAC) sequence.seq in
  proof_seq 

let simplify_lhs () = 
  Proofview.Goal.enter (fun goal -> 
    let lhs, _, type_param = extract_goal_eq_sides goal in
    let proof_seq = 
      try 
        Rust.simplify_expr lhs 
      with err -> 
        CErrors.user_err (str (Printexc.to_string err)) in

    let tac = multiple_rewrites_tac proof_seq type_param in 
    
    (* Apply reflexivity at the end if 
       it succeeds, otherwise just simplify  *)
    let tac_with_reflexivity = Proofview.tclTHEN tac (Tactics.reflexivity) in 
    let tac = Proofview.tclOR tac_with_reflexivity (fun _ -> tac) in
    let _ = if List.length proof_seq.seq = 0 then (warn "Could not achieve simplification.") in 

    tac
  )

let try_prove strat_name = 
  Proofview.Goal.enter (fun goal -> 
      let lhs, rhs, type_param = extract_goal_eq_sides goal in
      let proof_seq = 
        try 
          Rust.prove_eq lhs rhs Control.debug_egraphs strat_name
        with err -> 
          CErrors.user_err (str "Unable to prove equivalence.") in

      let proof_str = String.concat " " (List.map (fun x -> Parse_goal.rule_to_string x) proof_seq.seq) in
      let _ = debug ("Proof sequence: " ^ proof_str) in
      let tac = multiple_rewrites_tac proof_seq type_param in 
      
      (* Call auto to get rid of newly 
         created "Wf" goal *)
      let tac_with_auto = Proofview.tclTHEN tac (Auto.default_auto) in 

      (* Apply reflexivity at the end if 
          it succeeds, otherwise just simplify  *)
      let tac_with_reflexivity = Proofview.tclTHEN tac_with_auto (Tactics.reflexivity) in 
      let tac = Proofview.tclOR tac_with_reflexivity (fun _ -> tac) in
      let _ = if List.length proof_seq.seq = 0 then (warn "Could not achieve simplification.") in 
      let _ = debug ("") in

      tac
  )

let print_type c = 
  Proofview.Goal.enter (fun goal -> 
    let env = Proofview.Goal.env goal in
    let sigma = Proofview.Goal.sigma goal in
    let _ = Feedback.msg_notice (Pp.str  (C_utilities.term_kind_to_str env c sigma)) in

    Tacticals.tclIDTAC
  )

let config_egg ref = 
  let env = Global.env () in
     let sigma = Evd.from_env env in
     try
       let prod = Parse_record.access_record_body (Nametab.global ref) in
       let _ = debug_feedback ("Record: " ^ C_utilities.term_kind_to_str env prod sigma) in
       let constr_list = Parse_record.unpack_prod env prod sigma in
       let expr_list = List.map (fun (c, rule_name) -> (fst (Parse_goal.goal_to_sexp env c sigma), rule_name)) constr_list in
       let _ = 
        try 
          Rust.configure_egg expr_list
        with err -> 
          CErrors.user_err (str (Printexc.to_string err)) in
        
        Feedback.msg_notice (str "Configured successfully.")
     with err ->
       CErrors.user_err (str (Printexc.to_string err))