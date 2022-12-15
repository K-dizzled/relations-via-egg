let __coq_plugin_name = "coq-egg-tactic.cegg"
let _ = Mltop.add_known_module __coq_plugin_name

# 3 "src/cegg.mlg"
 

open Pp
open Ltac_plugin
(* open Utils *)
(* open Printer *)



let () = Tacentries.tactic_extend __coq_plugin_name "cegg_solve" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("Cegg", Tacentries.TyIdent ("solve", 
                                                        Tacentries.TyNil)), 
           (fun ist -> 
# 14 "src/cegg.mlg"
    
    Proofview.tclBIND (Proofview.Goal.goals) (fun goals -> 
      let goal = List.hd goals in
      Proofview.tclBIND (goal) (fun goal -> 
        let env = Proofview.Goal.env goal in
        let sigma = Proofview.Goal.sigma goal in
        let concl = Proofview.Goal.concl goal in

        let constr = EConstr.to_constr sigma concl in
        let pp_goal = Printer.pr_constr_env env sigma constr in
        let goal_str = Pp.string_of_ppcmds pp_goal in
        
        (* let g = Proofview.Goal.concl goal in
        let str_pp = Evar.print g in
        let str_goal = Pp.string_of_ppcmds str_pp in *)
        let _ = Feedback.msg_notice (str "Goal: " ++ str goal_str) in
        Tacticals.tclIDTAC
      ))
  
           )))]

