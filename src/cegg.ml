let __coq_plugin_name = "coq-egg-tactic.cegg"
let _ = Mltop.add_known_module __coq_plugin_name

# 3 "src/cegg.mlg"
 

open Pp
open Ltac_plugin
open Main_logic



let () = Tacentries.tactic_extend __coq_plugin_name "cegg_solve" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("Cegg", Tacentries.TyIdent ("solve", 
                                                        Tacentries.TyNil)), 
           (fun ist -> 
# 17 "src/cegg.mlg"
    
    let _ = Proofview.Goal.goal in
    let _ = Feedback.msg_notice (str message) in
    Tacticals.tclIDTAC 
  
           )))]

