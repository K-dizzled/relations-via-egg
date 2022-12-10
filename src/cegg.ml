let __coq_plugin_name = "coq-egg-tactic.cegg"
let _ = Mltop.add_known_module __coq_plugin_name

# 3 "src/cegg.mlg"
 

(* open Pp
open Ltac_plugin
open Stdarg *)



let () = Vernacextend.vernac_extend ~command:"SolveWithEgg" ~classifier:(fun _ -> Vernacextend.classify_as_query) ?entry:None 
         [(Vernacextend.TyML (false, Vernacextend.TyTerminal ("Solve", 
                                     Vernacextend.TyTerminal ("With", 
                                     Vernacextend.TyTerminal ("Egg", 
                                     Vernacextend.TyNil))), (let coqpp_body () = 
                                                            Vernacextend.vtdefault (fun () -> 
                                                            
# 12 "src/cegg.mlg"
                                () 
                                                            ) in fun ?loc ~atts ()
                                                            -> coqpp_body (Attributes.unsupported_attributes atts)), None))]

