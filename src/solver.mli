val time_tac : 
  string ->
  unit Proofview.tactic ->
  unit Proofview.tactic

val simplify_lhs : 
  unit -> 
  unit Proofview.tactic

val try_prove : 
  string ->
  unit Proofview.tactic

val config_egg : 
  Libnames.qualid -> 
  unit

val print_type : 
  EConstr.t -> 
  unit Proofview.tactic