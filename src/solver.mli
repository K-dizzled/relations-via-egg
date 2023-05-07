val time_tac : 
  string ->
  unit Proofview.tactic ->
  unit Proofview.tactic

val simplify_lhs : 
  unit -> 
  unit Proofview.tactic

val try_prove : 
  unit -> 
  unit Proofview.tactic

val config_egg : 
  Libnames.qualid -> 
  unit

val kek_tac : 
  unit -> 
  unit Proofview.tactic

val print_type : 
  EConstr.t -> 
  unit Proofview.tactic