exception Rewriting_exp of string

val get_thr_constr : 
  string -> 
  Constr.t

val rewrite : 
  string -> 
  Parse_goal.direction -> 
  unit Proofview.tactic

val rewrite_with : 
  string -> 
  Parse_goal.direction -> 
  Constr.t array -> 
  int -> 
  Constr.t -> 
  unit Proofview.tactic