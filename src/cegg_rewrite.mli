exception Rewriting_exp of string

val rewrite : 
  string -> 
  Parse_goal.direction -> 
  unit Proofview.tactic

val apply : 
  string -> 
  unit Proofview.tactic