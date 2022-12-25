open Evd
open Environ

exception Goal_parse_exp of string

type goal_s_expr =
  | Symbol of string
  | Application of string * goal_s_expr list

val s_expr_to_string : 
  goal_s_expr -> 
  string
  
val goal_to_s : 
  env -> 
  EConstr.t -> 
  evar_map -> 
  goal_s_expr

val split_goal : 
  goal_s_expr -> 
  goal_s_expr * goal_s_expr