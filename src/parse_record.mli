open Parse_goal

exception Record_parse_exp of string

val access_record_body : 
  Names.GlobRef.t -> 
  EConstr.t

val sexp_to_constr : 
  goal_s_expr -> 
  Constr.t -> 
  Constr.t

val unpack_prod : 
  Environ.env -> 
  EConstr.t -> 
  Evd.evar_map -> 
  (EConstr.t * string) list