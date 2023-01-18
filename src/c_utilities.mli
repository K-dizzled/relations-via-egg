val term_to_str :
    Environ.env ->
    EConstr.t ->
    Evd.evar_map ->
    string

val term_kind_to_str : 
    Environ.env -> 
    EConstr.t -> 
    Evd.evar_map -> 
    string