open Parse_goal

exception Record_parse_exp of string

let access_record_body gref =
  let open Names.GlobRef in
  match gref with
  | IndRef indr ->
    let (_, oib) = Global.lookup_inductive indr in

    let rec_constructors_list = Array.to_list oib.Declarations.mind_user_lc in 
    let constr = List.hd rec_constructors_list in
    
    EConstr.of_constr constr
  | _ -> raise (Record_parse_exp "Expected an inductive type") 

let rec unpack_prod env prod sigma = 
  match EConstr.kind sigma prod with
  | Prod (name, typ, body) -> 
    let bn = Context.binder_name name in 
    let costructor_name = Pp.string_of_ppcmds (Names.Name.print bn) in 
    if EConstr.isProd sigma body then
      (typ, costructor_name) :: (unpack_prod env body sigma)
    else
      [(typ, costructor_name)]
  | _ -> raise (Record_parse_exp "Expected a product")

let rec sexp_to_constr sexp =
  match sexp with
  | Symbol s -> Constr.mkVar (Names.Id.of_string s)
  | Application (s, args) -> 
    let econstr_args = List.map sexp_to_constr args in
    let f_constr = Cegg_rewrite.get_thr_constr s in 
    let first_arg_constr = Constr.mkVar (Names.Id.of_string "A") in 
    let econstr_args = first_arg_constr :: econstr_args in
    
    Constr.mkApp (f_constr, Array.of_list econstr_args)
  | _ -> raise (Record_parse_exp "Expected a symbol or application")