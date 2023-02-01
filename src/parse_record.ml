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