let term_to_str env trm sigma =
  let constr = EConstr.to_constr sigma trm in
  let pp_goal = Printer.pr_constr_env env sigma constr in
  Pp.string_of_ppcmds pp_goal

let rec term_kind_to_str env trm sigma = 
  match EConstr.kind sigma trm with
  | Rel _ -> "App"
  | Var _ -> "Var"
  | Meta _ -> "Lambda"
  | Evar _ -> "Evar"
  | Sort _ -> "Sort"
  | Cast _ -> "Cast"
  | Prod (a, b, c) -> 
    let name = Context.binder_name a in 
    let name = Pp.string_of_ppcmds (Names.Name.print name) in 
    "Name: " ^ 
    name ^
    " -- forall A : " ^
    (term_to_str env b sigma) ^
    " , " ^
    (term_kind_to_str env c sigma)
  | Lambda (x, t, body) -> 
    "Lambda with input type " ^ 
    (term_to_str env t sigma) ^ 
    " and body: " ^ 
    (term_to_str env body sigma)
  | LetIn _ -> "LetIn"
  | App (f, args) -> 
    let f_name = term_to_str env f sigma in
    let args_str = Array.fold_left (fun acc arg -> 
      acc ^ " " ^ (term_to_str env arg sigma)) "" args in
    "App " ^ f_name ^ " with args: " ^ args_str
  | Const _ -> "Const"
  | Ind _ -> "Ind"
  | Construct _ -> "Construct"
  | Case _ -> "Case"
  | Fix _ -> "Fix"
  | CoFix _ -> "CoFix"
  | Proj _ -> "Proj"
  | _ -> "Unknown"