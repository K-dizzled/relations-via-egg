let term_to_str env trm sigma =
  let constr = EConstr.to_constr sigma trm in
  let pp_goal = Printer.pr_constr_env env sigma constr in
  Pp.string_of_ppcmds pp_goal

let term_kind_to_str env trm sigma = 
  match EConstr.kind sigma trm with
  | Rel _ -> "App"
  | Var _ -> "Var"
  | Meta _ -> "Lambda"
  | Evar _ -> "Evar"
  | Sort _ -> "Sort"
  | Cast _ -> "Cast"
  | Prod _ -> "Prod"
  | Lambda (x, t, body) -> 
    "Lambda with input type " ^ 
    (term_to_str env t sigma) ^ 
    " and body: " ^ 
    (term_to_str env body sigma)
  | LetIn _ -> "LetIn"
  | App _ -> "App"
  | Const _ -> "Const"
  | Ind _ -> "Ind"
  | Construct _ -> "Construct"
  | Case _ -> "Case"
  | Fix _ -> "Fix"
  | CoFix _ -> "CoFix"
  | Proj _ -> "Proj"
  | _ -> "Unknown"