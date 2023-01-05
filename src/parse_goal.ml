exception Goal_parse_exp of string

type goal_s_expr =
  | Symbol of string
  | Application of string * goal_s_expr list

type direction = 
  | Forward
  | Backward

type rule = 
  { direction : direction;
    theorem : string; }

let rule_to_string rule = 
  let dir = 
    match rule.direction with
    | Forward -> "forward"
    | Backward -> "backward"
  in
  "(" ^ dir ^ " " ^ rule.theorem ^ ")"

type proof_seq = { seq : rule list; } [@@boxed]

let term_to_str env trm sigma =
  let constr = EConstr.to_constr sigma trm in
  let pp_goal = Printer.pr_constr_env env sigma constr in
  Pp.string_of_ppcmds pp_goal

let rec s_expr_to_string expr = 
  match expr with
  | Symbol s -> s
  | Application (f, args) -> 
    let args_repr = 
      List.map (fun arg -> s_expr_to_string arg) args
      |> String.concat " "
    in
    "(" ^ f ^ " " ^ args_repr ^ ")"

let rec goal_to_s env trm sigma = 
  match EConstr.kind sigma trm with
  | App (f, args) -> 
    let f_name = term_to_str env f sigma in
    (* Apparently, the first argument of Application is (relation A), 
       we will just drop it for now. *)
    let args = Array.sub args 1 (Array.length args - 1) in
    let args_repr = 
      Array.to_list args
      |> List.map (fun arg -> goal_to_s env arg sigma)
    in
    Application (f_name, args_repr)
  | Var n -> Symbol (Names.Id.to_string n)
  | _ -> raise (Goal_parse_exp "Invalid goal term.") 

let split_goal expr =
  match expr with
  | Application (f, args) -> 
    if List.length args != 2 then
      raise (Goal_parse_exp "Invalid goal term.")
    else
      (List.nth args 0, List.nth args 1)
  | _ -> raise (Goal_parse_exp "Invalid goal term.")
