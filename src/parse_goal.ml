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

type proof_seq = { seq : rule list; } [@@boxed]

let term_to_str env trm sigma =
  let constr = EConstr.to_constr sigma trm in
  let pp_goal = Printer.pr_constr_env env sigma constr in
  Pp.string_of_ppcmds pp_goal

(* Parse goal represented as a Ecostr to
   an s expression. Assumes that the term 
   contains only Applications and Variables *)
let rec goal_to_sexp env trm sigma = 
  match EConstr.kind sigma trm with
  | App (f, args) -> 
    let f_name = term_to_str env f sigma in
    (* The first element of the list is a
    type parameter and for now I just drop it *)
    let args = Array.sub args 1 (Array.length args - 1) in
    let args_repr = 
      Array.to_list args
      |> List.map (fun arg -> goal_to_sexp env arg sigma)
    in
    Application (f_name, args_repr)
  | Var n -> Symbol (Names.Id.to_string n)
  | _ -> raise (Goal_parse_exp "Conclusion of the goal must be an application.") 

(* Split the statement into a pair of lhs and rhs,
   throw Goal_parse_exp if the amount of 
   arguments is not equal to 2 *)
let split_goal expr =
  match expr with
  | Application (f, args) -> 
    if List.length args != 2 then
      raise (Goal_parse_exp "Must be a binary operator.")
    else
      if f = "@inclusion" then 
        (List.nth args 0, List.nth args 1)
      else 
        raise (Goal_parse_exp "Goal must be of form a ⊆ b.")
  | _ -> raise (Goal_parse_exp "Invalid term passed.")

(* Utility functions *)
let rule_to_string rule = 
  let dir = 
    match rule.direction with
    | Forward -> "forward"
    | Backward -> "backward"
  in
  "(" ^ dir ^ " " ^ rule.theorem ^ ")"

let rec s_expr_to_string expr = 
  match expr with
  | Symbol s -> s
  | Application (f, args) -> 
    let args_repr = 
      List.map (fun arg -> s_expr_to_string arg) args
      |> String.concat " "
    in
    "(" ^ f ^ " " ^ args_repr ^ ")"
