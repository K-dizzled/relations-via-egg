open C_utilities

exception Goal_parse_exp of string

type goal_s_expr =
  | Symbol of string
  | Application of string * goal_s_expr list
  | Lambda of goal_s_expr * goal_s_expr
  
type direction = 
  | Forward
  | Backward

type rule = 
  { direction : direction;
    theorem : string;
    rewrite_with : (string * goal_s_expr) list;
    rewrite_at : int; }

type proof_seq = { seq : rule list; } [@@boxed]

let rec goal_to_sexp_aux env trm sigma (type_param : EConstr.t option) : (goal_s_expr * EConstr.t option) =
  match EConstr.kind sigma trm with
  | App (f, args) -> 
    let f_name = term_to_str env f sigma in
    (* The first element of the list is a
    type parameter and for now I just drop it *)
    let extracted_type = args.(0) in
    let type_param : EConstr.t option = 
      match type_param with
      | None -> Some extracted_type
      | Some costr_type ->
        if EConstr.eq_constr sigma costr_type extracted_type then
          Some costr_type
        else
          raise (Goal_parse_exp "Something went wrong in type parameter extraction. Report an issue.") 
    in
    let args : EConstr.t array = Array.sub args 1 (Array.length args - 1) in
    let args_repr : (EConstr.t list) = Array.to_list args in
    let args_repr : (goal_s_expr list) = 
      List.map (fun arg -> fst (goal_to_sexp_aux env arg sigma type_param)) args_repr in 
    (Application (f_name, args_repr), type_param)
  | Var n -> (Symbol (Names.Id.to_string n), type_param)
  | Ind ((name, _), _) -> 
    let name_s = Names.MutInd.to_string name in
    (Symbol name_s, type_param)
  | Lambda (_, t, body) -> 
    let t_name = fst (goal_to_sexp_aux env t sigma type_param) in
    let body_repr = fst (goal_to_sexp_aux env body sigma type_param) in
    (Lambda (t_name, body_repr), type_param)
  | _ -> raise (Goal_parse_exp "Conclusion of the goal must be an application.") 

(* Parse goal represented as a Ecostr to
   an s expression. Assumes that the term 
   contains only Applications and Variables *)
let goal_to_sexp env trm sigma = 
  goal_to_sexp_aux env trm sigma (None)

(* Split the statement into a pair of lhs and rhs,
   throw Goal_parse_exp if the amount of 
   arguments is not equal to 2 *)
let split_goal expr =
  match expr with
  | Application (f, args) -> 
    if List.length args != 2 then
      raise (Goal_parse_exp "Must be a binary operator.")
    else
      if f = "@same_relation" then 
        (List.nth args 0, List.nth args 1)
      else 
        raise (Goal_parse_exp "Goal must be of form a ⊆ b.")
  | _ -> raise (Goal_parse_exp "Invalid term passed.")

let rec s_expr_to_string expr = 
  match expr with
  | Symbol s -> s
  | Application (f, args) -> 
    let args_repr = 
      List.map (fun arg -> s_expr_to_string arg) args
      |> String.concat " "
    in
    "(" ^ f ^ " " ^ args_repr ^ ")"
  | Lambda (var, body) -> 
    let var_str = s_expr_to_string var in
    let body_str = s_expr_to_string body in
    "(λ _: " ^ var_str ^ " => " ^ body_str ^ ")"

(* Utility functions *)
let rule_to_string rule = 
  let substs = 
    List.map (fun (a, b) -> a ^ " |-> " ^ (s_expr_to_string b)) rule.rewrite_with
    |> String.concat ", "
  in 
  let dir = 
    match rule.direction with
    | Forward -> "->"
    | Backward -> "<-"
  in
  "(rewrite " ^ dir ^ " (" ^ rule.theorem ^ " (" ^ substs ^ ")) at " ^ (string_of_int rule.rewrite_at) ^ ")"