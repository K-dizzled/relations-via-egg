exception Rewriting_exp of string

let get_thr_ref thr = 
  try Nametab.locate (Libnames.qualid_of_string thr) 
  with _e -> 
    raise (Rewriting_exp ("Unable to find theorem: " ^ thr))

let new_monomorphic_global gr =
  try UnivGen.constr_of_monomorphic_global (Global.env ()) gr
  with _e ->
    raise (Rewriting_exp ("Unable to get constr from global ref"))

let _get_fresh r = new_monomorphic_global r
let get_efresh r = EConstr.of_constr (new_monomorphic_global r)

let get_thr_econstr (thr : string) = 
  let (gr : Names.GlobRef.t) = get_thr_ref thr in 
  get_efresh gr 

let get_thr_constr (thr : string) = 
  let (gr : Names.GlobRef.t) = get_thr_ref thr in 
  _get_fresh gr

let general_rewrite (constr : EConstr.constr) (l2r : bool) (at_occ : int) =   
  Equality.general_rewrite ~where:None
    ~l2r:l2r
    (Locus.OnlyOccurrences [at_occ])
    ~freeze:true
    ~dep:false
    ~with_evars:true
    (constr, Tactypes.NoBindings)

let rewrite (thr : string) (dir : Parse_goal.direction) =
  let constr = get_thr_econstr thr in
  let l2r = match dir with
    | Parse_goal.Forward -> true
    | Parse_goal.Backward -> false
  in
  general_rewrite constr l2r 1 

let rewrite_with (thr : string) (dir : Parse_goal.direction) (with_constrs : Constr.t array) (at_occ : int) =
  let constr = get_thr_constr thr in
  let first_arg_constr = Constr.mkVar (Names.Id.of_string "A") in 
  let constr = 
    if Array.length with_constrs = 0 then 
      constr 
    else Constr.mkApp (constr, (Array.append [|first_arg_constr|] with_constrs)) in

  let l2r = match dir with
    | Parse_goal.Forward -> true
    | Parse_goal.Backward -> false
  in
  general_rewrite (EConstr.of_constr constr) l2r at_occ