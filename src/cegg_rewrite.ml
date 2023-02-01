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

let general_rewrite (constr : EConstr.constr) (l2r : bool) =   
  Equality.general_rewrite ~where:None
    ~l2r:l2r
    Locus.AllOccurrences
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
  general_rewrite constr l2r