open Evd

(* Util functions taken from: 
   https://github.com/tlringer/plugin-tutorial 
*)

type 'a state = evar_map * 'a

let global_env () =
  let env = Global.env () in
  Evd.from_env env, env

let push_local (n, t) env =
  EConstr.push_rel Context.Rel.Declaration.(LocalAssum (n, t)) env

let internalize env trm sigma =
  Constrintern.interp_constr_evars env sigma trm

let equal env trm1 trm2 sigma =
  let opt = Reductionops.infer_conv env sigma trm1 trm2 in
  match opt with
  | Some sigma -> sigma, true
  | None -> sigma, false