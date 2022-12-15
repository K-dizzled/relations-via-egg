open Evd
open Environ
open Constrexpr

type 'a state = evar_map * 'a

val global_env : unit -> env state

val push_local :
  Names.Name.t Context.binder_annot * EConstr.t -> (* name, type *)
  env -> (* environment *)
  env (* updated environment *)

val internalize :
  env -> (* environment *)
  constr_expr -> (* external representation *)
  evar_map -> (* state *)
  EConstr.t state (* stateful internal representation *)

val equal :
  env -> (* environment *)
  EConstr.t -> (* trm1 *)
  EConstr.t -> (* trm2 *)
  evar_map -> (* state *)
  bool state (* stateful (t1 = t2) *)