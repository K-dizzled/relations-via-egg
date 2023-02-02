[@@@warning "-67"]
module type CONTROL = sig
    val debug : bool

    val debug_feedback : bool
end
module Debug :
    functor (X : CONTROL) ->
sig
    val debug : string -> unit

    val debug_feedback : string -> unit
end
[@@@warning "+67"]