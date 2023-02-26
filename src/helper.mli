[@@@warning "-67"]
module type CONTROL = sig
    val debug : bool

    val debug_feedback : bool

    val debug_egraphs : bool

    val time : bool
end
module Debug :
    functor (X : CONTROL) ->
sig
    val debug : string -> unit

    val debug_feedback : string -> unit

    val time :
        ('a -> 'b) -> 'a -> (float -> unit, out_channel, unit) format -> 'b
end
[@@@warning "+67"]