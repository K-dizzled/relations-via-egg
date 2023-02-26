module type CONTROL = sig
  val debug : bool
  val debug_feedback : bool
  val debug_egraphs : bool
  val time : bool 
end

module Debug (X : CONTROL) = struct
  open X
  let debug x =
    if debug then
      Printf.printf "%s\n%!" x

  let debug_feedback x =
    if debug_feedback then
      Feedback.msg_notice (Pp.str x)

  let time f x fmt =
    if time then
      let t = Sys.time () in
      let r = f x in
        Printf.printf fmt  (Sys.time () -. t);
        r
    else f x
end