module type CONTROL = sig
  val debug : bool
  val debug_feedback : bool
  val debug_egraphs : bool
end

module Debug (X : CONTROL) = struct
  open X
  let debug x =
    if debug then
      Printf.printf "%s\n%!" x

  let debug_feedback x =
    if debug_feedback then
      Feedback.msg_notice (Pp.str x)
end