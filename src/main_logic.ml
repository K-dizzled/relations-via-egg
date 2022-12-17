let message = "Tactic invocated"

module Rust = struct
  external twice : int -> int = "rust_twice"
end