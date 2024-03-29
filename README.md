# Equality saturation for solving equalities of relational expressions

Andrei Kozyrev's Bachelor's Thesis. Thesis could be found [here](https://github.com/K-dizzled/equality-saturation-in-coq-thesis/blob/master/diploma.pdf).

## Building the project: 

### Pre-setup Cargo (only for Mac)
Add the following to your `~/.cargo/config` (create one if you don't have such file):
```console 
[target.x86_64-apple-darwin]
rustflags = [
  "-C", "link-arg=-undefined",
  "-C", "link-arg=dynamic_lookup",
]

[target.aarch64-apple-darwin]
rustflags = [
  "-C", "link-arg=-undefined",
  "-C", "link-arg=dynamic_lookup",
]
```

### Opam setup: 
Configure the opam environment:
```console
opam switch create 4.14.0 
eval $(opam env)
```

Setup dependencies:
```console
opam install coq=8.16.0
opam install merlin
opam install tuareg
opam install dune
```

Setup hahn library:
```console
opam repo add coq-released https://coq.inria.fr/opam/released
opam remote add coq-weakmemory-local -k git https://github.com/weakmemory/local-coq-opam-archive
opam install coq-hahn
```

Finish the setup:
```console
opam user-setup install
eval $(opam env)
```

Build the project:
```console
dune build
```

### To use from outside of the source folder: 
```console
dune build @install
opam install coq-via-egg-plugin .
```

Afterwards you can import and use the plugin in your Coq files like this: 
```coq
Declare ML Module "cegg_plugin:coq-via-egg-plugin.plugin".
From hahn Require Import Hahn.

Lemma test_with2 (A : Type) (r : relation A) : 
  (r^?)^+ ;; ((r^?)^?)^+ ≡ (r^?)^+ ;; (r^?)^*.
Proof.
  Cegg solve eq. 
Qed.
```

## Usage: 
* `Cegg config <reference>`: Configure the plugin with the given reference to a `Record` object. Allows to configure the ruleset for egg. It takes a user-defined list of rewrite rules and caches it for the later use in Cegg solve and Cegg solve eq.

  ```coq
  Record Wf :=
    { 
      mo_trans : mo ;; mo ⊆ mo ; 
      rf_mo : rf ;; mo ≡ ∅₂ ;
      rf_rf : rf ;; rf ≡ ∅₂ ;
    }.

  Cegg config Wf.
  ```
* `Cegg solve`: Simplifies the lhs of the equation.

  ```coq
  Lemma example1 (A : Type) (r : relation A) : 
    ((r ;; r^*)^?)^+ ;; ((r^?)^?)^+ ≡ r^*.
  Proof.
    Cegg solve. (* Changes goal to r^* ≡ r^* *)
  Qed.
  ```

  Tries to call `reflexivity` after the simplification.

* `Cegg solve eq`: Tries to prove the equivalence between the lhs and rhs of the equation.

  ```coq
  Lemma example2 (A : Type) (r : relation A) : 
    (r^?)^+ ;; ((r^?)^?)^+ ≡ (r^?)^+ ;; (r^?)^*.
  Proof.
    Cegg solve eq. (* Successfully proves equivalence and concludes the proof *)
  Qed.
  ```
* `Cegg solve eq using <strategy>`: Tries to prove the equivalence between the lhs and rhs of the equation using the given strategy. Available options: `bidi`, `intersect` and `search_both` (default). 
  - `search_both` builds an e-graph for lhs and searches for the rhs in it and vice-versa. Although it uses only oriented rules.
  - `bidi` builds an e-graph for the lhs using bidirectional rules and tries to find rhs in it. The slowest strategy, but manages to solve more equations.
  - `intersect` builds both e-graphs and checks their intersection to be non-empty. If it finds an element that is equivalent to both a and b, it concludes that a ≡ b and constructs a proof.

  ```coq
  Lemma example3 (A : Type) (r : relation A) : 
    (r^?)^+ ;; ((r^?)^?)^+ ≡ (r^?)^+ ;; (r^?)^*.
  Proof.
    (* Cegg solve eq using "intersect". *)
    (* Cegg solve eq using "bidi". *).
    Cegg solve eq using "search_both".
  Qed.
  ```

## Project Layout: 
* `src/`: The source code of the plugin.
* `theories/`: Code in `Coq` that is used for testing the plugin.
* `src/rust-egg/`: The source code of the rust part of the plugin.
* `src/rust-egg/src/config.rs`: Resrite system rules and constants.
* `src/rust-egg/src/goal_preprocess.rs`: Parsing data that have come from OCaml.
* `src/rust-egg/src/lib.rs`: The entry point of the rust part. Contains functions that are being called using the FFI from OCaml.
* `src/rust-egg/src/proof_strategy.rs`: Implementation of various proof strategies.
* `src/rust_api.ml`: FFI function signatures.
* `src/cegg.mlg`: Vernacular declarations of tactics and commands. 
* `src/solver.ml`: The entry point of the OCaml part. Contains functions that are being called from `src/cegg.mlg`. 
