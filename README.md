# Pre-setup Cargo (only for Mac)
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

# Installation: 
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

## To use from outside of the source folder: 
```console
dune build @install
opam install coq-via-egg-plugin .
```
