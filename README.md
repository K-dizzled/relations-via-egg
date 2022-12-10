# Installation: 
Configure the opam environment:
```console
opam create switch 4.14.0 
opam switch 4.14.0
eval $(opam env --switch=4.14.0)
```

Setup dependencies:
```console
opam install merlin
opam install tuareg
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
make .merlin
make
```

