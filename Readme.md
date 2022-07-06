# Concurrent Interaction Trees

This development is a companion to the POPL'23 submission "Choice Trees -- Representing Nondeterministic, Recursive, and Impure Programs in Coq".

## Meta

- Author(s): REDACTED
- License: MIT License
- Compatible Coq versions: 8.15
- Additional dependencies:
  - dune
  - [Extlib](https://github.com/coq-community/coq-ext-lib)
  - [InteractionTrees](https://github.com/DeepSpec/InteractionTrees)
  - [Equations](https://github.com/mattam82/Coq-Equations)
  - [Coinduction](https://github.com/damien-pous/coinduction)
  - [RelationAlgebra](https://github.com/damien-pous/relation-algebra)
  - [Alectryon](https://github.com/cpitclaudel/alectryon)
- Coq namespace: `CTree`

## Building instructions

### Installing dependencies

Installing the opam dependencies
```shell
opam install dune
opam install coq-ext-lib
opam install coq-itree
opam install coq-relation-algebra
opam install coq-coinduction
opam install coq-equations
```

### Obtaining the project

```shell
git clone https://github.com/redacted
cd ctrees
```

### Building the project

```shell
dune build
```
