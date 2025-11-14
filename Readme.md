# Choice Trees
[![Docker CI](https://github.com/vellvm/ctrees/workflows/Docker%20CI/badge.svg?branch=master)](https://github.com/vellvm/ctrees/actions?query=workflow:"Docker%20CI")
[![Nix](https://github.com/vellvm/ctrees/actions/workflows/nix-build.yml/badge.svg)](https://github.com/vellvm/ctrees/actions/workflows/nix-build.yml)

We develop a cousin of Interaction Trees, dubbed _ctrees_ with native support for internal non-determinism.

## Meta

- Author(s):
  - Nicolas Chappe
  - Paul He
  - Ludovic Henrio
  - Eleftherios Ioannidis
  - Yannick Zakowski
  - Steve Zdancewic
- License: MIT License
- Compatible Rocq versions: 9.0
- Additional dependencies:
  - dune
  - [Extlib](https://github.com/coq-community/coq-ext-lib)
  - [InteractionTrees](https://github.com/DeepSpec/InteractionTrees)
  - [Equations](https://github.com/mattam82/Coq-Equations)
  - [Coinduction](https://github.com/damien-pous/coinduction)
  - [RelationAlgebra](https://github.com/damien-pous/relation-algebra)
  - [Alectryon](https://github.com/cpitclaudel/alectryon)
- Rocq namespace: `CTree`

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
git clone https://github.com/vellvm/ctrees
cd ctrees
```

### Building the project

```shell
dune build
```
