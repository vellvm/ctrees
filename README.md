# Choice Trees
[![Docker CI](https://github.com/vellvm/ctrees/workflows/Docker%20CI/badge.svg?branch=dev)](https://github.com/vellvm/ctrees/actions?query=workflow:"Docker%20CI")
[![Nix](https://github.com/vellvm/ctrees/actions/workflows/nix-build.yml/badge.svg)](https://github.com/vellvm/ctrees/actions/workflows/nix-build.yml)

We develop a cousin of Interaction Trees, dubbed _Choice Trees_, with native support for non-determinism.

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
- Rocq namespace: `CTree`

## Related papers

- https://hal.science/hal-05154458
- https://dl.acm.org/doi/10.1145/3571254 (old)

## Building instructions

### Installing dependencies

Installing the opam dependencies
```shell
opam install coq-ext-lib coq-itree coq-relation-algebra coq-coinduction coq-equations
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

## Universe checking

Universe checking remains enabled throughout the library. The former
inconsistency came from monomorphic universe instances that identified event
and branch indices with the higher universes needed by nested choice trees,
state transformers, and interpreters. These declarations now keep their
universe levels independent and polymorphic.


