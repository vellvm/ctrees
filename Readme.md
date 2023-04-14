# Choice Trees
[![Docker CI](https://github.com/vellvm/ctrees/workflows/Docker%20CI/badge.svg?branch=master)](https://github.com/vellvm/ctrees/actions?query=workflow:"Docker%20CI")

A cousin of Interaction Trees, dubbed _ctrees_, with native support for internal non-determinism.

## Meta

- Author(s):
  - Nicolas Chappe
  - Paul He
  - Ludovic Henrio
  - Yannick Zakowski
  - Steve Zdancewic
- License: GPLv3
- Compatible Coq versions: 8.17
- Additional dependencies:
  - dune
  - [Extlib](https://github.com/coq-community/coq-ext-lib)
  - [InteractionTrees](https://github.com/DeepSpec/InteractionTrees)
  - [Equations](https://github.com/mattam82/Coq-Equations)
  - [Coinduction](https://github.com/damien-pous/coinduction)
  - [RelationAlgebra](https://github.com/damien-pous/relation-algebra)
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
git clone https://github.com/vellvm/ctrees
cd ctrees
```

### Building the project

```shell
dune build
```

## Associated publications

- Choice Trees: Representing Nondeterministic, Recursive, and Impure Programs in Coq.  
  Nicolas Chappe, Paul He, Ludovic Henrio, Yannick Zakowski, and Steve Zdancewic.  
  [POPL'23](https://dl.acm.org/doi/10.1145/3571254)

## Universe issue

Importing simultaneously some parts of the [Interaction Tree] library and of the [RelationAlgebra] library currently triggers a universe inconsistency, as discussed notably in [the following issue](https://github.com/DeepSpec/InteractionTrees/issues/254).

Until this problem is resolved, we hence disable universe checks in part of the library via the [Unset Universe Checking] option.
