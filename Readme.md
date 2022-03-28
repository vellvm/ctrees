# Concurrent Interaction Trees

We develop a cousin of Interaction Trees, dubbed _ctrees_ with native support for internal non-determinism.

## Meta

- Author(s):
  - Paul He
  - Ludovic Henrio
  - Yannick Zakowski
  - Steve Zdancewic
- License: MIT License
- Compatible Coq versions: 8.15
- Additional dependencies:
  - dune
  - [InteractionTrees](https://github.com/DeepSpec/InteractionTrees)
  - [Equations](https://github.com/mattam82/Coq-Equations)
  - [Coinduction](https://github.com/damien-pous/coinduction)
  - [RelationAlgebra](https://github.com/damien-pous/relation-algebra)
  - [alectryon](https://github.com/cpitclaudel/alectryon) 
- Coq namespace: `CTree`

## Building instructions

### Installing dependencies

Installing the opam dependencies
```shell
opam install dune
opam install coq-itree
opam install coq-relation-algebra
opam install coq-equations
```

Installing the required branches from [coinduction] (support for 8.15 is not yet on Opam):
```shell
git clone git@github.com:damien-pous/coinduction.git
cd coinduction
git checkout v8.15
cd ..
opam pin coinduction
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
