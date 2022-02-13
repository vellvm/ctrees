# Concurrent Interaction Trees

We develop a cousin of Interaction Trees, dubbed _ctrees_ with native support for internal non-determinism.

## Meta

- Author(s):
  - Paul He
  - Ludovic Henrio
  - Yannick Zakowski
  - Steve Zdancewic
- License: MIT License
- Compatible Coq versions: 8.14
- Additional dependencies:
  - dune
  - [InteractionTrees](https://github.com/DeepSpec/InteractionTrees)
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
```

Installing the required branches from [coinduction] and [relation-algebra]:
```shell
git clone git@github.com:damien-pous/coinduction.git
opam pin coinduction
git clone git@github.com:damien-pous/relation-algebra.git
cd relation-algebra
git checkout v8.14
cd ..
opam pin relation-algebra
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
