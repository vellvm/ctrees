# Concurrent Interaction Trees

We develop a cousin of Interaction Trees, dubbed _ctrees_ with native support for internal non-determinism.

## Meta

- Author(s):
  - Paul He
  - Ludovic Henrio
  - Yannick Zakowski
  - Steve Zdancewic
- License: MIT License
- Compatible Coq versions: 8.13 or later
- Additional dependencies:
  - dune
  - [InteractionTrees](https://github.com/DeepSpec/InteractionTrees)
- Coq namespace: `CTree`

## Building instructions

### Installing dependencies

```shell
opam install dune
opam install coq-itree
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
