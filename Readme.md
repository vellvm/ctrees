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
  - [InteractionTrees](https://github.com/DeepSpec/InteractionTrees) master
- Coq namespace: `CTree`

## Building instructions

### Installing dependencies

```shell
opam install coq-itrees
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
