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

### Building the project using coq_makefile

```shell
coq_makefile -f _CoqProject -o Makefile  # in case you want to regenerate it
make                                     # or make -j <number-of-cores-on-your-machine>
```

### Building the html documentation

This depends on [alectryon](https://github.com/cpitclaudel/alectryon). First install it with:

```shell
opam install coq-serapi
python3 -m pip install --user alectryon
```

Build with:

```shell
mkdir html-doc
alectryon --output-directory html-doc -Q theories OGS -R ./lib/InteractionTrees/theories ITree theories/{LCD.v,OGSD.v}
```

You should see some html files in the html-doc directory.
