# Concurrent Interaction Trees

This development is a companion to the POPL'23 conditionally accepted submission "Choice Trees -- Representing Nondeterministic, Recursive, and Impure Programs in Coq".

## Meta

- Author(s): Nicolas Chappe, Paul He, Ludovic Henrio, Yannick Zakowski, and Steve Zdancewic
- License: MIT License
- Compatible Coq versions: 8.16
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
opam install .
```

### Obtaining the project

```shell
git clone https://github.com/vellvm/ctrees.git
git checkout popl23
cd ctrees
```

### Building the project

```shell
dune build
```

## Paper to artifact correspondence

Note: this repository contains the version of our development restricting internal branching to finite indexes,
and bisimilarity to the homogeneous case, as described in the paper.
As mentioned (footnotes 7, 10 and 11), the theory straightforwardly extends at the cost of a heavier parameterization.
We refer the interested reader to our main active repository for details: https://github.com/vellvm/ctrees/

### Structure of the repository

- theories/: the [ctree] library, containing all of core theory described in Sections 1 to 5
- examples/: our case studies and illustrative examples:
  + examples/Coffee: an encoding of the standard coffee machine example to illustrate the distinction between bisimilarity and trace equivalence (not mentioned in the paper)
  + examples/ImpBr: Imp extended with non-deterministic branching, the motivating example used in Section 2 and 3.
  + examples/ccs: our ccs case study, described in Section 6
  + examples/Yield: our cooperative scheduling case study, described in Section 7

### Correspondence

Every definition and result presented in the paper is annotated with an hyperlink to its formal counter
part on our dedicated branch ( https://github.com/vellvm/ctrees/tree/popl23 ). The Zenodo artifact is an
exact copy of this branch.
We hence recommend the reviewers to favor these hyperlinks as an easy way to track the faithfulness
of our artifact.

As mentioned before, the only exception to this is the one result strictly relying on the
generalized development, i.e. the right hand-side of Lemma 5.2.
This result can be currently found here ( https://github.com/vellvm/ctrees/blob/choice-gen-hsim/theories/Interp/Sched.v#L227 ), but we do not guarantee the long term stability of this exact link.

### Universe issue

Importing simultaneously some parts of the [Interaction Tree] library and of the
[RelationAlgebra] library currently triggers a universe inconsistency. We hence
disable at the moment universe checks in the [theories/Interp/ITree],
[examples/Yield/Lang], and [examples/Yield/Par] files via the [Unset Universe
Checking] option.

This is a purely technical issue that affects in no way the soundness of our results.
We are planning to synchronize with the authors of the respective libraries at play to
find a patch to this issue.
