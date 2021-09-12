# A few notes on trailing things to consider

## Interpretation and scheduling

What do we want to do w.r.t. implementation of the internal choice?

From the perspective of reasoning, we don't need anything particular since the bisimulation should be precise enough to capture all equivalences w.r.t. this effect.
We could hence simply delegate the implementation on the OCaml side.

It could however also be interesting to study what it means to interpret it inside of Coq.

## Bisimulation and "Cosimulation"

The [BisimSched] rule amounts to the traditional bisimulation: locally, both computations challenge one another.

We could alternatively mimick the usual simulation, breaking the symmetry in the relation, and ask for both
computations to simulation one another -- let's call this to be in _cosimulation_.

It is well known that traditionally cosimulation is strictly weaker than bisimulation. Is it also the case in this setup?

## Weak bisimulation, barbed bisimulations and the whole zoo

From the perspective of a calculus like ccs of the pi-calculus, we expect to define an equivalence as ctree's notion of bisimulation applied to the representation function as ctrees of the terms.

However it is well known that there exists many bisimulations defined on top of the operational semantics of these calculi. Hence the question: which one do we get naturally, if any? And how would we get the others: by defining a different equivalence over ctrees, or by changing the representation function?
