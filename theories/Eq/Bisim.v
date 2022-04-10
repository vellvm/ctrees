(*|
Remarks and TODOs:
------------------
- Strong and weak bisimulations are only defined as relations enforcing
  equality of returned values. We should generalize this when needed.
- Weak bisimulation can also be defined as the strong game over [wtrans].
  Are we interested in doing so?

|*)

  End Weak.

End Bisim.

Module BisimNotations.

  Notation "t ~ u" := (sbisim t u) (at level 70).
  Notation st := (t sb).
  Notation sT := (T sb).
  Notation sbt := (bt sb).
  Notation sbT := (bT sb).
  (** notations  for easing readability in proofs by enhanced coinduction *)
  Notation "t [~] u" := (st  _ t u) (at level 79).
  Notation "t {~} u" := (sbt _ t u) (at level 79).

  Notation "p ≈ q" := (wbisim p q) (at level 70).
  Notation wt := (coinduction.t wb).
  Notation wT := (coinduction.T wb).
  Notation wbt := (coinduction.bt wb).
  Notation wbT := (coinduction.bT wb).
  (** notations  for easing readability in proofs by enhanced coinduction *)
  Notation "x [≈] y" := (wt _ x y) (at level 80).
  Notation "x {≈} y" := (wbt _ x y) (at level 80).

End BisimNotations.

