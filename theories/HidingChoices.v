(*|
==================
Hiding all choices
==================

.. coq::none
|*)
From Coinduction Require Import
	   coinduction rel tactics.

From RelationAlgebra Require Import
     monoid
     kat
     kat_tac
     prop
     rel
     srel
     comparisons
     rewriting
     normalisation.

From CTree Require Import
	   Utils CTrees Shallow Trans Equ Bisim.

Obligation Tactic := idtac.

Import CTree.
Import CTreeNotations.
Open Scope ctree.
Import Fin.

Definition hide' {E R} : ctree' E R -> ctree E R :=
  cofix hide t :=
    match t with
    | RetF v => Ret v
    | VisF e k => Vis e (fun x => hide (observe (k x)))
    | ChoiceF b n k => Choice false n (fun x => hide (observe (k x)))
    end.

Definition hide {E R} (t : ctree E R) := hide' (observe t).

Lemma wbisim_is_hidden_sbisim :
  forall {E R} (t u : ctree E R),
    t ≈ u <-> hide t ~ hide u.
Proof.
Admitted.

