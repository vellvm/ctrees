From CTree Require Export
  ITree.Eq.Core
  ITree.Eq.Bind.

From CTree Require Import ITree.Core.
From Coq Require Import Classes.Morphisms.

Export EquNotations.

Ltac observe_equ H :=
  lazymatch type of H with
  | observe ?t = RetF ?x =>
      let Heq := fresh "Eqt" in
      assert (Heq: t ≅ Ret x) by (step; cbn; rewrite H; reflexivity)
  | observe ?t = TauF ?t' =>
      let Heq := fresh "Eqt" in
      assert (Heq: t ≅ Tau t') by (step; cbn; rewrite H; reflexivity)
  | observe ?t = VisF ?e ?k =>
      let Heq := fresh "Eqt" in
      assert (Heq: t ≅ Vis e k) by (step; cbn; rewrite H; reflexivity)
  | RetF ?x = observe ?t => symmetry in H; observe_equ H
  | TauF ?t' = observe ?t => symmetry in H; observe_equ H
  | VisF ?e ?k = observe ?t => symmetry in H; observe_equ H
  | observe ?t = observe ?t' =>
      let Heq := fresh "Eqt" in        
      assert (Heq: t ≅ t') by (step; cbn; rewrite H; reflexivity)
  end.

Ltac observe_equ_all :=
  match goal with
  | H: _ = _ |- _ => (* Do something with hypothesis H *)
      observe_equ H;            
      clear H;
      observe_equ_all
  | _ => idtac
  end.

