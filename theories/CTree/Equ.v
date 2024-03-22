From CTree Require Export
  CTree.Eq.Core
  CTree.Eq.Bind.

From CTree Require Import
  CTree.Core.

From Coq Require Import
  Classes.Morphisms. 

Import CTreeNotations.
Local Open Scope ctree_scope.

Global Typeclasses Opaque equ.

Ltac observe_equ H :=
  lazymatch type of H with
  | observe ?t = RetF ?x =>
      let Heq := fresh "Eqt" in
      assert (Heq: t ≅ Ret x) by (step; cbn; rewrite H; reflexivity)
  | observe ?t = BrF ?n ?k =>
      let Heq := fresh "Eqt" in
      assert (Heq: t ≅ Br n k) by (step; cbn; rewrite H; reflexivity)
  | observe ?t = GuardF ?t' =>
      let Heq := fresh "Eqt" in
      assert (Heq: t ≅ Guard t') by (step; cbn; rewrite H; reflexivity)
  | observe ?t = VisF ?e ?k =>
      let Heq := fresh "Eqt" in
      assert (Heq: t ≅ Vis e k) by (step; cbn; rewrite H; reflexivity)
  | RetF ?x = observe ?t => symmetry in H; observe_equ H
  | VisF ?e ?k = observe ?t => symmetry in H; observe_equ H
  | GuardF ?t' = observe ?t => symmetry in H; observe_equ H
  | BrF ?n ?k = observe ?t => symmetry in H; observe_equ H
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
