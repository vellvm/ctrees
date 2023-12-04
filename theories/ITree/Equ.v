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

Inductive may_ret_{E X} `{Encode E}: X -> itree' E X -> Prop :=
| RetRet: forall x,
    may_ret_ x (RetF x)
| RetTau: 
  forall t t' x,
    may_ret_ x (observe t') ->
    t ≅ Tau t' ->
    may_ret_ x (observe t).
Global Hint Constructors may_ret_: core.

Definition may_ret{E X} `{Encode E} (x: X)(t: itree E X): Prop := may_ret_ x (observe t).
Global Hint Unfold may_ret: core.

Global Instance proper_may_ret{X}:
  Proper (eq ==> equ eq ==> iff) (may_ret (X:=X)).
Proof.
  unfold Proper, respectful; split; intros; subst.
  - generalize dependent y0.
    unfold may_ret in *.
    remember (observe x0) as Hx0.
    induction H1; intros. 
    step in H0; cbn in H0; inv H0; rewrite <- HeqHx0 in H; inv H.
    + econstructor.
    + observe_equ HeqHx0.
      eapply RetTau; eauto.
      now rewrite <- H0, <- Eqt.
  - generalize dependent x0.
    unfold may_ret in *.
    remember (observe y0) as Hy0.
    induction H1; intros. 
    step in H0; cbn in H0; inv H0; rewrite <- HeqHy0 in H1; inv H1.
    + econstructor.
    + observe_equ HeqHy0.
      eapply RetTau; eauto.
      now rewrite H0, <- Eqt.
Qed.

Global Instance proper_may_ret_{X}:
  Proper (eq ==> going (equ eq) ==> iff) (may_ret_ (X:=X)).
Proof.
  unfold Proper, respectful; intros.
  inv H0.
  eapply proper_may_ret in H1.
  unfold may_ret in H1; cbn in H1.
  apply H1.
  reflexivity.
Qed.

