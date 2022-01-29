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
	   Utils CTrees Shallow Trans Equ Bisim CTreesTheory.

Obligation Tactic := idtac.

Import CTree.
Import CTreeNotations.
Open Scope ctree.
Import Fin.

(* Definition hide' {E R} : ctree' E R -> ctree E R := *)
(*   cofix hide t := *)
(*     match t with *)
(*     | RetF v => Ret v *)
(*     | VisF e k => Vis e (fun x => hide (observe (k x))) *)
(*     | ChoiceF b n k => Choice false n (fun x => hide (observe (k x))) *)
(*     end. *)

(* Definition hide {E R} (t : ctree E R) := hide' (observe t). *)

Definition hide {E R} : ctree E R -> ctree E R :=
  cofix hide t :=
    match observe t with
    | RetF v => Ret v
    | VisF e k => Vis e (fun x => hide (k x))
    | ChoiceF b n k => Choice false n (fun x => hide (k x))
    end.

Notation hide_ t :=
  match observe t with
  | RetF v => Ret v
  | VisF e k => Vis e (fun x => hide (k x))
  | ChoiceF b n k => Choice false n (fun x => hide (k x))
  end.

Lemma unfold_hide {E R} (t : ctree E R) :
  hide t ≅ hide_ t.
Proof.
  now step.
Qed.

#[global] Instance hide_equ {E R} :
  Proper (equ eq ==> equ eq) (@hide E R).
Proof.
  unfold Proper, respectful.
  coinduction ? CIH.
  intros * EQ.
  cbn.
  rewrite 2 unfold_hide.
  step in EQ.
  inv EQ; cbn; auto.
Qed.

Ltac split_wtr WTR := destruct WTR as [?t2 [?t1 ?step1 ?step2] ?step3].

Lemma eq_observe_equ {E R} : forall (t u : ctree E R),
    observe t = observe u ->
    t ≅ u.
Proof.
  intros * EQ; now rewrite ctree_eta,EQ,<-ctree_eta.
Qed.

Lemma trans_hide {E R} :
  forall l (t u : ctree E R),
    l <> tau ->
    trans l t u ->
    trans l (hide t) (hide u).
Proof.
  intros * INEQ TR.
  cbn in *; unfold transR in *.
  genobs t ot; genobs u ou.
  revert t u Heqot Heqou.
  induction TR; intros; try easy.
  - rewrite unfold_hide, <- Heqot.
    eapply (trans_ChoiceI x); eauto.
    apply IHTR; auto.
  - rewrite unfold_hide, <- Heqot.
    constructor.
    rewrite H.
    rewrite 2 unfold_hide, Heqou; reflexivity.
  - rewrite unfold_hide, <- Heqot.
    rewrite unfold_hide, <- Heqou.
    econstructor.
Qed.

Lemma trans_tau_hide {E R} :
  forall l (t u v : ctree E R),
    trans tau t u ->
    trans l (hide u) (hide v) ->
    trans l (hide t) (hide v).
Proof.
  intros * TR1 TR2.
  remember tau as l'.
  cbn in TR1; unfold transR in TR1.
  genobs t ot; genobs u ou.
  revert t Heqot.
  induction TR1; try easy; intros.
  - rewrite unfold_hide, <- Heqot;
      eapply trans_ChoiceI; [|reflexivity]; eauto.
  - rewrite unfold_hide, <- Heqot.
    eapply (trans_ChoiceI x).
    eauto.
    rewrite H.
    apply eq_observe_equ in Heqou; rewrite Heqou; auto.
Qed.

Lemma trans_tau_hide' {E R} :
  forall l (t u v : ctree E R),
    l <> tau ->
    trans tau t u ->
    trans l u v ->
    trans l (hide t) (hide v).
Proof.
  intros * INEQ TR1 TR2.
  apply trans_hide in TR2; auto.
  eapply trans_tau_hide; eauto.
Qed.

Lemma transs_hide {E R} :
  forall l (t u v : ctree E R),
    l <> tau ->
    (trans tau)^* t u ->
    trans l u v ->
    trans l (hide t) (hide v).
Proof.
  intros * INEQ (n & TR); revert t u v TR.
  induction n as [| n IH]; intros.
  - cbn in TR.
    apply trans_hide; auto; now rewrite TR.
  - destruct TR as [? TR1 TRn].
    eapply trans_tau_hide; eauto.
Qed.

(* This does not hold: the taus in queue cannot be eaten *)
Lemma wtrans_hide {E R} :
  forall l (t u : ctree E R),
    l <> tau ->
    wtrans l t u ->
    trans l (hide t) (hide u).
Proof.
  intros * INEQ WTR.
  split_wtr WTR.
Abort.

Arguments wtrans : simpl never.
Lemma wbisim_is_hidden_sbisim :
  forall {E R} (t u : ctree E R),
    t ≈ u <-> hide t ~ hide u.
Proof.
  split.
  - revert t u.
    coinduction ? CIH.
    (* Why does symmetric loop? *)
    intros * EQ.
    split.
    + intros l t' TR.
      rewrite unfold_hide in TR.
      step in EQ; destruct EQ as [F _].
      cbn in F.
      unfold transR in F.
      desobs t.
      * specialize (F (val r) stuckI); destruct F; [constructor|].

Admitted.
