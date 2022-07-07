From ExtLib Require Import
     Structures.Functor
     Structures.Monad.

From CTree Require Import
     Eq.

Import MonadNotation.
Open Scope monad_scope.
Notation BrSF := (BrF true).
Notation BrDF := (BrF false).

Definition norm {E X} (t : ctree E X) : ctree E X :=
	CTree.iter (fun t =>
				        match observe t with
				        | RetF r => ret (inr r)
				        | BrDF n k =>
                    BrD n (fun x => ret (inl (k x)))
				        | BrSF n k =>
                    BrD n (fun x => Step (ret (inl (k x))))
				        | VisF e k => bind (mtrigger _ e) (fun x => ret (inl (k x)))
				        end) t.

Lemma unfold_norm {E X} (t : ctree E X) :
  norm t ≅
  match observe t with
	| RetF r => ret r
	| BrDF n k =>
      BrD n (fun x => Guard (norm (k x)))
	| BrSF n k =>
      BrD n (fun x => Step (Guard (norm (k x))))
	| VisF e k => bind (mtrigger _ e) (fun x => Guard (norm (k x)))
	end.
Proof.
  unfold norm at 1.
  rewrite unfold_iter.
  desobs t; cbn.
  - now rewrite bind_ret_l.
  - unfold mtrigger; rewrite bind_bind, !bind_trigger.
    step; constructor; intros ?.
    rewrite bind_ret_l.
    reflexivity.
  - destruct vis.
    + rewrite bind_br.
      step; constructor; intros ?.
      rewrite bind_Step; step; constructor; intros ?.
      rewrite bind_ret_l.
      step; constructor; auto.
    + rewrite bind_br.
      step; constructor; intros ?.
      rewrite bind_ret_l.
      step; constructor; auto.
Qed.

Lemma trans_norm_inv_strong :
  forall {E X} (t u v : ctree E X) l,
    (v ≅ norm t \/ v ≅ Guard (norm t)) ->
    trans l v u ->
    exists t', trans l t t'
          /\ (u ≅ norm t' \/ u ≅ Guard (norm t')).
Proof.
  intros * EQ TR.
  revert t EQ.
  unfold trans in TR; repeat red in TR.
  dependent induction TR.
  - intros ? [EQ | EQ].
    + rewrite ctree_eta, <- x, unfold_norm in EQ.
      setoid_rewrite (ctree_eta t).
      desobs t; try now step in EQ; inv EQ.
      destruct vis.
      * pose proof equ_br_invT _ _ EQ as [<- _].
        apply equ_br_invE with (x := x0) in EQ .
        rewrite EQ in TR.
        apply trans_step_inv in TR as [EQ' ->].
        eexists; split; eauto.
        etrans.

      * pose proof equ_br_invT _ _ EQ as [<- _].
        apply equ_br_invE with (x := x0) in EQ .
        specialize (IHTR _ _ eq_refl eq_refl).
        edestruct IHTR as (t' & ? & ?); eauto.
        exists t'.
        split.
        eapply trans_brD with (x := x0); eauto.
        eauto.

    + rewrite ctree_eta, <- x in EQ.
      pose proof equ_br_invT _ _ EQ as [-> _].
      apply equ_br_invE with (x := x0) in EQ .
      specialize (IHTR _ _ eq_refl eq_refl).
      edestruct IHTR as (t' & ? & ?); eauto.

  - (* G(t) ≅ BrS k : absurd *)
    intros ? [EQ | EQ].
    + rewrite ctree_eta, <- x1, unfold_norm in EQ.
      desobs t0; try now step in EQ; inv EQ.
      destruct vis; try now step in EQ; inv EQ.
    + rewrite ctree_eta, <- x1 in EQ.
      now step in EQ; inv EQ.

  - (* G(t) ≅ Vis e k : t ≅ Vis e k', k x ≅ Guard (G (k' x)) *)
    intros ? [EQ | EQ].
    + setoid_rewrite (ctree_eta t0).
      rewrite ctree_eta, <- x1, unfold_norm in EQ.
      rewrite (ctree_eta t), x in H.
      clear t x.
      desobs t0; try now step in EQ; inv EQ.
      2:destruct vis; try now step in EQ; inv EQ.
      cbn in *.
      unfold mtrigger in EQ; rewrite bind_trigger in EQ.
      pose proof equ_vis_invT _ _ _ _ EQ; subst.
      pose proof equ_vis_invE _ _ _ _ EQ as [-> EQ'].
      eexists; split.
      etrans.
      rewrite <- ctree_eta in H.
      rewrite <- H.
      rewrite EQ'.
      auto.
    + rewrite ctree_eta, <- x1 in EQ.
      now step in EQ; inv EQ.

  - (* G(t) ≅ Ret x : t ≅ Ret x *)
    intros ? [EQ | EQ].
    + setoid_rewrite (ctree_eta t).
      rewrite ctree_eta, <- x0, unfold_norm in EQ.
      desobs t; try now step in EQ; inv EQ.
      2:destruct vis; try now step in EQ; inv EQ.
      step in EQ; inv EQ.
      eexists; split.
      etrans.
      left.
      rewrite ctree_eta, <- x, unfold_norm.
      cbn.
      rewrite ! brD0_always_stuck.
      reflexivity.
    + rewrite ctree_eta, <- x0 in EQ.
      now step in EQ; inv EQ.
Qed.

Lemma trans_norm_inv :
  forall E X (t u : ctree E X) l,
    trans l (norm t) u ->
    exists t', trans l t t'
          /\ u ~ norm t'.
Proof.
  intros.
  edestruct @trans_norm_inv_strong as (t' & TR & EQ); [|eassumption|].
  left; eauto.
  exists t'; split; auto.
  destruct EQ as [EQ |EQ]; rewrite EQ; auto.
  rewrite sb_guard; auto.
Qed.

Ltac fold_bind :=
  repeat match goal with
           |- context [CTree.subst ?k ?t] => fold (CTree.bind t k)
         end.

#[global] Instance norm_equ E X : Proper (equ eq ==> equ eq) (@norm E X).
Proof.
  do 2 red.
  coinduction ? IH.
  intros * EQ.
  step in EQ.
  rewrite ! unfold_norm.
  cbn*.
  inv EQ; auto.
  - cbn.
    constructor; intros ?.
    fold_bind; rewrite ! bind_ret_l.
    step; constructor; intros _.
    auto.
  - destruct b; cbn.
    all: constructor; intros ?.
    all: repeat (step; constructor; intros ?).
    all: auto.
Qed.

Opaque CTree.bind.
Lemma trans_norm_strong :
  forall E X (t u : ctree E X) l,
    trans l t u ->
    exists u',
      trans l (norm t) u'
      /\ (u' ≅ norm u
         \/ u' ≅ Guard (norm u)).
Proof.
  intros * TR.
  (* revert t EQ. *)
  unfold trans in TR; repeat red in TR.
  dependent induction TR; intros.
  - (* destruct EQ as [EQ | EQ]. *)
    edestruct IHTR as (u' & TR' & EQ'); eauto.
    setoid_rewrite unfold_norm at 1; rewrite <- x.
    exists u'; split.
    eapply trans_brD with (x := x0); [| reflexivity].
    now apply trans_guard.
    auto.
  - setoid_rewrite unfold_norm at 1; rewrite <- x1.
    eexists; split.
    eapply trans_brD with (x := x0); [| reflexivity].
    etrans.
    right.
    step; constructor; intros ?.
    rewrite H.
    rewrite (ctree_eta t0),x,<- ctree_eta.
    auto.
  - setoid_rewrite unfold_norm at 1; rewrite <- x1.
    eexists; split.
    unfold mtrigger, MonadTrigger_ctree; cbn.
    rewrite bind_trigger.
    etrans.
    right.
    step; constructor; intros ?.
    rewrite H.
    rewrite (ctree_eta t0),x,<- ctree_eta.
    auto.
  - setoid_rewrite unfold_norm at 1; rewrite <- x0.
    eexists; split.
    (*
      Why do I need to cbn even if I add:
      Hint Unfold ret Monad_ctree : trans.
     *)
    cbn; etrans.
    left.
    rewrite unfold_norm, <- x; cbn.
    now rewrite ! brD0_always_stuck.
Qed.

Lemma trans_norm :
  forall E X (t u : ctree E X) l,
    trans l t u ->
    exists u',
      trans l (norm t) u'
      /\ u' ~ norm u.
Proof.
  intros * TR.
  edestruct trans_norm_strong as (u' & TR' & EQ'); eauto.
  exists u'; split; auto.
  destruct EQ' as [EQ' | EQ']; rewrite EQ'; auto.
  now rewrite sb_guard.
Qed.

Ltac sret  := apply step_sb_ret.
Ltac svis  := apply step_sb_vis.
Ltac sStep := apply step_sb_step.
Ltac sstep := sret || svis || sStep.

Lemma norm_is_bisimilar {E X} : forall (t : ctree E X),
    norm t ~ t.
Proof.
  coinduction ? IH.
  intros t.
  rewrite (ctree_eta t) at 2.
  rewrite unfold_norm.
  desobs t.
  - now cbn.
  - cbn*.
    unfold mtrigger; rewrite bind_trigger.
    sstep; intros ?.
    rewrite sb_guard.
    apply IH.
  - destruct vis.
    + cbn.
      split; intros ? ? TR.
      * inv_trans.
        subst.
        eexists.
        eapply trans_brS with (x := n0).
        rewrite EQ.
        rewrite sb_guard.
        apply IH.
      * cbn.
        inv_trans; subst.
        eexists.
        eapply trans_brD with (x := n0).
        2:etrans.
        etrans.
        rewrite sb_guard.
        rewrite EQ; apply IH.
    + split.
      * intros ? ? TR.
        cbn.
        inv_trans.
        edestruct trans_norm_inv as (u' & TR' & EQ'); eauto.
        eexists.
        eapply trans_brD with (x := n0); [| reflexivity].
        eassumption.
        rewrite EQ'; auto.
      * cbn; intros ? ? TR.
        inv_trans.
        edestruct trans_norm as (u' & TR' & EQ'); eauto.
        eexists.
        eapply trans_brD with (x := n0); [| reflexivity].
        apply trans_guard.
        eauto.
        rewrite EQ'; auto.
Qed.
