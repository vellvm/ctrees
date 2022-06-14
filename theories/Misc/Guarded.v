From ExtLib Require Import
     Structures.Functor
     Structures.Monad.

From CTree Require Import
     Eq.
(* Import ITree.Basics.Basics.Monads. *)
Import MonadNotation.
Open Scope monad_scope.
Notation ChoiceVF := (ChoiceF true).
Notation ChoiceIF := (ChoiceF false).

Definition guarded_form {E X} (t : ctree E X) : ctree E X :=
	CTree.iter (fun t =>
				        match observe t with
				        | RetF r => ret (inr r)
				        | ChoiceIF n k =>
                    ChoiceI n (fun x => ret (inl (k x)))
				        | ChoiceVF n k =>
                    ChoiceI n (fun x => TauV (ret (inl (k x))))
				        | VisF e k => bind (mtrigger _ e) (fun x => ret (inl (k x)))
				        end) t.

Lemma unfold_guarded_form {E X} (t : ctree E X) :
  guarded_form t ≅
  match observe t with
	| RetF r => ret r
	| ChoiceIF n k =>
      ChoiceI n (fun x => TauI (guarded_form (k x)))
	| ChoiceVF n k =>
      ChoiceI n (fun x => TauV (TauI (guarded_form (k x))))
	| VisF e k => bind (mtrigger _ e) (fun x => TauI (guarded_form (k x)))
	end.
Proof.
  unfold guarded_form at 1.
  rewrite unfold_iter.
  desobs t; cbn.
  - now rewrite bind_ret_l.
  - unfold mtrigger; rewrite bind_bind, !bind_trigger.
    step; constructor; intros ?.
    rewrite bind_ret_l.
    reflexivity.
  - destruct vis.
    + rewrite bind_choice.
      step; constructor; intros ?.
      rewrite bind_tauV; step; constructor; intros ?.
      rewrite bind_ret_l.
      step; constructor; auto.
    + rewrite bind_choice.
      step; constructor; intros ?.
      rewrite bind_ret_l.
      step; constructor; auto.
Qed.

Lemma trans_guarded_inv_strong :
  forall {E X} (t u v : ctree E X) l,
    (v ≅ guarded_form t \/ v ≅ TauI (guarded_form t)) ->
    trans l v u ->
    exists t', trans l t t'
          /\ (u ≅ guarded_form t' \/ u ≅ TauI (guarded_form t')).
Proof.
  intros * EQ TR.
  revert t EQ.
  unfold trans in TR; repeat red in TR.
  dependent induction TR.
  - intros ? [EQ | EQ].
    + rewrite ctree_eta, <- x, unfold_guarded_form in EQ.
      setoid_rewrite (ctree_eta t).
      desobs t; try now step in EQ; inv EQ.
      destruct vis.
      * pose proof equ_choice_invT _ _ EQ as [<- _].
        apply equ_choice_invE with (x := x0) in EQ .
        rewrite EQ in TR.
        apply trans_tauV_inv in TR as [EQ' ->].
        eexists; split; eauto.
        etrans.

      * pose proof equ_choice_invT _ _ EQ as [<- _].
        apply equ_choice_invE with (x := x0) in EQ .
        specialize (IHTR _ _ eq_refl eq_refl).
        edestruct IHTR as (t' & ? & ?); eauto.
        exists t'.
        split.
        eapply trans_choiceI with (x := x0); eauto.
        eauto.

    + rewrite ctree_eta, <- x in EQ.
      pose proof equ_choice_invT _ _ EQ as [-> _].
      apply equ_choice_invE with (x := x0) in EQ .
      specialize (IHTR _ _ eq_refl eq_refl).
      edestruct IHTR as (t' & ? & ?); eauto.

  - (* G(t) ≅ ChoiceV k : absurd *)
    intros ? [EQ | EQ].
    + rewrite ctree_eta, <- x1, unfold_guarded_form in EQ.
      desobs t0; try now step in EQ; inv EQ.
      destruct vis; try now step in EQ; inv EQ.
    + rewrite ctree_eta, <- x1 in EQ.
      now step in EQ; inv EQ.

  - (* G(t) ≅ Vis e k : t ≅ Vis e k', k x ≅ TauI (G (k' x)) *)
    intros ? [EQ | EQ].
    + setoid_rewrite (ctree_eta t0).
      rewrite ctree_eta, <- x1, unfold_guarded_form in EQ.
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
      rewrite ctree_eta, <- x0, unfold_guarded_form in EQ.
      desobs t; try now step in EQ; inv EQ.
      2:destruct vis; try now step in EQ; inv EQ.
      step in EQ; inv EQ.
      eexists; split.
      etrans.
      left.
      rewrite ctree_eta, <- x, unfold_guarded_form.
      cbn.
      rewrite ! choiceI0_always_stuck.
      reflexivity.
    + rewrite ctree_eta, <- x0 in EQ.
      now step in EQ; inv EQ.
Qed.

Lemma trans_guarded_inv :
  forall E X (t u : ctree E X) l,
    trans l (guarded_form t) u ->
    exists t', trans l t t'
          /\ u ~ guarded_form t'.
Proof.
  intros.
  edestruct @trans_guarded_inv_strong as (t' & TR & EQ); [|eassumption|].
  left; eauto.
  exists t'; split; auto.
  destruct EQ as [EQ |EQ]; rewrite EQ; auto.
  rewrite sb_tauI; auto.
Qed.

Ltac fold_bind :=
  repeat match goal with
           |- context [CTree.subst ?k ?t] => fold (CTree.bind t k)
         end.

#[global] Instance guarded_equ E X : Proper (equ eq ==> equ eq) (@guarded_form E X).
Proof.
  do 2 red.
  coinduction ? IH.
  intros * EQ.
  step in EQ.
  rewrite ! unfold_guarded_form.
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

(* TODO: bind simpl never globally? *)
(* TODO: Taus without continuation? *)
(* TODO: tactic for better stepping for equ *)
(* TODO: tactics for better stepping for sbisim (see a couple above) *)
(* Equality on [observe u] rewritten in [equ]? *)
Opaque CTree.bind.
Lemma trans_guarded_strong :
  forall E X (t u : ctree E X) l,
    trans l t u ->
    exists u',
      trans l (guarded_form t) u'
      /\ (u' ≅ guarded_form u
         \/ u' ≅ TauI (guarded_form u)).
Proof.
  intros * TR.
  (* revert t EQ. *)
  unfold trans in TR; repeat red in TR.
  dependent induction TR; intros.
  - (* destruct EQ as [EQ | EQ]. *)
    edestruct IHTR as (u' & TR' & EQ'); eauto.
    setoid_rewrite unfold_guarded_form at 1; rewrite <- x.
    exists u'; split.
    eapply trans_choiceI with (x := x0); [| reflexivity].
    now apply trans_tauI.
    auto.
  - setoid_rewrite unfold_guarded_form at 1; rewrite <- x1.
    eexists; split.
    eapply trans_choiceI with (x := x0); [| reflexivity].
    etrans.
    right.
    step; constructor; intros ?.
    rewrite H.
    rewrite (ctree_eta t0),x,<- ctree_eta.
    auto.
  - setoid_rewrite unfold_guarded_form at 1; rewrite <- x1.
    eexists; split.
    unfold mtrigger, MonadTrigger_ctree; cbn.
    rewrite bind_trigger.
    etrans.
    right.
    step; constructor; intros ?.
    rewrite H.
    rewrite (ctree_eta t0),x,<- ctree_eta.
    auto.
  - setoid_rewrite unfold_guarded_form at 1; rewrite <- x0.
    eexists; split.
    (*
      Why do I need to cbn even if I add:
      Hint Unfold ret Monad_ctree : trans.
     *)
    cbn; etrans.
    left.
    rewrite unfold_guarded_form, <- x; cbn.
    now rewrite ! choiceI0_always_stuck.
Qed.

Lemma trans_guarded :
  forall E X (t u : ctree E X) l,
    trans l t u ->
    exists u',
      trans l (guarded_form t) u'
      /\ u' ~ guarded_form u.
Proof.
  intros * TR.
  edestruct trans_guarded_strong as (u' & TR' & EQ'); eauto.
  exists u'; split; auto.
  destruct EQ' as [EQ' | EQ']; rewrite EQ'; auto.
  now rewrite sb_tauI.
Qed.

(* TODO: define properly the set of tactics in [sbisim] and kill this.
   TODO: this is not resilient enough, it loops if the goal is not exactly of the right shape
 *)
Ltac sret  := apply step_sb_ret.
Ltac svis  := apply step_sb_vis.
Ltac stauv := apply step_sb_tauV.
Ltac sstep := sret || svis || stauv.

Lemma guarded_is_bisimilar {E X} : forall (t : ctree E X),
    guarded_form t ~ t.
Proof.
  coinduction ? IH.
  intros t.
  rewrite (ctree_eta t) at 2.
  rewrite unfold_guarded_form.
  desobs t.
  - now cbn.
  - cbn*.
    unfold mtrigger; rewrite bind_trigger.
    sstep; intros ?.
    rewrite sb_tauI.
    apply IH.
  - destruct vis.
    + cbn.
      split; intros ? ? TR.
      * inv_trans.
        subst.
        eexists.
        eapply trans_choiceV with (x := n0).
        rewrite EQ.
        rewrite sb_tauI.
        apply IH.
      * cbn.
        inv_trans; subst.
        eexists.
        eapply trans_choiceI with (x := n0).
        2:etrans.
        etrans.
        rewrite sb_tauI.
        rewrite EQ; apply IH.
    + split.
      * intros ? ? TR.
        cbn.
        inv_trans.
        edestruct trans_guarded_inv as (u' & TR' & EQ'); eauto.
        eexists.
        eapply trans_choiceI with (x := n0); [| reflexivity].
        eassumption.
        rewrite EQ'; auto.
      * cbn; intros ? ? TR.
        inv_trans.
        edestruct trans_guarded as (u' & TR' & EQ'); eauto.
        eexists.
        eapply trans_choiceI with (x := n0); [| reflexivity].
        apply trans_tauI.
        eauto.
        rewrite EQ'; auto.
Qed.

