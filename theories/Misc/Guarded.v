From ExtLib Require Import
     Structures.Functor
     Structures.Monad.

From CTree Require Import
     CTree
     Eq
     Interp.Fold.

Import MonadNotation.
Open Scope monad_scope.

Definition guarded_form {E B X} `{B1 -< B} (t : ctree E B X) : ctree E B X :=
  CTree.iter (fun t =>
				        match observe t with
				        | RetF r => ret (inr r)
				        | BrDF n k => BrD n (fun x => ret (inl (k x)))
				        | BrSF n k => BrD n (fun x => Step (ret (inl (k x))))
				        | VisF e k => bind (mtrigger e) (fun x => ret (inl (k x)))
				        end) t.

(* TODO move *)
Arguments MonadTrigger_ctree /.

Lemma unfold_guarded_form {E B X} `{B1 -< B} (t : ctree E B X) :
  guarded_form t ≅
  match observe t with
	| RetF r => ret r
  | BrDF n k =>
      BrD n (fun x => Guard (guarded_form (k x)))
	| BrSF n k =>
      BrD n (fun x => Step (Guard (guarded_form (k x))))
	| VisF e k => bind (mtrigger e) (fun x => Guard (guarded_form (k x)))
	end.
Proof.
  unfold guarded_form at 1.
  rewrite unfold_iter.
  desobs t; cbn.
  - now rewrite bind_ret_l.
  - unfold mtrigger; cbn.
    rewrite bind_bind, !bind_trigger.
    step; constructor; intros ?.
    rewrite bind_ret_l.
    reflexivity.
  - destruct vis.
    + rewrite bind_br.
      step; constructor; intros ?.
      rewrite bind_step; step; constructor; intros ?.
      rewrite bind_ret_l.
      step; constructor; auto.
    + rewrite bind_br.
      step; constructor; intros ?.
      rewrite bind_ret_l.
      step; constructor; auto.
Qed.

Lemma trans_guarded_inv_strong :
  forall {E B X} `{HasStuck : B0 -< B} `{HasTau : B1 -< B} (t u v : ctree E B X) l,
    (v ≅ guarded_form t \/ v ≅ Guard (guarded_form t)) ->
    trans l v u ->
    exists t', trans l t t'
          /\ (u ≅ guarded_form t' \/ u ≅ Guard (guarded_form t')).
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
      * inv_equ. rewrite EQ0 in TR.
        apply trans_step_inv in TR as [EQ' ->].
        eexists; split; eauto.
        etrans.
      * inv_equ.
        specialize (IHTR _ _ eq_refl eq_refl).
        edestruct IHTR as (t' & ? & ?); eauto.
        exists t'.
        split.
        eapply trans_brD with (x := x0); eauto.
        eauto.

    + rewrite ctree_eta, <- x in EQ.
      inv_equ.
      specialize (IHTR _ _ eq_refl eq_refl).
      edestruct IHTR as (t' & ? & ?); eauto.

  - (* G(t) ≅ BrS k : absurd *)
    intros ? [EQ | EQ].
    + rewrite ctree_eta, <- x1, unfold_guarded_form in EQ.
      desobs t0; try now step in EQ; inv EQ.
      destruct vis; try now step in EQ; inv EQ.
    + rewrite ctree_eta, <- x1 in EQ.
      now step in EQ; inv EQ.

  - (* G(t) ≅ Vis e k : t ≅ Vis e k', k x ≅ Guard (G (k' x)) *)
    intros ? [EQ | EQ].
    + setoid_rewrite (ctree_eta t0).
      rewrite ctree_eta, <- x1, unfold_guarded_form in EQ.
      rewrite (ctree_eta t), x in H.
      clear t x.
      desobs t0; try now step in EQ; inv EQ.
      2:destruct vis; try now step in EQ; inv EQ.
      cbn in *.
      unfold mtrigger in EQ; rewrite bind_trigger in EQ.
      inv_equ.
      eexists; split.
      etrans.
      rewrite <- ctree_eta in H.
      rewrite <- H.
      rewrite EQ0.
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
      rewrite ! brD0_always_stuck.
      reflexivity.
    + rewrite ctree_eta, <- x0 in EQ.
      now step in EQ; inv EQ.
Qed.

Lemma trans_guarded_inv :
  forall E B X `(B0 -< B) `(B1 -< B) (t u : ctree E B X) l,
    trans l (guarded_form t) u ->
    exists t', trans l t t'
          /\ u ~ guarded_form t'.
Proof.
  intros.
  edestruct @trans_guarded_inv_strong as (t' & TR & EQ); [|eassumption|].
  left; eauto.
  exists t'; split; auto.
  destruct EQ as [EQ |EQ]; rewrite EQ; auto.
  rewrite sb_guard; auto.
Qed.

#[global] Instance guarded_equ E B X `(B1 -< B) : Proper (equ eq ==> equ eq) (@guarded_form E B X _).
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
    fold_subst; rewrite ! bind_ret_l.
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
  forall E B X `(HasStuck : B0 -< B) `(HasTau : B1 -< B) (t u : ctree E B X) l,
    trans l t u ->
    exists u',
      trans l (guarded_form t) u'
      /\ (u' ≅ guarded_form u
         \/ u' ≅ Guard (guarded_form u)).
Proof.
  intros * TR.
  (* revert t EQ. *)
  unfold trans in TR; repeat red in TR.
  dependent induction TR; intros.
  - (* destruct EQ as [EQ | EQ]. *)
    edestruct IHTR as (u' & TR' & EQ'); eauto.
    setoid_rewrite unfold_guarded_form at 1; rewrite <- x.
    exists u'; split.
    eapply trans_brD with (x := x0); [| reflexivity].
    now apply trans_guard.
    auto.
  - setoid_rewrite unfold_guarded_form at 1; rewrite <- x1.
    eexists; split.
    eapply trans_brD with (x := x0); [| reflexivity].
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
    now rewrite ! brD0_always_stuck.
Qed.

Lemma trans_guarded :
  forall E B X `(B0 -< B) `(B1 -< B) (t u : ctree E B X) l,
    trans l t u ->
    exists u',
      trans l (guarded_form t) u'
      /\ u' ~ guarded_form u.
Proof.
  intros * TR.
  edestruct trans_guarded_strong as (u' & TR' & EQ'); eauto.
  exists u'; split; eauto.
  destruct EQ' as [EQ' | EQ']; rewrite EQ'; auto.
  now rewrite sb_guard.
Qed.

(* TODO: define properly the set of tactics in [sbisim] and kill this.
   TODO: this is not resilient enough, it loops if the goal is not exactly of the right shape
 *)
Ltac sret  := apply step_sb_ret.
Ltac svis  := apply step_sb_vis_id || apply step_sb_vis.
Ltac sStep := apply step_sb_step.
Ltac sstep := sret || svis || sStep.

Lemma guarded_is_bisimilar {E B X} `{B0 -< B} `{B1 -< B} : forall (t : ctree E B X),
    guarded_form t ~ t.
Proof.
  coinduction ? IH.
  intros t.
  rewrite (ctree_eta t) at 2.
  rewrite unfold_guarded_form.
  desobs t.
  - now cbn.
  - cbn.
    unfold mtrigger; rewrite bind_trigger.
    svis; intros ?.
    rewrite sb_guard.
    apply IH.
    reflexivity.
  - destruct vis.
    + cbn.
      split; intros ? ? TR.
      * inv_trans.
        subst.
        do 2 eexists.
        split; [etrans |].
        split; [| reflexivity].
        rewrite EQ.
        rewrite sb_guard.
        apply IH.
      * cbn.
        inv_trans; subst.
        do 2 eexists.
        split; [etrans |].
        split; [| reflexivity ].
        rewrite sb_guard.
        rewrite EQ; apply IH.
    + split.
      * intros ? ? TR.
        cbn.
        inv_trans.
        edestruct trans_guarded_inv as (u' & TR' & EQ'); eauto.
        do 2 eexists.
        split; [etrans |].
        split; [| reflexivity].
        rewrite EQ'; auto.
      * cbn; intros ? ? TR.
        inv_trans.
        edestruct trans_guarded as (u' & TR' & EQ'); eauto.
        do 2 eexists.
        split; [etrans |].
        split; [| reflexivity].
        rewrite EQ'; auto.
Qed.
