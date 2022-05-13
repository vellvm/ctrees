From ExtLib Require Import
     Structures.Functor
     Structures.Monad.

From CTree Require Import
     Eq
     Interp.Interp.

Import ITree.Basics.Basics.Monads.
Import MonadNotation.
Open Scope monad_scope.

#[global] Instance ctree_trigger {E C} : MonadTrigger E (ctree E C) :=
  @CTree.trigger _ _.

#[global] Instance stateT_trigger {E S M} {MM : Monad M} {MT: MonadTrigger E M} :
  MonadTrigger E (stateT S M) :=
  fun _ e s => v <- mtrigger _ e;; ret (s, v).

Definition schedule {E C M : Type -> Type}
           {FM : Functor M} {MM : Monad M} {IM : MonadIter M} {FoM : MonadTrigger E M} (h : bool -> C ~> M) :
	ctree E C ~> M :=
  interp mtrigger h.
(*fun R =>
		iter (fun t =>
				    match observe t with
				    | RetF r => ret (inr r)
				    | @ChoiceF _ _ _ _ _ _ c k => bind (h c) (fun x => ret (inl (k x)))
				    | VisF e k => bind (mtrigger _ e) (fun x => ret (inl (k x)))
   end).*)

Definition schedule_cst {E C} `{C1 -< C} (h : bool -> C ~> ctree void1 C) : ctree E C ~> ctree E C :=
  schedule (fun b _ c => translate (fun _ (e : void1 _) => match e with end) (h b _ c)).

Program Definition round_robin {E} : ctree E (C01 +' Cn) ~> stateT nat (ctree E (C01 +' Cn)) :=
  schedule (
    fun (b : bool) T c s =>
      match c with
      | inr1 c => _
      | _ => r <- choice b c;; ret (s, r)
      end).
Next Obligation.
  destruct c. destruct n.
  - apply stuckI.
  - apply ret. split. apply (S n).
    eapply (@Fin.of_nat_lt (Nat.modulo s (S n))).
    apply NPeano.Nat.mod_upper_bound. auto with arith.
Defined.

(* TODO:
Can we do something with a stream?
One round robin per arity?
Random scheduler on the OCaml side?
Fairness? Too low level here I think? Maybe at the level of Imp.
Prove that the original computation simulates the scheduled one?
*)


(* TODO: move, use globally? *)
Notation ChoiceVF := (ChoiceF true).
Notation ChoiceIF := (ChoiceF false).

Definition guarded_form {E C X} `{C1 -< C} (t : ctree E C X) : ctree E C X :=
	CTree.iter (fun t =>
				        match observe t with
				        | RetF r => ret (inr r)
				        | ChoiceIF c k =>
                    ChoiceI c (fun x => Ret (inl (k x)))
				        | ChoiceVF c k =>
                    ChoiceI c (fun x => tauV (Ret (inl (k x))))
				        | VisF e k => bind (mtrigger _ e) (fun x => Ret (inl (k x)))
				        end) t.

Lemma unfold_guarded_form {E C X} `{C1 -< C} (t : ctree E C X) :
  guarded_form t ≅
  match observe t with
	| RetF r => ret r
	| ChoiceIF c k =>
      ChoiceI c (fun x => tauI (guarded_form (k x)))
	| ChoiceVF c k =>
      ChoiceI c (fun x => tauV (tauI (guarded_form (k x))))
	| VisF e k => bind (mtrigger _ e) (fun x => tauI (guarded_form (k x)))
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

Lemma foo {E C X} `{C0 -< C} l (t t' u : ctree E C X):
  t ~ t' ->
  trans l t u ->
  exists u', trans l t' u' /\ u ~ u'.
Proof.
  intros * EQ TR.
  step in EQ; destruct EQ as [F _]; apply F in TR; destruct TR; eauto.
Qed.

Lemma trans_guarded_inv_strong :
  forall {E C X} `{HasStuck : C0 -< C} `{HasTau : C1 -< C} (t u v : ctree E C X) l,
    (v ≅ guarded_form t \/ v ≅ tauI (guarded_form t)) ->
    trans l v u ->
    exists t', trans l t t'
          /\ (u ≅ guarded_form t' \/ u ≅ tauI (guarded_form t')).
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
      * pose proof equ_choice_invT _ _ _ _ EQ as [<- _].
        apply equ_choice_invE with (x := x0) in EQ .
        rewrite EQ in TR.
        apply trans_tauV_inv in TR as [EQ' ->].
        eexists; split; eauto.
        etrans.

      * pose proof equ_choice_invT _ _ _ _ EQ as [<- _].
        apply equ_choice_invE with (x := x0) in EQ .
        specialize (IHTR _ _ eq_refl eq_refl).
        edestruct IHTR as (t' & ? & ?); eauto.
        exists t'.
        split.
        eapply trans_choiceI with (x := x0); eauto.
        eauto.

    + rewrite ctree_eta, <- x in EQ.
      pose proof equ_choice_invT _ _ _ _ EQ as [-> _].
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
      rewrite subevent_subevent.
      rewrite ! choiceStuckI_always_stuck.
      reflexivity.
    + rewrite ctree_eta, <- x0 in EQ.
      now step in EQ; inv EQ.
Qed.

Lemma trans_guarded_inv :
  forall E C X `(C0 -< C) `(C1 -< C) (t u : ctree E C X) l,
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

#[global] Instance guarded_equ E C X `(C1 -< C) : Proper (equ eq ==> equ eq) (@guarded_form E C X _).
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
  forall E C X `(HasStuck : C0 -< C) `(HasTau : C1 -< C) (t u : ctree E C X) l,
    trans l t u ->
    exists u',
      trans l (guarded_form t) u'
      /\ (u' ≅ guarded_form u
         \/ u' ≅ tauI (guarded_form u)).
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
    unfold mtrigger, ctree_trigger; cbn.
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
    rewrite subevent_subevent.
    now rewrite ! choiceStuckI_always_stuck.
Qed.

Lemma trans_guarded :
  forall E C X `(C0 -< C) `(C1 -< C) (t u : ctree E C X) l,
    trans l t u ->
    exists u',
      trans l (guarded_form t) u'
      /\ u' ~ guarded_form u.
Proof.
  intros * TR.
  edestruct trans_guarded_strong as (u' & TR' & EQ'); eauto.
  exists u'; split; eauto.
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

Lemma guarded_is_bisimilar {E C X} `{C0 -< C} `{C1 -< C} : forall (t : ctree E C X),
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
    rewrite sb_tauI.
    apply IH.
  - destruct vis.
    + cbn.
      split; intros ? ? TR.
      * inv_trans.
        subst.
        eexists.
        eapply trans_choiceV with (x := c0).
        rewrite EQ.
        rewrite sb_tauI.
        apply IH.
      * cbn.
        inv_trans; subst.
        eexists.
        eapply trans_choiceI with (x := x).
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
        eapply trans_choiceI with (x := c0); [| reflexivity].
        eassumption.
        rewrite EQ'; auto.
      * cbn; intros ? ? TR.
        inv_trans.
        edestruct trans_guarded as (u' & TR' & EQ'); eauto.
        eexists.
        eapply trans_choiceI with (x := c0); [| reflexivity].
        apply trans_tauI.
        eauto.
        rewrite EQ'; auto.
Qed.

