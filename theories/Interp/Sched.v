From ExtLib Require Import
     Structures.Functor
     Structures.Monad.

From CTree Require Import
     Eq.

Import ITree.Basics.Basics.Monads.
Import MonadNotation.
Open Scope monad_scope.

#[global] Instance ctree_trigger {E} : MonadTrigger E (ctree E) :=
  @CTree.trigger _.

#[global] Instance stateT_trigger {E S M} {MM : Monad M} {MT: MonadTrigger E M} :
  MonadTrigger E (stateT S M) :=
  fun _ e s => v <- mtrigger _ e;; ret (s, v).

Definition schedule {E M : Type -> Type}
					 {FM : Functor M} {MM : Monad M} {IM : MonadIter M} {FoM : MonadTrigger E M}
					 (h : forall n, M (fin n)) :
	ctree E ~> M :=
  fun R =>
		iter (fun t =>
				    match observe t with
				    | RetF r => ret (inr r)
				    | @ChoiceF _ _ _ _ n k => bind (h n) (fun x => ret (inl (k x)))
				    | VisF e k => bind (mtrigger _ e) (fun x => ret (inl (k x)))
				    end).

Definition schedule_cst {E} (h : forall n, fin n) : ctree E ~> ctree E :=
  schedule (fun n => Ret (h n)).

Definition round_robin {E} : ctree E ~> stateT nat (ctree E).
  refine (schedule
            (fun n m =>
               (* m: branch to be scheduled
                  n: arity of the new node
                *)
               match n as n' return (ctree E (nat * fin n')) with
               | O => CTree.stuckI
               | 1 => Ret (m, Fin.F1)
               | S (S n) => (Ret (S m, @Fin.of_nat_lt (Nat.modulo m (S (S n))) _ _))
               end
         )).
  apply (NPeano.Nat.mod_upper_bound).
  auto with arith.
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

Definition guarded_form {E X} (t : ctree E X) : ctree E X :=
	CTree.iter (fun t =>
				        match observe t with
				        | RetF r => ret (inr r)
				        | ChoiceIF n k =>
                    ChoiceI n (fun x => Ret (inl (k x)))
				        | ChoiceVF n k =>
                    ChoiceI n (fun x => TauV (Ret (inl (k x))))
				        | VisF e k => bind (mtrigger _ e) (fun x => Ret (inl (k x)))
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

(* TODO: export globally? *)
From RelationAlgebra Require Import
     rel srel.

(* TODO: think about all this stuff and move it *)
Lemma step_sbisim_vis_gen {E X Y} (e : E X) (k k' : X -> ctree E Y) (R : rel _ _) :
  (Proper (equ eq ==> equ eq ==> Basics.impl) R) ->
  (forall x, R (k x) (k' x)) ->
  sb R (Vis e k) (Vis e k').
Proof.
  intros PR EQs.
  split; intros ? ? TR; inv_trans; subst.
  all: cbn; eexists; etrans; rewrite EQ; auto.
Qed.

Lemma step_sbisim_vis {E X Y} (e : E X) (k k' : X -> ctree E Y) (R : rel _ _) :
  (forall x, (st R) (k x) (k' x)) ->
  sb (st R) (Vis e k) (Vis e k').
Proof.
  apply step_sbisim_vis_gen.
  typeclasses eauto.
Qed.

Lemma step_sbisim_tauV_gen {E X} (t t' : ctree E X) (R : rel _ _) :
  (Proper (equ eq ==> equ eq ==> Basics.impl) R) ->
  (R t t') ->
  sb R (TauV t) (TauV t').
Proof.
  intros PR EQs.
  split; intros ? ? TR; inv_trans; subst.
  all: cbn; eexists; etrans; rewrite EQ; auto.
Qed.

Lemma step_sbisim_tauV {E X} (t t' : ctree E X) (R : rel _ _) :
  (st R t t') ->
  sb (st R) (TauV t) (TauV t').
Proof.
  apply step_sbisim_tauV_gen.
  typeclasses eauto.
Qed.

Ltac svis  := apply step_sbisim_vis.
Ltac stauv := apply step_sbisim_tauV.
Ltac sstep := svis || stauv.

Lemma step_sbisim_choiceI_gen {E X} n m (k : fin n -> ctree E X) (k' : fin m -> ctree E X) (R : rel _ _) :
  (forall x, exists y, sb R (k x) (k' y)) ->
  (forall y, exists x, sb R (k x) (k' y)) ->
  sb R (ChoiceI n k) (ChoiceI m k').
Proof.
  intros EQs1 EQs2.
  split; intros ? ? TR; inv_trans; subst.
  - destruct (EQs1 n0) as [x [F _]]; cbn in F.
    apply F in TR; destruct TR as [u' TR' EQ'].
    eexists.
    eapply trans_choiceI with (x := x); [|reflexivity].
    eauto.
    eauto.
  - destruct (EQs2 m0) as [x [_ B]]; cbn in B.
    apply B in TR; destruct TR as [u' TR' EQ'].
    eexists.
    eapply trans_choiceI with (x := x); [|reflexivity].
    eauto.
    eauto.
Qed.

Lemma step_sbisim_choiceI_id {E X} n (k k' : fin n -> ctree E X) (R : rel _ _) :
  (forall x, sb R (k x) (k' x)) ->
  sb R (ChoiceI n k) (ChoiceI n k').
Proof.
  intros; apply step_sbisim_choiceI_gen.
  intros x; exists x; apply H.
  intros x; exists x; apply H.
Qed.

Lemma step_sbisim_choiceI_id' {E X} n (k k' : fin n -> ctree E X)  :
  (forall x, (k x) ~ (k' x)) ->
  (ChoiceI n k) ~ (ChoiceI n k').
Proof.
  intros.
  step.
  eapply step_sbisim_choiceI_id.
  intros.
  specialize (H x).
  now step in H.
Qed.

Lemma foo {E X} l (t t' u : ctree E X):
  t ~ t' ->
  trans l t u ->
  exists u', trans l t' u' /\ u ~ u'.
Proof.
  intros * EQ TR.
  step in EQ; destruct EQ as [F _]; apply F in TR; destruct TR; eauto.
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
  cbn.
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

Lemma guarded_is_bisimilar {E X} : forall (t : ctree E X),
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

