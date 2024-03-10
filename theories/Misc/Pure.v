From CTree Require Import
     Eq Eq.Epsilon.

Variant pureb {E C X} (rec : ctree E C X -> Prop) (t : ctree E C X) : Prop :=
  | pureb_ret   (v : X) (EQ : t ≅ Ret v) : pureb rec t
  | pureb_delay {Y} (c: C Y) k (EQ : t ≅ BrD c k) (REC: forall v, rec (k v)) : pureb rec t.

Program Definition fpure {E C R} : mon (ctree E C R -> Prop) := {|body := pureb|}.
Next Obligation.
  inversion_clear H0; [eleft | eright]; eauto.
Qed.

Section pure.

  Context {E C : Type -> Type} {X : Type}.

  Class pure (t : ctree E C X) := pure_ : gfp (@fpure E C X) t.

  #[global] Instance pure_equ : Proper (@equ E C X X eq ==> flip impl) pure.
  Proof.
    cbn. intros. step in H0. inversion H0.
    - step. eleft. now rewrite H, EQ.
    - step. eright. now rewrite H, EQ. apply REC.
  Qed.

  #[global] Instance pure_ret r : pure (Ret r).
  Proof.
    step. now eleft.
  Qed.

  #[global] Instance pure_br {T} (c : C T) k :
    (forall x, pure (k x)) ->
    pure (BrD c k).
  Proof.
    intros. step. now eright.
  Qed.

  #[global] Instance pure_guard `{B1 -< C} t :
    pure t ->
    pure (Guard t).
  Proof.
    intros. unfold Guard. step. now eright.
  Qed.

  #[global] Instance pure_stuck `{B0 -< C} :
    pure stuckD.
  Proof.
    unfold stuckD. step. now eright.
  Qed.

  Lemma pure_brD_inv : forall {X} (c : C X) k x,
    pure (BrD c k) ->
    pure (k x).
  Proof.
    intros. step in H. inv H; inv_equ.
    rewrite EQ0. apply REC.
  Qed.

  Lemma pure_productive : forall (t : ctree E C X),
    pure t -> productive t -> exists r, t ≅ Ret r.
  Proof.
    intros. step in H. inv H; eauto.
    rewrite EQ in H0. inv H0; inv_equ.
  Qed.

  Lemma pure_epsilon :
    forall t t', pure t -> epsilon t t' -> pure t'.
  Proof.
    intros. rewrite ctree_eta in H. rewrite ctree_eta. red in H0. genobs t ot. genobs t' ot'.
    clear t t' Heqot Heqot'. induction H0.
    - now subs.
    - apply IHepsilon_. rewrite <- ctree_eta. eapply pure_brD_inv. apply H.
  Qed.

  Lemma trans_pure_is_val `{B0 -< C} (t t' : ctree E C X) l :
    pure t ->
    trans l t t' ->
    is_val l.
  Proof.
    intros. do 3 red in H1. genobs t ot. genobs t' ot'.
    assert (t ≅ go ot). { now rewrite Heqot, <- ctree_eta. } clear Heqot.
    revert t H0 H2. induction H1; intros; subst.
    - apply IHtrans_ with (t := k x); auto. 2: apply ctree_eta.
      rewrite H2 in H0. step in H0. inversion H0; inv_equ.
      rewrite EQ0. apply REC.
    - rewrite H2 in H1. step in H1. inversion H1; inv_equ.
    - rewrite H2 in H1. step in H1. inversion H1; inv_equ.
    - constructor.
  Qed.

  Lemma trans_bind_pure {Y} `{B0 -< C} (t : ctree E C X) k (u : ctree E C Y) l :
    pure t ->
    trans l (CTree.bind t k) u ->
    exists v, trans (val v) t stuckD /\ trans l (k v) u.
  Proof.
    intros. apply trans_bind_inv in H1 as [(? & ? & ? & ?) |].
    - now apply trans_pure_is_val in H2.
    - apply H1.
  Qed.

End pure.

#[global] Instance pure_map {E B X Y} : forall (t : ctree E B X) (f : X -> Y),
  pure t ->
  pure (CTree.map f t).
Proof.
  red. coinduction R CH. intros.
  step in H. destruct H.
  - eleft. rewrite EQ. rewrite map_ret. reflexivity.
  - eright.
    + rewrite EQ. unfold CTree.map. rewrite bind_br. reflexivity.
    + intros. apply CH. apply REC.
Qed.

Section pure_finite.

  Context {E C : Type -> Type} {X : Type}.

  Inductive pure_finite_ : ctree E C X -> Prop :=
    | puref_ret (v : X) t (EQ: t ≅ Ret v) : pure_finite_ t
    | puref_delay {Y} (c: C Y) (k : Y -> ctree E C X) t (EQ: t ≅ BrD c k) (REC: forall v, pure_finite_ (k v)) : pure_finite_ t.

  Class pure_finite (t : ctree E C X) : Prop :=
    pure_finite__ : pure_finite_ t.

  #[global] Instance pure_finite_equ :
    Proper (equ eq ==> flip impl) pure_finite.
  Proof.
    cbn. intros. revert x H. induction H0; intros.
    - eleft. now subs.
    - eright. now subs.
      intro. now eapply H.
  Qed.

  #[global] Instance pure_finite_ret r : pure_finite (Ret r).
  Proof.
    now eleft.
  Qed.

  #[global] Instance pure_finite_br {T} (c : C T) k :
    (forall x, pure_finite (k x)) ->
    pure_finite (BrD c k).
  Proof.
    now eright.
  Qed.

  #[global] Instance pure_finite_guard `{B1 -< C} t :
    pure_finite t ->
    pure_finite (Guard t).
  Proof.
    unfold Guard. now eright.
  Qed.

  #[global] Instance pure_finite_stuck `{B0 -< C} :
    pure_finite stuckD.
  Proof.
    unfold stuckD. now eright.
  Qed.

End pure_finite.

Lemma pure_finite_bind_R {E C X Y} :
  forall R t (k : X -> ctree E C Y),
  t (≅R) t ->
  pure_finite t ->
  (forall x, R x x -> pure_finite (k x)) ->
  pure_finite (CTree.bind t k).
Proof.
  intros. induction H0.
  - subs. inv_equ. rewrite bind_ret_l; auto.
  - subs. inv_equ. rewrite bind_br. apply pure_finite_br. auto.
Qed.

#[global] Instance pure_finite_bind {E C X Y} :
  forall t (k : X -> ctree E C Y),
  pure_finite t ->
  (forall x, pure_finite (k x)) ->
  pure_finite (CTree.bind t k).
Proof.
  intros. apply (pure_finite_bind_R eq); auto.
Qed.

#[global] Instance pure_pure_finite {E C X} :
  forall (t : ctree E C X),
  pure_finite t ->
  pure t.
Proof.
  intros. induction H; subs; step.
  - now eleft.
  - now eright.
Qed.

Lemma is_stuck_pure : forall {E B X Y} `{B0 -< B} t (k : X -> ctree E B Y),
  pure t ->
  (forall x, is_stuck (k x)) ->
  is_stuck (CTree.bind t k).
Proof.
  red. intros. intro.
  apply trans_bind_inv in H2 as [].
  - destruct H2 as (? & ? & ? & ?). subs.
    apply H2. eapply trans_pure_is_val; eauto.
  - destruct H2 as (? & ? & ?). now apply H1 in H3.
Qed.

(*|
A computation [is_simple] all its transitions are either:
- directly returning
- or reducing in one step to something of the shape [Guard* (Ret r)]
|*)
Class is_simple {E C X} (t : ctree E (B01 +' C) X) :=
  is_simple' : (forall l t', trans l t t' -> is_val l) \/
  (forall l t', trans l t t' -> exists r, epsilon_det t' (Ret r)).


Section is_simple_theory.

  Context {E C : Type -> Type} {X : Type}.

  #[global] Instance is_simple_equ :
    Proper (equ eq ==> iff) (@is_simple E C X).
  Proof.
    cbn. intros. unfold is_simple. setoid_rewrite H. reflexivity.
  Qed.

  #[global] Instance is_simple_ret : forall r, is_simple (Ret r : ctree E (B01 +' C) X).
  Proof.
    cbn. red. intros. left. intros. inv_trans. subst. constructor.
  Qed.

  #[global] Instance is_simple_guard_ret : forall r,
      is_simple (Guard (Ret r) : ctree E (B01 +' C) X).
  Proof.
    cbn. red. intros. left. intros. inv_trans. subst. constructor.
  Qed.

  #[global] Instance is_simple_br : forall (c: (B01 +' C) X),
      is_simple (branchD c : ctree E (B01 +' C) X).
  Proof.
    cbn. red. intros.
    left. intros. apply trans_brD_inv in H as []. inv_trans. subst. constructor.
  Qed.

  #[global] Instance is_simple_map :
    forall {Y} (t : ctree E (B01 +' C) X) (f : X -> Y),
    is_simple t -> is_simple (CTree.map f t).
  Proof.
    intros. destruct H.
    - left. intros.
      unfold CTree.map in H0. apply trans_bind_inv in H0 as ?.
      destruct H1 as [(? & ? & ? & ?) | (? & ? & ?)].
      + now apply H in H2.
      + apply trans_ret_inv in H2 as []. now subst.
    - right. intros.
      apply trans_bind_inv in H0 as ?.
      destruct H1 as [(? & ? & ? & ?) | (? & ? & ?)].
      + apply H in H2 as []. exists (f x0). subs.
        eapply Epsilon.epsilon_det_bind_ret_l. apply H2. reflexivity.
      + apply H in H1 as []. inv H1; inv_equ.
  Qed.

  #[global] Instance is_simple_liftState {St} :
    forall (t : ctree E (B01 +' C) X) (s : St),
    is_simple t -> is_simple (Monads.liftState t s).
  Proof.
    intros. cbn. typeclasses eauto.
  Qed.

  #[global] Instance is_simple_trigger :
    forall (e : E X),
    is_simple (CTree.trigger e : ctree E (B01 +' C) X).
  Proof.
    right. intros.
    unfold CTree.trigger in H. inv_trans. subst.
    exists x. now left.
  Qed.

  Lemma is_simple_brD : forall {Y} (c: (B01 +' C) X) (k : X -> ctree E (B01 +' C) Y) x,
      is_simple (BrD c k) -> is_simple (k x).
  Proof.
    intros. destruct H.
    - left. intros. eapply H. etrans.
    - right. intros. eapply H. etrans.
  Qed.

  #[global] Instance is_simple_pure :
    forall (t : ctree E (B01 +' C) X),
    pure t -> is_simple t.
  Proof.
    left. intros. eapply trans_pure_is_val; eassumption.
  Qed.

End is_simple_theory.
