From ExtLib Require Import
     Structures.Functor
     Structures.Monad.

From CTree Require Import
     Eq
     Eq.Epsilon
     Eq.SSimAlt
     Interp.Fold
     Interp.FoldCTree
     Interp.FoldStateT.

Import ITree.Basics.Basics.Monads.
Import MonadNotation.
Open Scope monad_scope.

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

End pure.

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

Lemma pure_pure_finite {E C X} :
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

Definition refine' {E C M : Type -> Type}
           {FM : Functor M} {MM : Monad M}
           {IM : MonadIter M} {FoM : MonadTrigger E M}
           {CM : MonadBr void1 M}
           (h : C ~> M) :
  ctree E (B01 +' C) ~> M :=
  refine (fun b X (c: (B01 +' C) X) =>
    match c, X return M X with
    | inl1 c, X => mbr b (inl1 c)
    | inr1 c, X => r <- h X c;; mbr b (inl1 (inr1 branch1));; ret r
    end).

Definition refine'_state {E C D St} (f : C ~> stateT St (ctree E (B01 +' D))) :
  ctree E (B01 +' C) ~> stateT St (ctree E (B01 +' D)) :=
  refine' (CM := MonadBr_stateT) f.

Import SSim'Notations.

Theorem ssim_pure {E F B C X} `{HasB0: B0 -< B} `{HasB0': B0 -< C} : forall (L : rel _ _) (t : ctree E B X),
  pure_finite t ->
  (forall x : X, L (val x) (val tt)) ->
  ssim L t (Ret tt : ctree F C unit).
Proof.
  intros. induction H.
  - subs. now apply ssim_ret.
  - subs. now apply ssim_brD_l.
Qed.

Unset Universe Checking.

Theorem refine_ctree_ssim {E B B' X} :
  forall (t : ctree E (B01 +' B) X) (h : B ~> ctree E (B01 +' B')),
  (forall X c, pure_finite (h X c)) ->
  refine' h _ t ≲ t.
Proof.
  intros. rewrite ssim_ssim'. red. revert t. coinduction R CH. intros.
  rewrite (ctree_eta t) at 2.
  setoid_rewrite unfold_refine. cbn.
  destruct (observe t) eqn:?.
  - apply step_ssbt'_ret. reflexivity.
  - setoid_rewrite bind_trigger.
    apply step_ss'_vis_id. intros. split; [|auto].
    step. apply step_ss'_guard_l. apply CH.
  - unfold mbr, MonadBr_ctree. destruct c.
    + setoid_rewrite bind_branch.
      apply step_ssbt'_br_id; auto. intros.
      step. apply step_ss'_guard_l. apply CH.
    + rewrite bind_bind.
      change (Br vis (inr1 b) k) with ((fun _ => Br vis (inr1 b) k) tt).
      setoid_rewrite <- bind_ret_l at 10.
      __upto_bind_ssim' (fun _ _ => True).
      { apply ssim_pure. apply H. intros. now constructor. }
      red. intros ? _ _. rewrite bind_bind, bind_branch.
      apply step_ssbt'_br; auto. intros _. exists x.
      rewrite bind_ret_l. step. apply step_ss'_guard_l. apply CH.
Qed.

Definition Rrr {St X} (p : St * X) (x : X) := snd p = x.
Definition Lrr {St E X} := @lift_val_rel E _ X (@Rrr St X).

Theorem refine_state_ssim {E B B' X St} :
  forall (t : ctree E (B01 +' B) X) (h : B ~> stateT St (ctree E (B01 +' B'))),
  (forall X c s, pure_finite (h X c s)) ->
  forall s, refine' h _ t s (≲@Lrr St E X) t.
Proof.
  intros. rewrite ssim_ssim'. red. revert t s. coinduction R CH. intros.
  rewrite (ctree_eta t) at 2.
  setoid_rewrite unfold_fold_state. cbn.
  destruct (observe t) eqn:?.
  - apply step_ssbt'_ret. constructor. reflexivity.
  - setoid_rewrite bind_trigger.
    rewrite bind_vis. apply step_ss'_vis_id. intros. split; [| constructor; etrans].
    step. rewrite bind_ret_l. apply step_ss'_guard_l. apply CH.
  - unfold mbr, MonadBr_ctree. destruct c.
    + setoid_rewrite bind_branch. setoid_rewrite bind_br.
      apply step_ssbt'_br_id; [| constructor; etrans]. intros.
      step. setoid_rewrite bind_ret_l. apply step_ss'_guard_l. apply CH.
    + rewrite bind_bind.
      change (Br vis (inr1 b) k) with ((fun _ => Br vis (inr1 b) k) tt).
      setoid_rewrite <- bind_ret_l at 12.
      __upto_bind_ssim' (fun _ _ => True).
      { apply ssim_pure. apply H. intros. now constructor. }
      red. intros ? _ _. rewrite bind_bind, bind_branch, bind_br.
      apply step_ssbt'_br; [| constructor; etrans]. intros ?. exists (snd x).
      rewrite bind_ret_l. step. rewrite bind_ret_l. apply step_ss'_guard_l. apply CH.
Qed.
