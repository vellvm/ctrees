From ExtLib Require Import
     Structures.Functor
     Structures.Monad.

From CTree Require Import
     Eq
     Eq.Epsilon
     Eq.SSimAlt
     Interp.Fold
     Interp.FoldCTree
     Interp.FoldStateT
     Misc.Pure.

Import ITree.Basics.Basics.Monads.
Import MonadNotation.
Open Scope monad_scope.

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
