Unset Universe Checking.

From ExtLib Require Import
     Structures.Functor
     Structures.Monad.

Unset Universe Checking.
From CTree Require Import
     Eq
     Eq.Epsilon
     Eq.SSimAlt
     Eq.OldAltEquiv.TransEquiv
     Eq.OldAltEquiv.SSimEquiv
     Interp.Fold
     Interp.FoldCTree
     Interp.FoldStateT.

Import ITree.Basics.Basics.Monads.
Import MonadNotation.
Open Scope monad_scope.

Unset Universe Checking.

Theorem refine_ctree_ssim {E B B' X} :
  forall (t : ctree E B X) (h : B ~> ctree E B'),
  (forall Z c, h Z c ≲ (branch c : ctree E B Z)) ->
  refine h t ≲ t.
Proof.
  intros. unfold ssimT. rewrite ssim_ssim'. revert t. coinduction R CH. intros.
  rewrite (ctree_eta t) at 2.
  setoid_rewrite unfold_refine. cbn.
  destruct (observe t) eqn:?.
  - apply step_ssbt'_ret. apply TransAlt.reflL. discriminate.
  - apply step_ss'_stuck.
  - apply step_ss'_step.
    + apply TransAlt.reflL. discriminate.
    + apply (b_chain R). now apply step_ss'_guard_l.
  - now apply step_ss'_guard.
  - setoid_rewrite bind_trigger.
    apply step_ss'_vis_id.
    + apply (b_chain R). apply step_ss'_passive_id; intros.
      * now apply (b_chain R), step_ss'_guard_l.
      * apply TransAlt.reflL. discriminate.
    + apply TransAlt.reflL. discriminate.
  - rewrite <- bind_branch.
    refine (sbind_chain_gen (R := chain_b R) (lift_L Leq) (TransAlt.Active (h X0 c)) (TransAlt.Active (branch c))
              (fun x => Guard (refine h (k x))) k eq _ _).
    + apply (gfp_chain (chain_b R)). exact (proj1 (ssim_ssim' _ _ _) (H X0 c)).
    + intros ?? <-. apply step_ss'_guard_l. apply CH.
Qed.

Definition Rrr {St X} (p : St * X) (x : X) := snd p = x.
Definition Lrr {St E X} := @Lvrel E _ X (@Rrr St X).

Theorem refine_state_ssim {E B B' X St} :
  forall (t : ctree E B X) (h : B ~> stateT St (ctree E B')),
  (forall Z c s, h Z c s (≲@Lrr St E Z) (branch c : ctree E B Z)) ->
  forall s, refine h t s (≲@Lrr St E X) t.
Proof.
  intros. unfold ssimT. rewrite ssim_ssim'. revert t s. coinduction R CH. intros.
  rewrite (ctree_eta t) at 2.
  setoid_rewrite unfold_refine_state. cbn.
  destruct (observe t) eqn:?.
  - apply step_ssbt'_ret. constructor. reflexivity.
  - apply step_ss'_stuck.
  - apply step_ss'_step.
    + constructor.
    + apply (b_chain R). apply step_ss'_guard_l. apply CH.
  - apply step_ss'_guard. apply CH.
  - setoid_rewrite bind_trigger.
    apply step_ss'_vis_id.
    + apply (b_chain R). apply step_ss'_passive_id; intros.
      * apply (b_chain R), step_ss'_guard_l, CH.
      * constructor. constructor.
    + constructor. constructor.
  - rewrite <- bind_branch.
    refine (sbind_chain_gen (R := chain_b R) (lift_L Lrr) (TransAlt.Active (h X0 c s)) (TransAlt.Active (branch c))
              (fun xs => Guard (refine h (k (snd xs)) (fst xs))) k Rrr _ _).
    + apply (gfp_chain (chain_b R)). exact (proj1 (ssim_ssim' _ _ _) (H X0 c s)).
    + intros ?? EQ; red in EQ; subst. apply step_ss'_guard_l. apply CH.
Qed.
