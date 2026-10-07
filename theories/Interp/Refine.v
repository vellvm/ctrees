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
     Interp.FoldStateT
     Misc.Pure.

Import ITree.Basics.Basics.Monads.
Import MonadNotation.
Open Scope monad_scope.

Theorem ssim_pure {E F B C X} : forall (L : lrel E F X unit) (t : ctree E B X),
  pure_finite t ->
  (forall x : X, L (val x) (val tt)) ->
  ssim L t (Ret tt : ctree F C unit).
Proof.
  intros. induction H; subs.
  - apply ssim_ret. now apply build_rel_val.
  - now apply ssim_stuck.
  - now apply ssim_br_l.
  - now apply ssim_guard_l.
Qed.

Unset Universe Checking.

Theorem refine_ctree_ssim {E B B' X} :
  forall (t : ctree E B X) (h : B ~> ctree E B'),
  (forall X c, pure_finite (h X c)) ->
  refine h t ≲ t.
Proof.
  intros. unfold ssimT. rewrite ssim_ssim'. red. revert t. coinduction R CH. intros.
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
  - pose proof (H X0 c) as PF. red in PF. induction PF.
    + rewrite EQ, bind_ret_l. apply step_ss'_br_r with (x := v). apply step_ss'_guard_l. apply CH.
    + rewrite EQ, bind_stuck. apply ss'_stuck.
    + rewrite EQ, bind_br. apply step_ss'_br_l. intros. apply (b_chain R), H0.
    + rewrite EQ, bind_guard. apply step_ss'_guard_l. apply (b_chain R), IHPF.
Qed.

Definition Rrr {St X} (p : St * X) (x : X) := snd p = x.
Definition Lrr {St E X} := @Lvrel E _ X (@Rrr St X).

Theorem refine_state_ssim {E B B' X St} :
  forall (t : ctree E B X) (h : B ~> stateT St (ctree E B')),
  (forall X c s, pure_finite (h X c s)) ->
  forall s, refine h t s (≲@Lrr St E X) t.
Proof.
  intros. unfold ssimT. rewrite ssim_ssim'. red. revert t s. coinduction R CH. intros.
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
  - pose proof (H X0 c s) as PF. red in PF. induction PF.
    + rewrite EQ, bind_ret_l. apply step_ss'_br_r with (x := snd v). apply step_ss'_guard_l. apply CH.
    + rewrite EQ, bind_stuck. apply ss'_stuck.
    + rewrite EQ, bind_br. apply step_ss'_br_l. intros. apply (b_chain R), H0.
    + rewrite EQ, bind_guard. apply step_ss'_guard_l. apply (b_chain R), IHPF.
Qed.
