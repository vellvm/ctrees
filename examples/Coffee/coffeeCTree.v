From RelationAlgebra Require Import
     monoid
     kat
     kat_tac
     prop
     rel
     srel
     comparisons
     rewriting
     normalisation.

From CTree Require Import
	   CTree
     Eq
     Eq.Trace
 	   Interp.Interp.

Import CTree.
Import CTreeNotations.
Open Scope ctree.

Variant E : Type -> Type :=
  | Coin      : E unit
  | ReqTea    : E unit
  | ReqCoffee : E unit
  | Tea       : E unit
  | Coffee    : E unit
.

Notation state := (ctree E void).

Definition vending : state :=
  cofix F :=
    trigger Coin;;
    brD2
      (trigger ReqTea;;
       vis Tea (fun _ => F))
      (trigger ReqCoffee;;
       vis Coffee (fun _ => F))
.

Definition reapoff : state :=
  cofix F :=
    brD2
    (trigger Coin;;
     trigger ReqTea;;
     vis Tea (fun _ => F))
    (trigger Coin;;
     trigger ReqCoffee;;
     vis Coffee (fun _ => F))
.

Theorem distinguishable : ~ (vending ≲ reapoff).
Proof.
  intros H.
  setoid_rewrite ctree_eta in H. play in H.
  setoid_rewrite bind_ret_l in EQ.
  apply trans_brD_inv in TR as (? & TR). destruct x0. inv_trans.
  - play in EQ. inv_trans. discriminate.
  - eapply ssim_brD_l_inv with (x := Fin.F1) in EQ.
    play in EQ. inv_trans. discriminate.
  Unshelve. all: auto.
Qed.

Theorem coffee_ssim : reapoff ≲ vending.
Proof.
  coinduction R CH.
  setoid_rewrite ctree_eta. cbn. setoid_rewrite bind_ret_l.
  apply step_ss_brD_l. intros.
  destruct x.
  - rewrite bind_trigger. apply step_ss_vis; auto. intros _.
    step. apply step_ss_brD_r with (x := Fin.F1).
    upto_bind_eq. now apply step_ss_vis.
  - rewrite bind_trigger. apply step_ss_vis; auto. intros _.
    step. apply step_ss_brD_r with (x := Fin.FS Fin.F1).
    upto_bind_eq. now apply step_ss_vis.
Qed.

Tactic Notation "play" "using" tactic(tac) :=
  __trace_play using tac.

Tactic Notation "play" := __trace_play.

Tactic Notation "play" "in" hyp(H) :=
  __trace_play in H.

Theorem coffee_traceq : traceq vending reapoff.
Proof.
  split; red; intros.
  - red. revert s H. coinduction R CH. intros.
    do 3 red. cbn.
    destruct s; auto. play in H.
    destruct s.
    2: play; now step.
    setoid_rewrite bind_ret_l in H.
    play in H. apply trans_brD_inv in TR as [].
    destruct x2; inv_trans; subst.
    + play using (apply trans_brD21; etrans).
      step. play.
      step. destruct s; auto. play in H. play.
    + play using (apply trans_brD22; etrans).
      step. play.
      step. destruct s; auto.
      play in H. play.
  - pose proof (ssim_tracincl _ _ coffee_ssim); auto.
Qed.
