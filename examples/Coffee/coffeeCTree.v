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
 	   Interp.Fold.

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

Notation state := (ctree E B2 void).

Definition vending : state :=
  cofix F :=
    trigger Coin;;
    br2
      (trigger ReqTea;;
       vis Tea (fun _ => F))
      (trigger ReqCoffee;;
       vis Coffee (fun _ => F))
.

Definition reapoff : state :=
  cofix F :=
    br2
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
  setoid_rewrite bind_ret_l in SS.
  apply trans_br_inv in TR as (? & TR). destruct x1. inv_trans.
  - dependent destruction EQ0. setoid_rewrite EQ in EQ0. 
    setoid_rewrite bind_ret_l in EQ0. 
    play in SS. apply Leq_eq in HL0. subst. rewrite EQ0 in TR. inv_trans.
    play in SS0. 
    apply Leq_eq in HL0; subst.
    setoid_rewrite bind_trigger in TR.
    inv_trans. 
  - apply Leq_eq in HL; subst x.
    setoid_rewrite bind_trigger in TR. inv_trans.
    pose proof (ssim_passive_inv_eq SS tt) as SS'.
    eapply ssim_br_l_inv with (x := true) in SS'.
    play in SS'. inv_trans. apply Leq_eq in HL. 
    dependent destruction EQl0. 
    dependent destruction HL.
    Unshelve. all: auto.  
Qed.

Theorem coffee_ssim : reapoff ≲ vending.
Proof.
  coinduction R CH.
  setoid_rewrite ctree_eta. cbn. setoid_rewrite bind_ret_l.
  apply ss_br_l. intros.
  destruct x.
  - rewrite bind_trigger. apply ss_vis; [constructor|]. intros [].
    exists tt. split; [|constructor].
    step. apply ss_br_r with (x := true).
    eapply ssim_bind_chain. reflexivity. cbn. intros _.
    apply ss_vis_id. constructor. split; [eauto|constructor].   
  - rewrite bind_trigger.
    apply ss_vis; [constructor|]; intros []; exists tt; split; [|constructor].
    step.
    apply ss_br_r with (x := false).
    apply ssim_bind_chain. reflexivity. intros _.
    apply ss_vis_id; [constructor | split; [eauto | constructor]].
Qed.

Tactic Notation "play" "using" tactic(tac) :=
  __trace_play using tac.

Tactic Notation "play" := __trace_play.

Tactic Notation "play" "in" hyp(H) :=
  __trace_play in H.

Lemma vending_unfold :
  vending ≅ vis Coin (fun _ => br2 (vis ReqTea (fun _ => vis Tea (fun _ => vending)))
                                   (vis ReqCoffee (fun _ => vis Coffee (fun _ => vending)))).
Proof.
  rewrite ctree_eta at 1. cbn. step. constructor. intros []. 
  change (subst ?k (Ret tt)) with (CTree.bind (Ret tt) k). rewrite bind_ret_l. cbn.
  now setoid_rewrite bind_trigger. 
Qed.

Lemma reapoff_unfold :
  reapoff ≅ br2 (vis Coin (fun _ => vis ReqTea (fun _ => vis Tea (fun _ => reapoff))))
                (vis Coin (fun _ => vis ReqCoffee (fun _ => vis Coffee (fun _ => reapoff)))).
Proof.
  rewrite ctree_eta at 1. cbn. 
  step. constructor.
  intros []; cbn; do 2 setoid_rewrite bind_trigger; reflexivity.
Qed.

Ltac trace_sync H s :=
  step; cbn; play; destruct s as [? s|]; [play in H | step; exact I].

Theorem coffee_traceq : traceq vending reapoff.
Proof.
  split; red; intros.
  - red. revert s H. coinduction R CH. intros.
    rewrite vending_unfold in H. do 2 red.
    destruct s as [? s|]; [| exact I]. play in H.
    setoid_rewrite reapoff_unfold.
    destruct s as [? s|].
    2: { play using (apply trans_br21; etrans). now step. }
    play in H.
    destruct s as [? s|].
    2: { play using (apply trans_br21; etrans). step. cbn. play. now step. }
    play in H.
    destruct n; inv_trans.
    + play using (apply trans_br21; etrans).
      step. cbn. play.
      do 3 trace_sync H s.
      step; cbn; play.
    + play using (apply trans_br22; etrans).
      step. cbn. play.
      do 3 trace_sync H s.
      step; cbn; play.
  - pose proof (ssim_tracincl _ _ coffee_ssim); auto.
Qed.
