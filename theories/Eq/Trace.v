From Stdlib Require Import Basics.

From Coinduction Require Import all.

From ITree Require Import Core.Subevent.
From CTree Require Import
  CTree
  Eq.Equ
  Eq.Trans
  Eq.SSim
  Eq.SBisim. 

(*|
Base coinductive definitions for execution traces and trace equivalence.
|*)

CoInductive trace {E R} :=
| Cons (l : @label E R) (s : trace)
| Nil.

(* Now defined over States. *)
Program Definition htr {E C X} :
  mon (@trace E X -> S E C X -> Prop) :=
  {| body R s st :=
    match s with
    | Cons l s' => (exists st', trans l st st' /\ R s' st')
    | Nil => True
    end
  |}.
Next Obligation.
  destruct a. destruct H0 as (? & ? & ?). 
  eauto.
  apply I. 
Defined.

Definition has_trace {E C X} := gfp (@htr E C X).

Definition tracincl {E C D X}
  (t : S E C X) (t' : S E D X) :=
  forall s, has_trace s t -> has_trace s t'.

Definition traceq {E C D X}
  (t : ctree E C X) (t' : ctree E D X) :=
  tracincl t t' /\ tracincl t' t.

(*|
Instances
|*)

#[global] Instance traceq_equ : forall {E C X} s,
  Proper (equ eq ==> impl) (@has_trace E C X s).
Proof.
  cbn. intros. step. destruct s; auto.
  step in H0. cbn in H0. destruct H0 as (? & Ht & ?).
  - rewrite H in Ht. exists x0. auto.
Qed.

#[global] Instance has_trace_Seq {E C X} s :
  Proper (Seq ==> impl) (@has_trace E C X s).
Proof.
  cbn. intros a b EQ H. step. destruct s; auto.
  step in H. destruct H as (st & TR & HT). rewrite EQ in TR. cbn. eauto.
Qed.

(*|
Tactics
|*)

Tactic Notation "__trace_play" "using" tactic(tac) :=
  eexists; try (rewrite ctree_eta; cbn); split; [now tac | auto].

Tactic Notation "__trace_play" :=
  __trace_play using (first [etrans | econstructor; reflexivity]).

Tactic Notation "__trace_play" "in" hyp(H) :=
  step in H; cbn in H;
  destruct H as (? & TR & H);
  try (rewrite ctree_eta in TR; cbn in TR);
  inv_trans; subst.

Lemma ssim_tracincl : forall {E C X} (t t' : S E C X),
ssim Leq t t' -> tracincl t t'.
Proof.
  intros E C X t t' H s H0. revert t t' H s H0.
  unfold has_trace at 2. coinduction R CH. intros.
  destruct s; [| exact I].
  step in H0. destruct H0 as (x & TR & HT).
  - step in H. cbn in H. apply H in TR as TR'. destruct TR' as (l' & st' & TR' & SIM & EQL).
    apply Leq_eq in EQL. subst l'.
    cbn. exists st'. split. 
    apply TR'. 
    apply CH with (t:=x); auto. 
Qed.

Lemma sbisim_traceq : forall {E C X} (t t' : ctree E C X),
  sbisim Leq t t' -> traceq t t'.
Proof.
  intros. split; apply ssim_tracincl; now apply sbisim_ssim_subrelation.
Qed.

(*|
One alternative version of traces, [htr_must]: after a question, a trace skips
the answer label and continues from every possible answer at once. This is a bit 
more ATL style, as the system MUST have a way to proceed no matter what the environment does. 

This is a bit more in line with 'must'-style reasoning, but is less expresive in the typical 
case since unanswerable questions discharge everything and there is no answer-dependent behavior. 

It would be more expressive as a tree: 

CoInductive strat {E X} :=
| SCons  (l : label E X) (s : strat)                 (* own step *)
| SAsk {Y} (e : E Y) (k : Y -> strat)               (* question: branch on answer *)
| SNil.
|*)

Program Definition htr_must {E C X} :
  mon (@trace E X -> S E C X -> Prop) :=
  {| body R s t :=
    match s with
    | Cons l s' => (exists t', trans l t (Active t') /\ R s' t') \/ 
                   (exists Y e f, trans l t (Passive e f) /\ forall x : Y, R s' (f x))
    | Nil => True
    end
  |}.
Next Obligation.
  destruct a. destruct H0 as [(? & ? & ?) | (Y & e & f & Ht & HX)]. 
  eauto. 
  right. exists Y, e, f. split; [eauto|]. intros. now apply H.  
  apply I.
Defined.

Definition has_trace_all {E C X} := gfp (@htr_must E C X).

Definition tracincl_all {E C D X}
  (t : S E C X) (t' : S E D X) :=
  forall s, has_trace_all s t -> has_trace_all s t'.

Definition traceq_all {E C D X}
  (t : ctree E C X) (t' : ctree E D X) :=
  tracincl_all t t' /\ tracincl_all t' t.

#[global] Instance traceq_all_equ : forall {E C X} s,
  Proper (equ eq ==> impl) (@has_trace_all E C X s).
Proof.
  cbn. intros. step. destruct s; auto.
  step in H0. cbn in H0. destruct H0 as [(? & Ht & ?) | (Y & e & f & Ht & HX)].
  - rewrite H in Ht. left. exists x0. auto.
  - rewrite H in Ht. right. exists Y, e, f. eauto.   
Qed.

Lemma transR_active_not_ask {E C X} : forall l (s : S E C X) t,
  transR l s (Active t) -> forall Y (e : E Y), l <> ask e.
Proof.
  intros * TR. remember (Active t) as u. induction TR; intros; subst; try discriminate; eauto.
Qed.

Lemma transR_not_ask_active {E C X} : forall l (s s' : S E C X),
  transR l s s' -> (forall Y (e : E Y), l <> ask e) -> exists u, s' = Active u.
Proof.
  intros * TR NA. induction TR; eauto.
  exfalso. eapply NA; reflexivity.
Qed.

Lemma transR_passive_ask {E C X Y} {e : E Y} {f} : forall l (s : S E C X), 
  transR l s (Passive e f) -> l = ask e. 
Proof. 
  intros * TR. remember (Passive e f) as p. 
  induction TR; eauto; try easy. 
  now dependent destruction Heqp.  
Qed. 

Lemma transR_ask_passive {E C X Y} {e : E Y} : forall (s : S E C X) t, 
  transR (ask e) s t -> exists f, t = (Passive e f). 
Proof. 
  intros * TR. remember (ask e) as a. induction TR; eauto; try easy. 
  dependent destruction Heqa. eauto. 
Qed. 


Lemma ssim_tracincl_all : forall {E C X} (t t' : S E C X),
ssim Leq t t' -> tracincl_all t t'.
Proof.
  intros E C X t t' H s H0. revert t t' H s H0.
  unfold has_trace_all at 2. coinduction R CH. intros.
  destruct s; [| exact I].
  step in H0. destruct H0 as [(x & TR & HT) | (Y & e & f & TR & HT)].
  - step in H. cbn in H. apply H in TR as TR'. destruct TR' as (l' & st' & TR' & SIM & EQL).
    apply Leq_eq in EQL. subst l'.
    destruct (transR_not_ask_active _ _ _ TR' (transR_active_not_ask _ _ _ TR)) as (u & ->).
    left. exists u. split; [exact TR' |]. eapply CH; eauto.
  - step in H. cbn in H. apply H in TR as TR'.
    destruct TR' as (l' & st' & TR' & SIM & EQL).
    apply Leq_eq in EQL. subst l'.
    apply transR_passive_ask in TR; subst l. 
    apply transR_ask_passive in TR' as TR''; destruct TR'' as (f' & ->). 
    pose proof (ssim_passive_inv_eq SIM) as SIMK.
    right. exists Y, e, f'. split. 
    exact TR'. intros. eapply CH; [apply SIMK | apply HT]. 
Qed. 
