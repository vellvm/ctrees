From Coq Require Import Basics.

From Coinduction Require Import
     coinduction rel tactics.

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

CoInductive trace {E} :=
| Cons (l : @label E) (s : trace)
| Nil.

Program Definition htr {E C X} `{HasStuck : B0 -< C} :
  mon (@trace E -> ctree E C X -> Prop) :=
  {| body R s t :=
    match s with
    | Cons l s' => exists t', trans l t t' /\ R s' t'
    | Nil => True
    end
  |}.
Next Obligation.
  destruct a. destruct H0 as (? & ? & ?). eauto. apply I.
Defined.

Definition has_trace {E C X} `{HasStuck : B0 -< C} := gfp (@htr E C X _).

Definition tracincl {E C D X Y} `{B0 -< C} `{B0 -< D}
  (t : ctree E C X) (t' : ctree E D Y) :=
  forall s, has_trace s t -> has_trace s t'.

Definition traceq {E C D X Y} `{B0 -< C} `{B0 -< D}
  (t : ctree E C X) (t' : ctree E D Y) :=
  tracincl t t' /\ tracincl t' t.

(*|
Instances
|*)

#[global] Instance traceq_equ : forall {E C X} `{B0 -< C} s,
  Proper (equ eq ==> impl) (@has_trace E C X _ s).
Proof.
  cbn. intros. step. destruct s; auto.
  step in H1. cbn in H1. destruct H1 as (? & ? & ?).
  rewrite H0 in H1. exists x0. auto.
Qed.

(*|
Tactics
|*)

Tactic Notation "__trace_play" "using" tactic(tac) :=
  eexists; rewrite ctree_eta;
  cbn; split; [now tac | auto].

Tactic Notation "__trace_play" := __trace_play using etrans.

Tactic Notation "__trace_play" "in" hyp(H) :=
  step in H; cbn in H;
  destruct H as (? & TR & H);
  rewrite ctree_eta in TR; cbn in TR;
  inv_trans; subst.

(*|
Trace inclusion is weaker than similarity,
and trace equivalence is weaker than bisimilarity.
|*)
Lemma ssim_tracincl : forall {E C X} `{B0 -< C} (t t' : ctree E C X),
  ssim eq t t' -> tracincl t t'.
Proof.
  red. red. intros. revert t t' H0 s H1. coinduction R CH. intros.
  simpl. destruct s; auto.
  step in H1. cbn in H1. destruct H1 as (? & ? & ?).
  step in H0. apply H0 in H1. destruct H1 as (? & ? & ? & ? & ?). subst.
  exists x1. split. apply H1. eapply CH. apply H3. red. apply H2.
Qed.

Lemma sbisim_traceq : forall {E C X} `{B0 -< C} (t t' : ctree E C X),
  sbisim eq t t' -> traceq t t'.
Proof.
  intros. split; apply ssim_tracincl; now apply sbisim_ssim.
Qed.
