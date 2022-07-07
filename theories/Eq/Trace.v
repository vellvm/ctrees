From Coq Require Import Basics.

From Coinduction Require Import
     coinduction rel tactics.

From ITree Require Import Core.Subevent.
From CTree Require Import
     CTree Eq.Equ Eq.Trans Eq.SBisim Eq.SSim.


(*|
Execution traces defined as colists and trace equivalence.
|*)

CoInductive trace {E} :=
| Cons (l : @label E) (s : trace)
| Nil.

Program Definition htr {E X} :
  mon (@trace E -> ctree E X -> Prop) :=
  {| body R s t :=
    match s with
    | Cons l s' => exists t', trans l t t' /\ R s' t'
    | Nil => True
    end
  |}.
Next Obligation.
  destruct a. destruct H0 as (? & ? & ?). eauto. apply I.
Defined.

Definition has_trace {E X} := gfp (@htr E X).

Definition tracincl {E X}
  (t t' : ctree E X) :=
  forall s, has_trace s t -> has_trace s t'.
Definition traceq {E X}
  (t t' : ctree E X) :=
  tracincl t t' /\ tracincl t' t.

(*|
Instances
|*)

#[global] Instance traceq_equ : forall {E X} s,
  Proper (equ eq ==> impl) (@has_trace E X s).
Proof.
  cbn. intros. step. destruct s; auto.
  step in H0. cbn in H0. destruct H0 as (? & ? & ?).
  rewrite H in H0. exists x0. auto.
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

Lemma ssim_tracincl : forall {E X} (t t' : ctree E X),
  ssim t t' -> tracincl t t'.
Proof.
  red. red. intros. revert t t' H s H0. coinduction R CH. intros.
  simpl. destruct s; auto.
  step in H0. cbn in H0. destruct H0 as (? & ? & ?).
  step in H. apply H in H0. destruct H0 as [? ? ?].
  exists x0. split. apply H0. eapply CH. apply H2. red. apply H1.
Qed.

Lemma sbisim_traceq : forall {E X} (t t' : ctree E X),
  sbisim t t' -> traceq t t'.
Proof.
  intros. split; apply ssim_tracincl; now apply sbisim_ssim.
Qed.
