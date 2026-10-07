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

Program Definition htr {E C X} :
  mon (@trace E X -> ctree E C X -> Prop) :=
  {| body R s t :=
    match s with
    (* TODO : Active or passive? *)
    | Cons l s' => exists t', trans l t (Active t') /\ R s' t'
    | Nil => True
    end
  |}.
Next Obligation.
  destruct a. destruct H0 as (? & ? & ?). eauto. apply I.
Defined.

Definition has_trace {E C X} := gfp (@htr E C X).

Definition tracincl {E C D X}
  (t : ctree E C X) (t' : ctree E D X) :=
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

(* Lemma ss_proper_trans :  *)

(*|
Trace inclusion is weaker than similarity,
and trace equivalence is weaker than bisimilarity.
|*)
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

Lemma ssim_tracincl : forall {E C X} (t t' : ctree E C X),
ssim Leq t t' -> tracincl t t'.
Proof.
  intros E C X t t' H s H0. revert t t' H s H0.
  unfold has_trace at 2. coinduction R CH. intros.
  destruct s; [| exact I].
  step in H0. destruct H0 as (x & TR & HT).
  step in H. cbn in H. apply H in TR as TR'. destruct TR' as (l' & st' & TR' & SIM & EQL).
  apply Leq_eq in EQL. subst l'.
  destruct (transR_not_ask_active _ _ _ TR' (transR_active_not_ask _ _ _ TR)) as (u & ->).
  exists u. split; [exact TR' |]. eapply CH; eauto.
Qed.

Lemma sbisim_traceq : forall {E C X} (t t' : ctree E C X),
  sbisim Leq t t' -> traceq t t'.
Proof.
  intros. split; apply ssim_tracincl; now apply sbisim_ssim_subrelation.
Qed.
