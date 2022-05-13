From Coinduction Require Import
     coinduction rel tactics.

From ITree Require Import Core.Subevent.
From CTree Require Import CTree Eq.Trans Eq.SBisim Eq.SSimTheory.

CoInductive trace {E} :=
| Cons (l : @label E) (s : trace)
| Nil.

Program Definition htr {E C X} `{HasStuck : C0 -< C} :
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

Definition has_trace {E C X} `{HasStuck : C0 -< C} := gfp (@htr E C X _).

Definition tracincl {E C D X Y} `{C0 -< C} `{C0 -< D}
  (t : ctree E C X) (t' : ctree E D Y) :=
  forall s, has_trace s t -> has_trace s t'.
Definition traceq {E C D X Y} `{C0 -< C} `{C0 -< D}
  (t : ctree E C X) (t' : ctree E D Y) :=
  tracincl t t' /\ tracincl t' t.

Lemma ssim_tracincl : forall {E C X} `{C0 -< C} (t t' : ctree E C X),
  ssim eq t t' -> tracincl t t'.
Proof.
  red. red. intros. revert t t' H0 s H1. coinduction R CH. intros.
  simpl. destruct s; auto.
  step in H1. cbn in H1. destruct H1 as (? & ? & ?).
  step in H0. apply H0 in H1. destruct H1 as (? & ? & ? & ? & ?). subst.
  exists x0. split. apply H1. eapply CH. apply H3. red. apply H2.
Qed.

Lemma sbisim_traceq : forall {E C X} `{C0 -< C} (t t' : ctree E C X),
  sbisim t t' -> traceq t t'.
Proof.
  intros. split; apply ssim_tracincl; now apply sbisim_ssim_eq.
Qed.
