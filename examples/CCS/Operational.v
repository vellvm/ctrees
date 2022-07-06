From CTreeCCS Require Import
  Syntax.
Import CCSNotations.
Open Scope term_scope.

Definition use_channel (c : chan) (a : option action) : bool :=
  match a with
  | Some (↑ c') | Some (↓ c') => (c =? c')%string
  | None => false
  end.

Inductive step : option action -> term -> term -> Prop :=

| SAct: forall a P,
    step (Some a) (a · P) P

| STau: forall P,
    step None (TauT P) P

| SSumL: forall P a P' Q
           (STEPL : step a P P'),
    step a (P ⊕ Q) P'
| SSumR: forall P Q a Q'
           (STEPR : step a Q Q'),
    step a (P ⊕ Q) Q'

| SParL: forall P a P' Q
           (STEPL : step a P P'),
    step a (P ∥ Q) (P' ∥ Q)
| SParR: forall P Q a Q'
           (STEPR : step a Q Q'),
    step a (P ∥ Q) (P ∥ Q')

| SPar: forall P a P' Q Q'
          (STEPL : step (Some a) P P')
          (STEPR : step (Some (op a)) Q Q'),
    step None (P ∥ Q) (P' ∥ Q')

| SRes: forall P a P' c
          (STEP : step a P P')
          (FC : use_channel c a = false),
    step a (P ∖ c) (P' ∖ c)

| SRep: forall P a P'
          (STEP : step a (P ∥ !P) P'),
    step a (!P) P'.

Module OpNotations.

  Notation "P '⊢' a '→op'  Q" := (step a P Q)  (at level 50).

End OpNotations.

Section Example.

  Fact ex1: forall P Q,
    step None (ex P Q) ((P ∥ Q) ∖ a).
    intros.
    apply SRes; auto.
    eapply SPar.
    eapply SSumL.
    unshelve eapply SAct.
    eapply SAct.
  Qed.

  Fact ex2: forall P Q,
      step (Some (↑b)) (ex P Q) ((0 ∥ ↓a · Q) ∖ a).
    intros.
    apply SRes; auto.
    eapply SParL.
    eapply SSumR.
    eapply SAct.
  Qed.

  Ltac inv_step :=
    match goal with
    | h: step _ _ _ |- _ => inversion h; subst; clear h
    end.
  Ltac inv h := inversion h; subst; clear h.

  Fact ex3 : forall P Q R α,
      step α (ex P Q) R ->
    (α = None /\ R = ((P ∥ Q) ∖ a)) \/
    (α = Some (↑b) /\ R = ((0 ∥ ↓a · Q) ∖ a)).
    intros.
    repeat inv_step; cbn in *; try (easy || eauto).
  Qed.

End Example.

From RelationAlgebra Require Import monoid kat prop rel comparisons kat_tac rewriting normalisation.
From Coinduction Require Import lattice coinduction rel tactics.

Program Definition s: mon (term -> term -> Prop) :=
  {| body R p q :=
    forall l p', step l p p' -> exists2 q', step l q q' & R p' q' |}.
Next Obligation. cbv. firstorder. Qed.

Notation b := (cap s (comp converse (comp s converse))).

Notation bisim := (gfp b: hrel _ _).
