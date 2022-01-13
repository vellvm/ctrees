From CTreeCCS Require Import
  Syntax.
Import CCSNotations.
Open Scope ccs_scope.

Definition use_channel (c : chan) (a : option action) : bool :=
  match a with
  | Some (↑ c') | Some (↓ c') => (c =? c')%string
  | None => false
  end.

Inductive step : term -> option action -> term -> Prop :=

| SAct: forall a P,
    step (a · P) (Some a) P

| STau: forall P,
    step (TauT P) None P

| SSumL: forall P a P' Q,
    step P a P' ->
    step (P ⊕ Q) a P'
| SSumR: forall P Q a Q',
    step Q a Q' ->
    step (P ⊕ Q) a Q'

| SParL: forall P a P' Q,
    step P a P' ->
    step (P ∥ Q) a (P' ∥ Q)
| SParR: forall P Q a Q',
    step Q a Q' ->
    step (P ∥ Q) a (P ∥ Q')

| SPar: forall P a P' Q Q',
    step P (Some a) P' ->
    step Q (Some (op a)) Q' ->
    step (P ∥ Q) None (P' ∥ Q')

| SRes: forall P a P' c,
    step P a P' ->
    use_channel c a = false ->
    step (P ∖ c) a (P' ∖ c)
.

Module OpNotations.

  Notation "P '⊢' a '→op'  Q" := (step P a Q)  (at level 50).

End OpNotations.

Section Example.

  Fact ex1: forall P Q,
    step (ex P Q) None ((P ∥ Q) ∖ a).
    intros.
    apply SRes; auto.
    eapply SPar.
    eapply SSumL.
    unshelve eapply SAct.
    eapply SAct.
  Qed.

  Fact ex2: forall P Q,
      step (ex P Q) (Some (↑b)) ((0 ∥ ↓a · Q) ∖ a).
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
      step (ex P Q) α R ->
    (α = None /\ R = ((P ∥ Q) ∖ a)) \/
    (α = Some (↑b) /\ R = ((0 ∥ ↓a · Q) ∖ a)).
    intros.
    repeat inv_step; cbn in *; try (easy || eauto).
  Qed.

End Example.
