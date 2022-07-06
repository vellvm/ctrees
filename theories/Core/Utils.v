From Coq Require Import Fin.
From Coq Require Export Program.Equality.
From Coinduction Require Import
	coinduction rel tactics.

Notation fin := Fin.t.

#[global] Arguments bt : simpl never.
Ltac next := unfold bt; cbn.
Tactic Notation "cbn*" := next.

Polymorphic Class MonadTrigger (E : Type -> Type) (M : Type -> Type) : Type :=
  mtrigger : forall X, E X -> M X.

Polymorphic Class MonadBr (M : Type -> Type) : Type :=
  mbr : forall (b : bool) (n: nat), M (Fin.t n).

Notation rel X Y := (X -> Y -> Prop).

Ltac invert :=
  match goal with
  | h : existT _ _ _ = existT _ _ _ |- _ => dependent induction h
  end.

Ltac copy h :=
  let foo := fresh "cpy" in
  assert (foo := h).

Ltac break :=
  repeat match goal with
         | h : _ \/ _  |- _ => destruct h
         | h : _ /\ _  |- _ => destruct h
         | h : exists x, _ |- _ => destruct h
         end.

(* A smarter version of this should be part of the [coinduction] library *)

Ltac step_ :=
  match goal with
  | |- gfp ?b ?x ?y => apply (proj2 (gfp_fp b x y))
  | |- body (t ?b) ?R ?x ?y => apply (bt_t b R x y)
  | |- gfp ?b ?x => apply (proj2 (gfp_fp b x))
  | |- body (t ?b) ?R ?x => apply (bt_t b R x)
  end.

Ltac step := first [step_ | red; step_].

Ltac step_in H :=
match type of H with
| gfp ?b ?x ?y => apply (gfp_fp b x y) in H
| body (t ?b) ?R ?x ?y => apply (bt_t b R x y) in H
| gfp ?b ?x => apply (gfp_fp b x) in H
| body (t ?b) ?R ?x => apply (bt_t b R x) in H
| _ => red in H; step_in H
end.
Tactic Notation "step" "in" ident(H) := step_in H.
