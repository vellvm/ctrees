From Coq Require Import Fin.
From Coq Require Export Program.Equality.

Notation fin := t.

From ITree Require Export Basics.Basics.

(* Polymorphic Class MonadTrigger (M : (Type -> Type) -> Type -> Type) : Type := *)
(*   trigger : forall {E: Type -> Type}, E ~> M E. *)

Polymorphic Class MonadChoice (M : Type -> Type) : Type :=
  choice : forall (n: nat), M (Fin.t n).

Notation rel X Y := (X -> Y -> Prop).

From Coinduction Require Import
	coinduction rel tactics.

(* A smarter version of this should be part of the [coinduction] library *)
Ltac step_in H :=
match type of H with
| gfp ?b ?x ?y => apply (gfp_fp b x y) in H
end;
simpl body in H.
Tactic Notation "step" "in" ident(H) := step_in H.

Ltac invert :=
  match goal with
  | h : existT _ _ _ = existT _ _ _ |- _ => dependent induction h
  end.
