From Coq Require Import Fin.
From Coq Require Export Program.Equality.

Notation fin := t.

>>>>>>> Stashed changes:theories/Utils.v
(* Polymorphic Class MonadTrigger (M : (Type -> Type) -> Type -> Type) : Type := *)
(*   trigger : forall {E: Type -> Type}, E ~> M E. *)
=======
Polymorphic Class MonadTrigger (E : Type -> Type) (M : Type -> Type) : Type :=
  trigger : E ~> M.
>>>>>>> Stashed changes:theories/Core/Utils.v

Polymorphic Class MonadChoice (M : Type -> Type) : Type :=
  choice : forall (b : bool) (n: nat), M (Fin.t n).

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

From Coinduction Require Import
	coinduction rel tactics.

(* A smarter version of this should be part of the [coinduction] library *)
Ltac step_in H :=
match type of H with
| gfp ?b ?x ?y => apply (gfp_fp b x y) in H
| body (t ?b) ?R ?x ?y => apply (bt_t b R x y) in H
| gfp ?b ?x => apply (gfp_fp b x) in H
| body (t ?b) ?R ?x => apply (bt_t b R x) in H
| _ => red in H; step_in H
end;
simpl body in H.
Tactic Notation "step" "in" ident(H) := step_in H.

