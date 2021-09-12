From Coq Require Import Fin.
From Coq Require Export Program.Equality.

Notation fin := t.

From ITree Require Export Basics.Basics.

Polymorphic Class MonadTrigger (M : Type -> Type) : Type :=
  trigger : forall {E: Type -> Type}, E ~> M.

Polymorphic Class MonadFork (M : Type -> Type) : Type :=
  fork : forall (n: nat), M (Fin.t n).

