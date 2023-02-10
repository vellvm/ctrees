From Coq Require Import
     Fin
     Nat
     List
     Relations.

From ITree Require Import
     Indexed.Sum
     CategoryOps.

From CTree Require Import
     CTree
     Eq.Equ
     Eq.Trans
     Interp.Fold
     Misc.Vectors
     Core.Utils.

Local Open Scope fin_vector_scope.
  
Set Implicit Arguments.

(*| Unique thread identifiers |*)
Notation id n := (fin (S n)).

(*| Thread IDs are a product of an effect [E] with a [uid] |*)
Variant switchE (n: nat): Type -> Type :=
  | Process (i: id n): switchE n unit.

Arguments Process {n}.

Definition switch {n E C} `{switchE n -< E} (i: id n): ctree E C unit :=
  trigger (Process i).


 
