From ITree Require Import Basics Indexed.Sum.
From CTree Require Import Core.Utils.

(*|
Nullary arity, encoding stuck processes
|*)
Variant B0 : Type -> Type := | branch0 : B0 void.

(*|
Unary arity, encoding taus/fuel/guards
|*)
Variant B1 : Type -> Type := | branch1 : B1 unit.

(*|
Commonly used bounded arities
|*)
Variant B2 : Type -> Type := | branch2 : B2 bool.
Variant T3 : Type := | t31 | t32 | t33.
Variant B3 : Type -> Type := | branch3 : B3 T3.
Variant T4 : Type := | t41 | t42 | t43 | t44.
Variant B4 : Type -> Type := | branch4 : B4 T4.

(*|
Finite unbounded arity
|*)
Variant Bn : Type -> Type := | branchn (n : nat) : Bn (fin n).

(*|
Countable branching
|*)
Variant BN : Type -> Type := | branchN : BN nat.

Notation B01 := (B0 +' B1).
Notation B02 := (B0 +' B1 +' B2).
