From ITree Require Import Basics Indexed.Sum.
From CTree Require Import Core.Utils.

(*|
Nullary arity, encoding stuck processes
|*)
Variant C0 : Type -> Type := | choice0 : C0 void.

(*|
Unary arity, encoding taus/fuel/guards
|*)
Variant C1 : Type -> Type := | choice1 : C1 unit.

(*|
Commonly used bounded arities
|*)
Variant C2 : Type -> Type := | choice2 : C2 bool.
Variant T3 : Type := | t31 | t32 | t33.
Variant C3 : Type -> Type := | choice3 : C3 T3.
Variant T4 : Type := | t41 | t42 | t43 | t44.
Variant C4 : Type -> Type := | choice4 : C4 T4.

(*|
Finite unbounded arity
|*)
Variant Cn : Type -> Type := | choicen (n : nat) : Cn (fin n).

(*|
Countable branching
|*)
Variant CN : Type -> Type := | choiceN : CN nat.

Notation C01 := (C0 +' C1).
