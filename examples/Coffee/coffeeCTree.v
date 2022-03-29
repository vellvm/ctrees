From CTree Require Import
	   Utils
	   CTrees
     Trans
 	   Interp
	   Equ
	   Bisim
     CTreesTheory
     Head.

Import CTreeNotations.
Open Scope ctree.

Variant E : Type -> Type :=
  | Coin      : E unit
  | ReqTea    : E unit
  | ReqCoffee : E unit
  | Tea       : E unit
  | Coffee    : E unit
.

Notation state := (ctree E void).

Definition vending : state :=
  cofix F :=
    trigger Coin;;
    choiceI2
      (trigger ReqTea;;
       vis Tea (fun _ => F))
      (trigger ReqCoffee;;
       vis Coffee (fun _ => F))
.

Definition reapoff : state :=
  cofix F :=
    choiceI2
    (trigger Coin;;
     trigger ReqTea;;
     vis Tea (fun _ => F))
    (trigger Coin;;
     trigger ReqCoffee;;
     vis Coffee (fun _ => F))
.

Theorem distinguishable : ~ (vending ~ reapoff).
Proof.
Admitted.

