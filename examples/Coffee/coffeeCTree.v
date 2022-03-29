From RelationAlgebra Require Import
     monoid
     kat
     kat_tac
     prop
     rel
     srel
     comparisons
     rewriting
     normalisation.

From CTree Require Import
	   Utils
	   CTrees
     Trans
 	   Interp
	   Equ
	   Bisim
     CTreesTheory
     Head.

Import CTree.
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

(* TODO: this whole proof is currently unacceptable, we should tweak things until it's actually clean *)
Theorem distinguishable : ~ (vending ~ reapoff).
Proof.
  intros EQ.
  step in EQ; fold (@sbisim E void) in *.
  destruct EQ as [F _].
  setoid_rewrite (ctree_eta vending) in F.
  cbn in F.
  edestruct F as [u' TR EQ]; [apply (trans_vis (x := tt)) | clear F].
  fold (@CTree.bind E unit void (Ret tt) (fun _ : unit =>
                                            choiceI2 (trigger ReqTea;; vis Tea (fun _ : unit => vending)) (trigger ReqCoffee;; vis Coffee (fun _ : unit => vending)))) in EQ.
  rewrite bind_ret_l in EQ.
  step in EQ; destruct EQ as [F _]; cbn in F.
  rewrite ctree_eta in TR; cbn in TR.
  apply trans_ChoiceI_inv in TR as [[|] h].
  - apply trans_trigger_inv in h.
    destruct h as ([] & EQ & _).
    edestruct F as [u'' TR _].
    apply trans_choiceI22,(trans_trigger (x := tt)).
    rewrite EQ in TR.
    apply trans_trigger_inv in TR as ([] & _ & abs).
    inv abs.
  - apply trans_trigger_inv in h.
    destruct h as ([] & EQ & _).
    edestruct F as [u'' TR _].
    apply trans_choiceI21,(trans_trigger (x := tt)).
    rewrite EQ in TR.
    apply trans_trigger_inv in TR as ([] & _ & abs).
    inv abs.
Qed.
