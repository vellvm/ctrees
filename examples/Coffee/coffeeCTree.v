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
	   CTree
     Eq
 	   Interp.Interp.

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

Notation state := (ctree E (C0 +' C2) void).

Definition vending : state :=
  cofix F :=
    trigger Coin;;
    chooseI2
      (trigger ReqTea;;
       vis Tea (fun _ => F))
      (trigger ReqCoffee;;
       vis Coffee (fun _ => F))
.

Definition reapoff : state :=
  cofix F :=
    chooseI2
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
  step in EQ.
  destruct EQ as [F _].
  setoid_rewrite (ctree_eta vending) in F.
  cbn in F.
  edestruct F as (u' & ? & TR & EQ & ?); [apply (trans_vis _ tt) | clear F; subst].
  fold (@CTree.bind E (C0 +' C2) unit void (Ret tt) (fun _ : unit =>
                                            chooseI2 (trigger ReqTea;; vis Tea (fun _ : unit => vending)) (trigger ReqCoffee;; vis Coffee (fun _ : unit => vending)))) in EQ.
  rewrite bind_ret_l in EQ.
  step in EQ; destruct EQ as [F _]; cbn in F.
  rewrite ctree_eta in TR; cbn in TR.
  inv_trans. destruct x.
  - inv_trans.
    edestruct F as (u'' & ? & TR & ? & ?); subst.
    apply trans_chooseI22,(trans_trigger _ tt).
    rewrite EQ in TR.
    inv_trans. inv EQl0.
  - inv_trans.
    edestruct F as (u'' & ? & TR & ? & ?); subst.
    apply trans_chooseI21,(trans_trigger _ tt).
    rewrite EQ in TR.
    inv_trans. inv EQl0.
Qed.
