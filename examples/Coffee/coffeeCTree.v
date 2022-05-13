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

Ltac etransH H := eassert (H := H _); lapply H; [ clear H | etrans ].

(* TODO: this whole proof is currently unacceptable, we should tweak things until it's actually clean *)
Theorem distinguishable : ~ (vending ~ reapoff).
Proof.
  intros EQ.
  step in EQ.
  destruct EQ as [F _].
  setoid_rewrite (ctree_eta vending) in F.
  cbn in F.
  specialize (F (obs Coin tt)). etransH F.
  intros (u' & ? & TR & EQ & ?).
  fold_bind.
  rewrite bind_ret_l in EQ.
  step in EQ; destruct EQ as [F _]; cbn in F.
  rewrite ctree_eta in TR; cbn in TR.
  inv_trans. destruct x0; inv_trans.
  - specialize (F (obs ReqCoffee tt)). etransH F.
    intros (u'' & ? & TR & ? & ?); subst.
    rewrite EQ in TR.
    inv_trans. inv EQl.
  - specialize (F (obs ReqTea tt)). etransH F.
    intros (u'' & ? & TR & ? & ?); subst.
    rewrite EQ in TR.
    inv_trans. inv EQl.
Qed.
