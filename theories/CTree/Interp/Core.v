From ExtLib Require Import
  Structures.MonadState
  Data.Monads.StateMonad
  Structures.Monad.

From CTree Require Import
  Classes
  CTree.Core
  Events.Core
  CTree.Events.Writer
  CTree.Events.State
  CTree.Equ.

From Coq Require Import Morphisms.

Import CTreeNotations.
Local Open Scope ctree_scope.

Set Implicit Arguments.
Generalizable All Variables.

(** ** Interpret *)
(** An event handler [E ~> M] defines a monad morphism
    [c   tree E ~> M] for any monad [M] with a loop operator. *)

Definition interp `{Encode E} {M : Type -> Type}
  {MM : Monad M} {MI : MonadIter M} {MB: MonadBr M} (h: E ~> M) : forall X, ctree E X -> M X :=
  fun R => iter (fun t =>
                match observe t with
                | RetF r => ret (inr r)
                | BrF n k => bind (mbr n) (fun x => ret (inl (k x)))
                | GuardF t => ret (inl t)
                | VisF e k => bind (h e) (fun x => ret (inl (k x)))
                end).

Arguments interp {E H M MM MI MB} h [X].

(*| Unfolding of [interp]. |*)
Notation _interp h t :=
  (match observe t with
   | RetF r => Ret r
   | GuardF t => Guard (interp h t)
   | BrF n k => Br n (fun x => Guard (interp h (k x)))
   | VisF e k => h e >>= (fun x => Guard (interp h (k x)))
  end).

Local Typeclasses Transparent equ.
Lemma unfold_interp `{Encode E} `{Encode F} {R} `{f : E ~> ctree F} (t : ctree E R) :
  interp f t ≅ _interp f t.
Proof.
  unfold interp, iter, MonadIter_ctree.
  rewrite unfold_iter.
  desobs t; cbn;
    rewrite ?bind_ret_l, ?bind_map, ?bind_bind.
  - reflexivity.
  - unfold mbr, MonadBr_ctree, Ctree.branch.
    rewrite bind_br.
    apply br_equ; intros.
    rewrite ?bind_ret_l.
    reflexivity.
  - reflexivity.
  - setoid_rewrite bind_ret_l.
    reflexivity.
Qed.

#[global] Instance interp_equ `{HE: Encode E} {X} {h: E ~> ctree E} :
  Proper (equ eq ==> equ eq) (@interp E _ _ _ _ _ h X).
Proof.
  unfold Proper, respectful.
  coinduction R CH.
  intros. setoid_rewrite unfold_iter.
  step in H. inv H. 
  - setoid_rewrite bind_ret_l; reflexivity.
  - setoid_rewrite bind_bind; setoid_rewrite bind_ret_l.
    upto_bind_equ. 
    constructor. intros.
    apply CH. apply H2.
  - setoid_rewrite bind_ret_l.
    constructor.
    apply CH. apply H2.
  - setoid_rewrite bind_bind.
    upto_bind_equ.
    setoid_rewrite bind_ret_l.
    constructor. 
    apply CH. apply H2.
Qed.
