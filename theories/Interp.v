(* begin hide *)
From Coinduction Require Import
     coinduction rel tactics.

From ExtLib Require Import
     Structures.Functor
     Structures.Monad.

From ITree Require Import
	Basics.Basics.

From CTree Require Import
		 Utils CTrees Equ Bisim CTreesTheory.

Import CTreeNotations.
Open Scope ctree_scope.

(* end hide *)

Definition translateF {E F R} (h : E ~> F) (rec: ctree E R -> ctree F R) (t : ctreeF E R _) : ctree F R  :=
	match t with
		| RetF x => Ret x
		| VisF e k => Vis (h _ e) (fun x => rec (k x))
		| ChoiceF b n k => Choice b n (fun x => rec (k x))
	end.

Definition translate {E F} (h : E ~> F) : ctree E ~> ctree F
	:= fun R => cofix translate_ t := translateF h translate_ (observe t).

Arguments translate {E F} h [T].

(** ** Interpret *)

(** An event handler [E ~> M] defines a monad morphism
		[ctree E ~> M] for any monad [M] with a loop operator. *)

Definition interp {E M : Type -> Type}
					 {FM : Functor M} {MM : Monad M} {IM : MonadIter M} {FoM : MonadChoice M}
					 (h : E ~> M) :
			ctree E ~> M := fun R =>
			iter (fun t =>
				match observe t with
				| RetF r => ret (inr r)
				| @ChoiceF _ _ _ b n k => bind (choice b n) (fun x => ret (inl (k x)))
				| VisF e k => fmap (fun x => inl (k x)) (h _ e)
				end).

Arguments interp {E M FM MM IM FoM} h [T].

(** Unfolding of [interp]. *)
Notation interp_ h t :=
  (match observe t with
  | RetF r => Ret r
	| VisF e k => bind (h _ e) (fun x => TauI (interp h (k x)))
	| @ChoiceF _ _ _ b n k => bind (choice b n) (fun x => TauI (interp h (k x)))
  end)%function.

(** Unfold lemma. *)
Lemma unfold_interp {E F R} {h : E ~> ctree F} (t : ctree E R) :
  interp h t ≅ interp_ h t.
Proof.
  unfold interp, Basics.iter, MonadIter_ctree.
  rewrite unfold_iter.
  destruct (observe t); cbn.
  - now rewrite ?bind_ret_l.
  - now rewrite bind_map, ?bind_ret_l.
  - rewrite bind_bind.
    setoid_rewrite bind_ret_l.
    reflexivity.
Qed.

(** ** [interp] and constructors *)

(** These are specializations of [unfold_interp], which can be added as
    rewrite hints.
 *)

Lemma interp_ret {E F R} {f : E ~> ctree F} (x: R):
  interp f (Ret x) ≅ Ret x.
Proof. now rewrite unfold_interp. Qed.

Lemma interp_tau {E F R} {f : E ~> ctree F} (t: ctree E R):
  interp f (TauI t) ≅ TauI (TauI (interp f t)).
Proof.
  rewrite unfold_interp.
  cbn.
  unfold choice, MonadChoice_ctree, CTree.choice. cbn.
  rewrite unfold_bind.
  cbn.
  setoid_rewrite bind_ret_l.
  reflexivity.
Qed.

Lemma interp_vis {E F R} {f : E ~> ctree F} U (e: E U) (k: U -> ctree E R) :
  interp f (Vis e k) ≅ x <- f _ e;; TauI (interp f (k x)).
Proof. now rewrite unfold_interp. Qed.

(*
Lemma interp_trigger {E F : Type -> Type} {R : Type}
      (f : E ~> (itree F))
      (e : E R) :
  interp f (ITree.trigger e) ≳ f _ e.
Proof.
  unfold ITree.trigger. rewrite interp_vis.
  setoid_rewrite interp_ret.
  setoid_rewrite tau_euttge. rewrite bind_ret_r.
  reflexivity.
Qed.

*)
