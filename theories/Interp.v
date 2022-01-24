(* begin hide *)
From ExtLib Require Import
     Structures.Functor
     Structures.Monad.

From ITree Require Import
	Basics.Basics.

From CTree Require Import
		 Utils CTrees Equ Bisim.

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
				| @ChoiceF _ _ _ _ n k => bind (choice n) (fun x => ret (inl (k x)))
				| VisF e k => fmap (fun x => inl (k x)) (h _ e)
				end).

Arguments interp {E M FM MM IM FoM} h [T].

(*
(** Unfolding of [interp]. *)
Notation interp_ h t :=
         (* {E F R} (h : E ~> ctree F) (ot : ctreeF E R _) : ctree F R := *)
  (match observe t with
  | RetF r => Ret r
	| VisF e k => fmap (fun x => TauI (interp h (k x))) (h _ e)
	| @ChoiceF _ _ _ _ n k => bind (choice n) (fun x => ret (inl (k x)))
  end).


(** Unfold lemma. *)
Lemma unfold_interp {E F R} {h : E ~> ctree F} (t : ctree E R) : 
  interp h t ≅ match observe t with
          | RetF r => Ret r
          | VisF e k => x <- h _ e;; TauI (interp h (k x))
          | ChoiceF b n k => Choice b n (fun i => (interp h (k i)))
          end.
Proof.
  unfold interp, Basics.iter, MonadIter_ctree.
  rewrite unfold_iter.
  destruct (observe t); cbn.
  - now rewrite ?bind_ret_l. 
  - now rewrite ?bind_ret_l. 
Qed.



(** ** [interp] and constructors *)

(** These are specializations of [unfold_interp], which can be added as
    rewrite hints.
 *)

Lemma interp_ret {E F R} {f : E ~> itree F} (x: R):
  interp f (Ret x) ≅ Ret x.
Proof. rewrite unfold_interp. reflexivity. Qed.

Lemma interp_tau {E F R} {f : E ~> itree F} (t: itree E R):
  eq_itree eq (interp f (Tau t)) (Tau (interp f t)).
Proof. rewrite unfold_interp. reflexivity. Qed.

Lemma interp_vis {E F R} {f : E ~> itree F} U (e: E U) (k: U -> itree E R) :
  eq_itree eq (interp f (Vis e k)) (ITree.bind (f _ e) (fun x => Tau (interp f (k x)))).
Proof. rewrite unfold_interp. reflexivity. Qed.

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
