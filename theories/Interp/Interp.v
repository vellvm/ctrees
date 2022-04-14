(* begin hide *)

From CTree Require Import
     CTree Eq.

From ExtLib Require Import
     Structures.Functor
     Structures.Monad.

Open Scope ctree_scope.
Import CTreeNotations.

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

Lemma interp_vis {E F R S} {f : E ~> ctree F} (e: E R) (k: R -> ctree E S) :
  interp f (Vis e k) ≅ x <- f _ e;; TauI (interp f (k x)).
Proof. now rewrite unfold_interp. Qed.

Lemma interp_choice {E F R} {f : E ~> ctree F} b n (k: _ -> ctree E R) :
  interp f (Choice b n k) ≅ x <- choice b n;; TauI (interp f (k x)).
Proof. now rewrite unfold_interp. Qed.

#[global] Instance interp_equ {E F R} (h : E ~> ctree F) :
  Proper (equ eq ==> equ eq) (interp h (T := R)).
Proof.
  cbn.
  coinduction ? CIH.
  intros * EQ; step in EQ.
  rewrite 2 unfold_interp.
  inv EQ; auto.
  - cbn -[ebt].
    upto_bind_eq.
    constructor; intros ?; auto.
  - cbn -[ebt].
    upto_bind_eq.
    constructor; intros ?; auto.
Qed.

(* Note: this is specialized to [ctree F] as target monad. *)
(* TODO: Incorporate Irene's work to generalize *)
Lemma interp_bind {E F R S} (h : E ~> ctree F) (t : ctree E R) (k : R -> ctree _ S) :
  interp h (t >>= k) ≅ interp h t >>= (fun x => interp h (k x)).
Proof.
  revert t.
  coinduction R' CIH.
  intros t.
  rewrite unfold_bind, (unfold_interp t).
  desobs t; cbn -[ebt].
  - now rewrite bind_ret_l.
  - rewrite interp_vis, bind_bind.
    upto_bind_eq.
    rewrite bind_choice.
    now constructor; intros.
  - rewrite interp_choice, bind_bind.
    upto_bind_eq.
    rewrite bind_choice.
    now constructor; intros.
Qed.

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

