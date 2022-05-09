(* begin hide *)

From CTree Require Import
     CTree Eq.

From ExtLib Require Import
     Structures.Functor
     Structures.Monad.

From ITree Require Import
	Basics.Basics
  Core.Subevent.

From CTree Require Import
		 CTree.

Import CTreeNotations.
Open Scope ctree_scope.
Import CTreeNotations.

(* end hide *)

Definition translateF {E F C R} (h : E ~> F) (rec: ctree E C R -> ctree F C R) (t : ctreeF E C R _) : ctree F C R  :=
	match t with
		| RetF x => Ret x
		| VisF e k => Vis (h _ e) (fun x => rec (k x))
		| ChoiceF b c k => Choice b c (fun x => rec (k x))
	end.

Definition translate {E F C} (h : E ~> F) : ctree E C ~> ctree F C
	:= fun R => cofix translate_ t := translateF h translate_ (observe t).

Arguments translate {E F C} h [T].

(** ** Interpret *)

(** An event handler [E ~> M] defines a monad morphism
		[ctree E C ~> M] for any monad [M] with a loop operator. *)
Definition interp {E C M : Type -> Type}
           {FM : Functor M} {MM : Monad M} {IM : MonadIter M}
           (h : E ~> M) (h' : bool -> C ~> M) :
			ctree E C ~> M := fun R =>
			iter (fun t =>
				match observe t with
				| RetF r => ret (inr r)
				| ChoiceF b c k => fmap (fun x => inl (k x)) (h' b _ c)
				| VisF e k => fmap (fun x => inl (k x)) (h _ e)
				end).

Arguments interp {E C M FM MM IM} h h' [T].

(** Unfolding of [interp]. *)
Notation interp_ h h' t :=
  (match observe t with
  | RetF r => Ret r
	| VisF e k => bind (h _ e) (fun x => tauI (interp h h' (k x)))
	| ChoiceF b c k => bind (h' b _ c) (fun x => tauI (interp h h' (k x)))
  end)%function.

Notation interpE h := (interp h (fun b _ c => choice b c)).

(* TODO [step] should refold  *)
Lemma bind_choice {E C R S X} b (c : C X) (k : _ -> ctree E C R) (h : _ -> ctree E C S):
      (Choice b c k) >>= h ≅ Choice b c (fun x => k x >>= h).
Proof.
  step; cbn; constructor; intros ?.
  reflexivity.
Qed.

Section Interp.

  Context {E F C D : Type -> Type} {X : Type} `{C1 -< D}.
  Context {h : E ~> ctree F D} {h' : bool -> C ~> ctree F D}.

  (** Unfold lemma. *)
  Lemma unfold_interp (t : ctree E C X) :
    interp h h' t ≅ interp_ h h' t.
  Proof.
    unfold interp, Basics.iter, MonadIter_ctree.
    rewrite unfold_iter.
    destruct (observe t); cbn.
    - now rewrite ?bind_ret_l.
    - now rewrite bind_map, ?bind_ret_l.
    - now rewrite bind_map.
  Qed.

  (** ** [interp] and constructors *)

  (** These are specializations of [unfold_interp], which can be added as
    rewrite hints.
   *)

  Lemma interp_ret (x: X):
    interp h h' (Ret x) ≅ Ret x.
  Proof. now rewrite unfold_interp. Qed.

  Lemma interp_vis {U} (e: E U) (k: U -> ctree E C X) :
    interp h h' (Vis e k) ≅ x <- h _ e;; tauI (interp h h' (k x)).
  Proof. now rewrite unfold_interp. Qed.

  Lemma interp_choice {U} b (c : C U) (k: _ -> ctree E C X) :
    interp h h' (Choice b c k) ≅ x <- h' b _ c;; tauI (interp h h' (k x)).
  Proof. now rewrite unfold_interp. Qed.

  #[global] Instance interp_equ :
    Proper (equ eq ==> equ eq) (interp h h' (T := X)).
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

End Interp.

Lemma interp_tau {E F C X} `{C1 -< C} (h : E ~> ctree F C) (t: ctree E C X):
  interpE h (tauI t) ≅ tauI (tauI (interpE h t)).
Proof.
  rewrite unfold_interp. setoid_rewrite bind_choice. cbn.
  apply equ_ChoiceF. intro.
  rewrite bind_ret_l. reflexivity.
Qed.

Section Interp.

  Context {E F C D : Type -> Type} {X : Type} `{C1 -< D}.
  Context {h : E ~> ctree F D} {h' : bool -> C ~> ctree F D}.

  (* Note: this is specialized to [ctree F] as target monad. *)
  (* TODO: Incorporate Irene's work to generalize *)
  Lemma interp_bind {S} (t : ctree E C X) (k : X -> ctree _ _ S) :
    interp h h' (t >>= k) ≅ interp h h' t >>= (fun x => interp h h' (k x)).
  Proof.
    revert t.
    coinduction X' CIH.
    intros t.
    rewrite unfold_bind, (unfold_interp t).
    desobs t; cbn -[ebt].
    - now rewrite bind_ret_l.
    - rewrite interp_vis, bind_bind.
      upto_bind_eq.
      rewrite bind_tauI.
      now constructor.
    - rewrite interp_choice, bind_bind.
      upto_bind_eq.
      rewrite bind_tauI.
      now constructor.
  Qed.

End Interp.
