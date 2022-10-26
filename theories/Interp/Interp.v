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
     CTreeDefinitions
     CTree.

Import CTreeNotations.
Open Scope ctree_scope.
Import CTreeNotations.

(* end hide *)

Definition translateF {E F C R} (h : E ~> F) (rec: ctree E C R -> ctree F C R) (t : ctreeF E C R _) : ctree F C R  :=
	match t with
		| RetF x => Ret x
		| VisF e k => Vis (h _ e) (fun x => rec (k x))
		| BrF b n k => Br b n (fun x => rec (k x))
	end.

Definition translate {E F C} (h : E ~> F) : ctree E C ~> ctree F C
	:= fun R => cofix translate_ t := translateF h translate_ (observe t).

Arguments translate {E F C} h [T].

(** ** Interpret *)
(** An event handler [E ~> M] defines a monad morphism
[ctree E C ~> M] for any monad [M] with a loop operator. *)

Definition interpE {E C M : Type -> Type} {FoM: MonadBr C M}
	   {FM : Functor M} {MM : Monad M} {IM : MonadIter M} 
	   (h : E ~> M) :
			ctree E C ~> M := fun R =>
			iter (fun t =>
				match observe t with
				| RetF r => ret (inr r)
				| @BrF _ _ _ _ b _ n k =>
                                    bind (mbr b n) (fun x => ret (inl (k x)))
				| VisF e k => fmap (fun x => inl (k x)) (h _ e)
				end).
Arguments interpE {E C M FoM FM MM IM} h [T].

(** Unfolding of [interpE]. *)
Notation interpE_ h t :=
  (match observe t with
   | RetF r => Ret r
   | VisF e k => bind (h _ e) (fun x => Guard (interpE h (k x)))
   | BrF b c k => bind (mbr b c) (fun x => Guard (interpE h (k x)))
  end)%function.

(* TODO [step] should refold  *)
Lemma bind_br {E C R S X} b (c : C X) (k : _ -> ctree E C R) (h : _ -> ctree E C S):
      (Br b c k) >>= h ≅ Br b c (fun x => k x >>= h).
Proof.
  step; cbn; constructor; intros ?.
  reflexivity.
Qed.

Section InterpE.

  Context {E F C : Type -> Type} {X : Type} `{B1 -< C}
          {h : E ~> ctree F C}.

  (** ** [interpE] and constructors *)

  (** These are specializations of [unfold_interpE], which can be added as
      rewrite hints.
   *)

  (** Unfold lemma. *)
  Lemma unfold_interpE (t: ctree E C X):
    interpE h t ≅ interpE_ h t.
  Proof.
    unfold interpE, Basics.iter, MonadIter_ctree, mbr, MonadBr_ctree, CTree.branch.
    rewrite unfold_iter.
    destruct (observe t); cbn.
    - now rewrite ?bind_ret_l.
    - now rewrite bind_map, ?bind_ret_l.
    - do 3 rewrite bind_br.
      apply br_equ; intros.
      do 3 rewrite bind_ret_l.
      apply br_equ; intros _.
      reflexivity.
  Qed.

  Lemma interpE_ret (x: X):
    interpE h (Ret x) ≅ Ret x.
  Proof. now rewrite unfold_interpE. Qed.

  Lemma interpE_vis {U} (e: E U) (k: U -> ctree E C X) :
    interpE h (Vis e k) ≅ x <- h _ e;; Guard (interpE h (k x)).
  Proof. now rewrite unfold_interpE. Qed.

  Lemma interpE_br {U} b (c : C U) (k: _ -> ctree E C X) :
    interpE h (Br b c k) ≅ x <- mbr b c;; Guard (interpE h (k x)).
  Proof. now rewrite unfold_interpE. Qed.

  #[global] Instance interpE_equ :
    Proper (equ eq ==> equ eq) (interpE h (T := X)).
  Proof.
    cbn.
    coinduction ? CIH.
    intros * EQ; step in EQ.
    rewrite 2 unfold_interpE.
    inv EQ; auto.
    - cbn -[ebt].
      upto_bind_eq.
      constructor; intros ?; auto.
    - cbn -[ebt].
      upto_bind_eq.
      constructor; intros ?; auto.
  Qed.

End InterpE.

Lemma interpE_tau {E F C X} `{B1 -< C} {h : E ~> ctree F C} (t: ctree E C X):
  interpE h (Guard t) ≅ Guard (Guard (interpE h t)).
Proof.
  rewrite unfold_interpE. setoid_rewrite bind_br.
  apply equ_BrF. intro.
  rewrite bind_ret_l. reflexivity.
Qed.

Section InterpE.

  Context {E F C : Type -> Type} {X : Type} `{B1 -< C}.
  Context {h : E ~> ctree F C}.

  (* Note: this is specialized to [ctree F] as target monad. *)
  (* TODO: Incorporate Irene's work to generalize *)
  Lemma interpE_bind {S} (t : ctree E C X) (k : X -> ctree _ _ S) :
    interpE h (t >>= k) ≅ interpE h t >>= (fun x => interpE h (k x)).
  Proof.
    revert t.
    coinduction X' CIH.
    intros t.
    rewrite unfold_bind, (unfold_interpE t).
    desobs t; cbn -[ebt].
    - now rewrite bind_ret_l.
    - rewrite interpE_vis, bind_bind.
      upto_bind_eq.
      rewrite bind_guard.
      now constructor.
    - rewrite interpE_br, bind_bind.
      upto_bind_eq.
      rewrite bind_guard.
      now constructor.
  Qed.

End InterpE.

(*| Counter-example showing that interpE does not preserve sbisim in the general case. |*)

Inductive VoidE : Type -> Type :=
| voidE : VoidE void.

Notation B012 := (B0 +' B1 +' B2).
#[local] Definition t1 := Ret 1 : ctree VoidE B012 nat.
#[local] Definition t2 := brD2 (Ret 1) (x <- trigger voidE;; match x : void with end) : ctree VoidE B012 nat.

Goal t1 ~ t2.
Proof.
  unfold t1, t2.
  rewrite brD2_commut.
  rewrite brD2_is_stuck. reflexivity.
  red. intros. intro. inv_trans.  destruct x.
Qed.

#[local] Definition h : VoidE ~> ctree VoidE B012.
Proof.
  intros. destruct H. exact (Step stuckD).
Defined.

Example interpE_sbsisim_counterexample : ~ (interpE h t1 ~ interpE h t2).
Proof.
  red. intros. unfold t2 in H.
  playR in H.
  rewrite unfold_interpE. cbn. setoid_rewrite bind_br.
  eapply trans_brD with (x := false).
  2: { rewrite bind_ret_l. reflexivity. }
  apply trans_guard. setoid_rewrite unfold_interpE. cbn. rewrite bind_step. etrans.
  rewrite unfold_interpE in TR. unfold t1, h in TR. cbn in TR. inv_trans.
Qed.

