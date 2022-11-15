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

(* end hide *)

(** ** Fold *)

(** The most general shape of fold over the structure takes two parameters:
    - an event handler [E ~> M] describing how to implement events
    - a local scheduler [B ~> M] describing valid branches
    and defines for it a monad morphism [ctree E B ~> M]
    for any monad [M] with a loop operator. *)
Definition fold {E B M : Type -> Type}
  {FM : Functor M} {MM : Monad M} {IM : MonadIter M}
  (h : E ~> M) (g : bool -> B ~> M) :
	ctree E B ~> M :=
  fun R =>
		iter (fun t =>
				    match observe t with
				    | RetF r => ret (inr r)
				    | BrF b c k => fmap (fun x => inl (k x)) (g b _ c)
				    | VisF e k => fmap (fun x => inl (k x)) (h _ e)
				    end).

Arguments fold {E B M FM MM IM} h g [T].

(** Unfolding of [fold]. *)
Notation fold_ h g t :=
  (match observe t with
  | RetF r => Ret r
	| VisF e k => bind (h _ e) (fun x => Guard (fold h g (k x)))
	| BrF b c k => bind (g b _ c) (fun x => Guard (fold h g (k x)))
  end)%function.

(** Implementing simultaneously external events while refining
    the internal non-determinism is somewhat uncommon.
    We hence also define two particular case:
    - [interp] only implements external events, and re-emit branches
    without cutting them (internalized in [M] via [MonadBr]
    - [refine] only refines the internal branches,
    and re-emit external events (internalized in [M] via [MonadTrigger]
  *)

Definition interp {E B M : Type -> Type}
  {FM : Functor M} {MM : Monad M} {IM : MonadIter M} {BM : MonadBr B M}
  (h : E ~> M) := fold h (fun b _ c => mbr b c).

Arguments interp {E B M FM MM IM BM} h [T].

(** Unfolding of [interp]. *)
Notation interp_ h t :=
  (match observe t with
  | RetF r => Ret r
	| VisF e k => bind (h _ e) (fun x => Guard (interp h (k x)))
	| BrF b c k => bind (mbr b c) (fun x => Guard (interp h (k x)))
  end)%function.

Definition refine {E B M : Type -> Type}
  {FM : Functor M} {MM : Monad M} {IM : MonadIter M} {TM : MonadTrigger E M}
  (g : bool -> B ~> M) := fold (fun _ e => mtrigger e) g.

Arguments refine {E B M FM MM IM TM} g [T].

(** Unfolding of [refine]. *)
Notation refine_ g t :=
  (match observe t with
  | RetF r => Ret r
	| VisF e k => bind (mtrigger e) (fun x => Guard (refine g (k x)))
	| BrF b c k => bind (g b _ c) (fun x => Guard (refine g (k x)))
  end)%function.

Definition translateF {E F C R}
  (h : E ~> F)
  (rec: ctree E C R -> ctree F C R)
  (t : ctreeF E C R _) : ctree F C R  :=
	match t with
	| RetF x => Ret x
	| VisF e k => Vis (h _ e) (fun x => rec (k x))
	| BrF b c k => Br b c (fun x => rec (k x))
	end.

Definition translate {E F C} (h : E ~> F) : ctree E C ~> ctree F C
	:= fun R => cofix translate_ t := translateF h translate_ (observe t).

Arguments translate {E F C} h [T].

(** Establishing generic results on [fold] is tricky: because it goes into
    a very generic monad [M], it requires some heavy axiomatization of this
    monad. Yoon et al.'s ICFP'22 develop the necessary tools to this end.
    For now, we simply specialize results to specific [M]s.
 *)
Section FoldCTree.

  Section With_Params.

    (** Specialization to [M = ctree F D] *)
    Context {E F C D: Type -> Type} {X : Type} `{B1 -< D}
      {h : E ~> ctree F D} {g : bool -> C ~> ctree F D}.

    (** ** [interpE] and constructors *)

    (** Unfold lemma. *)
    Lemma unfold_fold (t: ctree E C X):
      fold h g t ≅ fold_ h g t.
    Proof.
      unfold fold, Basics.iter, MonadIter_ctree, mbr, MonadBr_ctree, CTree.branch.
      rewrite unfold_iter.
      destruct (observe t); cbn.
      - now rewrite ?bind_ret_l.
      - now rewrite bind_map, ?bind_ret_l.
      - now rewrite bind_map.
    Qed.

    Lemma fold_ret (x: X):
      fold h g (Ret x) ≅ Ret x.
    Proof. now rewrite unfold_fold. Qed.

    Lemma fold_vis {U} (e: E U) (k: U -> ctree E C X) :
      fold h g (Vis e k) ≅ x <- h _ e;; Guard (fold h g (k x)).
    Proof. now rewrite unfold_fold. Qed.

    Lemma fold_br {U} b (c : C U) (k: _ -> ctree E C X) :
      fold h g (Br b c k) ≅ x <- g b _ c;; Guard (fold h g (k x)).
    Proof. now rewrite unfold_fold. Qed.

    #[global] Instance fold_equ :
      Proper (equ eq ==> equ eq) (fold h g (T := X)).
    Proof.
      cbn.
      coinduction ? CIH.
      intros * EQ; step in EQ.
      rewrite 2 unfold_fold.
      inv EQ; auto.
      - cbn -[ebt].
        upto_bind_eq.
        constructor; intros ?; auto.
      - cbn -[ebt].
        upto_bind_eq.
        constructor; intros ?; auto.
    Qed.

    (** Unfold lemma. *)
    Lemma unfold_interp `{C -< D} (t: ctree E C X):
      interp h t ≅ interp_ h t.
    Proof.
      unfold interp,fold, Basics.iter, MonadIter_ctree, mbr, MonadBr_ctree, CTree.branch.
      rewrite unfold_iter.
      destruct (observe t); cbn.
      - now rewrite ?bind_ret_l.
      - now rewrite bind_map, ?bind_ret_l.
      - now rewrite bind_map.
    Qed.

    Lemma interp_ret `{C -< D} (x: X):
      interp h (Ret x : ctree E C X) ≅ Ret x.
    Proof. now rewrite unfold_interp. Qed.

    Lemma interp_vis `{C -< D} {U} (e: E U) (k: U -> ctree E C X) :
      interp h (Vis e k) ≅ x <- h _ e;; Guard (interp h (k x)).
    Proof. now rewrite unfold_interp. Qed.

    Lemma interp_br `{C -< D} {U} b (c : C U) (k: _ -> ctree E C X) :
      interp h (Br b c k) ≅ x <- branch b c;; Guard (interp h (k x)).
    Proof. now rewrite unfold_interp. Qed.

    #[global] Instance interp_equ `{C -< D} :
      Proper (equ eq ==> equ eq) (interp (B := C) (M := ctree F D) h (T := X)).
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

    (** Unfold lemma. *)
    Lemma unfold_refine `{E -< F} (t: ctree E C X):
      refine g t ≅ refine_ g t.
    Proof.
      unfold refine,fold, Basics.iter, MonadIter_ctree, mbr, MonadBr_ctree, CTree.branch.
      rewrite unfold_iter.
      destruct (observe t); cbn.
      - now rewrite ?bind_ret_l.
      - now rewrite bind_map, ?bind_ret_l.
      - now rewrite bind_map.
    Qed.

    Lemma refine_ret `{E -< F} (x: X):
      refine g (Ret x : ctree E C X) ≅ Ret x.
    Proof. now rewrite unfold_refine. Qed.

    Lemma refine_vis `{E -< F} {U} (e: E U) (k: U -> ctree E C X) :
      refine g (Vis e k) ≅ x <- trigger e;; Guard (refine g (k x)).
    Proof. now rewrite unfold_refine. Qed.

    Lemma refine_br `{E -< F} {U} b (c : C U) (k: _ -> ctree E C X) :
      refine g (Br b c k) ≅ x <- g b _ c;; Guard (refine g (k x)).
    Proof. now rewrite unfold_refine. Qed.

    #[global] Instance refine_equ `{E -< F} :
      Proper (equ eq ==> equ eq) (refine (E := E) (M := ctree F _) g (T := X)).
    Proof.
      cbn.
      coinduction ? CIH.
      intros * EQ; step in EQ.
      rewrite 2 unfold_refine.
      inv EQ; auto.
      - cbn -[ebt].
        upto_bind_eq.
        constructor; intros ?; auto.
      - cbn -[ebt].
        upto_bind_eq.
        constructor; intros ?; auto.
    Qed.

  End With_Params.

  (** The following fact specialises further [interp] so that events are implemented into ctrees whose index for branches is unchanged.
      Most likely, this is the case in all applications.
   *)
  Lemma interp_guard {E F C X} `{B1 -< C} (h' : E ~> ctree F C) (t: ctree E C X):
    interp h' (Guard t) ≅ Guard (Guard (interp h' t)).
  Proof.
    rewrite unfold_interp. setoid_rewrite bind_br.
    apply equ_BrF. intro.
    rewrite bind_ret_l. reflexivity.
  Qed.

  Section InterpBind.

    Context {E F C D: Type -> Type} {X : Type} `{B1 -< D}.

    Lemma fold_bind (h : E ~> ctree F D) (g : bool -> C ~> ctree F D) {S} (t : ctree E C X) (k : X -> ctree _ _ S) :
      fold h g (t >>= k) ≅ fold h g t >>= (fun x => fold h g (k x)).
    Proof.
      revert t.
      coinduction X' CIH.
      intros t.
      rewrite unfold_bind, (unfold_fold t).
      desobs t; cbn -[ebt].
      - now rewrite bind_ret_l.
      - rewrite fold_vis, bind_bind.
        upto_bind_eq.
        rewrite bind_guard.
        now constructor.
      - rewrite fold_br, bind_bind.
        upto_bind_eq.
        rewrite bind_guard.
        now constructor.
    Qed.

    Lemma interp_bind (h : E ~> ctree F D) `{C -< D} {S} (t : ctree E C X) (k : X -> ctree _ _ S) :
      interp h (t >>= k) ≅ interp h t >>= (fun x => interp h (k x)).
    Proof.
      unfold interp.
      now rewrite fold_bind.
    Qed.

    Lemma refine_bind (g : bool -> C ~> ctree F D) `{E -< F} {S} (t : ctree E C X) (k : X -> ctree _ _ S) :
      refine g (t >>= k) ≅ refine g t >>= (fun x => refine g (k x)).
    Proof.
      unfold refine.
      now rewrite fold_bind.
    Qed.

  End InterpBind.

End FoldCTree.

(*|
Counter-example showing that interpE does not preserve sbisim in the general case.
|*)

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

Example interpE_sbsisim_counterexample : ~ (interp h t1 ~ interp h t2).
Proof.
  red. intros. unfold t2 in H.
  playR in H.
  rewrite unfold_interp. cbn. setoid_rewrite bind_br.
  eapply trans_brD with (x := false).
  2: { rewrite bind_ret_l. reflexivity. }
  apply trans_guard. setoid_rewrite unfold_interp. cbn. rewrite bind_step. etrans.
  rewrite unfold_interp in TR. unfold t1, h in TR. cbn in TR. inv_trans.
Qed.
