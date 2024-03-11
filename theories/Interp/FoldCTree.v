(* begin hide *)

From ExtLib Require Import
     Structures.Functor
     Structures.Monad.

From ITree Require Import
     Basics.Basics
     Core.Subevent.

From CTree Require Import
  CTree
  Eq
  Eq.Epsilon
  Eq.IterFacts
  Eq.SSimAlt
  Misc.Pure
  Fold.

Import CTreeNotations.
Open Scope ctree_scope.

(* end hide *)

(** Establishing generic results on [fold] is tricky: because it goes into
    a very generic monad [M], it requires some heavy axiomatization of this
    monad. Yoon et al.'s ICFP'22 develop the necessary tools to this end.
    For now, we simply specialize results to specific [M]s.
 *)

Section FoldCTree.

  Section With_Params.

    (** Specialization to [M = ctree F (B01 +' D)] *)
    Context {E F C D: Type -> Type} {X : Type}
      {h : E ~> ctree F (B01 +' D)} {g : bool -> B01 +' C ~> ctree F (B01 +' D)}.

    (** ** [interpE] and constructors *)

    (** Unfolding of [fold]. *)
    Notation fold_ h g t :=
      (match observe t with
       | RetF r => Ret r
	     | VisF e k => bind (h _ e) (fun x => Guard (fold h g (k x)))
	     | BrF b c k => bind (g b _ c) (fun x => Guard (fold h g (k x)))
       end)%function.

    (** Unfold lemma. *)
    Lemma unfold_fold (t: ctree E (B01 +' C) X):
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

    Lemma fold_vis {U} (e: E U) (k: U -> ctree E (B01 +' C) X) :
      fold h g (Vis e k) ≅ x <- h _ e;; Guard (fold h g (k x)).
    Proof. now rewrite unfold_fold. Qed.

    Lemma fold_br {U} b (c : (B01 +' C) U) (k: _ -> ctree E (B01 +' C) X) :
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

    (** Unfolding of [interp]. *)
    Notation interp_ h t :=
      (match observe t with
       | RetF r => Ret r
	     | VisF e k => bind (h _ e) (fun x => Guard (interp h (k x)))
	     | BrF b c k => bind (mbr b c) (fun x => Guard (interp h (k x)))
       end)%function.

    (** Unfold lemma. *)
    Lemma unfold_interp `{C -< D} (t: ctree E (B01 +' C) X):
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
      interp h (Ret x : ctree E (B01 +' C) X) ≅ Ret x.
    Proof. now rewrite unfold_interp. Qed.

    Lemma interp_vis `{C -< D} {U} (e: E U) (k: U -> ctree E (B01 +' C) X) :
      interp h (Vis e k) ≅ x <- h _ e;; Guard (interp h (k x)).
    Proof. now rewrite unfold_interp. Qed.

    Lemma interp_br `{C -< D} {U} b (c : (B01 +' C) U) (k: _ -> ctree E (B01 +' C) X) :
      interp h (Br b c k) ≅ x <- branch b c;; Guard (interp h (k x)).
    Proof. now rewrite unfold_interp. Qed.

    #[global] Instance interp_equ `{C -< D} {R} :
      Proper (equ R ==> equ R) (interp (B := C) (M := ctree F (B01 +' D)) h (T := X)).
    Proof.
      cbn.
      coinduction ? CIH.
      intros * EQ; step in EQ.
      rewrite 2 unfold_interp.
      inv EQ.
      - constructor; auto.
      - cbn -[ebt].
        upto_bind_eq.
        constructor; intros ?; auto.
      - cbn -[ebt].
        upto_bind_eq.
        constructor; intros ?; auto.
    Qed.

    (** Unfolding of [refine]. *)
    Notation refine_ g t :=
      (match observe t with
       | RetF r => Ret r
	     | VisF e k => bind (mtrigger e) (fun x => Guard (refine g (k x)))
	     | BrF b c k => bind (g b _ c) (fun x => Guard (refine g (k x)))
       end)%function.

    (** Unfold lemma. *)
    Lemma unfold_refine `{E -< F} (t: ctree E (B01 +' C) X):
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
      refine g (Ret x : ctree E (B01 +' C) X) ≅ Ret x.
    Proof. now rewrite unfold_refine. Qed.

    Lemma refine_vis `{E -< F} {U} (e: E U) (k: U -> ctree E (B01 +' C) X) :
      refine g (Vis e k) ≅ x <- trigger e;; Guard (refine g (k x)).
    Proof. now rewrite unfold_refine. Qed.

    Lemma refine_br `{E -< F} {U} b (c : (B01 +' C) U) (k: _ -> ctree E (B01 +' C) X) :
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
  Lemma interp_guard {E F C X} `{B1 -< C} (h' : E ~> ctree F (B01 +' C)) (t: ctree E (B01 +' C) X):
    interp h' (Guard t) ≅ Guard (Guard (interp h' t)).
  Proof.
    rewrite unfold_interp. setoid_rewrite bind_br.
    apply equ_BrF. intro.
    rewrite bind_ret_l. reflexivity.
  Qed.

  Section FoldBind.

    Context {E F C D: Type -> Type} {X : Type}.

    Lemma fold_bind (h : E ~> ctree F (B01 +' D)) (g : bool -> (B01 +' C) ~> ctree F (B01 +' D)) {S} (t : ctree E (B01 +' C) X) (k : X -> ctree _ _ S) :
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

    Lemma interp_bind (h : E ~> ctree F (B01 +' D)) `{C -< D} {S} (t : ctree E (B01 +' C) X) (k : X -> ctree _ _ S) :
      interp h (t >>= k) ≅ interp h t >>= (fun x => interp h (k x)).
    Proof.
      unfold interp.
      now rewrite fold_bind.
    Qed.

    Lemma refine_bind (g : bool -> (B01 +' C) ~> ctree F (B01 +' D)) `{E -< F} {S} (t : ctree E (B01 +' C) X) (k : X -> ctree _ _ S) :
      refine g (t >>= k) ≅ refine g t >>= (fun x => refine g (k x)).
    Proof.
      unfold refine.
      now rewrite fold_bind.
    Qed.

  End FoldBind.

End FoldCTree.

(*|
Counter-example showing that interp does not preserve sbisim in the general case.
|*)

Module CounterExample.

  Inductive VoidE : Type -> Type :=
  | voidE : VoidE void.

  Notation B012 := (B01 +' B2).
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

End CounterExample.

Section epsilon_interp_theory.

  Lemma interp_productive {E C F X} (h : E ~> ctree F (B01 +' C)) : forall (t : ctree E (B01 +' C) X),
      productive (interp h t) -> productive t.
  Proof.
    intros. inversion H;
      subst;
      rewrite unfold_interp in EQ;
      rewrite (ctree_eta t);
      destruct (observe t) eqn:?;
        (try destruct vis);
      (try step in EQ; inv EQ);
      try now econstructor.
  Qed.

  Lemma epsilon_interp : forall {E C F X}
                          (h : E ~> ctree F (B01 +' C)) (t t' : ctree E (B01 +' C) X),
      epsilon t t' -> epsilon (interp h t) (interp h t').
  Proof.
    intros. red in H. setoid_rewrite (ctree_eta t). setoid_rewrite (ctree_eta t').
    genobs t ot. genobs t' ot'. clear t Heqot t' Heqot'.
    induction H.
    - constructor. rewrite H. reflexivity.
    - rewrite unfold_interp. cbn. setoid_rewrite bind_br.
      apply EpsilonBr with (x := x). rewrite bind_ret_l.
      simpl. eapply EpsilonBr with (x:=tt). apply IHepsilon_.
  Qed.

End epsilon_interp_theory.

Lemma interp_ret_inv {E F B X} (h : E ~> ctree F (B01 +' B)) :
  forall (t : ctree E (B01 +' B) X) r,
  interp h t ≅ Ret r -> t ≅ Ret r.
Proof.
  intros. setoid_rewrite (ctree_eta t) in H. setoid_rewrite (ctree_eta t).
  destruct (observe t) eqn:?.
  - rewrite interp_ret in H. step in H. inv H. reflexivity.
  - rewrite interp_vis in H. apply ret_equ_bind in H as (? & ? & ?). step in H0. inv H0.
  - rewrite interp_br in H. setoid_rewrite bind_br in H. step in H. inv H.
Qed.

Lemma bind_guard_r {E B X Y} : forall (t : ctree E (B01 +' B) X) (k : X -> ctree E (B01 +' B) Y),
  x <- t;; Guard (k x) ≅ x <- (x <- t;; Guard (Ret x));; k x.
Proof.
  intros. rewrite bind_bind. upto_bind_eq. rewrite bind_guard. setoid_rewrite bind_ret_l. reflexivity.
Qed.

Lemma trans_val_interp {E F B X}
  (h : E ~> ctree F (B01 +' B)) :
  forall (t u : ctree E (B01 +' B) X) (v : X),
  trans (val v) t u ->
  trans (val v) (interp h t) stuckD.
Proof.
  intros.
  apply trans_val_epsilon in H as []. subs.
  eapply epsilon_interp in H.
  eapply epsilon_trans; [apply H |].
  rewrite interp_ret. etrans.
Qed.

Lemma trans_tau_interp {E F B X}
  (h : E ~> ctree F (B01 +' B)) :
  forall (t u : ctree E (B01 +' B) X),
  trans tau t u ->
  trans tau (interp h t) (Guard (interp h u)).
Proof.
  intros.
  apply trans_tau_epsilon in H as (? & ? & ? & ? & ? & ?). subs.
  eapply epsilon_interp in H.
  eapply epsilon_trans; [apply H |].
  rewrite interp_br, bind_branch.
  apply (trans_brS _ (fun x3 : x => Guard (interp h (x1 x3)))).
Qed.

Lemma trans_obs_interp_step {E F B X Y}
  (h : E ~> ctree F (B01 +' B)) :
  forall (t u : ctree E (B01 +' B) X) u' (e : E Y) x l,
  trans (obs e x) t u ->
  trans l (h _ e) u' ->
  ~ is_val l ->
  epsilon_det u' (Ret x) ->
  trans l (interp h t) (u';; Guard (interp h u)).
Proof.
  intros.
  apply trans_obs_epsilon in H as (? & ? & ?).
  setoid_rewrite H3. clear H3.
  apply epsilon_interp with (h := h) in H.
  rewrite interp_vis in H.
  eapply epsilon_trans. apply H.
  epose proof (epsilon_det_bind_ret_l_equ u' (fun x => Guard (interp h (x0 x))) x H2).
  rewrite <- H3; auto.
  apply trans_bind_l; auto.
Qed.

Lemma trans_obs_interp_pure {E F B X Y}
  (h : E ~> ctree F (B01 +' B)) :
  forall (t u : ctree E (B01 +' B) X) (e : E Y) x,
  trans (obs e x) t u ->
  trans (val x) (h _ e) stuckD ->
  epsilon (interp h t) (Guard (interp h u)).
Proof.
  intros t u e x TR TRh.
  apply trans_obs_epsilon in TR as (k & EPS & ?). subs.
  apply epsilon_interp with (h := h) in EPS.
  rewrite interp_vis in EPS.
  apply trans_val_epsilon in TRh as [EPSh _].
  eapply epsilon_bind_ret in EPSh.
  apply (epsilon_transitive _ _ _ EPS EPSh).
Qed.
