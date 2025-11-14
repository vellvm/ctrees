(* begin hide *)
Unset Universe Checking.

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
      {h : E ~> ctree F D} {g : C ~> ctree F D}.

    (** ** [interpE] and constructors *)
    Definition fold_ctree : forall [T], ctree E C T -> ctree F D T :=
      fold h g.
      (* fold (mstuck (M := ctree F D)) (mstep (M := ctree F D)) h (mbr (M := ctree F D)) g. *)
      (* fold (fun T => Stuck: ctree F D T) (Step (Ret tt)) h g. *)

    (** Unfolding of [fold]. *)
    Notation fold_ctree_ t :=
      (match observe t with
       | RetF r => Ret r
       | StuckF => Stuck
       | GuardF t => Guard (fold_ctree t)
       | StepF t => Step (Guard (fold_ctree t))
	     | VisF e k => CTree.bind (h _ e) (fun x => Guard (fold_ctree (k x)))
	     | BrF c k => CTree.bind (g _ c) (fun x => Guard (fold_ctree (k x)))
       end)%function.

    (** Unfold lemma. *)
    Lemma unfold_fold_ctree (t: ctree E C X):
      fold_ctree t ≅ fold_ctree_ t.
    Proof.
      unfold fold_ctree, fold, Basics.iter, MonadIter_ctree, mbr, MonadBr_ctree, CTree.branch.
      rewrite unfold_iter.
      destruct (observe t); cbn.
      - now rewrite ?bind_ret_l.
      - now rewrite ?bind_stuck.
      - setoid_rewrite bind_step.
        setoid_rewrite bind_step.
        setoid_rewrite bind_ret_l.
        now setoid_rewrite bind_ret_l.
      - now rewrite ?bind_ret_l.
      - now rewrite bind_map, ?bind_ret_l.
      - now rewrite bind_map.
    Qed.

    Lemma fold_ctree_ret (x: X):
      fold_ctree (Ret x) ≅ Ret x.
    Proof. now rewrite unfold_fold_ctree. Qed.

    Lemma fold_ctree_vis {U} (e: E U) (k: U -> ctree E C X) :
      fold_ctree (Vis e k) ≅ x <- h _ e;; Guard (fold_ctree (k x)).
    Proof. now rewrite unfold_fold_ctree. Qed.

    Lemma fold_ctree_stuck :
      fold_ctree (Stuck : ctree E C X) ≅ Stuck.
    Proof. now rewrite unfold_fold_ctree. Qed.

    Lemma fold_ctree_guard (t : ctree E C X) :
      fold_ctree (Guard t) ≅ Guard (fold_ctree t).
    Proof. now rewrite unfold_fold_ctree. Qed.

    Lemma fold_ctree_step (t : ctree E C X) :
      fold_ctree (Step t) ≅ Step (Guard (fold_ctree t)).
    Proof. now rewrite unfold_fold_ctree. Qed.

    Lemma fold_ctree_br {U} (c : C U) (k: _ -> ctree E C X) :
      fold_ctree (Br c k) ≅ x <- g _ c;; Guard (fold_ctree (k x)).
    Proof. now rewrite unfold_fold_ctree. Qed.

    #[global] Instance fold_ctree_equ :
      Proper (equ eq ==> equ eq) (fold_ctree (T := X)).
    Proof.
      cbn.
      coinduction r CIH.
      intros * EQ; step in EQ.
      rewrite 2 unfold_fold_ctree.
      inv EQ; auto.
      - constructor; eauto.
      - constructor; eauto.
        step; constructor; eauto.
      - upto_bind_eq.
        intros ?; constructor; auto.
      - upto_bind_eq.
        intros ?; constructor; auto.
    Qed.

    (** Unfolding of [interp]. *)

    Notation interp_ h t :=
      (match observe t with
       | RetF r => Ret r
       | StuckF => Stuck
       | GuardF t => Guard (interp h t)
       | StepF  t => Step  (Guard (interp h t))
	     | VisF e k => bind (h _ e) (fun x => Guard (interp h (k x)))
	     | BrF c k => bind (mbr _ c) (fun x => Guard (interp h (k x)))
       end)%function.

    (** Unfold lemma. *)
    Lemma unfold_interp `{C -< D} (t: ctree E C X):
      interp h t ≅ interp_ h t.
    Proof.
      unfold interp,fold, Basics.iter, MonadIter_ctree, mbr, MonadBr_ctree, CTree.branch.
      rewrite unfold_iter.
      destruct (observe t); cbn.
      - now rewrite ?bind_ret_l.
      - now rewrite bind_stuck.
      - repeat setoid_rewrite bind_step.
        step; constructor.
        now rewrite ?bind_ret_l.
      - now rewrite bind_ret_l.
      - now rewrite bind_map, ?bind_ret_l.
      - now rewrite bind_map.
    Qed.

    Lemma interp_ret `{C -< D} (x: X):
      interp h (Ret x : ctree E C X) ≅ Ret x.
    Proof. now rewrite unfold_interp. Qed.

    Lemma interp_stuck `{C -< D} :
      interp h (Stuck : ctree E C X) ≅ Stuck.
    Proof. now rewrite unfold_interp. Qed.

    Lemma interp_vis `{C -< D} {U} (e: E U) (k: U -> ctree E C X) :
      interp h (Vis e k) ≅ x <- h _ e;; Guard (interp h (k x)).
    Proof. now rewrite unfold_interp. Qed.

    Lemma interp_guard `{C -< D} (t : ctree E C X) :
      interp h (Guard t) ≅ Guard (interp h t).
    Proof. now rewrite unfold_interp. Qed.

    Lemma interp_step `{C -< D} (t : ctree E C X) :
      interp h (Step t) ≅ Step (Guard (interp h t)).
    Proof. now rewrite unfold_interp. Qed.

    Lemma interp_br `{C -< D} {U} (c : C U) (k: _ -> ctree E C X) :
      interp h (Br c k) ≅ x <- branch c;; Guard (interp h (k x)).
    Proof. now rewrite unfold_interp. Qed.

    Lemma interp_br' `{C -< D} {U} (c : C U) (k: _ -> ctree E C X) :
      interp h (Br c k) ≅ br c (fun x => Guard (interp h (k x))).
    Proof. rewrite interp_br; unfold branch; rewrite bind_br; setoid_rewrite bind_ret_l.
           reflexivity.
    Qed.

    #[global] Instance interp_equ `{C -< D} {R} :
      Proper (equ R ==> equ R) (interp (B := C) (M := ctree F D) h (T := X)).
    Proof.
      cbn.
      coinduction r CIH.
      intros * EQ; step in EQ.
      rewrite 2 unfold_interp.
      inv EQ.
      - constructor; auto.
      - constructor; auto.
      - constructor; auto.
      - constructor; step; constructor; auto.
      - upto_bind_eq; intros.
        constructor; eauto.
      - upto_bind_eq; intros.
        constructor; eauto.
    Qed.

    (** Unfolding of [refine]. *)
    Notation refine_ g t :=
      (match observe t with
       | RetF r => Ret r
       | StuckF => Stuck
       | GuardF t => Guard (refine g t)
       | StepF  t => Step  (Guard (refine g t))
		   | VisF e k => bind (mtrigger e) (fun x => Guard (refine g (k x)))
	     | BrF c k => bind (g _ c) (fun x => Guard (refine g (k x)))
       end)%function.

    (** Unfold lemma. *)
    Lemma unfold_refine `{E -< F} (t: ctree E C X):
      refine g t ≅ refine_ g t.
    Proof.
      unfold refine,fold, Basics.iter, MonadIter_ctree, mbr, MonadBr_ctree, CTree.branch.
      rewrite unfold_iter.
      destruct (observe t); cbn.
      - now rewrite ?bind_ret_l.
      - now rewrite bind_stuck.
      - repeat setoid_rewrite bind_step.
        step; constructor.
        now rewrite ?bind_ret_l.
      - now rewrite bind_ret_l.
      - now rewrite bind_map, ?bind_ret_l.
      - now rewrite bind_map.
    Qed.

    Lemma refine_ret `{E -< F} (x: X):
      refine g (Ret x : ctree E C X) ≅ Ret x.
    Proof. now rewrite unfold_refine. Qed.

    Lemma refine_vis `{E -< F} {U} (e: E U) (k: U -> ctree E C X) :
      refine g (Vis e k) ≅ x <- trigger e;; Guard (refine g (k x)).
    Proof. now rewrite unfold_refine. Qed.

    Lemma refine_trigger `{E -< F} (e: E X) :
        refine g (trigger e : ctree E C X) ~ (trigger e : ctree F D X).
    Proof.
      rewrite unfold_refine; cbn.
      setoid_rewrite sb_guard.
      setoid_rewrite refine_ret.
      now rewrite bind_ret_r.
    Qed.

    Lemma refine_guard `{E -< F} (t: ctree E C X) :
      refine g (Guard t) ≅ Guard (refine g t).
    Proof. now rewrite unfold_refine. Qed.

    Lemma refine_step `{E -< F} (t: ctree E C X) :
      refine g (Step t) ≅ Step (Guard (refine g t)).
    Proof. now rewrite unfold_refine. Qed.

    Lemma refine_br `{E -< F} {U} (c : C U) (k: _ -> ctree E C X) :
      refine g (Br c k) ≅ x <- g _ c;; Guard (refine g (k x)).
    Proof. now rewrite unfold_refine. Qed.

    #[global] Instance refine_equ `{E -< F} :
      Proper (equ eq ==> equ eq) (refine (E := E) (M := ctree F _) g (T := X)).
    Proof.
      cbn.
      coinduction r CIH.
      intros * EQ; step in EQ.
      rewrite 2 unfold_refine.
      inv EQ; try constructor; auto.
      - step; constructor; auto.
      - upto_bind_eq.
        intros ?; constructor; auto.
      - upto_bind_eq.
        intros ?; constructor; auto.
    Qed.

  End With_Params.

  Arguments fold_ctree {E F C D} h g [T].

  Section FoldBind.

    Context {E F C D: Type -> Type} {X : Type}.

    Lemma fold_ctree_bind (h : E ~> ctree F D) (g : C ~> ctree F D) {S} (t : ctree E C X) (k : X -> ctree _ _ S) :
      fold_ctree h g (t >>= k) ≅ fold_ctree h g t >>= (fun x => fold_ctree h g (k x)).
    Proof.
      revert t.
      coinduction r CIH.
      intros t.
      rewrite unfold_bind, (unfold_fold_ctree t).
      desobs t.
      - now rewrite bind_ret_l.
      - now rewrite bind_stuck, fold_ctree_stuck.
      - rewrite bind_step, fold_ctree_step, bind_guard.
        constructor; step; constructor.
        auto.
      - rewrite bind_guard, fold_ctree_guard.
        constructor; auto.
      - rewrite fold_ctree_vis, bind_bind.
        upto_bind_eq; intros.
        rewrite bind_guard.
        now constructor.
      - rewrite fold_ctree_br, bind_bind.
        upto_bind_eq; intros.
        rewrite bind_guard.
        now constructor.
    Qed.

    Lemma interp_bind (h : E ~> ctree F D) `{C -< D} {S} (t : ctree E C X) (k : X -> ctree _ _ S) :
      interp h (t >>= k) ≅ interp h t >>= (fun x => interp h (k x)).
    Proof.
      unfold interp.
      now setoid_rewrite fold_ctree_bind.
    Qed.

    Lemma refine_bind (g : C ~> ctree F D) `{E -< F} {S} (t : ctree E C X) (k : X -> ctree _ _ S) :
      refine g (t >>= k) ≅ refine g t >>= (fun x => refine g (k x)).
    Proof.
      unfold refine.
      now setoid_rewrite fold_ctree_bind.
    Qed.

  End FoldBind.

End FoldCTree.

(*|
Counter-example showing that interp does not preserve sbisim in the general case.
|*)

Module CounterExample.

  Inductive VoidE : Type -> Type :=
  | voidE : VoidE void.

  (* Notation B012 := (B01 +' B2). *)
  #[local] Definition t1 := Ret 1 : ctree VoidE B2 nat.
  #[local] Definition t2 := br2 (Ret 1) (x <- trigger voidE;; match x : void with end) : ctree VoidE B2 nat.

  Goal t1 ~ t2.
  Proof.
    unfold t1, t2.
    rewrite br2_commut.
    rewrite br2_is_stuck. reflexivity.
    red. intros. intro. inv_trans.  destruct x.
  Qed.

  #[local] Definition h : VoidE ~> ctree VoidE B2.
  Proof.
    intros. destruct X. exact (Step Stuck).
  Defined.

  Example interpE_sbsisim_counterexample : ~ (interp h t1 ~ interp h t2).
  Proof.
    red. intros. unfold t2 in H.
    playR in H.
    rewrite unfold_interp. cbn. setoid_rewrite bind_br.
    eapply trans_br with (x := false).
    2: { rewrite bind_ret_l. reflexivity. }
    apply trans_guard. setoid_rewrite unfold_interp. cbn. rewrite bind_step. etrans.
    rewrite unfold_interp in TR. unfold t1, h in TR. cbn in TR. inv_trans.
  Qed.

End CounterExample.

Section epsilon_interp_theory.

  Lemma interp_productive {E C F X} (h : E ~> ctree F C) : forall (t : ctree E C X),
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
                           (h : E ~> ctree F C) (t t' : ctree E C X),
      epsilon t t' -> epsilon (interp h t) (interp h t').
  Proof.
    intros. red in H. setoid_rewrite (ctree_eta t). setoid_rewrite (ctree_eta t').
    genobs t ot. genobs t' ot'. clear t Heqot t' Heqot'.
    induction H.
    - constructor. rewrite H. reflexivity.
    - rewrite unfold_interp. cbn. setoid_rewrite bind_br.
      apply epsilon_br with (x := x). rewrite bind_ret_l.
      simpl. eapply epsilon_guard. apply IHepsilon_.
    - rewrite unfold_interp. cbn.
      now apply epsilon_guard.
  Qed.

End epsilon_interp_theory.

Lemma interp_ret_inv {E F B X} (h : E ~> ctree F B) :
  forall (t : ctree E B X) r,
  interp h t ≅ Ret r -> t ≅ Ret r.
Proof.
  intros. setoid_rewrite (ctree_eta t) in H. setoid_rewrite (ctree_eta t).
  destruct (observe t) eqn:?; try now inv_equ.
  - rewrite interp_ret in H. step in H. inv H. reflexivity.
  - rewrite interp_vis in H. apply ret_equ_bind in H as (? & ? & ?). step in H0. inv H0.
Qed.

Lemma bind_guard_r {E B X Y} : forall (t : ctree E B X) (k : X -> ctree E B Y),
    x <- t;; Guard (k x) ≅ x <- (x <- t;; Guard (Ret x));; k x.
Proof.
  intros. rewrite bind_bind. upto_bind_eq; intros ?. rewrite bind_guard. setoid_rewrite bind_ret_l. reflexivity.
Qed.

Lemma trans_val_interp {E F B X}
  (h : E ~> ctree F B) :
  forall (t u : ctree E B X) (v : X),
  trans (val v) t u ->
  trans (val v) (interp h t) Stuck.
Proof.
  intros.
  apply trans_val_epsilon in H as []. subs.
  eapply epsilon_interp in H.
  eapply epsilon_trans; [apply H |].
  rewrite interp_ret. etrans.
Qed.

Lemma trans_tau_interp {E F B X}
  (h : E ~> ctree F B) :
  forall (t u : ctree E B X),
  trans τ t u ->
  trans τ (interp h t) (Guard (interp h u)).
Proof.
  intros.
  apply trans_τ_epsilon in H as (? & ? & ?). subs.
  eapply epsilon_interp in H.
  eapply epsilon_trans; [apply H |].
  rewrite interp_step.
  etrans.
Qed.

Lemma trans_obs_interp_step {E F B X Y}
  (h : E ~> ctree F B) :
  forall (t u : ctree E B X) u' (e : E Y) x l,
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
  (h : E ~> ctree F B) :
  forall (t u : ctree E B X) (e : E Y) x,
  trans (obs e x) t u ->
  trans (val x) (h _ e) Stuck ->
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
