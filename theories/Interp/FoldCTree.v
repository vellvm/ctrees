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
  Fold.

Import CTreeNotations.
Open Scope ctree_scope.

(* end hide *)

(** Establishing generic results on [fold] is tricky: because it goes into
    a very generic monad [M], it requires some heavy axiomatization of this
    monad. Yoon et al.'s ICFP'22 develop the necessary tools to this end.
    For now, we simply specialize results to specific [M]s.
 *)

Theorem ssim_interp_h {E F1 F2 C D1 D2 X Y}
  `{HasB0 : B0 -< D1} `{HasB1 : B1 -< D1} `{HasB0' : B0 -< D2} `{HasB1' : B1 -< D2}
  `{HC1 : C -< D1} `{HC2 : C -< D2}
  (Ldest : rel (@label F1) (@label F2)) :
  forall (h : E ~> ctree F1 D1) (h' : E ~> ctree F2 D2),
  (Ldest tau tau /\ forall (x : X), Ldest (val x) (val x)) ->
  (forall {Z} (e : E Z), h _ e (≲update_val_rel Ldest (@eq Z)) h' _ e) ->
  forall (x : Y) (k : Y -> ctree E C X), interp h (k x) (≲Ldest) interp h' (k x).
Proof.
  intros.
  eapply ssim_iter with (Ra := equ eq) (Rb := fun b b' => Ldest (val b) (val b')).
  2, 4: auto. 1: red; reflexivity.
  cbn. intros.
  setoid_rewrite ctree_eta in H1.
  destruct (observe a) eqn:?, (observe a') eqn:?; try now (step in H1; inv H1).
  - step. apply step_ss_ret. constructor. cbn. step in H1. inv H1. apply H.
  - unfold CTree.map.
    apply equ_vis_invT in H1 as ?. subst.
    eapply ssim_clo_bind_gen with (R0 := eq).
    + red. reflexivity.
    + eapply weq_ssim. apply update_val_rel_update_val_rel.
      apply equ_vis_invE in H1 as [<- ?]. apply H0.
    + intros. step. apply step_ss_ret. constructor.
      apply equ_vis_invE in H1 as [<- ?]. subst. apply H1.
  - unfold CTree.map. setoid_rewrite bind_branch.
    apply equ_br_invT in H1 as ?. destruct H2 as [<- <-].
    apply equ_br_invE in H1 as [<- ?].
    destruct vis.
    + step. apply step_ss_brS_id. intros.
      step. apply step_ss_ret. constructor.
      apply H1. right; etrans. apply H.
    + step. apply step_ss_brD_id. intros.
      apply step_ss_ret. constructor. apply H1.
Qed.

Section FoldCTree.

  Section With_Params.

    (** Specialization to [M = ctree F D] *)
    Context {E F C D: Type -> Type} {X : Type} `{B1 -< D}
      {h : E ~> ctree F D} {g : bool -> C ~> ctree F D}.

    (** ** [interpE] and constructors *)

    (** Unfolding of [fold]. *)
    Notation fold_ h g t :=
      (match observe t with
       | RetF r => Ret r
	     | VisF e k => bind (h _ e) (fun x => Guard (fold h g (k x)))
	     | BrF b c k => bind (g b _ c) (fun x => Guard (fold h g (k x)))
       end)%function.

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

    (** Unfolding of [interp]. *)
    Notation interp_ h t :=
      (match observe t with
       | RetF r => Ret r
	     | VisF e k => bind (h _ e) (fun x => Guard (interp h (k x)))
	     | BrF b c k => bind (mbr b c) (fun x => Guard (interp h (k x)))
       end)%function.

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

    (** Unfolding of [refine]. *)
    Notation refine_ g t :=
      (match observe t with
       | RetF r => Ret r
	     | VisF e k => bind (mtrigger e) (fun x => Guard (refine g (k x)))
	     | BrF b c k => bind (g b _ c) (fun x => Guard (refine g (k x)))
       end)%function.

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

  Section FoldBind.

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

  End FoldBind.

End FoldCTree.

(*|
Counter-example showing that interp does not preserve sbisim in the general case.
|*)

Module CounterExample.

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

End CounterExample.

(*|
In order to recover the congruence of [sbisim] for [interp], we restrict ourselves to
so-called "simple" handlers.
|*)

(* TODO move *)
#[global] Instance equ_Guard:
  forall {E B : Type -> Type} {R : Type} `{B1 -< B},
    Proper (equ eq ==> equ eq) (@Guard E B R _).
Proof.
  repeat intro.
  unfold Guard; now setoid_rewrite H0.
Qed.

Lemma void_unit_elim : @eq Type void unit -> False.
Proof.
  intros abs.
  assert (forall x : unit, False) by (rewrite <- abs; intros []).
  apply (H tt).
Qed.

Section is_simple.

(*|
Helper inductive: [transi h l t t'] judges that:
t -obs e1 x1> -obs e2 x2> .. -obs en xn> -l> t'
where forall i, [h ei -val xi> stuck]
Spelled out: we absorb a sequence of transitions in [t] that will become invisible after interpretation, until we reach a visible one.
|*)
   Inductive transi {E C F X} `{Stuck: B0 -< C} `{Tau: B1 -< C} (h : E ~> ctree F C) :
    @label F -> ctree E C X -> ctree E C X -> Prop :=
  | transi_val : forall (x : X) t t',
      trans (val x) t t' ->
      transi h (val x) t t'
  | transi_tau : forall t t',
      trans tau t t' ->
      transi h tau t t'
  | transi_obs : forall Y (e : E Y) x l t t' t'',
      trans (obs e x) t t' ->
      epsilon_det t'' (Ret x) ->
      trans l (h _ e) t'' ->
      transi h l t t'
  | transi_obs0 : forall Y (e : E Y) l x t t' t'',
      trans (obs e x) t t' ->
      transi h l t' t'' ->
      trans (val x) (h _ e) stuckD ->
      transi h l t t''.

(*|
A computation is [simple] all its transitions are either:
- directly returning
- or reducing in one step to something of the shape [Guard* (Ret r)]
|*)
  Definition is_simple {E C X} `{B0 -< C} `{B1 -< C} (t : ctree E C X) :=
    (forall l t', trans l t t' -> is_val l) \/
    (forall l t', trans l t t' -> exists r, epsilon_det t' (Ret r)).

(*|
A computation is [vsimple] if it is syntactically:
- a [Ret]
- or a [trigger]
|*)
   Definition vsimple {E C X} (t : ctree E C X) :=
    (exists x, t ≅ Ret x) \/ exists f, t ≅ CTree.trigger f.

  Section is_simple_theory.

    #[global] Instance is_simple_equ : forall {E C X} `{Stuck: B0 -< C} `{Tau: B1 -< C},
      Proper (equ eq ==> iff) (@is_simple E C X _ _).
    Proof.
      cbn. intros. unfold is_simple. setoid_rewrite H. reflexivity.
    Qed.

    Lemma is_simple_ret : forall {E C X} `{B0 -< C} `{B1 -< C} r, is_simple (Ret r : ctree E C X).
    Proof.
      cbn. red. intros. left. intros. inv_trans. subst. constructor.
    Qed.

    Lemma is_simple_guard_ret : forall {E C X} `{B0 -< C}`{B1 -< C}r,
        is_simple (Guard (Ret r) : ctree E C X).
    Proof.
      cbn. red. intros. left. intros. inv_trans. subst. constructor.
    Qed.

    Lemma is_simple_br : forall {E C X} `{Stuck: B0 -< C} `{Tau: B1 -< C} (n: C X),
        is_simple (mbr false n : ctree E C X).
    Proof.
      cbn. unfold mbr, MonadBr_ctree, CTree.branch. red. intros.
      left. intros. apply trans_brD_inv in H as []. inv_trans. subst. constructor.
    Qed.

    Lemma is_simple_brD : forall {E C X Y} `{Stuck: B0 -< C} `{Tau: B1 -< C} (n: C X) (k : X -> ctree E C Y) x,
        is_simple (BrD n k) -> is_simple (k x).
    Proof.
      intros. destruct H.
      - left. intros. eapply H. etrans.
      - right. intros. eapply H. etrans.
    Qed.

  End is_simple_theory.

  Section epsilon_interp_theory.

    Lemma interp_productive {E C F X}  `{Stuck: B0 -< C} `{Tau: B1 -< C} (h : E ~> ctree F C) : forall (t : ctree E C X),
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

    Lemma epsilon_interp : forall {E C F X} `{Tau: B1 -< C} `{Stuck: B0 -< C}
                            (h : E ~> ctree F C) (t t' : ctree E C X),
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

  Section transi_theory.

    Lemma transi_brD {E C F X Y} `{Stuck: B0 -< C} `{Tau: B1 -< C} (h : E ~> ctree F C) :
      forall l (t' : ctree E C X) (c: C Y) (k: Y -> ctree E C X) (x: Y),
        transi h l (k x) t' -> transi h l (BrD c k) t'.
    Proof.
      intros. inv H.
      - apply transi_val. etrans.
      - apply transi_tau. etrans.
      - eapply transi_obs; etrans.
      - eapply transi_obs0; etrans.
    Qed.

    #[global] Instance transi_equ :
      forall {E C F X} `{Stuck: B0 -< C} `{Tau: B1 -< C} (h : E ~> ctree F C) l,
        Proper (equ eq ==> equ eq ==> flip impl) (@transi E C F X _ _ h l).
    Proof.
      cbn. intros.
      revert x x0 H H0. induction H1; intros.
      - apply transi_val. rewrite H0, H1. apply H.
      - apply transi_tau. rewrite H0, H1. apply H.
      - rewrite <- H2, <- H3 in *. eapply transi_obs; eauto.
      - rewrite <- H2 in *. eapply transi_obs0; eauto.
    Qed.

    #[global] Instance transi_equ' :
      forall {E C F X}  `{Stuck: B0 -< C} `{Tau: B1 -< C} (h : E ~> ctree F C) l,
        Proper (equ eq ==> equ eq ==> impl) (@transi E C F X _ _ h l).
    Proof.
      cbn. intros. rewrite <- H, <- H0. apply H1.
    Qed.

    Lemma epsilon_transi {E C F X}  `{Stuck: B0 -< C} `{Tau: B1 -< C}  (h : E ~> ctree F C) :
      forall l (t t' t'' : ctree E C X), epsilon t t' -> transi h l t' t'' -> transi h l t t''.
    Proof.
      intros.
      red in H. rewrite (ctree_eta t). rewrite (ctree_eta t') in H0.
      genobs t ot. genobs t' ot'. clear t Heqot. clear t' Heqot'.
      revert l t'' H0. induction H; intros.
      - rewrite H. apply H0.
      - eapply transi_brD.
        setoid_rewrite <- ctree_eta in IHepsilon_.
        apply IHepsilon_; apply H0.
    Qed.

    Lemma transi_sbisim {E C F X}  `{Stuck: B0 -< C} `{Tau: B1 -< C} (h : E ~> ctree F C) :
      forall l (t t' u : ctree E C X), transi h l t t' ->
                                  t ~ u ->
                                  exists u', transi h l u u' /\ t' ~ u'.
    Proof.
      intros. revert u H0.
      induction H; intros.
      - step in H0. destruct H0 as [? _]. apply H0 in H; destruct H as (? & ? & ? & ? & ?); subst.
        eexists. split. apply transi_val. apply H. apply H1.
      - step in H0. destruct H0 as [? _]. apply H0 in H. destruct H as (? & ? & ? & ? & ?); subst.
        eexists. split. apply transi_tau. apply H. apply H1.
      - step in H2. destruct H2 as [? _]. apply H2 in H. destruct H as (? & ? & ? & ? & ?); subst.
        eexists. split. eapply transi_obs; eauto. apply H3.
      - step in H2. destruct H2 as [? _]. apply H2 in H. destruct H as (? & ? & ? & ? & ?); subst.
        apply IHtransi in H3 as (? & ? & ?).
        eexists. split. eapply transi_obs0; eauto. apply H4.
    Qed.

    Lemma transi_trans {E C F X} {Stuck: B0 -< C} {Tau: B1 -< C} (h : E ~> ctree F C)
      (Hh : forall X e, vsimple (h X e)) :
      forall l (t t' : ctree E C X),
        transi h l t t' -> exists t0, trans l (interp h t) t0 /\ epsilon_det t0 (interp h t').
    Proof.
      intros. induction H.
      - exists stuckD. apply trans_val_inv in H as ?.
        apply trans_val_epsilon in H as [].
        eapply epsilon_interp in H. rewrite interp_ret in H. setoid_rewrite H0.
        setoid_rewrite interp_br. setoid_rewrite bind_br. setoid_rewrite br0_always_stuck.
        eapply epsilon_trans in H; etrans.
      - exists (Guard (interp h t')). split; [| eright; eauto; now left ].
        apply trans_tau_epsilon in H as (? & ? & ? & ? & ? & ?).
        eapply epsilon_interp in H.
        rewrite H0.
        eapply epsilon_trans; etrans.
        setoid_rewrite interp_br. setoid_rewrite bind_br. setoid_rewrite bind_ret_l.
        econstructor. reflexivity.
      - exists (x <- t'';; Guard (interp h t')).
        split. 2: { eapply epsilon_det_bind_ret_l; eauto. eright; eauto. }
             apply trans_obs_epsilon in H as (? & ? & ?).
        eapply epsilon_interp in H. eapply epsilon_trans; etrans.
        setoid_rewrite interp_vis.
        eapply trans_bind_l with (k := fun x => Guard (interp h (x0 x))) in H1.
        setoid_rewrite epsilon_det_bind_ret_l_equ in H1 at 2; eauto.
        now setoid_rewrite H2.
        { intro. inv H3. apply trans_val_inv in H1. rewrite H1 in H0. inv H0. step in H3. inv H3. step in H4.
          cbn in H4.
          inv H4.
          now apply void_unit_elim.
        }
      - destruct IHtransi as (? & ? & ?).
        destruct (Hh Y e). 2: { destruct H4. rewrite H4 in H1. apply trans_vis_inv in H1 as (? & ? & ?). step in H1. inv H1. }
                         destruct H4. rewrite H4 in H1. inv_trans. subst.
        exists x0. split. 2: auto.
        apply trans_obs_epsilon in H as (? & ? & ?). eapply epsilon_interp in H.
        setoid_rewrite interp_vis in H. setoid_rewrite H4 in H. setoid_rewrite bind_ret_l in H.
        eapply epsilon_trans; etrans. setoid_rewrite <- H1. etrans.
    Qed.


  End transi_theory.

End is_simple.

(** Various lemmas for the proof that interp preserves sbisim in some cases. *)
Lemma interp_ret_inv {E F B X} {Tau: B1 -< B} (h : E ~> ctree F B) :
  forall (t : ctree E B X) r,
  interp h t ≅ Ret r -> t ≅ Ret r.
Proof.
  intros. setoid_rewrite (ctree_eta t) in H. setoid_rewrite (ctree_eta t).
  destruct (observe t) eqn:?.
  - rewrite interp_ret in H. step in H. inv H. reflexivity.
  - rewrite interp_vis in H. apply ret_equ_bind in H as (? & ? & ?). step in H0. inv H0.
  - rewrite interp_br in H. setoid_rewrite bind_br in H. step in H. inv H.
Qed.

Lemma bind_guard_r {E B X Y} {Tau: B1 -< B} : forall (t : ctree E B X) (k : X -> ctree E B Y),
  x <- t;; Guard (k x) ≅ x <- (x <- t;; Guard (Ret x));; k x.
Proof.
  intros. rewrite bind_bind. upto_bind_eq. rewrite bind_guard. setoid_rewrite bind_ret_l. reflexivity.
Qed.

Lemma trans_interp_inv_gen {E F B X Y} {Stuck: B0 -< B} {Tau: B1 -< B}
  (h : E ~> ctree F B) (Hh : forall X e, vsimple (h X e)) :
  forall l (k : Y -> ctree E B X) t' (pre : ctree F B Y),
  is_simple pre ->
  trans l (x <- pre;; interp h (k x)) t' ->
  exists t0, epsilon_det t' (interp h t0) /\
    ((exists l t1 x, trans l pre t1 /\ epsilon_det t1 (Ret x) /\ t0 ≅ k x) \/
    exists x, trans (val x) pre stuckD /\ trans l (interp h (k x)) t' /\ transi h l (k x) t0).
Proof.
  intros * Hpre H.
  do 3 red in H. remember (observe (x <- pre;; interp h (k x))) as oi.
  setoid_rewrite (ctree_eta t') at 1.
  setoid_rewrite (ctree_eta t') at 2.
  genobs t' ot'. clear t' Heqot'.
  assert (go oi ≅ x <- pre;; interp h (k x)).
  { rewrite Heqoi, <- ctree_eta. reflexivity. } clear Heqoi.
  revert Y k pre Hpre H0. induction H; intros.
  - (*apply Stepbr in H as ?.
    change (BrDF n k) with (observe (BrD n k)) in H1. rewrite H0 in H1.
       change t with (observe (go t)) in H1. rewrite trans__trans in H1.*)
    (* destruct n. now apply Fin.case0. *)
    symmetry in H0. apply br_equ_bind in H0 as ?.
    destruct H1 as [[] | (? & ? & ?)].
    + rewrite H1 in H0. rewrite bind_ret_l in H0. setoid_rewrite H1. clear pre Hpre H1.
      rewrite (ctree_eta (k0 x0)) in H0. destruct (observe (k0 x0)) eqn:?.
      * rewrite interp_ret in H0. step in H0. inv H0.
      * rewrite interp_vis in H0. apply br_equ_bind in H0 as ?. destruct H1 as [[] | (? & ? & ?)].
        --rewrite H1, bind_ret_l in H0.
          inv_equ.
          rewrite <- EQ in H.
          specialize (IHtrans_ _ (fun (_ : unit) => k1 x1) (Ret tt)).
          edestruct IHtrans_. { apply is_simple_ret. } { rewrite <- ctree_eta, bind_ret_l, EQ. reflexivity. }
          destruct H0. exists x2. split; auto. right. destruct H2.
          { destruct H2 as (? & ? & ? & ? & ? & ?). inv_trans. subst.
            inv H3. step in H2. inv H2. step in H5. inv H5.
            exfalso; now apply void_unit_elim.
          }
          destruct H2 as (_ & _ & ? & ?). exists x0. split. etrans. split.
          ++ setoid_rewrite (ctree_eta (k0 x0)). rewrite Heqc0.
             setoid_rewrite interp_vis. setoid_rewrite H1. setoid_rewrite bind_ret_l. apply trans_guard. apply H2.
          ++setoid_rewrite (ctree_eta (k0 x0)). rewrite Heqc0.
            eapply transi_obs0; etrans. rewrite H1. etrans.
        --destruct (Hh _ e).
          destruct H3. rewrite H3 in H1. step in H1. inv H1.
          destruct H3. rewrite H3 in H1. step in H1. inv H1.
      * rewrite interp_br in H0. setoid_rewrite bind_br in H0. setoid_rewrite bind_ret_l in H0.
        inv_equ.
        specialize (IHtrans_ _ (fun _ : unit => k1 x) (Guard (Ret tt))).
        edestruct IHtrans_ as (? & ? & ?).
        { apply is_simple_guard_ret. }
        { rewrite <- ctree_eta. setoid_rewrite bind_br. setoid_rewrite bind_ret_l. unfold Guard in EQ. now rewrite EQ. }
        destruct H1.
        { destruct H1 as (? & ? & ? & ? & ? & ?). inv_trans. subst.
          inv H2. step in H1. inv H1. step in H3. inv H3.
          exfalso; now apply void_unit_elim.
        }
        destruct H1 as (? & ? & ? & ?).
        exists x1. split; auto. right. exists x0. split; etrans. split.
        rewrite (ctree_eta (k0 x0)), Heqc0, interp_br. setoid_rewrite bind_br. setoid_rewrite bind_ret_l.
        eapply trans_brD. 2: reflexivity. apply trans_guard. apply H2.
        rewrite (ctree_eta (k0 x0)), Heqc0. eapply transi_brD; etrans.
    + specialize (IHtrans_ _ k0 (x0 x)).
      edestruct IHtrans_ as (? & ? & ?).
      { eapply is_simple_brD. red. setoid_rewrite <- H1. apply Hpre. }
      rewrite <- ctree_eta. apply H2. destruct H4 as [(? & ? & ? & ? & ? & ?) | (? & ? & ? & ?)].
      * (*setoid_rewrite H5 in H3. clear x1 H5.*)
        exists (k0 x4). split. { now rewrite H6 in H3. }
        left. eapply trans_brD in H4. 2: reflexivity. rewrite <- H1 in H4. eauto 6.
      * exists x1. split; auto. right. exists x2. rewrite H1. etrans.
  - symmetry in H0. apply br_equ_bind in H0 as ?. destruct H1 as [[] | (? & ? & ?)].
    + rewrite H1 in H0. rewrite bind_ret_l in H0.
      rewrite (ctree_eta (k0 x0)) in H0. destruct (observe (k0 x0)) eqn:?.
      * rewrite interp_ret in H0. step in H0. inv H0.
      * rewrite interp_vis in H0. apply br_equ_bind in H0 as ?.
        destruct H2 as [[] | (? & ? & ?)].
        { rewrite H2, bind_ret_l in H0. step in H0. inv H0. }
        pose proof (trans_brS c x1 x). rewrite <- H2 in H4.
        edestruct Hh. { destruct H5. rewrite H5 in H4. inv_trans. }
        destruct H5. rewrite H5 in H4. apply trans_vis_inv in H4 as (? & ? & ?). discriminate.
        (*--specialize (H3 x).
          (*rewrite H4 in H3. rewrite bind_ret_l in H3.*)
          exists (k1 x2).
          rewrite H in H3. split; auto. rewrite H3, <- ctree_eta.
          eapply epsilon_det_bind_ret_l; eauto. eapply epsilon_det_tau; eauto. constructor; auto.
          right. exists x0. rewrite H1. split; etrans.
          setoid_rewrite (ctree_eta (k0 x0)). setoid_rewrite Heqc. split.
          { setoid_rewrite interpE_vis. setoid_rewrite H2. setoid_rewrite bind_br.
            econstructor. rewrite <- ctree_eta, H3. reflexivity. }
          eapply transi_vis; eauto. rewrite H2. etrans.*)
      * rewrite interp_br in H0. setoid_rewrite bind_br in H0.
        inv_equ.
        specialize (EQ x).
        rewrite bind_ret_l, H in EQ.
        exists (k1 x). symmetry in EQ. split.
        { rewrite <- ctree_eta. rewrite EQ. eapply epsilon_det_tau; auto. }
        right. exists x0. rewrite H1. split; etrans.
        setoid_rewrite (ctree_eta (k0 x0)). setoid_rewrite Heqc0. split.
        { setoid_rewrite interp_br. rewrite EQ. setoid_rewrite bind_br. setoid_rewrite bind_ret_l.
          econstructor. now rewrite <- ctree_eta. }
        econstructor; etrans.
    + pose proof (trans_brS c x0 x).
      rewrite <- H1 in H3. edestruct Hpre.
      { apply H4 in H3. inv H3. }
      apply H4 in H3 as [].
      specialize (H2 x).
      (*rewrite H3, bind_ret_l in H2.*)
      exists (k0 x1). rewrite H in H2. split. { rewrite <- ctree_eta, H2. eapply epsilon_det_bind_ret_l; eauto. }
      left. exists tau, (x0 x), x1. split; auto. rewrite H1. etrans.
  - symmetry in H0. apply vis_equ_bind in H0 as ?. destruct H1 as [[] | (? & ? & ?)].
    + rewrite H1 in H0. rewrite bind_ret_l in H0.
     rewrite (ctree_eta (k0 x0)) in H0. destruct (observe (k0 x0)) eqn:?.
      * rewrite interp_ret in H0. step in H0. inv H0.
      * rewrite interp_vis in H0. apply vis_equ_bind in H0 as ?.
        destruct H2 as [[] | (? & ? & ?)].
        { rewrite H2, bind_ret_l in H0. step in H0. inv H0. }
        pose proof (trans_vis e x x1). rewrite <- H2 in H4.
        edestruct Hh. { destruct H5. rewrite H5 in H4. inv H4. }
        destruct H5. rewrite H5 in H4. (*destruct H4 as [? ?].*)
        specialize (H3 x). rewrite H5 in H2.
        inv_equ.
        rewrite <- EQ in *. rewrite bind_ret_l in H3.
        exists (k1 x).
        rewrite H in H3. split. { rewrite <- ctree_eta, H3. eright; eauto. }
        right.
        exists x0. rewrite H1. split; etrans.
        setoid_rewrite (ctree_eta (k0 x0)). setoid_rewrite Heqc. split.
        { setoid_rewrite interp_vis. rewrite H5. setoid_rewrite bind_vis.
          econstructor. rewrite bind_ret_l. rewrite <- H3, <- ctree_eta. reflexivity. }
        eapply transi_obs; etrans. rewrite H5. etrans.
      * rewrite interp_br in H0. setoid_rewrite bind_br in H0.
        step in H0. inv H0.
    + pose proof (trans_vis e x x0).
      rewrite <- H1 in H3. edestruct Hpre.
      { apply H4 in H3. inv H3. }
      apply H4 in H3 as [].
      specialize (H2 x).
      exists (k0 x1). rewrite H in H2. split.
      { rewrite <- ctree_eta, H2. eapply epsilon_det_bind_ret_l; eauto. }
      left. exists (obs e x), (x0 x), x1. split; auto. rewrite H1. etrans.
     - exists (stuckD). split.
       + left.
         setoid_rewrite interp_br. setoid_rewrite bind_br.
         rewrite !br0_always_stuck.
         step. constructor; intros [].
       + right. symmetry in H0. apply ret_equ_bind in H0 as (? & ? & ?).
         exists x. rewrite H. split; etrans. split.
         rewrite H0. rewrite br0_always_stuck. etrans.
         apply interp_ret_inv in H0. rewrite H0. constructor; etrans.
Qed.

Lemma trans_interpE_inv {E F B X} {Stuck: B0 -< B} {Tau: B1 -< B}
  (h : E ~> ctree F B) (Hh : forall X e, vsimple (h X e)) :
  forall l (t : ctree E B X) t',
  trans l (interp h t) t' ->
  exists l t0, epsilon_det t' (interp h t0) /\ transi h l t t0.
Proof.
  intros.
   assert (trans l (Guard (Ret tt);; interp h t) t').
   { etrans. }
  eapply trans_interp_inv_gen in H0; eauto. destruct H0 as (? & ? & ?).
  destruct H1 as [(? & ? & ? & ? & ? & ?) | (? & ? & ? & ?)].
  - inv_trans. subst. inv H2. step in H1. inv H1. step in H3. inv H3.
    exfalso; now apply void_unit_elim.
  - inv_trans. subst. eauto.
  - left. intros. inv_trans. subst. constructor.
Qed.

(** The main theorem stating that interp preserves sbisim. *)
Theorem interp_sbisim_gen {E F B X Y} {Stuck: B0 -< B} {Tau: B1 -< B}
  (h : E ~> ctree F B) (Hh : forall X e, vsimple (h X e)) :
  forall (k k' : X -> ctree E B Y) (pre pre' : ctree F B X),
  (forall x, sbisim eq (k x) (k' x)) ->
  pre ≅ pre' ->
  vsimple pre ->
  sbisim eq (a <- pre;; Guard (interp h (k a))) (a <- pre';; Guard (interp h (k' a))).
Proof.
  revert X. coinduction R CH. symmetric using idtac.
  { intros. apply H. now symmetry. now symmetry. red. now setoid_rewrite <- H1. }
  assert (CH' : forall (t t' : ctree E B Y), t ~ t' -> st eq R (interp h t) (interp h t')).
  {
    intros.
    assert (st eq R (a <- Ret tt;; Guard (interp h ((fun _ => t) a)))
      (a <- Ret tt;; Guard (interp h ((fun _ => t') a)))).
    { apply CH; eauto. left; eauto. }
    rewrite !bind_ret_l in H0.
    rewrite !sb_guard in H0.
    apply H0.
  }
  intros. setoid_rewrite <- H0. clear pre' H0.
  cbn; intros.
  copy H0. rewrite bind_guard_r in H0.
  eapply trans_interp_inv_gen in H0 as (? & ? & ?); auto.
  2: { destruct H1 as [[] | []]; rewrite H1.
       rewrite bind_ret_l. apply is_simple_guard_ret.
       rewrite bind_trigger. right. intros. inv_trans. subst.
       exists x0. rewrite EQ. eright. left. reflexivity. reflexivity.
  }
  destruct H2.
  + destruct H2 as (? & ? & ? & ? & ? & ?). rewrite H4 in H0. clear x H4.
    destruct H1 as [[] | []].
    * rewrite H1, bind_ret_l in H2. rewrite H1, bind_ret_l in cpy. inv_trans. subst.
      inv H3. step in H2. inv H2. step in H4. inv H4.
      exfalso; now apply void_unit_elim.
    * rewrite H1 in *. rewrite bind_trigger in H2. apply trans_vis_inv in H2 as (? & ? & ?). subst.
      (* todo lemma *)
      rewrite H2 in H3. inv H3. step in H4. inv H4.
      apply equ_br_invE in H5 as [_ H5]; specialize (H5 tt).
      rewrite <- H5 in H4. inv H4.
      2: { step in H6. inv H6. }
      step in H3. inv H3. clear x1 H2 t H5.
      rewrite bind_trigger in cpy. apply trans_vis_inv in cpy. destruct cpy as (? & ? & ?).
      exists l.
      subst.
      exists (Guard (interp h (k' x0))). rewrite H1. rewrite bind_trigger. split. now constructor.
      rewrite H2, !sb_guard. split; auto.
  + destruct H2 as (? & ? & ? & ?).
    destruct H1 as [[] | []]. 2: { rewrite H1 in H2. setoid_rewrite bind_trigger in H2. inv_trans. }
                            rewrite H1 in *. rewrite bind_ret_l in H2. inv_trans. subst. clear EQ.
    eapply transi_sbisim in H4; eauto. destruct H4 as (? & ? & ?).
    apply transi_trans in H2 as (? & ? & ?); auto.
    exists l, x2. rewrite H1, bind_ret_l.
    split.
    etrans.
    split; auto.
    assert (st eq R (interp h x) (interp h x0)).
    { apply CH'. apply H4. }
    rewrite sbisim_epsilon_det. 2: apply H0.
    setoid_rewrite sbisim_epsilon_det at 3. 2: apply H5.
    apply H6.
Qed.

#[global] Instance interp_sbisim {E F B R} {Stuck: B0 -< B} {Tau: B1 -< B}
  (h : E ~> ctree F B) (Hh : forall X e, vsimple (h X e)) :
  Proper (sbisim eq ==> sbisim eq) (interp (B := B) h (T := R)).
Proof.
  cbn. intros.
  assert (a <- Ret tt;; Guard (interp h ((fun _ => x) a)) ~
    a <- Ret tt;; Guard (interp h ((fun _ => y) a))).
  apply interp_sbisim_gen; auto.
  red; eauto.
  rewrite !bind_ret_l, !sb_guard in H0. apply H0.
Qed.

Lemma trans_val_interp {E F B X} `{HasB0: B0 -< B} `{HasB1: B1 -< B}
  (h : E ~> ctree F B) :
  forall (t u : ctree E B X) (v : X),
  trans (val v) t u ->
  trans (val v) (interp h t) stuckD.
Proof.
  intros.
  apply trans_val_epsilon in H as []. subs.
  eapply epsilon_interp in H.
  eapply epsilon_trans; [apply H |].
  rewrite interp_ret. etrans.
Qed.

Lemma trans_tau_interp {E F B X} `{HasB0: B0 -< B} `{HasB1: B1 -< B}
  (h : E ~> ctree F B) :
  forall (t u : ctree E B X),
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

Lemma trans_obs_interp_step {E F B X Y} `{HasB0: B0 -< B} `{HasB1: B1 -< B}
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

Lemma trans_obs_interp_pure {E F B X Y} `{HasB0: B0 -< B} `{HasB1: B1 -< B}
  (h : E ~> ctree F B) :
  forall (t u : ctree E B X) (e : E Y) x,
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
