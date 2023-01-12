(* begin hide *)

From ITree Require Import
     Basics.Basics
     Core.Subevent.

From CTree Require Import
  CTree
  Eq.

Import CTreeNotations.
Open Scope ctree_scope.

(* end hide *)

(*|
Helper inductive: [t0_det t t'] judges that [t' ≡ Guard* t]
|*)
  Inductive t0_det {E C X} `{B1 -< C}: relation (ctree E C X) :=
  | t0_det_id : forall t t', t ≅ t' -> t0_det t t'
  | t0_det_tau : forall t t' t'',
      t0_det t t' -> t'' ≅ Guard t -> t0_det t'' t'.

(*|
Helper inductive: [productive t] judges that [t]'s head constructor is not a [BrD]
|*)
  Inductive productive {E C X} : ctree E C X -> Prop :=
  | prod_ret {r t} (EQ: t ≅ Ret r) : productive t
  | prod_vis {Y} {e : E Y} {k t} (EQ: t ≅ Vis e k) : productive t
  | prod_tau {X} {c: C X} {k t} (EQ: t ≅ BrS c k) : productive t.

(*|
Helper inductive: [trans0 t t'] judges that [t'] is reachable from [t] by a path made of [BrD] branches.
|*)
  Inductive trans0_ {E C X} : ctree' E C X -> ctree' E C  X -> Prop :=
  | T0Id : forall t t', t ≅ t' -> trans0_ (observe t) (observe t')
  | T0Br : forall X (c: C X) k x t, trans0_ (observe (k x)) t -> trans0_ (BrDF c k) t.

  Definition trans0 {E C X} (t t' : ctree E C X) := trans0_ (observe t) (observe t').

  Section t0_det_theory.

    #[global] Instance t0_det_equ {E C X} `{Tau: B1 -< C}:
    Proper (equ eq ==> equ eq ==> flip impl) (@t0_det E C X _).
    Proof.
      cbn. intros.
      revert x H. induction H1; intros.
      - econstructor. now rewrite H0, H1.
      - eapply t0_det_tau. apply IHt0_det. apply H0. reflexivity. rewrite H2. apply H.
    Qed.

    #[global] Instance t0_det_equ' {E C X} `{Tau: B1 -< C}:
      Proper (equ eq ==> equ eq ==> impl) (@t0_det E C X _).
    Proof.
      cbn. intros. rewrite <- H, <- H0. apply H1.
    Qed.

    Lemma t0_det_bind {E C X Y} `{Tau: B1 -< C}: forall (t t' : ctree E C X) (k : X -> ctree E C Y),
        t0_det t t' ->
        t0_det (t >>= k) (t' >>= k).
    Proof.
      intros. induction H.
      - rewrite H. constructor. reflexivity.
      - rewrite H0. setoid_rewrite bind_guard. eapply t0_det_tau. apply IHt0_det. reflexivity.
    Qed.

    Lemma t0_det_bind_ret_l {E C X Y} `{Tau: B1 -< C}: forall (t : ctree E C X) t' (k : X -> ctree E C Y) x,
        t0_det t (Ret x) ->
        t0_det (k x) t' ->
        t0_det (t >>= k) t'.
    Proof.
      intros. remember (Ret x) as R. revert t' k x HeqR H0. induction H; intros; subst.
      - subst. rewrite H, bind_ret_l. apply H0.
      - rewrite H0. setoid_rewrite bind_guard.
        eapply t0_det_tau. 2: reflexivity. eapply IHt0_det. reflexivity. apply H1.
    Qed.

    Lemma t0_det_bind_ret_l_equ {E C X Y} `{Tau: B1 -< C}:
      forall (t : ctree E C X) (k : X -> ctree E C Y) x,
        t0_det t (Ret x) ->
        x <- t;; k x ≅ t;; k x.
    Proof.
      intros. remember (Ret x) as R. induction H; subst.
      - rewrite H. rewrite !bind_ret_l. reflexivity.
      - rewrite H0. rewrite !bind_guard. apply br_equ. intro. apply IHt0_det. reflexivity.
    Qed.

    Lemma sbisim_t0_det {E C X} `{Stuck: B0 -< C} `{Tau: B1 -< C}:
      forall (t t' : ctree E C X), t0_det t t' -> t ~ t'.
    Proof.
      intros. induction H.
      - now rewrite H.
      - rewrite H0. rewrite sb_guard. apply IHt0_det.
    Qed.

  End t0_det_theory.

  Section productive_theory.

    #[global] Instance productive_equ : forall {E C X}, Proper (equ eq ==> impl) (@productive E C X).
    Proof.
      cbn. intros. inv H0; rewrite H in *.
      - eapply prod_ret; eauto.
      - eapply prod_vis; eauto.
      - eapply prod_tau; eauto.
    Qed.

    #[global] Instance productive_equ' : forall {E C X}, Proper (equ eq ==> flip impl) (@productive E C X).
    Proof.
      cbn. intros. rewrite <- H in H0. apply H0.
    Qed.

  End productive_theory.

  Section trans0_theory.

    #[global] Instance trans0_equ_ {E C X} :
    Proper (going (equ eq) ==> going (equ eq) ==> impl) (@trans0_ E C X).
    Proof.
      cbn. intros.
      revert y y0 H H0. induction H1; intros.
      - pose (T0Id (go y) (go y0)). cbn in t0. apply t0.
        rewrite <- H0, <- H1, H. reflexivity.
      - destruct H. step in H. inv H. invert.
        econstructor.
        apply IHtrans0_.
        + constructor.
          rewrite <- !ctree_eta. apply REL.
        + apply H0.
    Qed.

    #[global] Instance trans0_equ_' {E C X} :
      Proper (going (equ eq) ==> going (equ eq) ==> flip impl) (@trans0_ E C X).
    Proof.
      cbn. intros. now rewrite <- H, <- H0 in H1.
    Qed.

    #[global] Instance trans0_equ {E C X} : Proper (equ eq ==> equ eq ==> iff) (@trans0 E C X).
    Proof.
      unfold trans0. split; intros.
      - now rewrite <- H, <- H0.
      - now rewrite H, H0.
    Qed.

    Lemma trans0_trans {E C X} `{Stuck: B0 -< C} : forall (t t' : ctree E C X),
        trans0 t t' -> forall l t'', trans l t' t'' -> trans l t t''.
    Proof.
      intros. red in H. rewrite ctree_eta. rewrite ctree_eta in H0.
      genobs t ot. genobs t' ot'. clear t Heqot t' Heqot'.
      induction H.
      - rewrite H. apply H0.
      - apply IHtrans0_ in H0. eapply trans_brD in H0. apply H0. rewrite <- ctree_eta. reflexivity.
    Qed.

    Lemma trans0_fwd : forall {E C X} (t : ctree E C X) k x (c : C X),
        trans0 t (BrD c k) -> trans0 t (k x).
    Proof.
      intros. red in H. red.
      genobs t ot. clear t Heqot.
      remember (observe (BrD c k)) as oc.
      revert c k x Heqoc. induction H.
      - intros. rewrite H, Heqoc. cbn. eapply T0Br. econstructor. reflexivity.
      - intros. subst. eapply T0Br. eapply IHtrans0_. reflexivity.
    Qed.

    Lemma trans_productive {E C X} `{Stuck: B0 -< C} l (t t'' : ctree E C X) : trans l t t'' -> exists t',
          trans0 t t' /\ productive t' /\ trans l t' t''.
    Proof.
      intros. do 3 red in H.
      setoid_rewrite (ctree_eta t). setoid_rewrite (ctree_eta t'').
      genobs t ot. genobs t'' ot''. clear t Heqot t'' Heqot''.
      induction H; intros.
      - destruct IHtrans_ as (? & ? & ? & ?).
        rewrite <- ctree_eta in H0. eapply T0Br in H0.
        exists x0. etrans.
      - eexists. split; [| split ].
        + left. reflexivity.
        + eapply prod_tau. reflexivity.
        + rewrite <- H, <- ctree_eta. etrans.
      - eexists. split; [| split ].
        + left. reflexivity.
        + eapply prod_vis. reflexivity.
        + rewrite <- H, <- ctree_eta. etrans.
      - eexists. split; [| split ].
        + left. reflexivity.
        + eapply prod_ret. reflexivity.
        + rewrite br0_always_stuck. etrans.
    Qed.

    Lemma trans_val_trans0 {E C X}  `{Stuck: B0 -< C}  : forall x (t t' : ctree E C X),
        trans (val x) t t' -> trans0 t (Ret x) /\ t' ≅ stuckD.
    Proof.
      intros. apply trans_productive in H as (? & ? & ? & ?).
      inv H0.
      - rewrite EQ in H, H1. inv_trans. subst. auto.
      - rewrite EQ in H1. inv_trans.
      - rewrite EQ in H1. inv_trans.
    Qed.

    Lemma trans_tau_trans0 {E C X}  `{Stuck: B0 -< C} : forall (t t' : ctree E C X),
        trans tau t t' -> exists X (c: C X) k x, trans0 t (BrS c k) /\ t' ≅ k x.
    Proof.
      intros. apply trans_productive in H as (? & ? & ? & ?).
      inv H0.
      - rewrite EQ in H1. inv_trans.
      - rewrite EQ in H1. inv_trans.
      - rewrite EQ in H1. inv_trans.
        do 2 eexists.
        exists k. exists x0.
        eauto.
    Qed.

    Lemma trans_obs_trans0 {E C X Y} `{Stuck: B0 -< C} : forall (t t' : ctree E C X) e (x : Y),
        trans (obs e x) t t' -> exists k, trans0 t (Vis e k) /\ t' ≅ k x.
    Proof.
      intros. apply trans_productive in H as (? & ? & ? & ?).
      inv H0.
      - rewrite EQ in H1. inv_trans.
      - rewrite EQ in H1. inv_trans.
        apply obs_eq_invT in EQl as ?. subst.
        apply obs_eq_inv in EQl as [<- <-]. etrans.
      - rewrite EQ in H1. inv_trans.
    Qed.

    Lemma productive_trans0 {E C X} : forall (t t' : ctree E C X),
        productive t -> trans0 t t' -> t ≅ t'.
    Proof.
      intros. setoid_rewrite ctree_eta.
      inversion H; subst; rewrite (ctree_eta t) in EQ; inversion H0; subst.
      - now rewrite H3.
      - rewrite <- H1 in EQ. step in EQ. inv EQ.
      - now rewrite H3.
      - rewrite <- H1 in EQ. step in EQ. inv EQ.
      - now rewrite H3.
      - rewrite <- H1 in EQ. step in EQ. inv EQ.
    Qed.

    Lemma ss_trans0_l {E F C D X Y L R} `{Stuck: B0 -< C} `{Stuck': B0 -< D}
        (t : ctree E C X) (u : ctree F D Y) :
      (forall t0, trans0 t t0 -> productive t0 -> ss L R t0 u) ->
      ss L R t u.
    Proof.
      intros. cbn. intros. apply trans_productive in H0 as (? & ? & ? & ?).
      red in H0.
      setoid_rewrite (ctree_eta t) in H. genobs t ot. clear t Heqot.
      rewrite (ctree_eta x) in H1, H2. genobs x ox. clear x Heqox.
      induction H0.
      - apply H in H1 as ?. 2: { rewrite H0. now left. }
        apply H3 in H2. apply H2.
      - apply IHtrans0_; auto. intros. apply H; auto. eright. apply H3.
    Qed.

    Lemma ss_trans0_r {E F C D X Y L R} `{Stuck: B0 -< C} `{Stuck': B0 -< D}
        (t : ctree E C X) (u u0 : ctree F D Y) :
      trans0 u u0 ->
      ss L R t u0 ->
      ss L R t u.
    Proof.
      intros. cbn. intros. apply H0 in H1 as (? & ? & ? & ? & ?).
      eapply trans0_trans in H1; eauto.
    Qed.

    Lemma ssim_trans0_l {E F C D X Y L} `{Stuck: B0 -< C} `{Stuck': B0 -< D}
        (t : ctree E C X) (u : ctree F D Y) :
      (forall t0, trans0 t t0 -> productive t0 -> ssim L t0 u) ->
      ssim L t u.
    Proof.
      intros. step. apply ss_trans0_l.
      intros. apply H in H1. now step in H1. assumption.
    Qed.

    Lemma ssim_trans0_r {E F C D X Y L} `{Stuck: B0 -< C} `{Stuck': B0 -< D}
        (t : ctree E C X) (u u0 : ctree F D Y) :
      trans0 u u0 ->
      ssim L t u0 ->
      ssim L t u.
    Proof.
      intros. cbn. intros.
      step in H0. step. eapply ss_trans0_r in H0; eauto.
    Qed.

  End trans0_theory.
