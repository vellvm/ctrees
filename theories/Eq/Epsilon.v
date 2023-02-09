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
Helper inductive: [epsilon_det t t'] judges that [t' ≡ Guard* t]
|*)
  Inductive epsilon_det {E C X} `{B1 -< C}: relation (ctree E C X) :=
  | epsilon_det_id : forall t t', t ≅ t' -> epsilon_det t t'
  | epsilon_det_tau : forall t t' t'',
      epsilon_det t t' -> t'' ≅ Guard t -> epsilon_det t'' t'.

(*|
Helper inductive: [productive t] judges that [t]'s head constructor is not a [BrD]
|*)
  Inductive productive {E C X} : ctree E C X -> Prop :=
  | prod_ret {r t} (EQ: t ≅ Ret r) : productive t
  | prod_vis {Y} {e : E Y} {k t} (EQ: t ≅ Vis e k) : productive t
  | prod_tau {X} {c: C X} {k t} (EQ: t ≅ BrS c k) : productive t.

(*|
Helper inductive: [epsilon t t'] judges that [t'] is reachable from [t] by a path made of [BrD] branches.
|*)
  Inductive epsilon_ {E C X} : ctree' E C X -> ctree' E C  X -> Prop :=
  | EpsilonId : forall t t', t ≅ t' -> epsilon_ (observe t) (observe t')
  | EpsilonBr : forall X (c: C X) k x t, epsilon_ (observe (k x)) t -> epsilon_ (BrDF c k) t.

  Definition epsilon {E C X} (t t' : ctree E C X) := epsilon_ (observe t) (observe t').

  Section epsilon_det_theory.

    #[global] Instance epsilon_det_equ {E C X} `{Tau: B1 -< C}:
    Proper (equ eq ==> equ eq ==> flip impl) (@epsilon_det E C X _).
    Proof.
      cbn. intros.
      revert x H. induction H1; intros.
      - econstructor. now rewrite H0, H1.
      - eapply epsilon_det_tau. apply IHepsilon_det. apply H0. reflexivity. rewrite H2. apply H.
    Qed.

    #[global] Instance epsilon_det_equ' {E C X} `{Tau: B1 -< C}:
      Proper (equ eq ==> equ eq ==> impl) (@epsilon_det E C X _).
    Proof.
      cbn. intros. rewrite <- H, <- H0. apply H1.
    Qed.

    #[global] Instance epsilon_det_refl {E C X} `{HasB1: B1 -< C} :
      Reflexive (@epsilon_det E C X _).
    Proof.
      now left.
    Qed.

    Lemma epsilon_det_bind {E C X Y} `{Tau: B1 -< C}: forall (t t' : ctree E C X) (k : X -> ctree E C Y),
        epsilon_det t t' ->
        epsilon_det (t >>= k) (t' >>= k).
    Proof.
      intros. induction H.
      - rewrite H. constructor. reflexivity.
      - rewrite H0. setoid_rewrite bind_guard. eapply epsilon_det_tau. apply IHepsilon_det. reflexivity.
    Qed.

    Lemma epsilon_det_bind_ret_l {E C X Y} `{Tau: B1 -< C}: forall (t : ctree E C X) t' (k : X -> ctree E C Y) x,
        epsilon_det t (Ret x) ->
        epsilon_det (k x) t' ->
        epsilon_det (t >>= k) t'.
    Proof.
      intros. remember (Ret x) as R. revert t' k x HeqR H0. induction H; intros; subst.
      - subst. rewrite H, bind_ret_l. apply H0.
      - rewrite H0. setoid_rewrite bind_guard.
        eapply epsilon_det_tau. 2: reflexivity. eapply IHepsilon_det. reflexivity. apply H1.
    Qed.

    Lemma epsilon_det_bind_ret_l_equ {E C X Y} `{Tau: B1 -< C}:
      forall (t : ctree E C X) (k : X -> ctree E C Y) x,
        epsilon_det t (Ret x) ->
        x <- t;; k x ≅ t;; k x.
    Proof.
      intros. remember (Ret x) as R. induction H; subst.
      - rewrite H. rewrite !bind_ret_l. reflexivity.
      - rewrite H0. rewrite !bind_guard. apply br_equ. intro. apply IHepsilon_det. reflexivity.
    Qed.

    Lemma epsilon_det_trans {E C X} `{Stuck: B0 -< C} `{Tau: B1 -< C} :
      forall l (t t' t'' : ctree E C X),
        epsilon_det t t' -> trans l t' t'' -> trans l t t''.
    Proof.
      intros. induction H.
      - now rewrite H.
      - apply IHepsilon_det in H0. apply trans_guard in H0. now rewrite <- H1 in H0.
    Qed.

    Lemma sbisim_epsilon_det {E C X} `{Stuck: B0 -< C} `{Tau: B1 -< C}:
      forall (t t' : ctree E C X), epsilon_det t t' -> t ~ t'.
    Proof.
      intros. induction H.
      - now rewrite H.
      - rewrite H0. rewrite sb_guard. apply IHepsilon_det.
    Qed.

  End epsilon_det_theory.

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

    Hint Constructors productive : trans.

    Lemma ctree_case_productive : forall {E C X} (t: ctree E C X),
      productive t \/ exists X (c : C X) k, t ≅ BrD c k.
    Proof.
      intros. setoid_rewrite (ctree_eta t). desobs t; etrans.
      destruct vis; etrans.
    Qed.

    Lemma productive_brD : forall {E C X Y} (c : C Y) (k : Y -> ctree E C X),
      ~ productive (BrD c k).
    Proof.
      intros ** ?. inversion H; inv_equ.
    Qed.

  End productive_theory.

  #[global] Hint Constructors productive : trans.
  #[global] Hint Resolve productive_brD : trans.

  Section epsilon_theory.

    #[global] Instance epsilon_equ_ {E C X} :
    Proper (going (equ eq) ==> going (equ eq) ==> impl) (@epsilon_ E C X).
    Proof.
      cbn. intros.
      revert y y0 H H0. induction H1; intros.
      - pose (EpsilonId (go y) (go y0)). cbn in e. apply e.
        rewrite <- H0, <- H1, H. reflexivity.
      - destruct H. step in H. inv H. invert.
        econstructor.
        apply IHepsilon_.
        + constructor.
          rewrite <- !ctree_eta. apply REL.
        + apply H0.
    Qed.

    #[global] Instance epsilon_equ_' {E C X} :
      Proper (going (equ eq) ==> going (equ eq) ==> flip impl) (@epsilon_ E C X).
    Proof.
      cbn. intros. now rewrite <- H, <- H0 in H1.
    Qed.

    #[global] Instance epsilon_equ {E C X} : Proper (equ eq ==> equ eq ==> iff) (@epsilon E C X).
    Proof.
      unfold epsilon. split; intros.
      - now rewrite <- H, <- H0.
      - now rewrite H, H0.
    Qed.

    #[global] Instance epsilon_refl {E C X} :
      Reflexive (@epsilon E C X).
    Proof.
      now left.
    Qed.

    Lemma epsilon_trans {E C X} `{Stuck: B0 -< C} : forall (t t' : ctree E C X),
        epsilon t t' -> forall l t'', trans l t' t'' -> trans l t t''.
    Proof.
      intros. red in H. rewrite ctree_eta. rewrite ctree_eta in H0.
      genobs t ot. genobs t' ot'. clear t Heqot t' Heqot'.
      induction H.
      - rewrite H. apply H0.
      - apply IHepsilon_ in H0. eapply trans_brD in H0. apply H0. rewrite <- ctree_eta. reflexivity.
    Qed.

    Lemma epsilon_fwd : forall {E C X} (t : ctree E C X) k x (c : C X),
        epsilon t (BrD c k) -> epsilon t (k x).
    Proof.
      intros. red in H. red.
      genobs t ot. clear t Heqot.
      remember (observe (BrD c k)) as oc.
      revert c k x Heqoc. induction H.
      - intros. rewrite H, Heqoc. cbn. eapply EpsilonBr. econstructor. reflexivity.
      - intros. subst. eapply EpsilonBr. eapply IHepsilon_. reflexivity.
    Qed.

    Lemma trans_epsilon {E C X} `{Stuck: B0 -< C} l (t t'' : ctree E C X) : trans l t t'' -> exists t',
          epsilon t t' /\ productive t' /\ trans l t' t''.
    Proof.
      intros. do 3 red in H.
      setoid_rewrite (ctree_eta t). setoid_rewrite (ctree_eta t'').
      genobs t ot. genobs t'' ot''. clear t Heqot t'' Heqot''.
      induction H; intros.
      - destruct IHtrans_ as (? & ? & ? & ?).
        rewrite <- ctree_eta in H0. eapply EpsilonBr in H0.
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

    Lemma trans_val_epsilon {E C X}  `{Stuck: B0 -< C}  : forall x (t t' : ctree E C X),
        trans (val x) t t' -> epsilon t (Ret x) /\ t' ≅ stuckD.
    Proof.
      intros. apply trans_epsilon in H as (? & ? & ? & ?).
      inv H0.
      - rewrite EQ in H, H1. inv_trans. subst. auto.
      - rewrite EQ in H1. inv_trans.
      - rewrite EQ in H1. inv_trans.
    Qed.

    Lemma trans_tau_epsilon {E C X}  `{Stuck: B0 -< C} : forall (t t' : ctree E C X),
        trans tau t t' -> exists X (c: C X) k x, epsilon t (BrS c k) /\ t' ≅ k x.
    Proof.
      intros. apply trans_epsilon in H as (? & ? & ? & ?).
      inv H0.
      - rewrite EQ in H1. inv_trans.
      - rewrite EQ in H1. inv_trans.
      - rewrite EQ in H1. inv_trans.
        do 2 eexists.
        exists k. exists x0.
        eauto.
    Qed.

    Lemma trans_obs_epsilon {E C X Y} `{Stuck: B0 -< C} : forall (t t' : ctree E C X) e (x : Y),
        trans (obs e x) t t' -> exists k, epsilon t (Vis e k) /\ t' ≅ k x.
    Proof.
      intros. apply trans_epsilon in H as (? & ? & ? & ?).
      inv H0.
      - rewrite EQ in H1. inv_trans.
      - rewrite EQ in H1. inv_trans. subst. etrans.
      - rewrite EQ in H1. inv_trans.
    Qed.

    Lemma productive_epsilon {E C X} : forall (t t' : ctree E C X),
        productive t -> epsilon t t' -> t ≅ t'.
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

    Lemma epsilon_det_epsilon {E C X} `{Stuck: B0 -< C} `{Tau: B1 -< C} : forall (t t' : ctree E C X),
        epsilon_det t t' -> epsilon t t'.
    Proof.
      intros. induction H.
      - now left.
      - rewrite H0. now right.
    Qed.

    Lemma ss_epsilon_l {E F C D X Y L R} `{Stuck: B0 -< C} `{Stuck': B0 -< D}
        (t : ctree E C X) (u : ctree F D Y) :
      (forall t0, epsilon t t0 -> productive t0 -> ss L R t0 u) ->
      ss L R t u.
    Proof.
      intros. cbn. intros. apply trans_epsilon in H0 as (? & ? & ? & ?).
      red in H0.
      setoid_rewrite (ctree_eta t) in H. genobs t ot. clear t Heqot.
      rewrite (ctree_eta x) in H1, H2. genobs x ox. clear x Heqox.
      induction H0.
      - apply H in H1 as ?. 2: { rewrite H0. now left. }
        apply H3 in H2. apply H2.
      - apply IHepsilon_; auto. intros. apply H; auto. eright. apply H3.
    Qed.

    Lemma ss_epsilon_r {E F C D X Y L R} `{Stuck: B0 -< C} `{Stuck': B0 -< D}
        (t : ctree E C X) (u u0 : ctree F D Y) :
      epsilon u u0 ->
      ss L R t u0 ->
      ss L R t u.
    Proof.
      intros. cbn. intros. apply H0 in H1 as (? & ? & ? & ? & ?).
      eapply epsilon_trans in H1; eauto.
    Qed.

    Lemma ssim_epsilon_l {E F C D X Y L} `{Stuck: B0 -< C} `{Stuck': B0 -< D}
        (t : ctree E C X) (u : ctree F D Y) :
      (forall t0, epsilon t t0 -> productive t0 -> ssim L t0 u) ->
      ssim L t u.
    Proof.
      intros. step. apply ss_epsilon_l.
      intros. apply H in H1. now step in H1. assumption.
    Qed.

    Lemma ssim_epsilon_r {E F C D X Y L} `{Stuck: B0 -< C} `{Stuck': B0 -< D}
        (t : ctree E C X) (u u0 : ctree F D Y) :
      epsilon u u0 ->
      ssim L t u0 ->
      ssim L t u.
    Proof.
      intros. cbn. intros.
      step in H0. step. eapply ss_epsilon_r in H0; eauto.
    Qed.

  End epsilon_theory.
