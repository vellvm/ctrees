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
  Inductive epsilon_det {E C X}: relation (ctree E C X) :=
  | epsilon_det_id : forall t t', t ≅ t' -> epsilon_det t t'
  | epsilon_det_guard : forall t t' t'',
      epsilon_det t t' -> t'' ≅ Guard t -> epsilon_det t'' t'.

(*|
Helper inductive: [productive t] judges that [t]'s head constructor is not a [Br]
|*)
  Inductive productive {E C X} : ctree E C X -> Prop :=
  | prod_ret {r t} (EQ: t ≅ Ret r) : productive t
  | prod_vis {Y} {e : E Y} {k t} (EQ: t ≅ Vis e k) : productive t
  | prod_step {t u} (EQ: t ≅ Step u) : productive t.

(*|
Helper inductive: [epsilon t t'] judges that [t'] is reachable from [t] by a path made of [Br] branches.
|*)
  Inductive epsilon_ {E C X} : ctree' E C X -> ctree' E C  X -> Prop :=
  | epsilon_id : forall t t', t ≅ t' -> epsilon_ (observe t) (observe t')
  | epsilon_br : forall X (c: C X) k x t, epsilon_ (observe (k x)) t -> epsilon_ (BrF c k) t
  | epsilon_guard : forall t u, epsilon_ (observe u) t -> epsilon_ (GuardF u) t.

  Definition epsilon {E C X} (t t' : ctree E C X) := epsilon_ (observe t) (observe t').
  Hint Constructors epsilon_det productive epsilon_ : core.

  Section epsilon_det_theory.

    #[global] Instance epsilon_det_equ {E C X}:
    Proper (equ eq ==> equ eq ==> flip impl) (@epsilon_det E C X).
    Proof.
      cbn. intros.
      revert x H. induction H1; intros.
      - econstructor. now rewrite H0, H1.
      - eapply epsilon_det_guard. apply IHepsilon_det. apply H0. reflexivity. rewrite H2. apply H.
    Qed.

    #[global] Instance epsilon_det_equ' {E C X}:
      Proper (equ eq ==> equ eq ==> impl) (@epsilon_det E C X).
    Proof.
      cbn. intros. rewrite <- H, <- H0. apply H1.
    Qed.

    #[global] Instance epsilon_det_refl {E C X} :
      Reflexive (@epsilon_det E C X).
    Proof.
      now left.
    Qed.

    #[global] Instance Transitive_epsilon_det {E C X} :
      Transitive (@epsilon_det E C X).
    Proof.
      cbn. intros. induction H.
      - now subs.
      - subs. eright. now apply IHepsilon_det. reflexivity.
    Qed.

    Lemma epsilon_det_bind {E C X Y}: forall (t t' : ctree E C X) (k : X -> ctree E C Y),
        epsilon_det t t' ->
        epsilon_det (t >>= k) (t' >>= k).
    Proof.
      intros. induction H.
      - setoid_rewrite H. constructor. reflexivity.
      - rewrite H0. setoid_rewrite bind_guard. eapply epsilon_det_guard. apply IHepsilon_det. reflexivity.
    Qed.

    Lemma epsilon_det_bind_ret_l {E C X Y}: forall (t : ctree E C X) t' (k : X -> ctree E C Y) x,
        epsilon_det t (Ret x) ->
        epsilon_det (k x) t' ->
        epsilon_det (t >>= k) t'.
    Proof.
      intros. remember (Ret x) as R. revert t' k x HeqR H0. induction H; intros; subst.
      - subst. rewrite H, bind_ret_l. apply H0.
      - rewrite H0. setoid_rewrite bind_guard.
        eapply epsilon_det_guard. 2: reflexivity. eapply IHepsilon_det. reflexivity. apply H1.
    Qed.

    Lemma epsilon_det_bind_ret_l_equ {E C X Y}:
      forall (t : ctree E C X) (k : X -> ctree E C Y) x,
        epsilon_det t (Ret x) ->
        x <- t;; k x ≅ t;; k x.
    Proof.
      intros. remember (Ret x) as R. induction H; subst.
      - rewrite H. rewrite !bind_ret_l. reflexivity.
      - rewrite H0. rewrite !bind_guard. apply guard_equ.
        apply IHepsilon_det. reflexivity.
    Qed.

    Lemma epsilon_det_trans {E C X} :
      forall l (t t' t'' : ctree E C X),
        epsilon_det t t' -> trans l t' t'' -> trans l t t''.
    Proof.
      intros. induction H.
      - now rewrite H.
      - apply IHepsilon_det in H0. apply trans_guard in H0. now rewrite <- H1 in H0.
    Qed.

    Lemma sbisim_epsilon_det {E C X}:
      forall (t t' : ctree E C X), epsilon_det t t' -> t ≃ t'.
    Proof.
      intros. induction H.
      - now rewrite H.
      - rewrite H0. rewrite sbisim_guard. apply IHepsilon_det.
    Qed.

  End epsilon_det_theory.

  Section productive_theory.

    #[global] Instance productive_equ : forall {E C X}, Proper (equ eq ==> impl) (@productive E C X).
    Proof.
      cbn. intros. inv H0; rewrite H in *.
      - eapply prod_ret; eauto.
      - eapply prod_vis; eauto.
      - eapply prod_step; eauto.
    Qed.

    #[global] Instance productive_equ' : forall {E C X}, Proper (equ eq ==> flip impl) (@productive E C X).
    Proof.
      cbn. intros. rewrite <- H in H0. apply H0.
    Qed.

    #[local] Hint Constructors productive : trans.

    Lemma ctree_case_productive : forall {E C X} (t: ctree E C X),
      productive t
      \/ (exists X (c : C X) k, t ≅ Br c k)
      \/ (exists u, t ≅ Guard u)
      \/ t ≅ Stuck.
    Proof.
      intros.
      rewrite ctree_eta.
      destruct (observe t) eqn:EQ; etrans.
      right; right; left; setoid_rewrite (ctree_eta t); rewrite EQ; etrans.
      right; left; setoid_rewrite (ctree_eta t); rewrite EQ; etrans.
    Qed.

    Lemma productive_guard : forall {E C X} (t : ctree E C X),
      ~ productive (Guard t).
    Proof.
      intros ** ?. inversion H; inv_equ.
    Qed.

    Lemma productive_br : forall {E C X Y} (c : C Y) (k : Y -> ctree E C X),
      ~ productive (Br c k).
    Proof.
      intros ** ?. inversion H; inv_equ.
    Qed.

    Lemma productive_stuck : forall {E C X},
      ~ productive (Stuck : ctree E C X).
    Proof.
      intros ** ?. inversion H; inv_equ.
    Qed.

    Lemma productive_bind : forall {E C X Y} t (k : Y -> ctree E C X), productive (t >>= k) -> productive t.
    Proof.
      intros. inversion H; inv_equ; subst.
      - apply ret_equ_bind in EQ as (? & ? & ?). subs. now eapply prod_ret.
      - apply vis_equ_bind in EQ as [(? & ? & ?) | (? & ? & ?)]; subs.
        + now eapply prod_ret.
        + now eapply prod_vis.
      - apply step_equ_bind in EQ as [(? & ? & ?) | (? & ? & ?)]; subs.
        + now eapply prod_ret.
        + now eapply prod_step.
    Qed.

  End productive_theory.

  #[global] Hint Constructors productive : trans.
  #[global] Hint Resolve productive_br : trans.

  Section epsilon_theory.

    #[global] Instance epsilon_equ_ {E C X} :
    Proper (going (equ eq) ==> going (equ eq) ==> impl) (@epsilon_ E C X).
    Proof.
      cbn. intros.
      revert y y0 H H0. induction H1; intros.
      - pose (epsilon_id (go y) (go y0)). cbn in e. apply e.
        rewrite <- H0, <- H1, H. reflexivity.
      - destruct H. step in H. inv H. invert.
        econstructor.
        apply IHepsilon_.
        + constructor.
          rewrite <- !ctree_eta. apply REL.
        + apply H0.
      - destruct H; step in H; inv H.
        constructor; apply IHepsilon_.
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

    #[global] Instance epsilon__refl {E C X} :
      Reflexive (@epsilon_ E C X).
    Proof.
      intros ?.
      change x with (observe (go x)).
      now apply epsilon_id.
    Qed.

    #[global] Instance epsilon_refl {E C X} :
      Reflexive (@epsilon E C X).
    Proof.
      now constructor 1.
    Qed.

    Lemma epsilon_Br {E C X Y} : forall (t' : ctree E C X) k (c : C Y) x,
      epsilon (k x) t' -> epsilon (Br c k) t'.
    Proof.
      intros. econstructor 2; apply H.
    Qed.

    Lemma epsilon_case {E C X} : forall (t t' : ctree E C X),
      epsilon t t' ->
      t ≅ t'
      \/ (exists Y (c : C Y) k x, t ≅ Br c k /\ epsilon (k x) t')
      \/ (exists u, t ≅ Guard u /\ epsilon u t').
    Proof.
      intros * EPS.
      inversion EPS; [left | right; left | right; right].
      - setoid_rewrite ctree_eta. now rewrite <- H, H1, H0.
      - subst. exists X0, c, k, x. split; auto. now rewrite H, <- ctree_eta.
      - eexists; split; eauto.
        now rewrite H, <- ctree_eta.
    Qed.

    Lemma epsilon_trans {E C X} : forall (t t' : ctree E C X),
        epsilon t t' -> forall l t'', trans l t' t'' -> trans l t t''.
    Proof.
      intros. red in H. rewrite ctree_eta. rewrite ctree_eta in H0.
      genobs t ot. genobs t' ot'. clear t Heqot t' Heqot'.
      induction H.
      - rewrite H. apply H0.
      - apply IHepsilon_ in H0. rewrite <- ctree_eta in H0. eapply trans_br in H0. apply H0. 
      - apply IHepsilon_ in H0; rewrite <- ctree_eta in H0; etrans.
    Qed.

    Lemma epsilon_fwd : forall {E C X Y} (t : ctree E C X) k x (c : C Y),
        epsilon t (Br c k) -> epsilon t (k x).
    Proof.
      intros. red in H. red.
      genobs t ot. clear t Heqot.
      remember (observe (Br c k)) as oc.
      revert c k x Heqoc. induction H.
      - intros. rewrite H, Heqoc. cbn. eapply epsilon_br. econstructor. reflexivity.
      - intros. subst. eapply epsilon_br. eapply IHepsilon_. reflexivity.
      - intros; subst; eapply epsilon_guard, IHepsilon_; reflexivity.
    Qed.

    Lemma epsilon_fwd' : forall {E C X} (t u : ctree E C X),
        epsilon t (Guard u) -> epsilon t u.
    Proof.
      intros. red in H. red.
      genobs t ot. clear t Heqot.
      remember (observe (Guard u)) as oc.
      revert u Heqoc. induction H.
      - intros. rewrite H, Heqoc. cbn. eapply epsilon_guard. econstructor. reflexivity.
      - intros. subst. eapply epsilon_br. eapply IHepsilon_. reflexivity.
      - intros; subst; eapply epsilon_guard, IHepsilon_; reflexivity.
    Qed.

    Lemma trans_epsilon {E C X} l (t : ctree E C X) t'' : trans l t t'' -> exists t',
          epsilon t t' /\ productive t' /\ trans l t' t''.
    Proof.
      intros H. cbv in H.
      dependent induction H.
      - edestruct4 IHtransR; eauto.
        setoid_rewrite H; rewrite H0 in H2.
        cbv; eauto.
      - edestruct4 IHtransR; eauto.
        setoid_rewrite H.
        cbv; eauto.
      - setoid_rewrite H.
        setoid_rewrite H0.
        exists (Step t'); split3; eauto.
      - setoid_rewrite H.
        eauto 5.
      - setoid_rewrite H.
        setoid_rewrite H0.
        exists (Ret r); split3; eauto.
    Qed.
    
    Lemma trans_val_epsilon {E C X} : forall x (t : ctree E C X) t',
        trans (val x) t t' -> epsilon t (Ret x).
    Proof.
      intros. apply trans_epsilon in H as (? & ? & ? & ?).
      inv H0.
      - rewrite EQ in H, H1. inv_trans. subst. auto.
      - rewrite EQ in H1. inv_trans.
      - rewrite EQ in H1. inv_trans.
    Qed.

    Lemma trans_τ_epsilon {E C X} : forall (t t' : ctree E C X),
        trans τ t t' -> exists u, epsilon t (Step u) /\ t' ≅ u.
    Proof.
      intros. apply trans_epsilon in H as (? & ? & ? & ?).
      inv H0.
      - rewrite EQ in H1. inv_trans.
      - rewrite EQ in H1. inv_trans.
      -  rewrite EQ in H1,H.
         clear x EQ.
         inv_trans.
         inv EQ.
         eauto.
    Qed.

    Lemma trans_ask_epsilon {E C X Y} : forall (t : ctree E C X) t' (e : E Y),
        trans (ask e) t t' -> exists k, epsilon t (Vis e k) /\ Seq t' (β e k).
    Proof.
      intros. apply trans_epsilon in H as (? & ? & ? & ?).
      inv H0.
      - rewrite EQ in H1. inv_trans.
      - rewrite EQ in H1. inv_trans.
        rewrite EQ in H.
        pose proof ask_invT EQl; subst.
        pose proof ask_inv EQl; subst.
        eauto.
      - rewrite EQ in H1. inv_trans.
    Qed.

    Lemma productive_epsilon {E C X} : forall (t t' : ctree E C X),
        productive t -> epsilon t t' -> t ≅ t'.
    Proof.
      intros. setoid_rewrite ctree_eta.
      inversion H; subst; rewrite (ctree_eta t) in EQ; inversion H0; subst.
      all: try now rewrite H3.
      all: try now (rewrite <- H1 in EQ; step in EQ; inv EQ).
    Qed.

    #[global] Instance epsilon_transitive {E C X} : Transitive (@epsilon E C X).
    Proof.
      red. intros t u v ? ?. red in H.
      rewrite (ctree_eta t). rewrite (ctree_eta u) in H0.
      genobs t ot. genobs u ou. clear t Heqot u Heqou.
      revert v H0. induction H; intros.
      - subs. apply H0.
      - setoid_rewrite <- ctree_eta in IHepsilon_.
        econstructor 2. now apply IHepsilon_.
      - setoid_rewrite <- ctree_eta in IHepsilon_.
        econstructor 3. now apply IHepsilon_.
    Qed.

    Lemma epsilon_bind_l {E C X Y} : forall t t' (k : Y -> ctree E C X),
      epsilon t t' -> epsilon (t >>= k) (t' >>= k).
    Proof.
      intros. setoid_rewrite (ctree_eta t). setoid_rewrite (ctree_eta t').
      red in H. genobs t ot. genobs t' ot'. clear t Heqot t' Heqot'.
      induction H.
      - subs. reflexivity.
      - rewrite bind_br. econstructor 2. rewrite (ctree_eta (k0 x)). apply IHepsilon_.
      - rewrite bind_guard. econstructor 3; eauto.
    Qed.

    Lemma epsilon_bind_ret {E C X Y} : forall t (k : Y -> ctree E C X) v,
      epsilon t (Ret v) -> epsilon (t >>= k) (k v).
    Proof.
      intros. rewrite <- (bind_ret_l v k).
      now apply epsilon_bind_l.
    Qed.

    Lemma epsilon_bind {E C X Y} : forall t u (k : Y -> ctree E C X) v,
      epsilon t (Ret v) -> epsilon (k v) u -> epsilon (t >>= k) u.
    Proof.
      intros. eapply epsilon_bind_ret in H.
      eapply epsilon_transitive; eassumption.
    Qed.

    Lemma epsilon_bind_inv {E C X Y} : forall t u (k : Y -> ctree E C X),
      epsilon (t >>= k) u ->
        (exists u', u ≅ u' >>= k /\ epsilon t u') \/
        (exists v, epsilon t (Ret v) /\ epsilon (k v) u).
    Proof.
      intros. setoid_rewrite (ctree_eta t). setoid_rewrite (ctree_eta u).
      red in H. remember (observe _) as ot.
      assert (go ot ≅ t >>= k). { now rewrite Heqot, <- ctree_eta. }
      genobs u ou. clear u Heqou Heqot.
      revert t H0. induction H; intros.
      - left. exists t0. rewrite <- H, H0, <- !ctree_eta. auto.
      - setoid_rewrite (ctree_eta t0) in H0. destruct (observe t0) eqn:?; inv_equ.
        + right. exists r. split; auto.
          rewrite bind_ret_l in H0. rewrite <- H0. apply epsilon_br with (x := x). apply H.
        + rewrite bind_br in H0.
          inv_equ.
          specialize (IHepsilon_ (k1 x)).
          rewrite <- ctree_eta in IHepsilon_.
          apply IHepsilon_ in EQ. destruct EQ as [(? & ? & ?) | (? & ? & ?)].
          * left. exists x0. split; auto. eapply epsilon_br; eassumption.
          * right. exists x0. split; auto. eapply epsilon_br; eassumption.
      - setoid_rewrite (ctree_eta t0) in H0. destruct (observe t0) eqn:?; inv_equ.
        + right. exists r. split; auto.
          rewrite bind_ret_l in H0. rewrite <- H0. apply epsilon_guard, H.
        + rewrite bind_guard in H0.
          inv_equ.
          rewrite (ctree_eta u) in H0; apply IHepsilon_ in H0.
          destruct H0 as [(? & ? & ?) | (? & ? & ?)].
          * left. exists x. split; auto. eapply epsilon_guard; eassumption.
          * right. exists x. split; auto. eapply epsilon_guard; eassumption.
    Qed.

    Lemma epsilon_det_epsilon {E C X} : forall (t t' : ctree E C X),
        epsilon_det t t' -> epsilon t t'.
    Proof.
      intros. induction H.
      - now constructor.
      - rewrite H0. now constructor.
    Qed.

    Lemma ss_epsilon_l {E F C D X Y L R}
        (t t0 : ctree E C X) (u : ctree F D Y) :
      epsilon t0 t ->
      ss L R t0 u ->
      ss L R t u.
    Proof.
      intros. cbn. intros.
      eapply epsilon_trans in H1; [| eassumption].
      apply H0 in H1 as (? & ? & ? & ? & ?). eauto 6.
    Qed.

    (* Is this one really useful? *)
    Lemma ss_epsilon_l' {E F C D X Y L R}
        (t : ctree E C X) (u : ctree F D Y) :
      (forall t0, epsilon t t0 -> productive t0 -> ss L R t0 u) ->
      ss L R t u.
    Proof.
      intros. cbn. intros. apply trans_epsilon in H0 as (? & ? & ? & ?).
      red in H0.
      setoid_rewrite (ctree_eta t) in H. genobs t ot. clear t Heqot.
      rewrite (ctree_eta x) in H1, H2. genobs x ox. clear x Heqox.
      induction H0.
      - apply H in H1 as ?. 2: { rewrite H0. now constructor. }
        apply H3 in H2. apply H2.
      - apply IHepsilon_; auto. intros. apply H; auto. econstructor 2. apply H3.
      - apply IHepsilon_; auto. intros. apply H; auto. econstructor 3. apply H3.
    Qed.

    Lemma ss_epsilon_r {E F C D X Y L R}
        (t : ctree E C X) (u u0 : ctree F D Y) :
      epsilon u u0 ->
      ss L R t u0 ->
      ss L R t u.
    Proof.
      intros. cbn. intros. apply H0 in H1 as (? & ? & ? & ? & ?).
      eapply epsilon_trans in H1; eauto.
    Qed.

    Lemma ssim_epsilon_l {E F C D X Y L}
        (t0 t : ctree E C X) (u : ctree F D Y) :
      epsilon t0 t ->
      ssim L t0 u ->
      ssim L t u.
    Proof.
      intros. cbn. intros.
      step in H0. step. eapply ss_epsilon_l in H0; eauto.
    Qed.

    Lemma ssim_epsilon_l' {E F C D X Y L}
        (t : ctree E C X) (u : ctree F D Y) :
      (forall t0, epsilon t t0 -> productive t0 -> ssim L t0 u) ->
      ssim L t u.
    Proof.
      intros. step. apply ss_epsilon_l'.
      intros. apply H in H1. now step in H1. assumption.
    Qed.

    Lemma ssim_epsilon_r {E F C D X Y L}
        (t : ctree E C X) (u u0 : ctree F D Y) :
      epsilon u u0 ->
      ssim L t u0 ->
      ssim L t u.
    Proof.
      intros. cbn. intros.
      step in H0. step. eapply ss_epsilon_r in H0; eauto.
    Qed.

    Notation "l ⊢ x → y" := (hrel_of (trans l) x y) (at level 10, x at next level, y at next level, only printing).
    Notation "x" := (α x) (at level 9, only printing).
    
    Lemma ssim_ret_epsilon {E F C D X Y L} :
      forall r (u : ctree F D Y),
      (Ret r : ctree E C X) (≲L) u ->
      exists r', epsilon u (Ret r') /\ L (val r) (val r').
    Proof.
      intros * SIM *.
      play in SIM.
      invL.
      apply trans_val_epsilon in TR.
      etrans.
    Qed.

    Lemma ssim_vis_epsilon {E F C D X Y Z L} :
      forall e (k : Z -> ctree E C X) (u : ctree F D Y),
      Vis e k (≲L) u ->
      forall x, exists Z' (e' : F Z') k' y,
        epsilon u (Vis e' k') /\
        k x (≲L) k' y /\
        L (ask e) (ask e') /\
        L (rcv e x) (rcv e' y).
    Proof.
      intros * SIM *.
      apply ssim_vis_l_inv in SIM as (? & ? & ? & TR & ? & SIM).
      apply trans_epsilon in TR. destruct TR as (u' & EPS & PROD & TR).
      destruct PROD; subs; inv_trans.
      dependent induction EQ.
      pose proof ask_invT EQl; subst.
      pose proof ask_inv EQl; subst.
      destruct (SIM x) as (? & ? & ?).
      rewrite EQ in H2.
      ex4; split4; eauto; etrans.
    Qed.

    Lemma ssim_brS_epsilon {E F C D X Y Z L} :
      forall c (k : Z -> ctree E C X) (u : ctree F D Y),
      BrS c k (≲L) u ->
      forall x,
      (exists v, epsilon u (Step v) /\ k x (≲L) v).
    Proof.
      intros * SIM *.
      step in SIM. cbn in SIM. specialize (SIM τ (k x) (trans_brS _ _ _)).
      destruct SIM as (l' & u'' & TR & SIM & EQ).
      apply trans_epsilon in TR. destruct TR as (u' & EPS & PROD & TR).
      destruct PROD; subs; inv_trans; etrans.
      invL.
      invL.
    Qed.

  End epsilon_theory.

#[global] Hint Resolve epsilon_trans : trans.
