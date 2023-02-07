From Coq Require Import
     Program
     List
     Logic.FinFun
     Logic.FunctionalExtensionality
     Logic.IndefiniteDescription
     micromega.Lia
     Init.Specif
     Fin.

From RelationAlgebra Require Import
     monoid
     kat
     kat_tac
     prop
     rel
     srel
     comparisons
     rewriting
     normalisation.

From Equations Require Import Equations.

(* Universe issue, TO FIX *)
Unset Universe Checking.
Unset Auto Template Polymorphism.

From ITree Require Import
     State.

From CTree Require Import
     CTree
	 Eq
 	 Interp.Interp.

From CTreeYield Require Import
     Utils.

Import ListNotations.
Import CTreeNotations.


(** Events used to model yields and forks in our language.
    Yield is reused to label a yield after scheduling *)
Variant yieldE : Type -> Type :=
  | Yield : yieldE unit.
Variant forkE : Type -> Type :=
  | Fork : forkE bool.
(** Event to label a spawned thread *)
Variant spawnE : Type -> Type :=
  | Spawn : spawnE unit.

Section parallel.
  Context {E : Type -> Type}.

  Definition thread := ctree (yieldE +' forkE +' E) unit.
  Definition completed := ctree (yieldE +' spawnE +' E) unit.
  Definition vec n := fin n -> thread.

  (** Scheduling a thread pool *)
  Equations schedule_match
             (schedule : forall (n : nat), vec n -> option (fin n) -> completed)
             (n : nat)
             (v: vec n)
    : option (fin n) -> completed :=
    (* If no thread is focused, and there are none left in the pool, we are done *)
    schedule_match schedule 0 v None :=
      Ret tt;

    (* If no thread is focused, but there are some left in the pool, we pick one *)
    schedule_match schedule (S n) v None :=
      Vis (inl1 Yield)
          (fun _ =>
             BrD (S n) (fun i' => schedule (S n) v (Some i')));

    (* If a thread is focused on, we analyze its head constructor *)
    schedule_match schedule (S n) v (Some i) with observe (v i) =>
      {
        (* If it's a [Ret], we simply remove it from the pool and focus *)
        schedule_match _ _ _ _ (RetF _) :=
        Guard (schedule n (remove_vec v i) None);

        (* If it's a [Br], we propagate the br and update the thread *)
        schedule_match _ _ _ _ (BrF b n' k) :=
        Br b n' (fun i' => schedule (S n) (replace_vec v i (k i')) (Some i));

        (* If it's a [Yield], we remove the focus *)
        schedule_match _ _ _ _ (VisF (inl1 Yield) k) :=
        Guard (schedule (S n) (replace_vec v i (k tt)) None);

        (* If it's a [Fork], we extend the pool *)
        schedule_match _ _ _ _ (VisF (inr1 (inl1 Fork)) k) :=
        Vis (inr1 (inl1 Spawn)) (* label with an event *)
            (fun _ =>
               schedule
                 (S (S n))
                 (* Note that [cons_vec] puts the new thread on the front of the vector *)
                 (cons_vec (k true) (replace_vec v i (k false)))
                 (* We stay with the old thread; we don't yield at a fork *)
                 (Some (FS i)));

        (* Other events are not touched in scheduling *)
        schedule_match _ _ _ _ (VisF (inr1 (inr1 s)) k) :=
        Vis (inr1 (inr1 s)) (fun x => (schedule (S n) (replace_vec v i (k x)) (Some i)));

      }.
  (* Transparent schedule_match. *)
  CoFixpoint schedule := schedule_match schedule.

  Lemma rewrite_schedule n v i : schedule n v i ≅ schedule_match schedule n v i.
  Proof.
    step. eauto.
  Qed.

  #[global] Instance equ_schedule n :
    Proper ((pwr (equ eq)) ==> pwr (equ eq)) (schedule n).
  Proof.
    cbn. revert n.
    coinduction r CIH. intros n v1 v2 Hv i.
    do 2 rewrite rewrite_schedule.
    destruct i as [i |].
    2: {
      destruct n; auto. constructor. intros.
      step. econstructor. intros. apply CIH; auto.
    }
    destruct n as [| n]; auto.
    pose proof (Hv i).
    simp schedule_match.
    step in H. cbn. inv H; eauto. 2: destruct e. 3: destruct s. all: cbn.
    - clear H1 H2. destruct y; cbn in *; auto.
      constructor. intros. apply CIH.
      apply remove_vec_relation; auto.
    - clear H1 H2. destruct y.
      constructor. intros. eapply CIH.
      apply replace_vec_relation; auto.
    - destruct f. constructor. intros. eapply CIH.
      apply cons_vec_relation; auto.
      apply replace_vec_relation; auto.
    - constructor. intros. apply CIH.
      apply replace_vec_relation; auto.
    - constructor. intros. apply CIH.
      apply replace_vec_relation; auto.
  Qed.

  (*** how the scheduler behaves affects a thread *)
  (** inverting the case when a [schedule] is a [BrD] *)
  Lemma BrD_schedule_inv n1 k n2 (v : vec n2) i :
    BrD n1 k ≅ schedule n2 v (Some i) ->
    (exists k', v i ≅ BrD n1 k' /\
             forall i', k i' ≅ schedule n2 (replace_vec v i (k' i')) (Some i)) \/
      (exists k', v i ≅ Vis (inl1 Yield) k' /\
               n1 = 1%nat /\
               forall i', k i' ≅ schedule n2 (replace_vec v i (k' tt)) None) \/
      (exists n2' H1, v i ≅ Ret () /\
                   n1 = 1%nat /\
                   forall i', k i' ≅ schedule n2' (remove_vec_helper n2 n2' v i H1) None).
  Proof.
    intros Hequ.
    rewrite rewrite_schedule in Hequ.
    destruct n2 as [| n2]; [inv i |].
    simp schedule_match in Hequ.
    destruct (observe (v i)) eqn:?; cbn in Hequ.
    - destruct r.
      right. right. step in Hequ. pose proof (equb_br_invT _ _ Hequ) as [? _]. subst.
      pose proof (equb_br_invE _ _ Hequ).
      exists n2, eq_refl. split; auto. step. rewrite Heqc. reflexivity.
    - destruct e; [destruct y | destruct s; [destruct f |]]; try solve [step in Hequ; inv Hequ].
      step in Hequ. pose proof (equb_br_invT _ _ Hequ) as [? _]. subst.
      pose proof (equb_br_invE _ _ Hequ).
      right. left. eexists. split; auto. step. rewrite Heqc. reflexivity.
    - destruct vis; [step in Hequ; inv Hequ |].
      pose proof (equ_br_invT _ _ Hequ) as [? _]; subst.
      pose proof (equ_br_invE _ _ Hequ).
      left. exists k0. split; auto.
      step. rewrite Heqc. reflexivity.
  Qed.

  (** Helper lemmas for when [schedule] transitions with a [val] *)
  Lemma trans_schedule_val_1 {X} n v i (x : X) t :
    trans (val x) (schedule n v (Some i)) t ->
    n = 1%nat.
  Proof.
    intro. unfold trans in *; cbn in H. red in H.
    remember (observe (schedule n v (Some i))).
    pose proof (ctree_eta (go (observe (schedule n v (Some i))))).
    rewrite <- Heqc in H0 at 1. cbn in H0. clear Heqc.
    remember (observe t). remember (val x).
    revert n t v i x Heql Heqc0 H0.
    induction H; intros n' t' v i x' Heql Heq Hequ; try inv Heql; subst.
    - rewrite <- ctree_eta in Hequ.
      apply BrD_schedule_inv in Hequ. destruct Hequ as [? | [? | ?]].
      + destruct H0 as (k' & Hvic & Hk).
        eapply IHtrans_; eauto.
        rewrite Hk. reflexivity.
      + destruct H0 as (k' & Hvic & Hn & Hk). subst.
        rewrite Hk in H. rewrite rewrite_schedule in H.
        destruct n'; [inv i | inv H].
      + destruct H0 as (n'' & Hn2' & Hvic & Hn & Hk).
        rewrite Hk in H. rewrite rewrite_schedule in H.
        destruct n''; auto. inv H.
    - invert. rewrite rewrite_schedule in Hequ.
      destruct n'; [inv i |].
      simp schedule_match in Hequ.
      destruct (observe (v i)) eqn:Hv; cbn in Hequ.
      + destruct r; step in Hequ; inv Hequ.
      + destruct e; [destruct y | destruct s; [destruct f |]]; step in Hequ; inv Hequ.
      + step in Hequ; inv Hequ.
  Qed.

  Lemma trans_schedule_thread_val {X} v i (x : X) t :
    trans (val x) (schedule 1 v (Some i)) t ->
    trans (val x) (v i) CTree.stuckD.
  Proof.
    intro. unfold trans in *; cbn in H. red in H.
    remember (observe (schedule 1 v (Some i))).
    pose proof (ctree_eta (go (observe (schedule 1 v (Some i))))).
    rewrite <- Heqc in H0 at 1. cbn in H0. clear Heqc.
    remember (observe t). remember (val x).
    revert t v i x Heql Heqc0 H0.
    induction H; intros t' v i x' Heql Heq Hequ; try inv Heql; subst.
    - rewrite <- ctree_eta in Hequ. cbn.
      apply BrD_schedule_inv in Hequ. destruct Hequ as [? | [? | ?]].
      + destruct H0 as (k' & Hvic & Hk).
        setoid_rewrite Hk in IHtrans_. rewrite Hvic. econstructor.
        specialize (IHtrans_ _ (replace_vec v i (k' x)) i _ eq_refl eq_refl).
        rewrite replace_vec_eq in IHtrans_. apply IHtrans_. reflexivity.
      + destruct H0 as (k' & Hvic & Hn & Hk). subst.
        rewrite Hk in H. inv H.
      + destruct H0 as (n2' & Hn2' & Hvic & Hn & Hk).
        assert (n2' = O). { clear Hk. inv Hn2'. reflexivity. } subst.
        rewrite Hk in H. rewrite rewrite_schedule in H. simp schedule_match in H.
        apply trans_ret_inv in H. destruct H. inv H0. invert.
        rewrite Hvic. constructor.
    - invert.
      rewrite rewrite_schedule in Hequ.
      simp schedule_match in Hequ.
      destruct (observe (v i)) eqn:Hv; cbn in Hequ.
      + destruct r. step in Hequ. inv Hequ.
      + destruct e; [destruct y | destruct s; [destruct f |]]; step in Hequ; inv Hequ.
      + step in Hequ; inv Hequ.
  Qed.

  (** [schedule] transitions with an [obs] of a [Yield] *)
  Lemma trans_schedule_obs_yield_None n v t (Hbound : forall i, brD_bound 1 (v i)) :
    trans (obs (inl1 Yield) tt) (schedule n v None) t ->
    exists n', n = S n' /\ t ≅ BrD n (fun i => schedule n v (Some i)).
  Proof.
    unfold trans. intros. cbn in H. red in H.
    remember (observe (schedule n v None)).
    pose proof (ctree_eta (go (observe (schedule n v None)))).
    rewrite <- Heqc in H0 at 1. cbn in H0. clear Heqc.
    remember (observe t). remember (obs _ _).
    revert t n v Heqc0 Heql H0 Hbound.
    induction H; intros t' n' v Heq Heql Hequ Hbound; subst; try inv Heql.
    2: {
      invert. destruct n'.
      - rewrite <- ctree_eta in Hequ.
      rewrite rewrite_schedule in Hequ. simp schedule_match in Hequ. step in Hequ. inv Hequ.
      - rewrite <- ctree_eta in Hequ.
        rewrite rewrite_schedule in Hequ. simp schedule_match in Hequ.
        step in Hequ. inv Hequ. invert. exists n'.
        rewrite ctree_eta. rewrite <- Heq. rewrite <- H. rewrite REL. split; auto.
    }
    destruct n'.
    - rewrite <- ctree_eta in Hequ.
      rewrite rewrite_schedule in Hequ. simp schedule_match in Hequ. step in Hequ. inv Hequ.
    - rewrite <- ctree_eta in Hequ.
      rewrite rewrite_schedule in Hequ. simp schedule_match in Hequ. step in Hequ. inv Hequ.
  Qed.

  Lemma trans_schedule_obs_yield_Some n v i t (Hbound : forall i, brD_bound 1 (v i)) :
    trans (obs (inl1 Yield) tt) (schedule n v (Some i)) t ->
    (exists n',
        trans (val ()) (v i) CTree.stuckD /\
          {H: n = S (S n') &
                t ≅ BrD (S n') (fun i' => schedule (S n') (remove_vec_helper n (S n') v i H) (Some i'))}) \/
      (exists k, visible (v i) (Vis (inl1 Yield) k) /\
              t ≅ BrD n (fun i' => schedule n (replace_vec v i (k tt)) (Some i'))).
  Proof.
    unfold trans. intros. cbn in H. red in H.
    remember (observe (schedule n v (Some i))).
    pose proof (ctree_eta (go (observe (schedule n v (Some i))))).
    rewrite <- Heqc in H0 at 1. cbn in H0. clear Heqc.
    remember (observe t). remember (obs _ _).
    revert t n v i Heqc0 Heql H0 Hbound.
    induction H; intros t' n' v i Heq Heql Hequ Hbound; subst; try inv Heql.
    2: {
      (* not possible to immediately start with a Yield, must have a BrD first *)
      invert. destruct n'; try inv i.
      rewrite rewrite_schedule in Hequ. simp schedule_match in Hequ.
      destruct (observe (v i)) eqn:?; cbn in Hequ.
      - step in Hequ; inv Hequ.
      - destruct e; [destruct y | destruct s; [destruct f |]].
          try solve [step in Hequ; inv Hequ].
        rewrite <- ctree_eta in Hequ. step in Hequ; inv Hequ. invert.
        rewrite <- ctree_eta in Hequ. step in Hequ; inv Hequ. invert.
      - step in Hequ; inv Hequ.
    }
    {
      rewrite <- ctree_eta in Hequ.
      apply BrD_schedule_inv in Hequ. destruct Hequ as [? | [? | ?]].
      - destruct H0 as (k' & Hvi & Hk).
        edestruct IHtrans_; [reflexivity | reflexivity | rewrite Hk; reflexivity | | |].
        + intros i'. destruct (Fin.eq_dec i i'); subst.
          * rewrite replace_vec_eq. specialize (Hbound i').
            rewrite Hvi in Hbound.
            step in Hbound. inv Hbound. invert. apply H2.
          * rewrite replace_vec_neq; auto.
        + destruct H0 as (n'' & Ht & ? & Hequ). subst.
          left. cbn in *. rewrite replace_vec_eq in Ht.
          rewrite <- remove_vec_replace_vec_eq in Hequ.
          exists n''. split; [| exists eq_refl].
          * rewrite Hvi. red. econstructor. apply Ht.
          * apply Hequ.
        + destruct H0 as (k'' & Hvis & Hequ).
          right. rewrite replace_vec_eq in Hvis.
          exists k''. split.
          * rewrite Hvi. red. econstructor. apply Hvis.
          * rewrite Hequ. step. constructor. intros.
            rewrite replace_vec_twice. auto.
      - (* the thread is a Yield *)
        clear IHtrans_. destruct H0 as (k' & Hvi & ? & Hk); subst.
        right. eexists. split.
        rewrite Hvi. constructor. reflexivity.
        rewrite Hk in H. cbn in H.
        apply trans_schedule_obs_yield_None in H.
        + destruct H as (? & ? & ?); subst. auto.
        + eapply replace_vec_brD_bound; auto.
          specialize (Hbound i).
          rewrite Hvi in Hbound.
          step in Hbound. inv Hbound. invert. apply H1.
      - (* the thread is a Ret *)
        clear IHtrans_. destruct H0 as (n'' & ? & Hvi & ? & Hk). subst. cbn in *.
        (* apply trans_schedule_obs_yield_None in H; auto. *)
        left. rewrite Hk in H.
        (* destruct n''; [inv H |]. *)
        apply trans_schedule_obs_yield_None in H.
        2: apply remove_vec_brD_bound; auto.
        destruct H as (n' & ? & ?). subst.
        exists n'. split; auto.
        + rewrite Hvi. constructor.
        + exists eq_refl. auto.
    }
  Qed.

  (** [schedule] transitions with an [obs] of a [Fork] *)
  (** [schedule] transitions with an [obs] of an event of type [E] *)
  (*  TODO *)

  (** [schedule] transitions with a [tau]: impossible case *)
  Lemma trans_schedule_thread_tau_none n v t :
    trans tau (schedule n v None) t ->
    False.
  Proof.
    intros Ht.
    unfold trans in Ht. cbn in Ht. red in Ht. destruct n; inv Ht.
  Qed.

  (** [schedule] transitions with a [tau] *)
  Lemma trans_schedule_thread_tau_some n v i t (Hbound : brD_bound 1 (v i)) :
    trans tau (schedule n v (Some i)) t ->
      (exists t', trans tau (v i) t' /\
               brD_bound 1 t' /\
               t ≅ schedule n (replace_vec v i t') (Some i)).
  Proof.
    unfold trans. intros. cbn in H. red in H.
    remember (observe (schedule n v (Some i))).
    pose proof (ctree_eta (go (observe (schedule n v (Some i))))).
    rewrite <- Heqc in H0 at 1. cbn in H0. clear Heqc.
    remember (observe t). remember tau.
    revert t n v i Heqc0 Heql H0 Hbound.
    induction H; intros t' n' v i Heq Heql Hequ Hbound; subst; try inv Heql.
    {
      rewrite <- ctree_eta in Hequ.
      apply BrD_schedule_inv in Hequ. destruct Hequ as [? | [? | ?]].
      - destruct H0 as (k' & Hvi & Hk).
        edestruct IHtrans_; auto; clear IHtrans_.
        rewrite Hk. reflexivity.
        rewrite replace_vec_eq. rewrite Hvi in Hbound.
        step in Hbound. inv Hbound. invert. apply H2. cbn in *.
        rename x0 into t''.
        destruct H0 as (Ht & Hbound' & Hequ).
        rewrite replace_vec_eq in Ht. rewrite replace_vec_twice in Hequ.
        exists t''. split; [| split]; auto.
        rewrite Hvi. red. econstructor. eauto.
      - clear IHtrans_. destruct H0 as (k' & Hequ & ? & Hk). subst.
        rewrite Hk in H. apply trans_schedule_thread_tau_none in H. contradiction.
      - clear IHtrans_. destruct H0 as (n'' & ? & Hvi & ? & Hk). subst. cbn in *.
        rewrite Hk in H. apply trans_schedule_thread_tau_none in H. contradiction.
    }
    {
      destruct n'; try inv i.
      rewrite rewrite_schedule in Hequ. simp schedule_match in Hequ.
      destruct (observe (v i)) eqn:?; cbn in Hequ.
      - step in Hequ. inv Hequ.
      - destruct e; [destruct y | destruct s; [destruct f |]]; cbn in Hequ; step in Hequ; inv Hequ.
      - destruct (equ_br_invT _ _ Hequ). subst.
        pose proof (equ_br_invE _ _ Hequ). cbn.
        exists (k0 x). split; [| split]; auto.
        + red. rewrite Heqc. econstructor; eauto.
        + step in Hbound. pose proof (ctree_eta (v i)). erewrite Heqc in H1.
          rewrite H1 in Hbound. inv Hbound. invert. auto.
        + rewrite ctree_eta. rewrite <- Heq. rewrite <- ctree_eta. rewrite <- H.
          rewrite H0. auto.
     }
  Qed.

  (*** how a thread [trans] affects the scheduler [trans] *)

  (** thread transitions with a val *)
  Lemma trans_thread_schedule_val_1 {X} v i (x : X) t :
    trans (val x) (v i) t ->
    trans (val x) (schedule 1 v (Some i)) CTree.stuckD.
  Proof.
    intro. unfold trans in *; cbn in H. red in H.
    remember (observe (v i)).
    pose proof (ctree_eta (go (observe (v i)))).
    rewrite <- Heqc in H0 at 1. cbn in H0. clear Heqc.
    remember (observe t). cbn. remember (val x).
    revert t v i x Heql Heqc0 H0.
    induction H; intros t' v i x' Heql Heq Hequ; try inv Heql.
    - step in Hequ. inv Hequ. invert.
      rewrite rewrite_schedule. simp schedule_match. rewrite <- H4.
      econstructor. eapply IHtrans_; try reflexivity. rewrite REL.
      rewrite replace_vec_eq. reflexivity.
    - invert. step in Hequ. inv Hequ.
      rewrite rewrite_schedule. simp schedule_match. rewrite <- H.
      destruct y. econstructor; eauto.
      rewrite rewrite_schedule. constructor.
  Qed.

  Lemma trans_thread_schedule_val_SS n v i t :
    trans (val ()) (v i) t ->
    trans (obs (inl1 Yield) ())
          (schedule (S (S n)) v (Some i))
          (BrD (S n) (fun i' => (schedule (S n) (remove_vec v i) (Some i')))).
  Proof.
    unfold trans; intro. cbn in *. red in H.
    remember (observe (v i)).
    pose proof (ctree_eta (go (observe (v i)))).
    rewrite <- Heqc in H0 at 1. cbn in H0. clear Heqc.
    remember (observe t). remember (val ()).
    revert t v i Heql Heqc0 H0.
    induction H; intros t' v i Heql Heq Hequ; try inv Heql.
    - step in Hequ. inv Hequ. invert.
      epose proof (IHtrans_ t' (replace_vec v i (k2 x)) i eq_refl eq_refl _).
      Unshelve.
      2: { rewrite REL. rewrite replace_vec_eq. reflexivity. }
      setoid_rewrite rewrite_schedule at 1. simp schedule_match. rewrite <- H4. cbn.
      econstructor. erewrite <- remove_vec_replace_vec_eq in H0. apply H0.
    - invert. step in Hequ. inv Hequ.
      setoid_rewrite rewrite_schedule at 1. simp schedule_match. rewrite <- H. cbn.
      constructor. constructor.
      rewrite rewrite_schedule. simp schedule_match. econstructor.
      step. econstructor. reflexivity.
  Qed.

  (** thread transitions with a tau *)
  Lemma trans_thread_schedule_tau n v i t :
    trans tau (v i) t ->
    trans tau (schedule (S n) v (Some i)) (schedule (S n) (replace_vec v i t) (Some i)).
  Proof.
    unfold trans; intro. cbn in *. red in H.
    remember (observe (v i)).
    pose proof (ctree_eta (go (observe (v i)))).
    rewrite <- Heqc in H0 at 1. cbn in H0. clear Heqc.
    remember (observe t). remember tau.
    revert t v i Heql Heqc0 H0.
    induction H; intros t' v i Heql Heq Hequ; try inv Heql.
    - step in Hequ. inv Hequ. invert.
      rewrite rewrite_schedule. simp schedule_match. rewrite <- H4.
      constructor 1 with (x:=x).
      erewrite <- (replace_vec_twice (S n) v i (k2 x) t').
      apply IHtrans_; auto.
      rewrite replace_vec_eq. rewrite REL. reflexivity.
    - step in Hequ. inv Hequ. invert.
      rewrite rewrite_schedule. simp schedule_match. rewrite <- H4.
      constructor 2 with (x:=x).
      pose proof (ctree_eta t).
      rewrite Heq in H0. clear Heq. rename H0 into Heq. rewrite <- ctree_eta in Heq.
      apply equ_schedule. (* TODO: some instance is missing *)
      apply replace_vec_relation; repeat intro; try reflexivity.
      rewrite <- Heq. rewrite <- REL. auto.
  Qed.

  (*** how thread struture (via [visible]) affects the scheduler [trans] *)

  (** when the thread is a yield *)
  Lemma visible_yield_trans_schedule n v i k (Hbound : brD_bound 1 (v i)) :
    visible (v i) (Vis (inl1 Yield) k) ->
    trans (obs (inl1 Yield) tt)
          (schedule (S n) v (Some i))
          (BrD (S n) (fun i' => (schedule (S n) (replace_vec v i (k tt)) (Some i')))).
  Proof.
    intros. cbn in *. red in H |- *. red.
    remember (observe (v i)). remember (observe (Vis _ k)).
    revert v i k Heqc Heqc0 Hbound.
    induction H; intros; subst; try inv Heqc0.
    - edestruct @brD_bound_1_inv as (? & Hbound').
      {
        assert (v i ≅ BrD n0 k).
        rewrite ctree_eta. rewrite <- Heqc. reflexivity.
        rewrite H0 in Hbound. apply Hbound.
      } subst.
      rewrite rewrite_schedule at 1. simp schedule_match.
      rewrite <- Heqc. constructor 1 with (x:=x).
      rewrite <- (replace_vec_twice _ v i (k x) (k0 tt)).
      eapply IHvisible_; auto; rewrite replace_vec_eq; eauto.
    - invert.
      rewrite rewrite_schedule at 1. simp schedule_match.
      rewrite <- Heqc. econstructor. constructor.
      rewrite rewrite_schedule at 1. simp schedule_match.
      econstructor. step. constructor. intros. apply equ_schedule.
      apply replace_vec_relation; repeat intro; auto.
  Qed.

  (** when the thread is a fork *)
  Lemma visible_fork_trans_schedule n v i k (Hbound : brD_bound 1 (v i)) :
    visible (v i) (Vis (inr1 (inl1 Fork)) k) ->
    trans (obs (inr1 (inl1 Spawn)) tt)
          (schedule (S n) v (Some i))
          (schedule (S (S n))
                    (cons_vec (k true)
                              (replace_vec v i (k false)))
                    (Some (FS i))).
  Proof.
    intros. cbn in *. red in H |- *. red.
    remember (observe (v i)). remember (observe (Vis _ k)).
    revert v i k Heqc Heqc0 Hbound.
    induction H; intros; subst; try inv Heqc0.
    - edestruct @brD_bound_1_inv as (? & Hbound').
      {
        assert (v i ≅ BrD n0 k).
        rewrite ctree_eta. rewrite <- Heqc. reflexivity.
        rewrite H0 in Hbound. apply Hbound.
      } subst.
      rewrite rewrite_schedule at 1. simp schedule_match.
      rewrite <- Heqc. constructor 1 with (x:=x).
      rewrite <- (replace_vec_twice _ v i (k x) (k0 false)).
      eapply IHvisible_; auto; rewrite replace_vec_eq; eauto.
    - invert.
      rewrite rewrite_schedule at 1. simp schedule_match.
      rewrite <- Heqc. econstructor. apply equ_schedule.
      apply cons_vec_relation; auto.
      apply replace_vec_relation; repeat intro; auto.
  Qed.

  (** when the thread is a [E] event *)
  Lemma visible_E_trans_schedule {X} n v i (s : E X) k x (Hbound : brD_bound 1 (v i)) :
    visible (v i) (Vis (inr1 (inr1 s)) k) ->
    trans (obs (inr1 (inr1 s)) x)
          (schedule (S n) v (Some i))
          (schedule (S n) (replace_vec v i (k x)) (Some i)).
  Proof.
    intros. cbn in *. red in H |- *. red.
    remember (observe (v i)). remember (observe (Vis _ k)).
    revert v i k Heqc Heqc0 Hbound.
    induction H; intros; subst; try inv Heqc0.
    - edestruct @brD_bound_1_inv as (? & Hbound').
      {
        assert (v i ≅ BrD n0 k).
        rewrite ctree_eta. rewrite <- Heqc. reflexivity.
        rewrite H0 in Hbound. apply Hbound.
      } subst.
      rewrite rewrite_schedule at 1. simp schedule_match.
      rewrite <- Heqc. econstructor.
      rewrite <- (replace_vec_twice _ v i (k x0) (k0 x)).
      eapply IHvisible_; auto; rewrite replace_vec_eq; eauto.
    - invert.
      rewrite rewrite_schedule at 1. simp schedule_match.
      rewrite <- Heqc. econstructor. apply equ_schedule.
      apply replace_vec_relation; repeat intro; auto.
  Qed.

  (*** Putting everything together *)
  Lemma schedule_permutation n (v1 v2 : vec n) i (p q : fin n -> fin n)
        (Hbound1 : forall i, brD_bound 1 (v1 i))
        (Hbound2 : forall i, brD_bound 1 (v2 i))
        (Hpq : forall i, p (q i) = i)
        (Hqp : forall i, q (p i) = i)
        (Hsb1 : forall i, v1 i ~ v2 (p i))
        (Hsb2 : forall i, v2 i ~ v1 (q i)) :
    schedule n v1 (Some i) ~ schedule n v2 (Some (p i)).
  Proof.
    revert n v1 v2 i p q Hbound1 Hbound2 Hpq Hqp Hsb1 Hsb2.
    coinduction r CIH.
    symmetric using idtac.
    {
      intros. rewrite <- (Hqp i) at 2.
      eapply H; auto.
    }
    intros n v1 v2 i p q Hbound1 Hbound2 Hpq Hqp Hsb1 Hsb2 l t Ht. cbn in *.
    destruct l.
    - apply trans_schedule_thread_tau_some in Ht; auto.
      assert (Hinjp : Injective p) by (eapply bijective_injective; eauto).
      assert (Hinjq : Injective q) by (eapply bijective_injective; eauto).
      destruct n; try inv i.
      destruct Ht as (t' & Ht & Hbound & Hequ).
      pose proof (Hsb1 i). step in H. destruct H as [Hf _].
      edestruct Hf as [? ? ?]; eauto.
      pose proof (trans_brD_bound _ _ _ _ _ (Hbound2 _) H) as Hbound'.
      apply trans_thread_schedule_tau in H.
      eexists; eauto. rewrite Hequ.
      eapply CIH; clear CIH; eauto.
      1, 2: try solve [apply replace_vec_brD_bound; auto].
      + intros. destruct (Fin.eq_dec i i0).
        * subst. do 2 (rewrite replace_vec_eq; auto).
        * do 2 (rewrite replace_vec_neq; auto).
      + intros. destruct (Fin.eq_dec (p i) i0).
        * subst. rewrite Hqp. do 2 (rewrite replace_vec_eq; auto). symmetry; auto.
        * do 2 (rewrite replace_vec_neq; auto). intro.
          apply (f_equal p) in H1. rewrite Hpq in H1. contradiction.
    - destruct e; [destruct y; destruct v | destruct s; [destruct s; destruct v |]].
      + apply trans_schedule_obs_yield_Some in Ht; auto. destruct Ht.
        * (* The thread finished *)
          destruct H as (n' & Ht & (? & Hequ)); subst. cbn in *.
          assert (Hinjp : Injective p) by (eapply bijective_injective; eauto).
          assert (Hinjq : Injective q) by (eapply bijective_injective; eauto).

          pose proof (@remove_at_permutation_correct (yieldE +' forkE +' E) unit _ _ _ i Hpq Hqp Hinjp Hinjq) as (Hpq' & Hqp').
          edestruct (@remove_at_permutation_vectors (yieldE +' forkE +' E) unit n') as (Hpq'' & Hqp''); eauto.
          pose proof (Hsb1 i). step in H. destruct H as [Hf _].
          edestruct Hf as [? ? ?]; eauto.
          apply trans_thread_schedule_val_SS in H.
          exists (BrD (S n') (fun i' : fin (S n') => schedule
                                               (S n')
                                               (remove_vec v2 (p i))
                                               (Some
                                                  ((projT1 (@remove_at_permutation (yieldE +' forkE +' E) unit _ p i Hinjp))
                                                     (projT1 (@remove_at_permutation (yieldE +' forkE +' E) unit _ q (p i) Hinjq) i'))))).
          2: {
            rewrite Hequ. cbn.
            setoid_rewrite <- (bind_ret_l _ (fun x => schedule
                                                    (S n')
                                                    (remove_vec v1 i)
                                                    (Some x))).
            setoid_rewrite <- (bind_ret_l _ (fun x => schedule
                                                    (S n')
                                                    (remove_vec v2 (p i))
                                                    (Some ((projT1 (remove_at_permutation p i Hinjp)) x)))).
            do 2 erewrite <- bind_br.
            eapply st_clo_bind.
            {
              apply sb_brD.
              - intros y. exists ((projT1 (@remove_at_permutation (yieldE +' forkE +' E) unit _ p i Hinjp)) y). rewrite Hqp'. auto.
              - intros y. exists ((projT1 (@remove_at_permutation (yieldE +' forkE +' E) unit _ q (p i) Hinjq)) y). auto.
            }
            intros.
            eapply CIH; clear CIH.
            intros; apply remove_vec_brD_bound; auto.
            intros; apply remove_vec_brD_bound; auto.
            apply Hpq'.
            apply Hqp'.
            apply Hpq''.
            apply Hqp''.
          }
          replace (fun i' : fin (S n') =>
                     schedule (S n') (remove_vec v2 (p i))
                              (Some
                                 (projT1 (remove_at_permutation p i Hinjp)
                                         (projT1 (remove_at_permutation q (p i) Hinjq) i')))) with
            (fun i' : fin (S n') =>
               schedule (S n') (remove_vec v2 (p i))
                        (Some i')).
          2: { apply functional_extensionality. intros. rewrite Hpq'. reflexivity. }
          auto.
        * (* The thread yields *)
          destruct n; try inv i.
          destruct H as (k & Hvis & Hequ).
          pose proof Hvis as Hvis'.
          eapply sbisim_visible in Hvis'. 5: apply Hsb1. all: auto.
          destruct Hvis' as (k' & Hvis' & Hk).
          exists (BrD (S n) (fun i' => schedule (S n) (replace_vec v2 (p i) (k' tt)) (Some (p (q i'))))).
          2: { rewrite Hequ.
               setoid_rewrite <- (bind_ret_l _ (fun x => schedule
                                                       (S n)
                                                       (replace_vec v1 i (k ()))
                                                       (Some x))).
               setoid_rewrite <- (bind_ret_l _ (fun x => schedule
                                                       (S n)
                                                       (replace_vec v2 (p i) (k' ()))
                                                       (Some (p x)))).
               do 2 erewrite <- bind_br.
               eapply st_clo_bind.
               {
                 apply sb_brD.
                 - intros x. exists (p x). rewrite Hqp. reflexivity.
                 - intros x. exists (q x). reflexivity.
               }
               intros. eapply CIH; clear CIH; eauto.
               - intro. apply replace_vec_brD_bound; auto.
                 eapply visible_brD_bound in Hvis; eauto.
                 eapply trans_brD_bound; eauto. constructor. reflexivity.
               - intro. apply replace_vec_brD_bound; auto.
                 eapply visible_brD_bound in Hvis'; eauto.
                 eapply trans_brD_bound; eauto. constructor. reflexivity.
               - intros. destruct (Fin.eq_dec i i0).
                 + subst. do 2 rewrite replace_vec_eq; auto.
                 + do 2 (rewrite replace_vec_neq; auto). intro.
                   apply (f_equal q) in H. do 2 rewrite Hqp in H. contradiction.
               - intros. destruct (Fin.eq_dec (p i) i0).
                 + subst. rewrite Hqp. do 2 rewrite replace_vec_eq; auto. symmetry; auto.
                 + do 2 (rewrite replace_vec_neq; auto). intro.
                   apply (f_equal p) in H. rewrite Hpq in H. contradiction.
          }
          (* some proper instance is missing so I had to do this *)
          replace (fun i' : fin (S n) =>
                     schedule (S n) (replace_vec v2 (p i) (k' ())) (Some (p (q i')))) with
            (fun i' : fin (S n) =>
               schedule (S n) (replace_vec v2 (p i) (k' ())) (Some i')).
          2: { apply functional_extensionality. intros. rewrite Hpq. reflexivity. }
          eapply visible_yield_trans_schedule; auto.
      + (* the thread forks a new thread *)
        admit.
      + (* there is some other event *)
        admit.
    - pose proof (trans_schedule_val_1 _ _ _ _ _ Ht). subst.
      pose proof (trans_val_inv Ht).
      pose proof (Hsb1 i). step in H0. destruct H0 as [Hf _].
      pose proof (trans_schedule_thread_val _ _ _ _ Ht) as Hv1.
      edestruct Hf; eauto.
      apply trans_thread_schedule_val_1 in H0. eexists; eauto. rewrite H. reflexivity.
  Qed.

  Definition perm_id {n} : fin n -> fin n := fun i => i.

  Lemma sbisim_schedule n (v1 v2 : vec n) i
        (Hbound1 : forall i, brD_bound 1 (v1 i))
        (Hbound2 : forall i, brD_bound 1 (v2 i))
        (Hsb : forall i, v1 i ~ v2 i) :
    schedule n v1 (Some i) ~ schedule n v2 (Some i).
  Proof.
    replace i with (perm_id i) at 2; auto.
    eapply schedule_permutation; auto. symmetry. auto.
  Qed.

End parallel.
