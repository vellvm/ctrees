From Stdlib Require Import
     Program
     List
     Logic.FunctionalExtensionality
     Logic.IndefiniteDescription
     Vectors.FinFun
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
 	Interp.FoldStateT.

From CTreeYield Require Import
  Util.

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

  Definition thread := ctree (yieldE +' forkE +' E) void1 unit.
  Definition completed := ctree (yieldE +' spawnE +' E) Bn unit.
  Definition vec n := fin n -> thread.

  (** Scheduling a thread pool *)
  Equations schedule_match
             (schedule : forall (n : nat), vec n -> option (fin n) -> completed)
             (n : nat)
             (v: vec n)
    : option (fin n) -> completed :=
    (* If no thread is focused, and there are none left in the pool, we are done *)
    schedule_match schedule 0 v None :=
      Ret ();

    (* If no thread is focused, but there are some left in the pool, we pick one *)
    schedule_match schedule (S n) v None :=
      Vis (inl1 Yield)
          (fun _ =>
             Br (branchn (S n)) (fun i' => schedule (S n) v (Some i')));

    (* If a thread is focused on, we analyze its head constructor *)
    schedule_match schedule (S n) v (Some i) with observe (v i) =>
      {
        (* If it's a [Ret], we simply remove it from the pool and focus *)
        schedule_match _ _ _ _ (RetF _) :=
        Guard (schedule n (remove_vec v i) None);

        (* If it's a [Br], we propagate the br and update the thread *)
        schedule_match _ _ _ _ (BrF n' k) :=
          match n' with end;
        (* br n' (fun i' => schedule (S n) (replace_vec v i (k i')) (Some i)); *)

        (* If it's a [Guard], we propagate the Guard and update the thread *)
        schedule_match _ _ _ _ (GuardF t) :=
        Guard (schedule (S n) (replace_vec v i t) (Some i));

        (* If it's a [Step], we propagate the step and update the thread *)
        schedule_match _ _ _ _ (StepF t) :=
        Step (schedule (S n) (replace_vec v i t) (Some i));

        (* If it's a [Stuck], we are stuck *)
        schedule_match _ _ _ _ StuckF :=
        Stuck;

        (* If it's a [Yield], we remove the focus *)
        schedule_match _ _ _ _ (VisF (inl1 Yield) k) :=
        Guard (schedule (S n) (replace_vec v i (k ())) None);

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
        schedule_match _ _ _ _ (VisF (inr1 (inr1 e)) k) :=
        Vis (inr1 (inr1 e)) (fun x => (schedule (S n) (replace_vec v i (k x)) (Some i)));

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
    step in H. cbn. inv H; eauto. 4: destruct e. 5: destruct s. all: cbn.
    - clear H1 H2. destruct y; cbn in *; auto.
      constructor. intros. apply CIH.
      apply remove_vec_relation; auto.
    - constructor. eapply CIH.
      apply replace_vec_relation; auto.
    - constructor. eapply CIH.
      apply replace_vec_relation; auto.
    - clear H1 H2. destruct y.
      constructor. intros. eapply CIH.
      apply replace_vec_relation; auto.
    - destruct f. constructor. intros. eapply CIH.
      apply cons_vec_relation; auto.
      apply replace_vec_relation; auto.
    - constructor. intros. apply CIH.
      apply replace_vec_relation; auto.
    (* - constructor. intros. apply CIH. *)
      (* apply replace_vec_relation; auto. *)
  Qed.

  (*** how the scheduler behaves affects a thread *)
  (** inverting the case when a [schedule] is a [Br] *)
  Lemma Br_schedule_inv n1 (e : Bn (fin n1)) k n2 (v : vec n2) i :
    Br e k ≅ schedule n2 v (Some i) -> False.
  (*   (exists k', v i ≅ Br e k' /\ *)
  (*            forall i', k i' ≅ schedule n2 (replace_vec v i (k' i')) (Some i)). *)
  Proof.
    intros Hequ.
    rewrite rewrite_schedule in Hequ.
    destruct n2 as [| n2]; [inv i |].
    simp schedule_match in Hequ.
    destruct (observe (v i)) eqn:?; cbn in Hequ; inv_equ.
    destruct e0; [destruct y | destruct s; [destruct f |]]; try solve [step in Hequ; inv Hequ].
    destruct c.
  Qed.

  Lemma guard_schedule_inv t n (v : vec (S n)) (i : fin (S n)) :
    Guard t ≅ schedule _ v (Some i) ->
    (exists  t', v i ≅ Guard t' /\
             t ≅ schedule (S n) (replace_vec v i t') (Some i)) \/

    (exists k, v i ≅ Vis (inl1 Yield) k /\
               t ≅ schedule (S n) (replace_vec v i (k ())) None) \/
      (v i ≅ Ret tt /\ t ≅ schedule n (remove_vec v i) None).
  Proof.
    intros Hequ.
    rewrite rewrite_schedule in Hequ.
    simp schedule_match in Hequ.
    destruct (observe (v i)) eqn:?; cbn in Hequ; inv_equ; auto.
    - right; right.
      destruct r.
      split; auto.
      step; rewrite Heqc; reflexivity.
    - left; eexists; split; eauto.
      step; rewrite Heqc; reflexivity.
    - destruct e; [destruct y | destruct s]; inv_equ.
      right; left; auto.
      eexists; split.
      step; rewrite Heqc; reflexivity.
      auto.
      destruct f; inv_equ.
    - destruct c.
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
    induction H; intros n' ?t' v i x' Heql Heq Hequ; try inv Heql; subst.
    - rewrite <- ctree_eta in Hequ.
      destruct c.
      now exfalso; apply Br_schedule_inv in Hequ.
    - rewrite <- ctree_eta in Hequ.
      destruct n' as [| n]; [inv i |].
      apply guard_schedule_inv in Hequ.
      destruct Hequ as [Hequ | [Hequ | Hequ]].
      + destruct Hequ as (t' & Hvic & Ht).
        eapply IHtrans_; eauto.
        rewrite Ht. reflexivity.
      + destruct Hequ as (k' & Hvic & Hk).
        rewrite Hk in H. rewrite rewrite_schedule in H.
        inv H.
      + destruct Hequ as [EQ EQ'].
        rewrite EQ' in H. rewrite rewrite_schedule in H.
        destruct n; auto. inv H.

    - invert. rewrite rewrite_schedule in Hequ.
      destruct n'; [inv i |].
      simp schedule_match in Hequ.
      destruct (observe (v i)) eqn:Hv; cbn in Hequ; inv_equ.
      destruct e; [destruct y | destruct s; [destruct f |]]; step in Hequ; inv Hequ.
      destruct c.
  Qed.

  Lemma trans_schedule_thread_val {X} v i (x : X) t :
    trans (val x) (schedule 1 v (Some i)) t ->
    trans (val x) (v i) Stuck.
  Proof.
    intro. unfold trans in *; cbn in H. red in H.
    remember (observe (schedule 1 v (Some i))).
    pose proof (ctree_eta (go (observe (schedule 1 v (Some i))))).
    rewrite <- Heqc in H0 at 1. cbn in H0. clear Heqc.
    remember (observe t). remember (val x).
    revert t v i x Heql Heqc0 H0.
    induction H; intros ?t' v i x' Heql Heq Hequ; try inv Heql; subst.
    - rewrite <- ctree_eta in Hequ. cbn.
      destruct c.
      exfalso; now apply Br_schedule_inv in Hequ.
    - rewrite <- ctree_eta in Hequ.
      apply guard_schedule_inv in Hequ.
      destruct Hequ as [Hequ | [Hequ | Hequ]].
      + destruct Hequ as (k' & Hvic & Hk).
        rewrite Hvic. econstructor.
        specialize (IHtrans_ _ (replace_vec v i k') i _ eq_refl eq_refl).
        setoid_rewrite Hk in IHtrans_.
        rewrite replace_vec_eq in IHtrans_. apply IHtrans_. reflexivity.
      + destruct Hequ as (k' & Hvic & Hk).
        rewrite Hk in H. rewrite rewrite_schedule in H.
        inv H.
      + destruct Hequ as [EQ EQ'].
        rewrite EQ' in H. rewrite rewrite_schedule in H.
        simp schedule_match in H.
        apply trans_ret_inv in H. destruct H. inv H0. invert.
        rewrite EQ.
        cbn.
        constructor.
    - invert.
      rewrite rewrite_schedule in Hequ.
      simp schedule_match in Hequ.
      destruct (observe (v i)) eqn:Hv; cbn in Hequ; inv_equ.
      destruct e; [destruct y | destruct s; [destruct f |]]; step in Hequ; inv Hequ.
      destruct c.
  Qed.

  (** [schedule] transitions with an [obs] of a [Yield] *)
  Lemma trans_schedule_obs_yield_None n v t :
    trans (obs (inl1 Yield) ()) (schedule n v None) t ->
    exists n', n = S n' /\
            t ≅ Br (branchn n) (fun i => schedule n v (Some i)).
  Proof.
    unfold trans. intros. cbn in H. red in H.
    remember (observe (schedule n v None)).
    pose proof (ctree_eta (go (observe (schedule n v None)))).
    rewrite <- Heqc in H0 at 1. cbn in H0. clear Heqc.
    remember (observe t). remember (obs _ _).
    revert t n v Heqc0 Heql H0.
    induction H; intros ?t' n' v Heq Heql Hequ; subst; try inv Heql.
    3: {
      invert. destruct n'; inv_equ.
      rewrite <- ctree_eta in Hequ.
      rewrite rewrite_schedule in Hequ. simp schedule_match in Hequ.
      step in Hequ. inv Hequ. invert. exists n'.
      rewrite ctree_eta. rewrite <- Heq. rewrite <- H. rewrite REL. split; auto.
    }
    - destruct n'; inv_equ.
    - destruct n'; inv_equ.
  Qed.

  Lemma trans_schedule_obs_yield_Some n v i t :
    trans (obs (inl1 Yield) ()) (schedule n v (Some i)) t ->

    (exists n',
        trans (val ()) (v i) Stuck /\
          {H: n = S (S n') &
                t ≅ Br (branchn (S n')) (fun i' => schedule (S n') (remove_vec_helper n (S n') v i H) (Some i'))}) \/
    (exists k, visible (v i) (Vis (inl1 Yield) k) /\
            t ≅ Br (branchn n) (fun i' => schedule n (replace_vec v i (k ())) (Some i'))).
  Proof.
    unfold trans. intros. cbn in H. red in H.
    remember (observe (schedule n v (Some i))).
    pose proof (ctree_eta (go (observe (schedule n v (Some i))))).
    rewrite <- Heqc in H0 at 1. cbn in H0. clear Heqc.
    remember (observe t). remember (obs _ _).
    revert t n v i Heqc0 Heql H0.
    induction H; intros ?t' n' v i Heq Heql Hequ; subst; try inv Heql.
    3: {
      (* not possible to immediately start with a Yield, must have a BrD first *)
      invert. destruct n'; try inv i.
      rewrite rewrite_schedule in Hequ. simp schedule_match in Hequ.
      destruct (observe (v i)) eqn:?; cbn in Hequ; inv_equ.
      - destruct e; [destruct y | destruct s; [destruct f |]].
          try solve [step in Hequ; inv Hequ].
        rewrite <- ctree_eta in Hequ. step in Hequ; inv Hequ. invert.
        rewrite <- ctree_eta in Hequ. step in Hequ; inv Hequ. invert.
      - destruct c.
    }
    {
      rewrite <- ctree_eta in Hequ.
      destruct n'; [inv i |].
      destruct c.
      exfalso; eapply Br_schedule_inv, Hequ.
    }
    rewrite <- ?ctree_eta in Hequ.
    destruct n'; [inv i |].
    eapply guard_schedule_inv in Hequ as [Hequ | [Hequ | Hequ]].
    - destruct Hequ as (k' & Hvi & Hk).
      edestruct IHtrans_; [reflexivity | reflexivity | | |].
      rewrite <- ?ctree_eta, Hk; reflexivity.
      + destruct H0 as (n'' & Ht & ? & Hequ).
        left. cbn in *. rewrite replace_vec_eq in Ht.
        exists n''. split.
        rewrite Hvi; constructor; apply Ht.
        exists x.
        rewrite Hequ.
        step; constructor; intros ?.
        now rewrite <- remove_vec_helper_replace_vec_eq.
      + destruct H0 as (? & Hvis & Ht).
        rewrite replace_vec_eq in Hvis.
        right; eexists; split.
        * rewrite Hvi; constructor; apply Hvis.
        * rewrite Ht. apply br_equ; intros ?.
          rewrite replace_vec_twice. auto.
    - destruct Hequ as (k' & Hvi & Hk).
      clear IHtrans_.
      right.
      eexists. split.
      rewrite Hvi. constructor. reflexivity.
      rewrite Hk in H.
      apply trans_schedule_obs_yield_None in H.
      destruct H as (? & ? & ?); subst. auto.
    - left.
      destruct Hequ as (Hvi & Hk).
      clear IHtrans_. cbn in *.
      rewrite Hk in H.
      apply trans_schedule_obs_yield_None in H.
      destruct H as (?n' & ? & ?). subst.
      eexists. split.
      + rewrite Hvi. constructor.
      + exists eq_refl. auto.
  Qed.

  (** [schedule] transitions with an [obs] something that is not a [Yield]: impossible case *)
  Lemma trans_schedule_obs_e_none X e (x : X) n v t :
    trans (obs (inr1 e) x) (schedule n v None) t ->
    False.
  Proof.
    intros Ht.
    unfold trans in Ht. cbn in Ht. red in Ht.
    rewrite rewrite_schedule in *. destruct n; inv Ht. invert.
    destruct (observe (schedule_match schedule (S n) v None)) eqn:?; invert.
  Qed.

  (** [schedule] transitions with an [obs] of a [Spawn] *)
  Lemma trans_schedule_obs_spawn_some n v i t :
    trans (obs (inr1 (inl1 Spawn)) ()) (schedule n v (Some i)) t ->
    (exists k, visible (v i) (Vis (inr1 (inl1 Fork)) k) /\
            t ≅ schedule
              (S n)
              (cons_vec (k true) (replace_vec v i (k false)))
              (Some (FS i))).
  Proof.
    unfold trans. intros. cbn in H. red in H.
    remember (observe (schedule n v (Some i))).
    pose proof (ctree_eta (go (observe (schedule n v (Some i))))).
    rewrite <- Heqc in H0 at 1. cbn in H0. clear Heqc.
    remember (observe t). remember (obs _ _).
    revert t n v i Heqc0 Heql H0.
    induction H; intros ?t' n' v i Heq Heql Hequ; subst;
      try inv Heql; rewrite <- ctree_eta in Hequ.
    - destruct c.
      exfalso; now apply Br_schedule_inv in Hequ.
    - destruct n' as [| n']; [inv i |].
      apply guard_schedule_inv in Hequ. destruct Hequ as [? | [? | ?]].
      + destruct H0 as (k' & Hvi & Hk).
        edestruct IHtrans_ as (k'' & Hvis & Hequ); clear IHtrans_.
        3: { rewrite Hk. reflexivity. } all: try reflexivity.
        rewrite replace_vec_eq in Hvis.
        eexists. split.
        * rewrite Hvi. econstructor. apply Hvis.
        * rewrite replace_vec_twice in Hequ. apply Hequ.
      + clear IHtrans_. destruct H0 as (k' & Hequ & Hk).
        rewrite Hk in H. apply trans_schedule_obs_e_none in H. contradiction.
      + clear IHtrans_. destruct H0 as (Hvi & Hk).
        rewrite Hk in H. apply trans_schedule_obs_e_none in H. contradiction.
    - invert. destruct n'; try inv i.
      rewrite rewrite_schedule in Hequ. simp schedule_match in Hequ.
      destruct (observe (v i)) eqn:?; cbn in Hequ; inv_equ.
      + destruct e; [destruct y | destruct s; [destruct f |]]; inv_equ.
        * eexists. split.
          cbn. red. rewrite Heqc. constructor. reflexivity.
          rewrite ctree_eta. rewrite <- Heq. rewrite <- H. rewrite EQ.
          rewrite <- ctree_eta. reflexivity.
      + destruct c.
  Qed.

  (** [schedule] transitions with an [obs] of an event of type [E] *)
  Lemma trans_schedule_obs_e_some X e (x : X) n v i t :
    trans (obs (inr1 (inr1 e)) x) (schedule n v (Some i)) t ->
    (exists k, visible (v i) (Vis (inr1 (inr1 e)) k) /\
            t ≅ schedule
              n
              (replace_vec v i (k x))
              (Some i)).
  Proof.
    unfold trans. intros. cbn in H. red in H.
    remember (observe (schedule n v (Some i))).
    pose proof (ctree_eta (go (observe (schedule n v (Some i))))).
    rewrite <- Heqc in H0 at 1. cbn in H0. clear Heqc.
    remember (observe t). remember (obs _ _).
    revert t n v i Heqc0 Heql H0.
    induction H; intros ?t' n' v i Heq Heql Hequ; subst;
      try inv Heql; rewrite <- ctree_eta in Hequ.
    - exfalso; now destruct c; apply Br_schedule_inv in Hequ.
    - destruct n'; [inv i |].
      apply guard_schedule_inv in Hequ. destruct Hequ as [? | [? | ?]].
      + destruct H0 as (k' & Hvi & Hk).
        edestruct IHtrans_ as (k'' & Hvis & Hequ); clear IHtrans_.
        3: { rewrite Hk. reflexivity. } all: try reflexivity.
        rewrite replace_vec_eq in Hvis.
        eexists. split.
        * rewrite Hvi. econstructor. apply Hvis.
        * rewrite replace_vec_twice in Hequ. apply Hequ.
      + clear IHtrans_. destruct H0 as (k' & Hequ & Hk).
        rewrite Hk in H. apply trans_schedule_obs_e_none in H. contradiction.
      + clear IHtrans_. destruct H0 as (Hvi & Hk).
        rewrite Hk in H. apply trans_schedule_obs_e_none in H. contradiction.
    - invert. destruct n'; try inv i.
      rewrite rewrite_schedule in Hequ. simp schedule_match in Hequ.
      destruct (observe (v i)) eqn:?; cbn in Hequ; inv_equ.
      + destruct e0; [destruct y | destruct s; [destruct f |]]; inv_equ.
        inv EQe.
        eexists. split.
        * cbn. red. rewrite Heqc. cbn. constructor. reflexivity.
        * rewrite ctree_eta. rewrite <- Heq. rewrite <- H. rewrite EQ.
          rewrite <- ctree_eta. reflexivity.
      + destruct c.
  Qed.

  (** [schedule] transitions with a [tau]: impossible case *)
  Lemma trans_schedule_thread_tau_none n v t :
    trans τ (schedule n v None) t ->
    False.
  Proof.
    intros Ht.
    unfold trans in Ht. cbn in Ht. red in Ht. destruct n; inv Ht.
  Qed.

  (** [schedule] transitions with a [tau] *)
  Lemma trans_schedule_thread_tau_some n v i t :
    trans τ (schedule n v (Some i)) t ->
      (exists t', trans τ (v i) t' /\
               t ≅ schedule n (replace_vec v i t') (Some i)).
  Proof.
    unfold trans. intros. cbn in H. red in H.
    remember (observe (schedule n v (Some i))).
    pose proof (ctree_eta (go (observe (schedule n v (Some i))))).
    rewrite <- Heqc in H0 at 1. cbn in H0. clear Heqc.
    remember (observe t). remember τ.
    revert t n v i Heqc0 Heql H0.
    induction H; intros ?t' n' v i Heq Heql Hequ; subst; try inv Heql.
    - rewrite <- ctree_eta in Hequ.
      destruct c.
      exfalso; now apply Br_schedule_inv in Hequ.
    - rewrite <- ctree_eta in Hequ.
      destruct n'; [inv i|].
      apply guard_schedule_inv in Hequ. destruct Hequ as [? | [? | ?]].
      + destruct H0 as (k' & Hvi & Hk).
        edestruct IHtrans_; auto; clear IHtrans_.
        rewrite Hk. reflexivity.
        destruct H0 as (Ht & Hequ).
        rewrite replace_vec_eq in Ht. rewrite replace_vec_twice in Hequ.
        eexists. split; eauto.
        rewrite Hvi. red. econstructor. eauto.
      + clear IHtrans_. destruct H0 as (k' & Hequ & Hk).
        rewrite Hk in H. apply trans_schedule_thread_tau_none in H. contradiction.
      + clear IHtrans_. destruct H0 as (Hvi & Hk). subst. cbn in *.
        rewrite Hk in H. apply trans_schedule_thread_tau_none in H. contradiction.
    - destruct n'; try inv i.
      rewrite rewrite_schedule in Hequ. simp schedule_match in Hequ.
      destruct (observe (v i)) eqn:?; cbn in Hequ; inv_equ.
      + eexists; split.
        * red. red. rewrite Heqc. econstructor; eauto.
        * rewrite ctree_eta. rewrite <- Heq. rewrite <- ctree_eta. rewrite <- Hequ.
          auto.
      + destruct e; [destruct y | destruct s; [destruct f |]]; cbn in Hequ; step in Hequ; inv Hequ.
      + destruct c.
  Qed.

  (*** how a thread [trans] affects the scheduler [trans] *)

  (** thread transitions with a val *)
  Lemma trans_thread_schedule_val_1 {X} v i (x : X) t :
    trans (val x) (v i) t ->
    trans (val x) (schedule 1 v (Some i)) Stuck.
  Proof.
    intro. unfold trans in *; cbn in H. red in H.
    remember (observe (v i)).
    pose proof (ctree_eta (go (observe (v i)))).
    rewrite <- Heqc in H0 at 1. cbn in H0. clear Heqc.
    remember (observe t). cbn. remember (val x).
    revert t v i x Heql Heqc0 H0.
    induction H; intros ?t' v i x' Heql Heq Hequ; try inv Heql.
    - destruct c.
    - step in Hequ. inv Hequ.
      rewrite rewrite_schedule. simp schedule_match. rewrite <- H2.
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
          (Br (branchn (S n)) (fun i' => (schedule (S n) (remove_vec v i) (Some i')))).
  Proof.
    unfold trans; intro. cbn in *. red in H.
    remember (observe (v i)).
    pose proof (ctree_eta (go (observe (v i)))).
    rewrite <- Heqc in H0 at 1. cbn in H0. clear Heqc.
    remember (observe t). remember (val ()).
    revert t v i Heql Heqc0 H0.
    induction H; intros ?t' v i Heql Heq Hequ; try inv Heql.
    - destruct c.
    - step in Hequ. inv Hequ.
      epose proof (IHtrans_ t'0 (replace_vec v i u) i eq_refl eq_refl _).
      Unshelve.
      2: { rewrite <- ?ctree_eta. rewrite REL, replace_vec_eq. reflexivity. }
      setoid_rewrite rewrite_schedule at 1. simp schedule_match. rewrite <- H2. cbn.
      econstructor. erewrite <- remove_vec_replace_vec_eq in H0.
      apply H0.
    - invert. step in Hequ. inv Hequ.
      setoid_rewrite rewrite_schedule at 1. simp schedule_match. rewrite <- H. cbn.
      constructor.
      rewrite rewrite_schedule. simp schedule_match. econstructor.
      step. econstructor. reflexivity.
  Qed.

  (** thread transitions with a tau *)
  Lemma trans_thread_schedule_tau n v i t :
    trans τ (v i) t ->
    trans τ (schedule (S n) v (Some i)) (schedule (S n) (replace_vec v i t) (Some i)).
  Proof.
    unfold trans; intro. cbn in *. red in H.
    remember (observe (v i)).
    pose proof (ctree_eta (go (observe (v i)))).
    rewrite <- Heqc in H0 at 1. cbn in H0. clear Heqc.
    remember (observe t). remember τ.
    revert t v i Heql Heqc0 H0.
    induction H; intros ?t' v i Heql Heq Hequ; try inv Heql.
    - destruct c.
    - step in Hequ. inv Hequ.
      rewrite rewrite_schedule. simp schedule_match. rewrite <- H2.
      constructor.
      erewrite <- (replace_vec_twice (S n) v i u t'0).
      apply IHtrans_; auto.
      rewrite replace_vec_eq. rewrite REL. reflexivity.
    - step in Hequ. inv Hequ.
      rewrite rewrite_schedule. simp schedule_match. rewrite <- H2.
      constructor.
      apply equ_schedule.
      apply replace_vec_relation; repeat intro; try reflexivity.
      rewrite <- REL, <- H.
      step; rewrite Heq; auto.
  Qed.

  (*** how thread struture (via [visible]) affects the scheduler [trans] *)

  (** when the thread is a yield *)
  Lemma visible_yield_trans_schedule n v i k :
    visible (v i) (Vis (inl1 Yield) k) ->
    trans (obs (inl1 Yield) ())
          (schedule (S n) v (Some i))
          (Br (branchn (S n)) (fun i' => (schedule (S n) (replace_vec v i (k ())) (Some i')))).
  Proof.
    intros. cbn in *. red in H |- *. red.
    remember (observe (v i)). remember (observe (Vis _ k)).
    revert v i k Heqc Heqc0.
    induction H; intros; subst; try inv Heqc0.
    - destruct c.
    - rewrite rewrite_schedule at 1. simp schedule_match.
      rewrite <- Heqc. constructor.
      rewrite <- (replace_vec_twice _ v i t (k ())).
      eapply IHvisible_; auto; rewrite replace_vec_eq; eauto.
    - invert.
      rewrite rewrite_schedule at 1. simp schedule_match.
      rewrite <- Heqc. econstructor.
      rewrite rewrite_schedule at 1. simp schedule_match.
      econstructor. step. constructor. intros. apply equ_schedule.
      apply replace_vec_relation; repeat intro; auto.
  Qed.

  (** when the thread is a fork *)
  Lemma visible_fork_trans_schedule n v i k :
    visible (v i) (Vis (inr1 (inl1 Fork)) k) ->
    trans (obs (inr1 (inl1 Spawn)) ())
          (schedule (S n) v (Some i))
          (schedule (S (S n))
                    (cons_vec (k true)
                              (replace_vec v i (k false)))
                    (Some (FS i))).
  Proof.
    intros. cbn in *. red in H |- *. red.
    remember (observe (v i)). remember (observe (Vis _ k)).
    revert v i k Heqc Heqc0.
    induction H; intros; subst; try inv Heqc0.
    - destruct c.
    - rewrite rewrite_schedule at 1. simp schedule_match.
      rewrite <- Heqc. constructor.
      rewrite <- (replace_vec_twice _ v i t (k false)).
      eapply IHvisible_; auto; rewrite replace_vec_eq; eauto.
    - invert.
      rewrite rewrite_schedule at 1. simp schedule_match.
      rewrite <- Heqc. econstructor. apply equ_schedule.
      apply cons_vec_relation; auto.
      apply replace_vec_relation; repeat intro; auto.
  Qed.

  (** when the thread is a [E] event *)
  Lemma visible_E_trans_schedule {X} n v i (s : E X) k x :
    visible (v i) (Vis (inr1 (inr1 s)) k) ->
    trans (obs (inr1 (inr1 s)) x)
          (schedule (S n) v (Some i))
          (schedule (S n) (replace_vec v i (k x)) (Some i)).
  Proof.
    intros. cbn in *. red in H |- *. red.
    remember (observe (v i)). remember (observe (Vis _ k)).
    revert v i k Heqc Heqc0.
    induction H; intros; subst; try inv Heqc0.
    - destruct c.
    - rewrite rewrite_schedule at 1. simp schedule_match.
      rewrite <- Heqc. econstructor.
      rewrite <- (replace_vec_twice _ v i t (k x)).
      eapply IHvisible_; auto; rewrite replace_vec_eq; eauto.
    - invert.
      rewrite rewrite_schedule at 1. simp schedule_match.
      rewrite <- Heqc. econstructor. apply equ_schedule.
      apply replace_vec_relation; repeat intro; auto.
  Qed.

  (*** Putting everything together *)
  Lemma schedule_permutation n (v1 v2 : vec n) i (p q : fin n -> fin n)
        (Hpq : forall i, p (q i) = i)
        (Hqp : forall i, q (p i) = i)
        (Hsb1 : forall i, v1 i ~ v2 (p i))
        (Hsb2 : forall i, v2 i ~ v1 (q i)) :
    schedule n v1 (Some i) ~ schedule n v2 (Some (p i)).
  Proof.
    revert n v1 v2 i p q Hpq Hqp Hsb1 Hsb2.
    coinduction r CIH.
    symmetric using idtac.
    {
      intros. rewrite <- (Hqp i) at 2.
      eapply H; auto.
    }
    intros n v1 v2 i p q Hpq Hqp Hsb1 Hsb2 l t Ht. cbn in *.
    destruct l.
    - apply trans_schedule_thread_tau_some in Ht; auto.
      assert (Hinjp : FinFun.Injective p) by (eapply bijective_injective; eauto).
      assert (Hinjq : FinFun.Injective q) by (eapply bijective_injective; eauto).
      destruct n; try inv i.
      destruct Ht as (t' & Ht & Hequ).
      pose proof (Hsb1 i). step in H. destruct H as [Hf _].
      edestruct Hf as (? & ? & ? & ? & <-); eauto.
      apply trans_thread_schedule_tau in H.
      do 2 eexists; split; [| split]; eauto.
      rewrite Hequ.
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
          assert (Hinjp : FinFun.Injective p) by (eapply bijective_injective; eauto).
          assert (Hinjq : FinFun.Injective q) by (eapply bijective_injective; eauto).

          epose proof (@remove_at_permutation_correct (yieldE +' forkE +' E) _ unit _ _ _ i Hpq Hqp Hinjp Hinjq) as (Hpq' & Hqp').
          edestruct (@remove_at_permutation_vectors (yieldE +' forkE +' E) void1 unit n') as (Hpq'' & Hqp''); eauto.
          pose proof (Hsb1 i). step in H. destruct H as [Hf _].
          edestruct Hf as (? & ? & ? & ? & ?); eauto; subst.
          apply trans_thread_schedule_val_SS in H.
          exists (obs (inl1 Yield) ()).
          exists (Br (branchn (S n'))
               (fun i' : fin (S n') => schedule
                                      (S n')
                                      (remove_vec v2 (p i))
                                      (Some
                                         ((projT1 (@remove_at_permutation (yieldE +' forkE +' E) void1 unit _ p i Hinjp))
                                            (projT1 (@remove_at_permutation (yieldE +' forkE +' E) void1 unit _ q (p i) Hinjq) i'))))).
          split; [| split].
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
            upto_bind with eq.
            {
              apply Lequiv_sbisim with eq.
              symmetry; apply update_val_rel_eq.
              apply sbisim_br.
              - intros y. exists ((projT1 (@remove_at_permutation (yieldE +' forkE +' E) void1 unit _ p i Hinjp)) y). rewrite Hqp'. auto.
              - intros y. exists ((projT1 (@remove_at_permutation (yieldE +' forkE +' E) void1 unit _ q (p i) Hinjq)) y). auto.
            }
            intros; subst.
            eapply CIH; clear CIH.
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
          auto. reflexivity.
        * (* The thread yields *)
          destruct n; try inv i.
          destruct H as (k & Hvis & Hequ).
          pose proof Hvis as Hvis'.
          eapply sbisim_visible in Hvis'. 3: apply Hsb1. 2: exists tt; auto.
          destruct Hvis' as (k' & Hvis' & Hk).
          eexists.
          exists (Br (branchn (S n)) (fun i' => schedule (S n) (replace_vec v2 (p i) (k' ())) (Some (p (q i'))))).
          split; [| split].
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
               upto_bind with eq.
               {
                 apply Lequiv_sbisim with eq.
                 symmetry; apply update_val_rel_eq.
                 apply sbisim_br.
                 - intros x. exists (p x). rewrite Hqp. reflexivity.
                 - intros x. exists (q x). reflexivity.
               }
               intros. subst; eapply CIH; clear CIH; eauto.
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
          eapply visible_yield_trans_schedule; auto. auto.
      + (* the thread forks a new thread *)
        destruct n; try inv i.
        apply trans_schedule_obs_spawn_some in Ht.
        destruct Ht as (k & Hvis & Hequ).
        pose proof Hvis as Hvis'.
        eapply sbisim_visible in Hvis'. 3: apply Hsb1. 2: exists true; auto.
        destruct Hvis' as (k' & Hvis' & Hk).
        pose proof (cons_permutation_correct _ _ Hpq Hqp) as (Hpq' & Hqp').
        destruct (cons_permutation p) as (p' & Hp1 & Hp2).
        destruct (cons_permutation q) as (q' & Hq1 & Hq2). cbn in *.
        eexists.
        exists (schedule
             (S (S n))
             (cons_vec (k' true) (replace_vec v2 (p i) (k' false)))
             (Some (p' (FS i)))).
        split; [| split].
        2: {
          rewrite Hequ. eapply CIH; auto.
          - intros. dependent destruction i0.
            + rewrite Hp1. simp cons_vec.
            + rewrite Hp2. simp cons_vec. destruct (Fin.eq_dec i i0); subst.
              * do 2 (rewrite replace_vec_eq; auto).
              * do 2 (rewrite replace_vec_neq; auto). intro.
                apply (f_equal q) in H. do 2 rewrite Hqp in H. contradiction.
          - intros. dependent destruction i0.
            + rewrite Hq1. simp cons_vec. symmetry. auto.
            + rewrite Hq2. simp cons_vec. destruct (Fin.eq_dec (p i) i0).
              * subst. rewrite Hqp. do 2 (rewrite replace_vec_eq; auto). symmetry; auto.
              * do 2 (rewrite replace_vec_neq; auto). intro.
                apply (f_equal p) in H. rewrite Hpq in H. contradiction.
        }
        rewrite Hp2. apply visible_fork_trans_schedule; auto. auto.
      + (* there is some other event *)
        destruct n; [inv i |].
        apply trans_schedule_obs_e_some in Ht; auto.
        destruct Ht as (k & Hvis & Hequ).
        pose proof Hvis as Hvis'.
        eapply sbisim_visible in Hvis'. 3: apply Hsb1. all: eauto.
        destruct Hvis' as (k' & Hvis' & ?).
        eexists.
        exists (schedule (S n) (replace_vec v2 (p i) (k' v)) (Some (p i))).
        split; [| split].
        2: {
          rewrite Hequ. eapply CIH; clear CIH; eauto.
          - intros. destruct (Fin.eq_dec i i0).
            + subst. do 2 rewrite replace_vec_eq; auto.
            + do 2 (rewrite replace_vec_neq; auto). intro.
              apply (f_equal q) in H0. do 2 rewrite Hqp in H0. contradiction.
          - intros. destruct (Fin.eq_dec (p i) i0).
            + subst. rewrite Hqp. do 2 rewrite replace_vec_eq; auto. symmetry; auto.
            + do 2 (rewrite replace_vec_neq; auto). intro.
              apply (f_equal p) in H0. rewrite Hpq in H0. contradiction.
        }
        apply visible_E_trans_schedule; eauto. auto.
    - pose proof (trans_schedule_val_1 _ _ _ _ _ Ht). subst.
      pose proof (trans_val_inv Ht).
      pose proof (Hsb1 i). step in H0. destruct H0 as [Hf _].
      pose proof (trans_schedule_thread_val _ _ _ _ Ht) as Hv1.
      edestruct Hf as (? & ? & ? & ? & ?); eauto. subst.
      apply trans_thread_schedule_val_1 in H0. do 2 eexists; split; [| split]; eauto.
      rewrite H. reflexivity.
  Qed.

  Definition perm_id {n} : fin n -> fin n := fun i => i.

  Lemma sbisim_schedule n (v1 v2 : vec n) i
        (Hsb : forall i, v1 i ~ v2 i) :
    schedule n v1 (Some i) ~ schedule n v2 (Some i).
  Proof.
    replace i with (perm_id i) at 2; auto.
    eapply schedule_permutation; auto. symmetry. auto.
  Qed.

End parallel.
