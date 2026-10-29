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

#[local] Notation S := Datatypes.S (only parsing).


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

  Lemma schedule_None_0 v : schedule 0 v None ≅ Ret ().
  Proof.
    rewrite rewrite_schedule. now simp schedule_match.
  Qed.

  Lemma schedule_None_S n v :
    schedule (S n) v None ≅ Vis (inl1 Yield) (fun _ => Br (branchn (S n)) (fun i' => schedule (S n) v (Some i'))).
  Proof.
    rewrite rewrite_schedule. now simp schedule_match.
  Qed.

  Lemma trans_schedule_val_None m (w : vec m) (x : unit) u :
    trans (val x) (α schedule m w None) u -> m = 0%nat.
  Proof.
    intros TR. destruct m as [| m]; auto.
    rewrite schedule_None_S in TR. inv_trans.
  Qed.

  (** Helper lemmas for when [schedule] transitions with a [val] *)
  Lemma trans_schedule_val_1 n v i (x : unit) st :
    trans (val x) (α schedule n v (Some i)) st ->
    n = 1%nat.
  Proof.
    intros TR. cbn in TR.
    assert (GEN : forall a b, transR (val x) a b -> forall n v i, a ⩸ (α schedule n v (Some i)) -> n = 1%nat).
    2: { eapply GEN; [exact TR | reflexivity]. }
    clear. intros a b TR. remember (val x) as l eqn:Hl.
    induction TR; intros n v i Ha; dependent destruction Ha; try discriminate.
    - rewrite EQ in H. exfalso. destruct c. symmetry in H. exact (Br_schedule_inv _ _ _ _ _ _ H).
    - rewrite EQ in H. destruct n as [| n]; [inv i |].
      symmetry in H. apply guard_schedule_inv in H as [(t'' & Hv & Ht) | [(k & Hv & Ht) | (Hv & Ht)]].
      + eapply IHTR; [exact Hl | constructor; exact Ht].
      + subst l. exfalso.
        assert (Ht' : (α t') ⩸ (α schedule (S n) (replace_vec v i (k ())) None)) by (constructor; exact Ht).
        rewrite Ht' in TR. apply trans_schedule_val_None in TR. discriminate.
      + subst l.
        assert (Ht' : (α t') ⩸ (α schedule n (remove_vec v i) None)) by (constructor; exact Ht).
        rewrite Ht' in TR. apply trans_schedule_val_None in TR. now subst.
    - rewrite EQ in H. exfalso. destruct n as [| n]; [inv i |].
      rewrite rewrite_schedule in H. simp schedule_match in H.
      destruct (observe (v i)) eqn:Hv; cbn in H; inv_equ.
      + destruct e as [y | [f | e0]]; [destruct y | destruct f |]; cbn in H; inv_equ.
      + destruct c.
  Qed.

  Lemma trans_schedule_thread_val v i (x : unit) st :
    trans (val x) (α schedule 1 v (Some i)) st ->
    trans (val x) (α v i) (α Stuck).
  Proof.
    intros TR. cbn in TR.
    assert (GEN : forall a b, transR (val x) a b -> forall v i, a ⩸ (α schedule 1 v (Some i)) ->
      trans (val x) (α v i) (α Stuck)).
    2: { eapply GEN; [exact TR | reflexivity]. }
    clear. intros a b TR. remember (val x) as l eqn:Hl.
    induction TR; intros v i Ha; dependent destruction Ha; try discriminate.
    - rewrite EQ in H. exfalso. destruct c. symmetry in H. exact (Br_schedule_inv _ _ _ _ _ _ H).
    - rewrite EQ in H.
      symmetry in H. apply guard_schedule_inv in H as [(t'' & Hv & Ht) | [(k & Hv & Ht) | (Hv & Ht)]].
      + specialize (IHTR Hl (replace_vec v i t'') i). rewrite replace_vec_eq in IHTR.
        rewrite Hv. apply trans_guard. apply IHTR. constructor; exact Ht.
      + subst l. exfalso.
        assert (Ht' : (α t') ⩸ (α schedule 1 (replace_vec v i (k ())) None)) by (constructor; exact Ht).
        rewrite Ht' in TR. apply trans_schedule_val_None in TR. discriminate.
      + rewrite Hv. destruct x. etrans.
    - rewrite EQ in H. exfalso.
      rewrite rewrite_schedule in H. simp schedule_match in H.
      destruct (observe (v i)) eqn:Hv; cbn in H; inv_equ.
      + destruct e as [y | [f | e0]]; [destruct y | destruct f |]; cbn in H; inv_equ.
      + destruct c.
  Qed.

  (** [schedule] transitions with an [obs] of a [Yield] *)
  Lemma trans_schedule_ask_yield_None n v st :
    trans (ask (inl1 Yield)) (α schedule n v None) st ->
    exists n', n = S n' /\
            st ⩸ (β (inl1 Yield) (fun _ => Br (branchn n) (fun i => schedule n v (Some i)))).
  Proof.
    intros TR. destruct n as [| n].
    - rewrite schedule_None_0 in TR. inv_trans.
    - rewrite schedule_None_S in TR. inv_trans. subst. exists n. split; auto.
  Qed.

  Lemma trans_schedule_ask_yield_Some n v i st :
    trans (ask (inl1 Yield)) (α schedule n v (Some i)) st ->
    (exists n',
        trans (val ()) (α v i) (α Stuck) /\
          {H: n = S (S n') &
                st ⩸ (β (inl1 Yield) (fun _ => Br (branchn (S n')) (fun i' => schedule (S n') (remove_vec_helper n (S n') v i H) (Some i'))))}) \/
    (exists k, visible (v i) (Vis (inl1 Yield) k) /\
            st ⩸ (β (inl1 Yield) (fun _ => Br (branchn n) (fun i' => schedule n (replace_vec v i (k ())) (Some i'))))).
  Proof.
    intros TR. cbn in TR.
    assert (GEN : forall a b, transR (ask (inl1 Yield)) a b -> forall n v i, a ⩸ (α schedule n v (Some i)) ->
    (exists n',
        trans (val ()) (α v i) (α Stuck) /\
          {H: n = S (S n') &
                b ⩸ (β (inl1 Yield) (fun _ => Br (branchn (S n')) (fun i' => schedule (S n') (remove_vec_helper n (S n') v i H) (Some i'))))}) \/
    (exists k, visible (v i) (Vis (inl1 Yield) k) /\
            b ⩸ (β (inl1 Yield) (fun _ => Br (branchn n) (fun i' => schedule n (replace_vec v i (k ())) (Some i')))))).
    2: { eapply GEN; [exact TR | reflexivity]. }
    clear. intros a b TR. remember (ask (inl1 Yield)) as l eqn:Hl.
    induction TR; intros n v i Ha; dependent destruction Ha; try discriminate.
    - rewrite EQ in H. exfalso. destruct c. symmetry in H. exact (Br_schedule_inv _ _ _ _ _ _ H).
    - rewrite EQ in H. destruct n as [| n]; [inv i |].
      symmetry in H. apply guard_schedule_inv in H as [(t'' & Hv & Ht) | [(k & Hv & Ht) | (Hv & Ht)]].
      + destruct (IHTR Hl _ (replace_vec v i t'') i) as [(n'' & TRv & Hn & EQ3) | (k & VIS & EQ3)]; [constructor; exact Ht | |].
        * left. rewrite replace_vec_eq in TRv. exists n''. split.
          { rewrite Hv. apply trans_guard. exact TRv. }
          exists Hn. rewrite EQ3. constructor. intros _. step. constructor. intros i'.
          now rewrite <- remove_vec_helper_replace_vec_eq.
        * right. rewrite replace_vec_eq in VIS. exists k. split.
          { rewrite Hv. red. cbn. constructor. exact VIS. }
          rewrite EQ3. constructor. intros _. step. constructor. intros i'.
          now rewrite replace_vec_twice.
      + subst l. right. exists k. split.
        { rewrite Hv. red. cbn. constructor. reflexivity. }
        assert (Ht' : (α t') ⩸ (α schedule (S n) (replace_vec v i (k ())) None)) by (constructor; exact Ht).
        rewrite Ht' in TR. apply trans_schedule_ask_yield_None in TR as (? & _ & EQ3). exact EQ3.
      + subst l. left.
        assert (Ht' : (α t') ⩸ (α schedule n (remove_vec v i) None)) by (constructor; exact Ht).
        rewrite Ht' in TR. apply trans_schedule_ask_yield_None in TR as (n'' & -> & EQ3).
        exists n''. split.
        { rewrite Hv. etrans. }
        exists eq_refl. exact EQ3.
    - rewrite EQ in H. destruct n as [| n]; [inv i |].
      rewrite rewrite_schedule in H. simp schedule_match in H.
      dependent destruction Hl.
      destruct (observe (v i)) eqn:Hv; cbn in H; try (step in H; inv H; fail).
      + destruct e as [y | [f | e1]]; [destruct y | destruct f |]; cbn in H; step in H; dependent destruction H.
      + destruct c.
  Qed.

  (** [schedule] transitions with an [obs] something that is not a [Yield]: impossible case *)
  Lemma trans_schedule_ask_e_none X (e : (spawnE +' E) X) n v st :
    trans (ask (inr1 e)) (α schedule n v None) st ->
    False.
  Proof.
    intros TR. destruct n as [| n].
    - rewrite schedule_None_0 in TR. inv_trans.
    - rewrite schedule_None_S in TR. inv_trans.
  Qed.

  (** [schedule] transitions with an [obs] of a [Spawn] *)
  Lemma trans_schedule_ask_spawn_some n v i st :
    trans (ask (inr1 (inl1 Spawn))) (α schedule n v (Some i)) st ->
    (exists k, visible (v i) (Vis (inr1 (inl1 Fork)) k) /\
            st ⩸ (β (inr1 (inl1 Spawn)) (fun _ => schedule
              (S n)
              (cons_vec (k true) (replace_vec v i (k false)))
              (Some (FS i))))).
  Proof.
    intros TR. cbn in TR.
    assert (GEN : forall a b, transR (ask (inr1 (inl1 Spawn))) a b -> forall n v i, a ⩸ (α schedule n v (Some i)) ->
      exists k, visible (v i) (Vis (inr1 (inl1 Fork)) k) /\
        b ⩸ (β (inr1 (inl1 Spawn)) (fun _ => schedule (S n) (cons_vec (k true) (replace_vec v i (k false))) (Some (FS i))))).
    2: { eapply GEN; [exact TR | reflexivity]. }
    clear. intros a b TR. remember (ask (inr1 (inl1 Spawn))) as l eqn:Hl.
    induction TR; intros n v i Ha; dependent destruction Ha; try discriminate.
    - rewrite EQ in H. exfalso. destruct c. symmetry in H. exact (Br_schedule_inv _ _ _ _ _ _ H).
    - rewrite EQ in H. destruct n as [| n]; [inv i |].
      symmetry in H. apply guard_schedule_inv in H as [(t'' & Hv & Ht) | [(k & Hv & Ht) | (Hv & Ht)]].
      + destruct (IHTR Hl _ (replace_vec v i t'') i) as (k & VIS & EQ3); [constructor; exact Ht |].
        rewrite replace_vec_eq in VIS.
        exists k. split.
        * rewrite Hv. red. cbn. constructor. exact VIS.
        * rewrite EQ3. constructor. intros x. now rewrite replace_vec_twice.
      + subst l. exfalso.
        assert (Ht' : (α t') ⩸ (α schedule (S n) (replace_vec v i (k ())) None)) by (constructor; exact Ht).
        rewrite Ht' in TR. eapply trans_schedule_ask_e_none. exact TR.
      + subst l. exfalso.
        assert (Ht' : (α t') ⩸ (α schedule n (remove_vec v i) None)) by (constructor; exact Ht).
        rewrite Ht' in TR. eapply trans_schedule_ask_e_none. exact TR.
    - rewrite EQ in H. destruct n as [| n]; [inv i |].
      rewrite rewrite_schedule in H. simp schedule_match in H.
      dependent destruction Hl.
      destruct (observe (v i)) eqn:Hv; cbn in H; try (step in H; inv H; fail).
      + destruct e as [y | [f | e1]]; [destruct y | destruct f |]; cbn in H; step in H; dependent destruction H.
        exists k0. split.
        * rewrite (ctree_eta (v i)), Hv. red. cbn. constructor. reflexivity.
        * constructor. intros x. symmetry. apply REL.
      + destruct c.
  Qed.

  (** [schedule] transitions with an [obs] of an event of type [E] *)
  Lemma trans_schedule_ask_e_some X (e : E X) n v i st :
    trans (ask (inr1 (inr1 e))) (α schedule n v (Some i)) st ->
    (exists k, visible (v i) (Vis (inr1 (inr1 e)) k) /\
            st ⩸ (β (inr1 (inr1 e)) (fun x => schedule
              n
              (replace_vec v i (k x))
              (Some i)))).
  Proof.
    intros TR. cbn in TR.
    assert (GEN : forall a b, transR (ask (inr1 (inr1 e))) a b -> forall n v i, a ⩸ (α schedule n v (Some i)) ->
      exists k, visible (v i) (Vis (inr1 (inr1 e)) k) /\
        b ⩸ (β (inr1 (inr1 e)) (fun x => schedule n (replace_vec v i (k x)) (Some i)))).
    2: { eapply GEN; [exact TR | reflexivity]. }
    clear. intros a b TR. remember (ask (inr1 (inr1 e))) as l eqn:Hl.
    induction TR; intros n v i Ha; dependent destruction Ha; try discriminate.
    - rewrite EQ in H. exfalso. destruct c. symmetry in H. exact (Br_schedule_inv _ _ _ _ _ _ H).
    - rewrite EQ in H. destruct n as [| n]; [inv i |].
      symmetry in H. apply guard_schedule_inv in H as [(t'' & Hv & Ht) | [(k & Hv & Ht) | (Hv & Ht)]].
      + destruct (IHTR Hl _ (replace_vec v i t'') i) as (k & VIS & EQ3); [constructor; exact Ht |].
        rewrite replace_vec_eq in VIS.
        exists k. split.
        * rewrite Hv. red. cbn. constructor. exact VIS.
        * rewrite EQ3. constructor. intros x. now rewrite replace_vec_twice.
      + subst l. exfalso.
        assert (Ht' : (α t') ⩸ (α schedule (S n) (replace_vec v i (k ())) None)) by (constructor; exact Ht).
        rewrite Ht' in TR. eapply trans_schedule_ask_e_none. exact TR.
      + subst l. exfalso.
        assert (Ht' : (α t') ⩸ (α schedule n (remove_vec v i) None)) by (constructor; exact Ht).
        rewrite Ht' in TR. eapply trans_schedule_ask_e_none. exact TR.
    - rewrite EQ in H. destruct n as [| n]; [inv i |].
      rewrite rewrite_schedule in H. simp schedule_match in H.
      dependent destruction Hl.
      destruct (observe (v i)) eqn:Hv; cbn in H; try (step in H; inv H; fail).
      + destruct e0 as [y | [f | e1]]; [destruct y | destruct f |]; cbn in H; step in H; dependent destruction H.
        exists k0. split.
        * rewrite (ctree_eta (v i)), Hv. red. cbn. constructor. reflexivity.
        * constructor. intros x. symmetry. apply REL.
      + destruct c.
  Qed.

  (** [schedule] transitions with a [tau]: impossible case *)
  Lemma trans_schedule_thread_tau_none n v st :
    trans τ (α schedule n v None) st ->
    False.
  Proof.
    intros TR. destruct n as [| n].
    - rewrite schedule_None_0 in TR. inv_trans.
    - rewrite schedule_None_S in TR. inv_trans.
  Qed.

  (** [schedule] transitions with a [tau] *)
  Lemma trans_schedule_thread_tau_some n v i st :
    trans τ (α schedule n v (Some i)) st ->
      (exists t', trans τ (α v i) (α t') /\
               st ⩸ (α schedule n (replace_vec v i t') (Some i))).
  Proof.
    intros TR. cbn in TR.
    assert (GEN : forall a b, transR τ a b -> forall n v i, a ⩸ (α schedule n v (Some i)) ->
      exists t', trans τ (α v i) (α t') /\ b ⩸ (α schedule n (replace_vec v i t') (Some i))).
    2: { eapply GEN; [exact TR | reflexivity]. }
    clear. intros a b TR. remember τ as l eqn:Hl.
    induction TR; intros n v i Ha; dependent destruction Ha; try discriminate.
    - rewrite EQ in H. exfalso. destruct c. symmetry in H. exact (Br_schedule_inv _ _ _ _ _ _ H).
    - rewrite EQ in H. destruct n as [| n]; [inv i |].
      symmetry in H. apply guard_schedule_inv in H as [(t'' & Hv & Ht) | [(k & Hv & Ht) | (Hv & Ht)]].
      + destruct (IHTR Hl _ (replace_vec v i t'') i) as (t3 & TR3 & EQ3); [constructor; exact Ht |].
        rewrite replace_vec_eq in TR3. rewrite replace_vec_twice in EQ3.
        exists t3. split; [| exact EQ3].
        rewrite Hv. apply trans_guard. exact TR3.
      + subst l. exfalso. eapply trans_schedule_thread_tau_none.
        assert (Ht' : (α t') ⩸ (α schedule (S n) (replace_vec v i (k ())) None)) by (constructor; exact Ht).
        cbn. rewrite <- Ht'. exact TR.
      + subst l. exfalso. eapply trans_schedule_thread_tau_none.
        assert (Ht' : (α t') ⩸ (α schedule n (remove_vec v i) None)) by (constructor; exact Ht).
        cbn. rewrite <- Ht'. exact TR.
    - rewrite EQ in H. destruct n as [| n]; [inv i |].
      rewrite rewrite_schedule in H. simp schedule_match in H.
      destruct (observe (v i)) eqn:Hv; cbn in H; inv_equ.
      + exists t0. split.
        * rewrite (ctree_eta (v i)), Hv. apply trans_step.
        * constructor. rewrite H0, <- H. reflexivity.
      + destruct e as [y | [f | e0]]; [destruct y | destruct f |]; cbn in H; inv_equ.
      + destruct c.
  Qed.

  (*** how a thread [trans] affects the scheduler [trans] *)

  (** thread transitions with a val *)
  Lemma trans_thread_schedule_val_1 v i (x : unit) st :
    trans (val x) (α v i) st ->
    trans (val x) (α schedule 1 v (Some i)) (α Stuck).
  Proof.
    intros TR. cbn in TR.
    assert (GEN : forall a b, transR (val x) a b -> forall v i, a ⩸ (α v i) ->
      trans (val x) (α schedule 1 v (Some i)) (α Stuck)).
    2: { eapply GEN; [exact TR | reflexivity]. }
    clear. intros a b TR. remember (val x) as l eqn:Hl.
    induction TR; intros v i Ha; dependent destruction Ha; try discriminate.
    - destruct c.
    - rewrite EQ in H. step in H. inv H.
      rewrite rewrite_schedule. simp schedule_match. rewrite <- H1. cbn.
      apply trans_guard.
      apply IHTR; auto.
      rewrite replace_vec_eq. constructor. now symmetry.
    - rewrite EQ in H. step in H. inv H.
      rewrite rewrite_schedule. simp schedule_match. rewrite <- H2. cbn.
      apply trans_guard. rewrite rewrite_schedule. simp schedule_match.
      destruct x, r. etrans.
  Qed.

  Lemma trans_thread_schedule_val_SS n v i st :
    trans (val ()) (α v i) st ->
    trans (ask (inl1 Yield))
          (α schedule (S (S n)) v (Some i))
          (β (inl1 Yield) (fun _ => Br (branchn (S n)) (fun i' => (schedule (S n) (remove_vec v i) (Some i'))))).
  Proof.
    intros TR. cbn in TR.
    assert (GEN : forall a b, transR (val ()) a b -> forall v i, a ⩸ (α v i) ->
      trans (ask (inl1 Yield)) (α schedule (S (S n)) v (Some i))
        (Trans.Passive (inl1 Yield) (fun _ : unit => Br (branchn (S n)) (fun i' => schedule (S n) (remove_vec v i) (Some i'))))).
    2: { eapply GEN; [exact TR | reflexivity]. }
    clear. intros a b TR. remember (val ()) as l eqn:Hl.
    induction TR; intros v i Ha; dependent destruction Ha; try discriminate.
    - destruct c.
    - rewrite EQ in H. step in H. inv H.
      rewrite rewrite_schedule. simp schedule_match. rewrite <- H1. cbn.
      apply trans_guard.
      rewrite (remove_vec_replace_vec_eq v i t0).
      apply IHTR; auto.
      rewrite replace_vec_eq. constructor. now symmetry.
    - rewrite EQ in H. step in H. inv H.
      rewrite rewrite_schedule. simp schedule_match. rewrite <- H2. cbn.
      apply trans_guard. rewrite rewrite_schedule. simp schedule_match.
      eapply Trans.Transask. reflexivity.
  Qed.

  (** thread transitions with a tau *)
  Lemma trans_thread_schedule_tau n v i t :
    trans τ (α v i) (α t) ->
    trans τ (α schedule (S n) v (Some i)) (α schedule (S n) (replace_vec v i t) (Some i)).
  Proof.
    intros TR. cbn in TR.
    enough (GEN : forall a b, transR τ a b -> forall v i t, a ⩸ (α v i) -> b ⩸ (α t) ->
      trans τ (α schedule (S n) v (Some i)) (α schedule (S n) (replace_vec v i t) (Some i))).
    { eapply GEN; [exact TR | reflexivity | reflexivity]. }
    clear. intros a b TR. remember τ as l eqn:Hl.
    induction TR; intros v i t0 Ha Hb; dependent destruction Ha; try discriminate.
    - destruct c.
    - rewrite EQ in H. step in H. inv H.
      rewrite rewrite_schedule. simp schedule_match. rewrite <- H1. cbn.
      apply trans_guard.
      erewrite <- (replace_vec_twice (S n) v i t1 t0).
      apply IHTR; auto.
      rewrite replace_vec_eq. constructor. now symmetry.
    - rewrite EQ in H. step in H. inv H. dependent destruction Hb.
      rewrite rewrite_schedule. simp schedule_match. rewrite <- H2. cbn.
      assert (EQs : schedule (S n) (replace_vec v i t0) (Some i) ≅ schedule (S n) (replace_vec v i t1) (Some i)).
      { apply equ_schedule.
        apply replace_vec_relation; [repeat intro; reflexivity | reflexivity | rewrite <- EQ0, H0; now symmetry]. }
      rewrite EQs. apply trans_step.
  Qed.
    



  (*** how thread struture (via [visible]) affects the scheduler [trans] *)

  (** when the thread is a yield *)
  Lemma visible_yield_trans_schedule n v i k :
    visible (v i) (Vis (inl1 Yield) k) ->
    trans (ask (inl1 Yield))
          (α schedule (S n) v (Some i))
          (β (inl1 Yield) (fun _ => Br (branchn (S n)) (fun i' => (schedule (S n) (replace_vec v i (k ())) (Some i'))))).
  Proof.
    intros H. cbn in *. red in H.
    remember (observe (v i)). remember (observe (Vis _ k)).
    revert v i k Heqc Heqc0.
    induction H; intros; subst; try inv Heqc0.
    - destruct c.
    - rewrite rewrite_schedule at 1. simp schedule_match.
      rewrite <- Heqc. cbn. apply trans_guard.
      rewrite <- (replace_vec_twice _ v i t (k ())).
      eapply IHvisible_; [| reflexivity]. now rewrite replace_vec_eq.
    - invert.
      rewrite rewrite_schedule at 1. simp schedule_match.
      rewrite <- Heqc. cbn. apply trans_guard.
      rewrite rewrite_schedule at 1. simp schedule_match.
      assert (SQ : (Trans.Passive (inl1 Yield) (fun _ : unit => Br (branchn (S n)) (fun i' => schedule (S n) (replace_vec v i (k ())) (Some i'))))
                   ⩸ (Trans.Passive (inl1 Yield) (fun _ : unit => Br (branchn (S n)) (fun i' => schedule (S n) (replace_vec v i (k1 ())) (Some i'))))).
      { constructor. intros x. step. constructor. intros i'. apply equ_schedule.
        apply replace_vec_relation; [repeat intro; reflexivity | reflexivity | symmetry; apply H]. }
      rewrite SQ. eapply Trans.Transask. reflexivity.
  Qed.

  (** when the thread is a fork *)
  Lemma visible_fork_trans_schedule n v i k :
    visible (v i) (Vis (inr1 (inl1 Fork)) k) ->
    trans (ask (inr1 (inl1 Spawn)))
          (α schedule (S n) v (Some i))
          (β (inr1 (inl1 Spawn)) (fun _ => schedule (S (S n))
                    (cons_vec (k true)
                              (replace_vec v i (k false)))
                    (Some (FS i)))).
  Proof.
    intros H. cbn in *. red in H.
    remember (observe (v i)). remember (observe (Vis _ k)).
    revert v i k Heqc Heqc0.
    induction H; intros; subst; try inv Heqc0.
    - destruct c.
    - rewrite rewrite_schedule at 1. simp schedule_match.
      rewrite <- Heqc. cbn. apply trans_guard.
      rewrite <- (replace_vec_twice _ v i t (k false)).
      eapply IHvisible_; [| reflexivity]. now rewrite replace_vec_eq.
    - invert.
      rewrite rewrite_schedule at 1. simp schedule_match.
      rewrite <- Heqc. cbn.
      assert (SQ : (Trans.Passive (inr1 (inl1 Spawn)) (fun _ : unit => schedule (S (S n)) (cons_vec (k true) (replace_vec v i (k false))) (Some (FS i))))
                   ⩸ (Trans.Passive (inr1 (inl1 Spawn)) (fun _ : unit => schedule (S (S n)) (cons_vec (k1 true) (replace_vec v i (k1 false))) (Some (FS i))))).
      { constructor. intros x. apply equ_schedule.
        apply cons_vec_relation; [symmetry; apply H |].
        apply replace_vec_relation; [repeat intro; reflexivity | reflexivity | symmetry; apply H]. }
      rewrite SQ. eapply Trans.Transask. reflexivity.
  Qed.

  (** when the thread is a [E] event *)
  Lemma visible_E_trans_schedule {X} n v i (s : E X) k :
    visible (v i) (Vis (inr1 (inr1 s)) k) ->
    trans (ask (inr1 (inr1 s)))
          (α schedule (S n) v (Some i))
          (β (inr1 (inr1 s)) (fun x => schedule (S n) (replace_vec v i (k x)) (Some i))).
  Proof.
    intros H. cbn in *. red in H.
    remember (observe (v i)). remember (observe (Vis _ k)).
    revert v i k Heqc Heqc0.
    induction H; intros; subst; try inv Heqc0.
    - destruct c.
    - rewrite rewrite_schedule at 1. simp schedule_match.
      rewrite <- Heqc. cbn. apply trans_guard.
      assert (Hf : (fun x => schedule (S n) (replace_vec v i (k x)) (Some i)) =
                   (fun x => schedule (S n) (replace_vec (replace_vec v i t) i (k x)) (Some i)))
        by (apply functional_extensionality; intros; now rewrite replace_vec_twice).
      rewrite Hf. eapply IHvisible_; [| reflexivity]. now rewrite replace_vec_eq.
    - invert.
      rewrite rewrite_schedule at 1. simp schedule_match.
      rewrite <- Heqc. cbn.
      assert (SQ : (Trans.Passive (inr1 (inr1 s)) (fun x : X => schedule (S n) (replace_vec v i (k x)) (Some i)))
                   ⩸ (Trans.Passive (inr1 (inr1 s)) (fun x : X => schedule (S n) (replace_vec v i (k1 x)) (Some i)))).
      { constructor. intros x. apply equ_schedule.
        apply replace_vec_relation; [repeat intro; reflexivity | reflexivity | symmetry; apply H]. }
      rewrite SQ. eapply Trans.Transask. reflexivity.
  Qed.

  (*** Putting everything together *)
  Lemma replace_vec_perm_l n (v1 v2 : vec n) i (p q : fin n -> fin n)
        (Hqp : forall i, q (p i) = i)
        (Hsb1 : forall i, v1 i ≃ v2 (p i)) t1 t2 (Ht : t1 ≃ t2) :
    forall i0, replace_vec v1 i t1 i0 ≃ replace_vec v2 (p i) t2 (p i0).
  Proof.
    intros i0. destruct (Fin.eq_dec i i0).
    - subst. now rewrite !replace_vec_eq.
    - rewrite !replace_vec_neq; auto.
      intro H. apply (f_equal q) in H. rewrite !Hqp in H. contradiction.
  Qed.

  Lemma replace_vec_perm_r n (v1 v2 : vec n) i (p q : fin n -> fin n)
        (Hpq : forall i, p (q i) = i)
        (Hqp : forall i, q (p i) = i)
        (Hsb2 : forall i, v2 i ≃ v1 (q i)) t1 t2 (Ht : t2 ≃ t1) :
    forall i0, replace_vec v2 (p i) t2 i0 ≃ replace_vec v1 i t1 (q i0).
  Proof.
    intros i0. destruct (Fin.eq_dec (p i) i0).
    - subst. rewrite Hqp. now rewrite !replace_vec_eq.
    - rewrite !replace_vec_neq; auto.
      intro H. apply (f_equal p) in H. rewrite Hpq in H. contradiction.
  Qed.

  Lemma trans_rcv_active {Y} (e : (yieldE +' spawnE +' E) Y) y (t : completed) st :
    trans (rcv e y) (α t) st -> False.
  Proof.
    intros TR. cbn in TR. remember (Trans.Active t) as a eqn:Ha. remember (rcv e y) as l eqn:Hl.
    revert t Ha. induction TR; intros t0 Ha; try discriminate; eauto.
  Qed.

  Lemma transR_tau_active {F C X} (s st : Trans.S F C X) :
    transR τ s st -> exists u, st = Trans.Active u.
  Proof.
    intros TR. remember τ as l eqn:Hl. induction TR; try discriminate; eauto.
  Qed.

  Lemma schedule_br_chain (r : Chain (@sb (yieldE +' spawnE +' E) _ Bn Bn unit unit Leq)) m
        (CIH : forall (v1 v2 : vec m) (i : fin m) (p q : fin m -> fin m),
            (forall i, p (q i) = i) -> (forall i, q (p i) = i) ->
            (forall i, v1 i ≃ v2 (p i)) -> (forall i, v2 i ≃ v1 (q i)) ->
            elem r (α schedule m v1 (Some i)) (α schedule m v2 (Some (p i))))
        (w1 w2 : vec m) (pp qq : fin m -> fin m)
        (H1 : forall j, pp (qq j) = j) (H2 : forall j, qq (pp j) = j)
        (H3 : forall j, w1 j ≃ w2 (pp j)) (H4 : forall j, w2 j ≃ w1 (qq j)) :
    elem r (α Br (branchn m) (fun i' => schedule m w1 (Some i')))
           (α Br (branchn m) (fun i' => schedule m w2 (Some i'))).
  Proof.
    assert (EQ1 : Br (branchn m) (fun i' => schedule m w1 (Some i')) ≅
                  CTree.bind (Br (branchn m) (fun x => Ret x)) (fun x => schedule m w1 (Some x))).
    { rewrite bind_br. step. constructor. intros. now rewrite bind_ret_l. }
    assert (EQ2 : Br (branchn m) (fun i' => schedule m w2 (Some i')) ≅
                  CTree.bind (Br (branchn m) (fun x => Ret x)) (fun x => schedule m w2 (Some x))).
    { rewrite bind_br. step. constructor. intros. now rewrite bind_ret_l. }
    rewrite EQ1, EQ2.
    apply (@SBisim.bind_chain_gen _ _ _ _ _ _ _ _ Leq (fun x y => y = pp x) r).
    - apply sbisim_br.
      + intros x. exists (pp x). apply sbisim_ret. reflexivity.
      + intros y. exists (qq y). apply sbisim_ret. cbn. now rewrite H1.
    - intros x y ->. eapply CIH; eauto.
  Qed.

  Lemma schedule_permutation n (v1 v2 : vec n) i (p q : fin n -> fin n)
        (Hpq : forall i, p (q i) = i)
        (Hqp : forall i, q (p i) = i)
        (Hsb1 : forall i, v1 i ≃ v2 (p i))
        (Hsb2 : forall i, v2 i ≃ v1 (q i)) :
    schedule n v1 (Some i) ≃ schedule n v2 (Some (p i)).
  Proof.
    revert n v1 v2 i p q Hpq Hqp Hsb1 Hsb2.
    coinduction r CIH.
    symmetric using idtac.
    { intros. rewrite <- (Hqp i) at 2. eapply H; auto. }
    intros n v1 v2 i p q Hpq Hqp Hsb1 Hsb2 l st Ht. cbn in *.
    destruct l as [| Y e | Y e y | x].
    - apply trans_schedule_thread_tau_some in Ht as (t' & Ht & Hequ).
      destruct n; try inv i.
      pose proof (Hsb1 i) as H. step in H. destruct H as [Hf _].
      edestruct Hf as (l' & u' & TR' & SIM & HL); [exact Ht |].
      apply Leq_eq in HL. subst l'.
      destruct (transR_tau_active _ _ TR') as (u & ->).
      apply trans_thread_schedule_tau with (n := n) in TR'.
      do 2 eexists. split; [exact TR' | split; [| constructor]].
      rewrite Hequ.
      eapply CIH; clear CIH; eauto.
      + apply replace_vec_perm_l with (q := q); auto.
      + apply replace_vec_perm_r; auto. now symmetry.
    - destruct e as [y | [s | e0]]; [destruct y | destruct s |].
      + apply trans_schedule_ask_yield_Some in Ht as [(n' & Hv1 & (Hn & Hequ)) | (k & Hvis & Hequ)].
        * subst n. cbn in Hequ.
          assert (Hinjp : FinFun.Injective p) by (eapply bijective_injective; eauto).
          assert (Hinjq : FinFun.Injective q) by (eapply bijective_injective; eauto).
          epose proof (@remove_at_permutation_correct (yieldE +' forkE +' E) _ unit _ _ _ i Hpq Hqp Hinjp Hinjq) as (Hpq' & Hqp').
          edestruct (@remove_at_permutation_vectors (yieldE +' forkE +' E) void1 unit n') as (Hpq'' & Hqp''); eauto.
          pose proof (Hsb1 i) as H. step in H. destruct H as [Hf _].
          edestruct Hf as (l' & u' & TR' & SIM & HL); [exact Hv1 |].
          apply Leq_eq in HL. subst l'.
          apply trans_thread_schedule_val_SS with (n := n') in TR'.
          set (p' := projT1 (remove_at_permutation p i Hinjp)) in *.
          set (q' := projT1 (remove_at_permutation q (p i) Hinjq)) in *.
          do 2 eexists. split; [exact TR' | split; [| constructor; constructor]].
          rewrite Hequ. apply (b_chain r). split.
          -- intros l' st' TR2. apply trans_passive_inv' in TR2 as ([] & SEQ & ->).
             exists (rcv (inl1 Yield) tt). eexists. split; [econstructor; reflexivity | split; [| constructor; constructor]].
             rewrite SEQ. apply schedule_br_chain with (pp := p') (qq := q'); auto. intros. eapply CIH; eauto.
          -- intros l' st' TR2. apply trans_passive_inv' in TR2 as ([] & SEQ & ->).
             exists (rcv (inl1 Yield) tt). eexists. split; [econstructor; reflexivity | split; [| constructor; constructor]].
             rewrite SEQ. cbn. apply schedule_br_chain with (pp := p') (qq := q'); auto. intros. eapply CIH; eauto.
        * destruct n; [inv i |].
          pose proof Hvis as Hvis'.
          eapply sbisim_visible in Hvis'; [| apply Hsb1].
          destruct Hvis' as (k' & Hvis' & Hk).
          apply visible_yield_trans_schedule with (n := n) in Hvis'.
          do 2 eexists. split; [exact Hvis' | split; [| constructor; constructor]].
          rewrite Hequ. apply (b_chain r). split.
          -- intros l' st' TR2. apply trans_passive_inv' in TR2 as ([] & SEQ & ->).
             exists (rcv (inl1 Yield) tt). eexists. split; [econstructor; reflexivity | split; [| constructor; constructor]].
             rewrite SEQ. apply schedule_br_chain with (pp := p) (qq := q); auto.
             ++ intros. eapply CIH; eauto.
             ++ apply replace_vec_perm_l with (q := q); auto.
             ++ apply replace_vec_perm_r; auto. now symmetry.
          -- intros l' st' TR2. apply trans_passive_inv' in TR2 as ([] & SEQ & ->).
             exists (rcv (inl1 Yield) tt). eexists. split; [econstructor; reflexivity | split; [| constructor; constructor]].
             rewrite SEQ. cbn. apply schedule_br_chain with (pp := p) (qq := q); auto.
             ++ intros. eapply CIH; eauto.
             ++ apply replace_vec_perm_l with (q := q); auto.
             ++ apply replace_vec_perm_r; auto. now symmetry.
      + destruct n; [inv i |].
        apply trans_schedule_ask_spawn_some in Ht as (k & Hvis & Hequ).
        pose proof Hvis as Hvis'.
        eapply sbisim_visible in Hvis'; [| apply Hsb1].
        destruct Hvis' as (k' & Hvis' & Hk).
        pose proof (cons_permutation_correct _ _ Hpq Hqp) as (Hpq' & Hqp').
        destruct (cons_permutation p) as (p' & Hp1 & Hp2).
        destruct (cons_permutation q) as (q' & Hq1 & Hq2). cbn in *.
        assert (HC1 : forall i0, cons_vec (k true) (replace_vec v1 i (k false)) i0 ≃ cons_vec (k' true) (replace_vec v2 (p i) (k' false)) (p' i0)).
        { intros i0. dependent destruction i0.
          - rewrite Hp1. simp cons_vec; auto.
          - rewrite Hp2. simp cons_vec; try apply replace_vec_perm_l with (q := q); auto. }
        assert (HC2 : forall i0, cons_vec (k' true) (replace_vec v2 (p i) (k' false)) i0 ≃ cons_vec (k true) (replace_vec v1 i (k false)) (q' i0)).
        { intros i0. dependent destruction i0.
          - rewrite Hq1. simp cons_vec; now symmetry.
          - rewrite Hq2. simp cons_vec; try (apply replace_vec_perm_r; auto; now symmetry). }
        apply visible_fork_trans_schedule with (n := n) in Hvis'.
        rewrite <- Hp2 in Hvis'.
        do 2 eexists. split; [exact Hvis' | split; [| constructor; constructor]].
        rewrite Hequ. apply (b_chain r). split.
        * intros l' st' TR'. apply trans_passive_inv' in TR' as (x & SEQ & ->).
          exists (rcv (inr1 (inl1 Spawn)) x). eexists. split; [econstructor; reflexivity | split; [| constructor; constructor]].
          rewrite SEQ. eapply CIH; eauto.
        * intros l' st' TR'. apply trans_passive_inv' in TR' as (x & SEQ & ->).
          exists (rcv (inr1 (inl1 Spawn)) x). eexists. split; [econstructor; reflexivity | split; [| constructor; constructor]].
          rewrite SEQ. cbn. eapply CIH; eauto.
      + destruct n; [inv i |].
        apply trans_schedule_ask_e_some in Ht as (k & Hvis & Hequ).
        pose proof Hvis as Hvis'.
        eapply sbisim_visible in Hvis'; [| apply Hsb1].
        destruct Hvis' as (k' & Hvis' & Hk).
        apply visible_E_trans_schedule with (n := n) in Hvis'.
        do 2 eexists. split; [exact Hvis' | split; [| constructor; constructor]].
        rewrite Hequ. apply (b_chain r). split.
        * intros l' st' TR'. apply trans_passive_inv' in TR' as (x & SEQ & ->).
          exists (rcv (inr1 (inr1 e0)) x). eexists. split; [econstructor; reflexivity | split; [| constructor; constructor]].
          rewrite SEQ. eapply CIH; clear CIH; eauto.
          -- apply replace_vec_perm_l with (q := q); auto.
          -- apply replace_vec_perm_r; auto. now symmetry.
        * intros l' st' TR'. apply trans_passive_inv' in TR' as (x & SEQ & ->).
          exists (rcv (inr1 (inr1 e0)) x). eexists. split; [econstructor; reflexivity | split; [| constructor; constructor]].
          rewrite SEQ. cbn. eapply CIH; clear CIH; eauto.
          -- apply replace_vec_perm_l with (q := q); auto.
          -- apply replace_vec_perm_r; auto. now symmetry.
    - exfalso. eapply trans_rcv_active. exact Ht.
    - pose proof (trans_schedule_val_1 _ _ _ _ _ Ht). subst.
      pose proof (trans_val_inv' Ht) as Hst.
      pose proof (trans_schedule_thread_val _ _ _ _ Ht) as Hv1.
      pose proof (Hsb1 i) as H. step in H. destruct H as [Hf _].
      edestruct Hf as (l' & u' & TR' & SIM & HL); [exact Hv1 |].
      apply Leq_eq in HL. subst l'.
      apply trans_thread_schedule_val_1 in TR'.
      do 2 eexists. split; [exact TR' | split; [| constructor; reflexivity]].
      rewrite Hst. reflexivity.
  Qed.

  Definition perm_id {n} : fin n -> fin n := fun i => i.

  Lemma sbisim_schedule n (v1 v2 : vec n) i
        (Hsb : forall i, v1 i ≃ v2 i) :
    schedule n v1 (Some i) ≃ schedule n v2 (Some i).
  Proof.
    replace i with (perm_id i) at 2; auto.
    eapply schedule_permutation; auto. intros. symmetry. auto.
  Qed.

End parallel.
