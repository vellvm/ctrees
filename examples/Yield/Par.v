From Coq Require Import
     Program
     List
     Logic.FunctionalExtensionality
     micromega.Lia
     Init.Specif.

From CTree Require Import
       CTrees
	   Utils
	   CTrees
 	   Interp
	   Equ
	   Bisim
       Shallow
       CTreesTheory
       Trans.

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

From ITree Require Import
     Sum.

From Coinduction Require Import
	coinduction rel tactics.

Import ListNotations.
Import CTreeNotations.

Variant yieldE S : Type -> Type :=
| Yield : S -> yieldE S S.

Variant spawnE : Type -> Type :=
| Spawn : spawnE bool.

Section parallel.
  Context {config : Type}.

  Definition parE c := yieldE c +' spawnE.

  Definition thread := Monads.stateT config
                                     (ctree (parE config))
                                     unit.

  Definition completed := Monads.stateT config (ctree void1) unit.

  Definition vec n := fin n -> thread.

  Definition vec_relation {n : nat} (P : rel _ _) (v1 v2 : vec n) : Prop :=
    forall i c, P (v1 i c) (v2 i c).

  Instance vec_relation_symmetric n (P : rel _ _) `{@Symmetric _ P} :
    Symmetric (@vec_relation n P).
  Proof. repeat intro. auto. Qed.

  Definition remove_front_vec {n : nat} (v : vec (S n)) : vec n :=
    fun i => v (Fin.FS i).

  Lemma remove_front_vec_vec_relation n P (v1 v2 : vec (S n)) :
    vec_relation P v1 v2 ->
    vec_relation P (remove_front_vec v1) (remove_front_vec v2).
  Proof.
    repeat intro. apply H.
  Qed.

  Program Fixpoint remove_vec {n : nat} (v : vec (S n)) (i : fin (S n)) : vec n :=
    match i with
    (* this is the one we're removing *)
    | Fin.F1 => remove_front_vec v
    (* not yet at the index we want to ignore *)
    | Fin.FS j => fun i' =>
                   match i' with
                   (* before the index we're removing *)
                   | Fin.F1 => v Fin.F1
                   (* after the index we're removing, so look at the rest of the vector, minus the first element, which we don't care about *)
                   | Fin.FS j' => remove_vec (remove_front_vec v) j j'
                   end
    end.

  Lemma remove_vec_vec_relation n P (v1 v2 : vec (S n)) i :
    vec_relation P v1 v2 ->
    vec_relation P (remove_vec v1 i) (remove_vec v2 i).
  Proof.
    intros. unfold remove_vec.
    dependent induction i; [apply remove_front_vec_vec_relation; auto |].
    repeat intro. destruct i0; auto. apply IHi; auto. cbn.
    repeat intro. apply remove_front_vec_vec_relation; auto.
  Qed.

  Definition remove_vec_helper n n' (v : vec n) (i : fin n) (H : n = S n')
    : vec n'.
    subst. apply remove_vec; eauto.
  Defined.

  Definition replace_vec {n : nat} (v : vec n) (i : fin n) (t : thread) : vec n :=
    fun i' => if Fin.eqb i i' then t else v i'.

  Lemma remove_front_vec_replace_vec n (v : vec (S n)) i t :
    remove_front_vec (replace_vec v (Fin.FS i) t) =
      replace_vec (remove_front_vec v) i t.
  Proof. reflexivity. Qed.

  Lemma remove_vec_replace_vec_eq {n} (v : vec (S n)) i t :
    remove_vec v i = remove_vec (replace_vec v i t) i.
  Proof.
    dependent induction i.
    - unfold remove_vec. unfold remove_front_vec. cbn. reflexivity.
    - unfold remove_vec. cbn. apply functional_extensionality. intros.
      dependent destruction x; auto.
      erewrite IHi; eauto.
  Qed.

  Lemma remove_vec_helper_replace_vec_eq {n n'} (v : vec n) i t H :
    remove_vec_helper n n' v i H = remove_vec_helper n n' (replace_vec v i t) i H.
  Proof.
    subst. cbn. eapply remove_vec_replace_vec_eq.
  Qed.

  Lemma replace_vec_vec_relation n P (v1 v2 : vec n) i t1 t2 :
    vec_relation P v1 v2 ->
    (forall x, P (t1 x) (t2 x)) ->
    vec_relation P (replace_vec v1 i t1) (replace_vec v2 i t2).
  Proof.
    unfold replace_vec. repeat intro. destruct (Fin.eqb i i0); auto.
  Qed.

  Lemma replace_vec_twice n (v : vec n) i t1 t2 :
    replace_vec (replace_vec v i t1) i t2 = replace_vec v i t2.
  Proof.
    unfold replace_vec. apply functional_extensionality. intro.
    destruct (Fin.eqb i x) eqn:?; auto.
  Qed.

  Lemma replace_vec_eq n (v : vec n) i t :
    (replace_vec v i t) i = t.
  Proof.
    unfold replace_vec.
    assert (i = i) by reflexivity. apply Fin.eqb_eq in H. rewrite H.
    reflexivity.
  Qed.

  Lemma replace_vec_same n (v : vec n) i :
    replace_vec v i (v i) = v.
  Proof.
    unfold replace_vec. apply functional_extensionality. intro.
    destruct (Fin.eqb i x) eqn:?; auto.
    apply Fin.eqb_eq in Heqb. subst. auto.
  Qed.

  Program Definition cons_vec {n : nat} (t : thread) (v : vec n) : vec (S n) :=
    fun i => match i with
          | Fin.F1 => t
          | Fin.FS i' => v i'
          end.

  Lemma cons_vec_vec_relation n P (v1 v2 : vec n) t1 t2 :
    vec_relation P v1 v2 ->
    (forall x, P (t1 x) (t2 x)) ->
    vec_relation P (cons_vec t1 v1) (cons_vec t2 v2).
  Proof.
    unfold cons_vec. repeat intro. dependent destruction i; auto.
  Qed.

  (* Program Definition append_vec {n : nat} (v : vec n) (t : thread) : vec (S n) := *)
  (*   fun i => let i' := Fin.to_nat i in *)
  (*         match PeanoNat.Nat.eqb (`i') n with *)
  (*         | true => t *)
  (*         | false => v (@Fin.of_nat_lt (`i') _ _) *)
  (*         end. *)
  (* Next Obligation. *)
  (*   (* why is the space after ` necessary...... *) *)
  (*   assert ((` (Fin.to_nat i)) <> n). *)
  (*   { *)
  (*     pose proof (Bool.reflect_iff _ _ (PeanoNat.Nat.eqb_spec (` (Fin.to_nat i)) n)). *)
  (*     intro. rewrite H in H0. rewrite H0 in Heq_anonymous. inv Heq_anonymous. *)
  (*   } *)
  (*   pose proof (proj2_sig (Fin.to_nat i)). *)
  (*   simpl in H0. lia. *)
  (* Defined. *)

  (* Lemma append_vec_vec_relation n P (v1 v2 : vec n) t1 t2 : *)
  (*   vec_relation P v1 v2 -> *)
  (*   (forall x, P (t1 x) (t2 x)) -> *)
  (*   vec_relation P (append_vec v1 t1) (append_vec v2 t2). *)
  (* Proof. *)
  (*   unfold append_vec. repeat intro. *)
  (* Qed. *)

  (* Alternate definition: factoring out the yielding effect *)
  Definition schedule_match
             (schedule : forall (n : nat), vec n -> option (fin n) -> thread)
             (n : nat)
             (v: vec n)
    : option (fin n) -> thread.
    refine
      (fun (oi : option (fin n)) c =>
         match oi with
         | None   => match n with
                    | O => Ret (c, tt)
                    | _ => ChoiceV n (fun i' => schedule n v (Some i') c)
                    end
         | Some i =>
             match (observe (v i c)) with
             | RetF (c', _) =>
                 match n as m return n = m -> _ with
                 | 0 => _
                 | S n' => fun H1 => TauI (schedule n' (remove_vec_helper n n' v i H1) None c')
                 end (eq_refl n)
             | ChoiceF b n' k => Choice b n' (fun i' => schedule n (replace_vec v i (fun _ => k i')) (Some i) c)
             | VisF (inl1 e) k =>
                 match e in yieldE _ R return (R -> ctree (parE config) (config * unit)) -> _ with
                 | Yield _ s' =>
                     fun k => TauI (schedule n (replace_vec v i k) None s')
                 end k
             | VisF (inr1 e) k =>
                 match e in spawnE R return (R -> ctree (parE config) (config * unit)) -> _ with
                 | Spawn =>
                     fun k =>
                       TauV (schedule
                               (S n)
                               (cons_vec (fun _ => k true) (replace_vec v i (fun _ => k false)))
                               (* The [i] here means that we don't yield at a spawn *)
                               (Some (Fin.L_R 1 i)) (* view [i] as a [fin (n + 1)] *)
                               c) (* this [c] doesn't matter, since the running thread won't use it *)
                 end k
             end
         end).
    - intro. subst. inv i.
  Defined.

  CoFixpoint schedule := schedule_match schedule.

  Lemma rewrite_schedule n v i c : schedule n v i c ≅ schedule_match schedule n v i c.
  Proof.
    step. eauto.
  Qed.

  #[global] Instance equ_schedule n :
    Proper ((vec_relation (equ eq)) ==> eq ==> pwr (equ eq)) (schedule n).
  Proof.
    intros x y H ? i ? c. subst. revert n x y i c H.
    coinduction r CIH. intros n v1 v2 i c Hv.
    do 2 rewrite rewrite_schedule. unfold schedule_match. cbn.
    destruct i as [i |].
    2: { destruct n; auto. cbn. constructor. intros. apply CIH; auto. }
    pose proof (Hv i c). step in H. inv H; eauto. 2: destruct e.
    - clear H1 H2. destruct y. destruct n; cbn in *; auto.
      constructor. intros. apply CIH.
      apply remove_vec_vec_relation; auto.
    - clear H1 H2. destruct y. cbn.
      constructor. intros. eapply CIH.
      apply replace_vec_vec_relation; auto.
    - destruct s. constructor. intros. eapply CIH.
      apply cons_vec_vec_relation; auto.
      apply replace_vec_vec_relation; auto.
    - cbn. constructor. intros. apply CIH.
      apply replace_vec_vec_relation; auto.
  Qed.

  (** Helper lemmas for dealing with [schedule] *)

  Lemma ChoiceI_schedule_inv n1 k n2 (v : vec n2) i c :
    ChoiceI n1 k ≅ schedule n2 v (Some i) c ->
    (exists k', v i c ≅ ChoiceI n1 k' /\
             forall i', k i' ≅ schedule n2 (replace_vec v i (fun _ => k' i')) (Some i) c) \/
      (exists c' k', v i c ≅ Vis (inl1 (Yield config c')) k' /\
                  n1 = 1%nat /\
                  forall i', k i' ≅ schedule n2 (replace_vec v i k') None c') \/
      (exists c' n2' H1, v i c ≅ Ret (c', ()) /\
                      n1 = 1%nat /\
                      forall i', k i' ≅ schedule n2' (remove_vec_helper n2 n2' v i H1) None c').
  Proof.
    intros Hequ.
    rewrite rewrite_schedule in Hequ. unfold schedule_match in Hequ. cbn in Hequ.
    destruct (observe (v i c)) eqn:?.
    - destruct r, u, n2; [inv i |].
      right. right.
      step in Hequ. pose proof (equF_choice_invT _ _ Hequ) as [? _]. subst.
      pose proof (equF_choice_invE _ _ Hequ).
      do 3 eexists. split; auto.
      step. rewrite Heqc0. reflexivity.
    - destruct e; [destruct y | destruct s]. 2: step in Hequ; inv Hequ.
      step in Hequ. pose proof (equF_choice_invT _ _ Hequ) as [? _]. subst.
      pose proof (equF_choice_invE _ _ Hequ).
      right. left.
      do 2 eexists. split; [| split]; auto.
      step. rewrite Heqc0. reflexivity.
    - destruct vis; [step in Hequ; inv Hequ |].
      pose proof (equ_choice_invT _ _ Hequ) as [? _]; subst.
      pose proof (equ_choice_invE _ _ Hequ).
      left.
      exists k0. split; auto.
      rewrite ctree_eta. rewrite Heqc0. reflexivity.
  Qed.

  (** Helper lemmas for when [schedule] transitions with a [val] *)
  Lemma trans_schedule_val_1 {X} n v i c (x : X) t :
    trans (val x) (schedule n v (Some i) c) t ->
    n = 1%nat.
  Proof.
    intro. cbn in H. red in H.
    remember (observe (schedule n v (Some i) c)).
    pose proof (ctree_eta (go (observe (schedule n v (Some i) c)))).
    rewrite <- Heqc0 in H0 at 1. cbn in H0. clear Heqc0.
    remember (observe t). remember (val x).
    revert t v i c x Heql Heqc1 H0.
    induction H; intros t' v i c c' Heql Heq Hequ; try inv Heql; subst.
    - rewrite <- ctree_eta in Hequ.
      apply ChoiceI_schedule_inv in Hequ. destruct Hequ as [? | [? | ?]].
      + destruct H0 as (k' & Hvic & Hk).
        eapply IHtrans_; eauto.
        rewrite Hk. auto.
      + destruct H0 as (c'' & k' & Hvic & Hn & Hk). subst.
        rewrite Hk in H. rewrite rewrite_schedule in H. unfold schedule_match in H.
        destruct n; [inv i | inv H].
      + destruct H0 as (c'' & n' & Hn2' & Hvic & Hn & Hk).
        (* assert (n2' = O). { clear Hk. inv Hn2'. reflexivity. } subst. *)
        rewrite Hk in H. rewrite rewrite_schedule in H. unfold schedule_match in H.
        destruct n'; auto. inv H.
    - apply inj_pair2 in H1. subst.
      rewrite rewrite_schedule in Hequ. unfold schedule_match in Hequ.
      destruct (observe (v i c)) eqn:Hv.
      + destruct r, u; step in Hequ; inv Hequ.
        destruct n; [inv i | inv H].
      + destruct e; [destruct y | destruct s]; step in Hequ; inv Hequ.
      + step in Hequ; inv Hequ.
  Qed.

  Lemma trans_schedule_thread_val {X} v i c (x : X) t :
    trans (val x) (schedule 1 v (Some i) c) t ->
    trans (val x) (v i c) CTree.stuckI.
  Proof.
    intro. cbn in H. red in H.
    remember (observe (schedule 1 v (Some i) c)).
    pose proof (ctree_eta (go (observe (schedule 1 v (Some i) c)))).
    rewrite <- Heqc0 in H0 at 1. cbn in H0. clear Heqc0.
    remember (observe t). remember (val x).
    revert t v i c x Heql Heqc1 H0.
    induction H; intros t' v i c c' Heql Heq Hequ; try inv Heql; subst.
    - rewrite <- ctree_eta in Hequ.
      apply ChoiceI_schedule_inv in Hequ. destruct Hequ as [? | [? | ?]].
      + destruct H0 as (k' & Hvic & Hk).
        setoid_rewrite Hk in IHtrans_.
        rewrite Hvic.
        econstructor.
        specialize (IHtrans_ _ (replace_vec v i (fun _ : config => k' x)) i c _ eq_refl eq_refl).
        rewrite replace_vec_eq in IHtrans_. apply IHtrans_. reflexivity.
      + destruct H0 as (c'' & k' & Hvic & Hn & Hk). subst.
        rewrite Hk in H. rewrite rewrite_schedule in H. unfold schedule_match in H.
        inv H.
      + destruct H0 as (c'' & n2' & Hn2' & Hvic & Hn & Hk).
        assert (n2' = O). { clear Hk. inv Hn2'. reflexivity. } subst.
        rewrite Hk in H. rewrite rewrite_schedule in H. unfold schedule_match in H.
        apply trans_ret_inv in H. destruct H. inv H. apply inj_pair2 in H3. subst.
        rewrite Hvic. constructor.
    - apply inj_pair2 in H1. subst.
      rewrite rewrite_schedule in Hequ. unfold schedule_match in Hequ.
      destruct (observe (v i c)) eqn:Hv.
      + destruct r, u. step in Hequ. inv Hequ.
      + destruct e; [destruct y | destruct s]; step in Hequ; inv Hequ.
      + step in Hequ; inv Hequ.
  Qed.

  Lemma trans_thread_schedule_val_1 {X} v i c (x : X) t :
    trans (val x) (v i c) t ->
    trans (val x) (schedule 1 v (Some i) c) CTree.stuckI.
  Proof.
    intro. cbn in H. red in H.
    remember (observe (v i c)).
    pose proof (ctree_eta (go (observe (v i c)))).
    rewrite <- Heqc0 in H0 at 1. cbn in H0. clear Heqc0.
    remember (observe t). remember (val x).
    revert t v i c x Heql Heqc1 H0.
    induction H; intros t' v i c x' Heql Heq Hequ; try inv Heql.
    - (* is there a better way to do this *)
      step in Hequ. inv Hequ. apply inj_pair2 in H3; subst.
      rewrite rewrite_schedule. unfold schedule_match. rewrite <- H4.
      econstructor. eapply IHtrans_; try reflexivity. rewrite REL.
      rewrite replace_vec_eq. reflexivity.
    - apply inj_pair2 in H1. subst.
      step in Hequ. inv Hequ.
      rewrite rewrite_schedule. unfold schedule_match. rewrite <- H.
      destruct y, u. econstructor; eauto.
      rewrite rewrite_schedule. unfold schedule_match. constructor.
  Qed.

  (** [schedule] cannot transition with an [obs] *)
  Lemma trans_schedule_obs {X} n v o c (e : parE config X) (x : X) t :
    trans (obs e x) (schedule n v o c) t ->
    False.
  Proof.
    intro. destruct o as [i |].
    2: {
      rewrite rewrite_schedule in H. unfold schedule_match in H. destruct n; inv H.
    }
    cbn in H. red in H.
    remember (observe (schedule n v (Some i) c)).
    pose proof (ctree_eta (go (observe (schedule n v (Some i) c)))).
    rewrite <- Heqc0 in H0 at 1. cbn in H0. clear Heqc0.
    remember (observe t). remember (obs _ _).
    revert t n v i c e x Heql Heqc1 H0.
    induction H; intros t' n' v i c e' x' Heql Heq Hequ; try inv Heql; subst.
    - rewrite <- ctree_eta in Hequ.
      apply ChoiceI_schedule_inv in Hequ. destruct Hequ as [? | [? | ?]].
      + destruct H0 as (k' & Hvic & Hk).
        setoid_rewrite Hk in IHtrans_.
        eapply IHtrans_; eauto.
      + destruct H0 as (c' & k' & Hvic & ? & Hk). subst.
        setoid_rewrite Hk in H.
        rewrite rewrite_schedule in H. unfold schedule_match in H. destruct n'; inv H.
      + destruct H0 as (c' & n'' & ? & Hvic & ? & Hk). subst.
        setoid_rewrite Hk in H.
        rewrite rewrite_schedule in H. unfold schedule_match in H. destruct n''; inv H.
    - apply inj_pair2 in H2, H3. subst.
      rewrite rewrite_schedule in Hequ. unfold schedule_match in Hequ.
      destruct (observe (v i c)) eqn:Hv.
      + destruct r, n'. inv i. destruct n'; step in Hequ; inv Hequ.
      + destruct e; [destruct y | destruct s]; step in Hequ; inv Hequ.
      + step in Hequ; inv Hequ.
  Qed.

  #[global] Instance sbisim_schedule n :
    Proper ((vec_relation sbisim) ==> eq ==> eq ==> sbisim) (schedule n).
  Proof.
    repeat intro. subst. revert n x y y0 y1 H.
    coinduction r CIH.
    symmetric using intuition.
    intros n v1 v2 o c Hv l t Ht.
    destruct l.
    - admit.
    - apply trans_schedule_obs in Ht. contradiction.
    - destruct o as [i |].
      + pose proof (trans_schedule_val_1 _ _ _ _ _ _ Ht). subst.
        pose proof (trans_val_inv Ht).
        specialize (Hv i c). step in Hv. destruct Hv as [Hf Hb].
        pose proof (trans_schedule_thread_val _ _ _ _ _ Ht) as Hv1.
        edestruct Hf; eauto.
        apply trans_thread_schedule_val_1 in H0. eexists; eauto. rewrite H. reflexivity.
      + rewrite rewrite_schedule in Ht. unfold schedule_match in Ht.
        destruct n; [| inv Ht].
        destruct (trans_ret_inv Ht). inv H. apply inj_pair2 in H3. subst.
        exists CTree.stuckI.
        * rewrite rewrite_schedule. unfold schedule_match. constructor.
        * rewrite H0. reflexivity.
  Admitted.

  Definition schedule'_match
          (schedule' : forall (n : nat), vec n -> vec n)
          (n : nat)
          (v: vec n)
    : vec n.
    refine
      (fun (i : fin n) c =>
         match (observe (v i c)) with
         | RetF (c', _) =>
           match n as m return n = m -> _ with
           | 0 => _
           | S n' => match n' as m return n' = m -> _ with
                   | 0 => fun H1 H2 => Ret (c', tt)
                   | S n'' => fun H1 H2 => ChoiceV
                                       n'
                                       (fun i' => schedule' n' (remove_vec_helper n n' v i H2) i' c')
                   end (eq_refl n')
           end (eq_refl n)
         | ChoiceF b n' k => Choice b n' (fun i' => schedule' n (replace_vec v i (fun _ => k i')) i c)
         | VisF (inl1 e) k =>
           match e in yieldE _ R return (R -> ctree (parE config) (config * unit)) -> _ with
           | Yield _ s' =>
             fun k => ChoiceV
                     n
                     (fun i' => schedule' n (replace_vec v i k) i' s')
           end k
         | VisF (inr1 e) k =>
           match e in spawnE R return (R -> ctree (parE config) (config * unit)) -> _ with
           | Spawn =>
             fun k =>
               TauV (schedule'
                       (S n)
                       (cons_vec (fun _ => k true) (replace_vec v i (fun _ => k false)))
                       (* The [i] here means that we don't yield at a spawn *)
                       (Fin.L_R 1 i) (* view [i] as a [fin (n + 1)] *)
                       c) (* this [c] doesn't matter, since the running thread won't use it *)
           end k
         end).
    - intro. subst. inv i.
  Defined.

  CoFixpoint schedule' := schedule'_match schedule'.

  Lemma rewrite_schedule' n v i c : schedule' n v i c ≅ schedule'_match schedule' n v i c.
  Proof.
    step. eauto.
  Qed.

  #[global] Instance equ_schedule' n :
    Proper ((vec_relation (equ eq)) ==> vec_relation (equ eq)) (schedule' n).
  Proof.
    repeat intro. revert H. revert x y i c. revert n.
    coinduction r CIH. intros n v1 v2 i c Hv.
    do 2 rewrite rewrite_schedule'. unfold schedule'_match. cbn.
    pose proof (Hv i c). step in H. inv H; eauto. 2: destruct e.
    - clear H1 H2. destruct y. destruct n; cbn in *; auto.
      destruct n; cbn; auto. constructor. intros. apply CIH.
      apply remove_vec_vec_relation; auto.
    - clear H1 H2. destruct y. cbn.
      constructor. intros. eapply CIH.
      apply replace_vec_vec_relation; auto.
    - destruct s. constructor. intros. eapply CIH.
      apply cons_vec_vec_relation; auto.
      apply replace_vec_vec_relation; auto.
    - cbn. constructor. intros. apply CIH.
      apply replace_vec_vec_relation; auto.
  Qed.

  Lemma ChoiceI_schedule'_inv n1 k n2 (v : vec n2) i c :
    ChoiceI n1 k ≅ schedule' n2 v i c ->
    exists k', v i c ≅ ChoiceI n1 k' /\
            forall i', k i' ≅ schedule' n2 (replace_vec v i (fun _ => k' i')) i c.
  Proof.
    intros Hequ.
    rewrite rewrite_schedule' in Hequ. unfold schedule'_match in Hequ. cbn in Hequ.
    destruct (observe (v i c)) eqn:?.
    - destruct r, n2; [inv i |]. destruct n2; step in Hequ; inv Hequ.
    - destruct e; [destruct y | destruct s]; step in Hequ; inv Hequ.
    - destruct vis; [step in Hequ; inv Hequ |].
      destruct (equ_choice_invT _ _ Hequ); subst. clear H0.
      epose proof (equ_choice_invE _ _ Hequ). clear Hequ. cbn in H.
      exists k0. split; auto.
      rewrite ctree_eta. rewrite Heqc0. reflexivity.
  Qed.

  Lemma ChoiceV_schedule'_inv n1 n2 (v : vec n2) i i' c k k' :
    ChoiceV n1 k ≅ schedule' n2 v i c ->
    observe (v i c) = ChoiceF true n1 k' -> (* can replace with ≅ if needed *)
    k i' ≅ schedule' n2 (replace_vec v i (fun _ => k' i')) i c.
  Proof.
    intros Hequ Heq.
    rewrite rewrite_schedule' in Hequ. unfold schedule'_match in Hequ. cbn in Hequ.
    rewrite Heq in Hequ.
    pose proof (equ_choice_invE _ _ Hequ). cbn in H.
    rewrite H. reflexivity.
  Qed.


  Lemma trans_schedule'_val_1 {X} n v i c (x : X) t :
    trans (val x) (schedule' n v i c) t ->
    n = 1%nat.
  Proof.
    intro. cbn in H. red in H.
    remember (observe (schedule' n v i c)).
    pose proof (ctree_eta (go (observe (schedule' n v i c)))).
    rewrite <- Heqc0 in H0 at 1. cbn in H0. clear Heqc0.
    remember (observe t). remember (val x).
    revert t n v i c x Heql Heqc1 H0.
    induction H; intros t' n' v i c x' Heql Heq Hequ; try inv Heql; subst.
    - rewrite <- ctree_eta in Hequ.
      apply ChoiceI_schedule'_inv in Hequ. destruct Hequ as (k' & Hequ & Hk).
      setoid_rewrite Hk in IHtrans_.
      eapply IHtrans_; eauto.
    - apply inj_pair2 in H1. subst.
      rewrite rewrite_schedule' in Hequ. unfold schedule'_match in Hequ.
      destruct (observe (v i c)) eqn:Hv.
      + destruct n'; [inv i |]. destruct n'; [| destruct r; step in Hequ; inv Hequ]; auto.
      + destruct e; [destruct y | destruct s]; step in Hequ; inv Hequ.
      + step in Hequ; inv Hequ.
  Qed.

  Lemma trans_schedule'_thread_val {X} v i c (x : X) t :
    trans (val x) (schedule' 1 v i c) t ->
    trans (val x) (v i c) CTree.stuckI.
  Proof.
    intro. cbn in H. red in H.
    remember (observe (schedule' 1 v i c)).
    pose proof (ctree_eta (go (observe (schedule' 1 v i c)))).
    rewrite <- Heqc0 in H0 at 1. cbn in H0. clear Heqc0.
    remember (observe t). remember (val x).
    revert t v i c x Heql Heqc1 H0.
    induction H; intros t' v i c c' Heql Heq Hequ; try inv Heql; subst.
    - rewrite <- ctree_eta in Hequ.
      apply ChoiceI_schedule'_inv in Hequ. destruct Hequ as (k' & Hequ & Hk).
      setoid_rewrite Hk in IHtrans_.
      rewrite Hequ.
      econstructor.
      specialize (IHtrans_ _ (replace_vec v i (fun _ : config => k' x)) i c _ eq_refl eq_refl).
      rewrite replace_vec_eq in IHtrans_. apply IHtrans_. reflexivity.
    - apply inj_pair2 in H1. subst.
      rewrite rewrite_schedule' in Hequ. unfold schedule'_match in Hequ.
      destruct (observe (v i c)) eqn:Hv.
      + cbn. red. rewrite Hv. destruct r, u.
        step in Hequ. inv Hequ. constructor.
      + destruct e; [destruct y | destruct s]; step in Hequ; inv Hequ.
      + step in Hequ; inv Hequ.
  Qed.

  Lemma trans_schedule'_obs {X} n v i c (e : parE config X) (x : X) t :
    trans (obs e x) (schedule' n v i c) t ->
    False.
  Proof.
    intro. cbn in H. red in H.
    remember (observe (schedule' n v i c)).
    pose proof (ctree_eta (go (observe (schedule' n v i c)))).
    rewrite <- Heqc0 in H0 at 1. cbn in H0. clear Heqc0.
    remember (observe t). remember (obs _ _).
    revert t n v i c e x Heql Heqc1 H0.
    induction H; intros t' n' v i c e' x' Heql Heq Hequ; try inv Heql; subst.
    - rewrite <- ctree_eta in Hequ.
      apply ChoiceI_schedule'_inv in Hequ. destruct Hequ as (k' & Hequ & Hk).
      setoid_rewrite Hk in IHtrans_.
      eapply IHtrans_; eauto.
    - apply inj_pair2 in H2, H3. subst.
      rewrite rewrite_schedule' in Hequ. unfold schedule'_match in Hequ.
      destruct (observe (v i c)) eqn:Hv.
      + destruct n'. inv i. destruct r. destruct n'; step in Hequ; inv Hequ.
      + destruct e; [destruct y | destruct s]; step in Hequ; inv Hequ.
      + step in Hequ; inv Hequ.
  Qed.

  Lemma trans_schedule'_thread_tau n v i c t:
    trans tau (schedule' n v i c) t ->
    (exists (c' : config) n' i',
        trans (val (c', ())) (v i c) CTree.stuckI /\
          {H: n = S (S n') &
                t ≅ schedule' (S n') (remove_vec_helper n (S n') v i H) i' c'}) \/
      (exists t', trans tau (v i c) t' /\
               t ≅ schedule' n (replace_vec v i (fun _ => t')) i c) \/
      (exists c' k, visible (v i c) (Vis (inl1 (Yield _ c')) k) /\
                 exists i', t ≅ schedule' n (replace_vec v i k) i' c') \/
      (exists k, visible (v i c) (Vis (inr1 Spawn) k) /\
              t ≅ schedule'
                (S n)
                (cons_vec (fun _ => k true) (replace_vec v i (fun _ => k false)))
                (Fin.L_R 1 i)
                c).
  Proof.
    intro. cbn in H. red in H.
    remember (observe (schedule' n v i c)).
    pose proof (ctree_eta (go (observe (schedule' n v i c)))).
    rewrite <- Heqc0 in H0 at 1. cbn in H0. clear Heqc0.
    remember (observe t). remember tau.
    revert t n v i c Heqc1 Heql H0.
    induction H; intros t' n' v i c Heq Heql Hequ; subst.
    - rewrite <- ctree_eta in Hequ.
      apply ChoiceI_schedule'_inv in Hequ. destruct Hequ as (k' & Hequ & Hk).
      setoid_rewrite Hk in IHtrans_.
      edestruct IHtrans_ as [? | [? | [? | ?]]]; eauto; clear IHtrans_.
      + left. destruct H0 as (c' & n'' & i' & Ht & Hn' & Ht').
        exists c', n'', i'. rewrite replace_vec_eq in Ht. split.
        * rewrite Hequ. econstructor. apply Ht.
        * econstructor. rewrite Ht'.
          erewrite <- remove_vec_helper_replace_vec_eq. reflexivity.
      + right. left. destruct H0 as (t'' & Ht & Ht'). rewrite replace_vec_eq in Ht.
        exists t''. split.
        * rewrite Hequ. econstructor. apply Ht.
        * rewrite replace_vec_twice in Ht'. apply Ht'.
      + right. right. left. destruct H0 as (c' & k'' & Hvis & i' & Ht').
        rewrite replace_vec_eq in Hvis.
        exists c', k''. split.
        * rewrite Hequ. econstructor. apply Hvis.
        * exists i'. setoid_rewrite replace_vec_twice in Ht'. apply Ht'.
      + right. right. right. destruct H0 as (kb & Hvis & Ht').
        rewrite replace_vec_eq in Hvis.
        exists kb. split.
        * rewrite Hequ. econstructor. apply Hvis.
        * rewrite replace_vec_twice in Ht'. apply Ht'.
    - rewrite rewrite_schedule' in Hequ. unfold schedule'_match in Hequ.
      destruct (observe (v i c)) eqn:Hv; [| destruct e |].
      + destruct r, u, n'; [inv i |]; destruct n'; [step in Hequ; inv Hequ |].
        left.
        pose proof (ctree_eta t). rewrite Heq in H0. rewrite <- ctree_eta in H0.
        clear Heq. rename H0 into Heq. cbn in *.
        destruct (equ_choice_invT _ _ Hequ) as [? _]; subst.
        pose proof (equ_choice_invE _ _ Hequ) as Hk. cbn in Hk.
        eexists. exists n', x. split.
        * cbn. red. rewrite Hv. constructor.
        * exists eq_refl.
          rewrite <- Heq. rewrite <- H. rewrite Hk. reflexivity.
      + right. right. left. destruct y. cbn in Hequ.
        exists c0, k0. split.
        * cbn. red. rewrite Hv. constructor. reflexivity.
        * pose proof (ctree_eta t). rewrite Heq in H0. rewrite <- ctree_eta in H0.
          setoid_rewrite <- H0. setoid_rewrite <- H.
          destruct (equ_choice_invT _ _ Hequ); subst. clear H2.
          exists x. pose proof (equ_choice_invE _ _ Hequ). setoid_rewrite H1.
          reflexivity.
      + right. right. right. destruct s. cbn in Hequ.
        destruct (equ_choice_invT _ _ Hequ) as [? _]. subst.
        pose proof (equ_choice_invE _ _ Hequ) as Hk. cbn in Hk.
        eexists. split.
        * cbn. red. rewrite Hv. constructor. reflexivity.
        * rewrite ctree_eta. rewrite <- Heq. rewrite <- ctree_eta.
          rewrite <- H. apply Hk.
      + destruct vis; [| step in Hequ; inv Hequ].
        right. left.
        destruct (equ_choice_invT _ _ Hequ); subst. clear H1.
        eexists. split.
        * cbn. red. rewrite Hv. constructor 2 with (x := x). reflexivity.
        * pose proof (equ_choice_invE _ _ Hequ).
          pose proof (ctree_eta t). rewrite Heq in H1. rewrite <- ctree_eta in H1.
          rewrite <- H1. rewrite <- H. rewrite H0. reflexivity.
    - clear H.
      rewrite rewrite_schedule' in Hequ. unfold schedule'_match in Hequ.
      destruct (observe (v i c)) eqn:Hv.
      + destruct n'. inv i. destruct r. destruct n'; step in Hequ; inv Hequ.
      + destruct e0; [destruct y | destruct s]; step in Hequ; inv Hequ.
      + step in Hequ; inv Hequ.
    - inv Heql.
  Qed.

  Lemma trans_thread_schedule'_val_1 {X} v i c (x : X) t :
    trans (val x) (v i c) t ->
    trans (val x) (schedule' 1 v i c) CTree.stuckI.
  Proof.
    intro. cbn in H. red in H.
    remember (observe (v i c)).
    pose proof (ctree_eta (go (observe (v i c)))).
    rewrite <- Heqc0 in H0 at 1. cbn in H0. clear Heqc0.
    remember (observe t). remember (val x).
    revert t v i c x Heql Heqc1 H0.
    induction H; intros t' v i c x' Heql Heq Hequ; try inv Heql.
    - (* is there a better way to do this *)
      step in Hequ. inv Hequ. apply inj_pair2 in H3; subst.
      rewrite rewrite_schedule'. unfold schedule'_match. rewrite <- H4.
      econstructor. eapply IHtrans_; try reflexivity. rewrite REL.
      rewrite replace_vec_eq. reflexivity.
    - apply inj_pair2 in H1. subst.
      step in Hequ. inv Hequ.
      rewrite rewrite_schedule'. unfold schedule'_match. rewrite <- H.
      destruct y, u. econstructor.
  Qed.

  Lemma trans_thread_schedule'_val_SS n v i c (c' : config) t :
    trans (val (c', ())) (v i c) t ->
    forall i', trans tau (schedule' (S (S n)) v i c) (schedule' (S n) (remove_vec v i) i' c').
  Proof.
    intro. cbn in H. red in H.
    remember (observe (v i c)).
    pose proof (ctree_eta (go (observe (v i c)))).
    rewrite <- Heqc0 in H0 at 1. cbn in H0. clear Heqc0.
    remember (observe t). remember (val (c', ())).
    revert t v i c c' Heql Heqc1 H0.
    induction H; intros t' v i c x' Heql Heq Hequ i'; try inv Heql.
    - (* is there a better way to do this *)
      step in Hequ. inv Hequ. apply inj_pair2 in H3; subst.
      setoid_rewrite rewrite_schedule' at 1. unfold schedule'_match. rewrite <- H4.
      epose proof (IHtrans_ t' (replace_vec v i (fun _ => k2 x)) i c x' eq_refl eq_refl _ i').
      Unshelve. 2: { rewrite REL. rewrite replace_vec_eq. reflexivity. }
      econstructor.
      erewrite <- remove_vec_replace_vec_eq in H0. apply H0.
    - apply inj_pair2 in H0. subst. step in Hequ. inv Hequ.
      setoid_rewrite rewrite_schedule' at 1. unfold schedule'_match. rewrite <- H.
      econstructor. reflexivity.
  Qed.

  Lemma trans_thread_schedule'_tau n v i c t :
    trans tau (v i c) t ->
    trans tau (schedule' n v i c) (schedule' n (replace_vec v i (fun _ => t)) i c).
  Proof.
    intro. cbn in H. red in H.
    remember (observe (v i c)).
    pose proof (ctree_eta (go (observe (v i c)))).
    rewrite <- Heqc0 in H0 at 1. cbn in H0. clear Heqc0.
    remember (observe t). remember tau.
    revert t v i c Heql Heqc1 H0.
    induction H; intros t' v i c Heql Heq Hequ; try inv Heql.
    - step in Hequ. inv Hequ. apply inj_pair2 in H3; subst.
      rewrite rewrite_schedule'. unfold schedule'_match. rewrite <- H4.
      constructor 1 with (x:=x).
      erewrite <- (replace_vec_twice n v i (fun _ => k2 x) (fun _ => t')).
      apply IHtrans_; auto.
      rewrite replace_vec_eq. rewrite REL. reflexivity.
    - step in Hequ. inv Hequ. apply inj_pair2 in H3; subst.
      rewrite rewrite_schedule'. unfold schedule'_match. rewrite <- H4.
      constructor 2 with (x:=x).
      pose proof (ctree_eta t).
      rewrite Heq in H0. clear Heq. rename H0 into Heq. rewrite <- ctree_eta in Heq.
      apply equ_schedule'. (* TODO: some instance is missing *)
      apply replace_vec_vec_relation; repeat intro; try reflexivity.
      rewrite <- Heq. rewrite <- REL. auto.
  Qed.

  Lemma trans_thread_schedule'_spawn n (v : vec n) i c k b :
    trans (obs (inr1 (Spawn)) b) (v i c) (k b) ->
    trans tau (schedule' n v i c)
          (schedule'
             (S n)
             (cons_vec (fun _ => k true) (replace_vec v i (fun _ => k false)))
             (Fin.L_R 1 i)
             c).
  Proof.
    intro. cbn in H. red in H.
    remember (observe (v i c)).
    pose proof (ctree_eta (go (observe (v i c)))).
    rewrite <- Heqc0 in H0 at 1. cbn in H0. clear Heqc0.
    remember (obs _ b) as l.
    remember (observe (k b)) as k'.
    revert b k n v i c H0 Heql Heqk'.
    induction H; intros; subst; try inv Heql.
    - step in H0. inv H0. apply inj_pair2 in H4. subst.
      rewrite rewrite_schedule'. unfold schedule'_match. rewrite <- H5.
      constructor 1 with (x:=x).
      rewrite <- (replace_vec_twice n0 v i (fun _ => k3 x) (fun _ => k0 false)).
      eapply IHtrans_; eauto. rewrite REL. rewrite replace_vec_eq. reflexivity.
    - step in H0. inv H0. apply inj_pair2 in H3, H4, H5, H6. subst.
      rewrite rewrite_schedule'. unfold schedule'_match. rewrite <- H7.
      constructor 2 with (x:=Fin.F1).
  Abort.

  (* actually this is trivial, it's just by defn *)
  Lemma trans_forall_spawn (e : parE config bool) (k : bool -> ctree (parE config) (config * ())) k' :
    (forall b, trans (obs (inr1 (Spawn)) b) (Vis e k) (k' b)) ->
    forall b, k b ≅ k' b.
  Proof.
    intros. specialize (H b). inv H.
    apply inj_pair2 in H2, H3, H4, H5. subst.
    rewrite (ctree_eta t) in H1. rewrite H6 in H1.
    rewrite <- ctree_eta in H1. auto.
  Qed.

  Lemma trans_thread_schedule'_spawn n v i c k :
    (forall b, trans (obs (inr1 (Spawn)) b) (v i c) (k b)) ->
    trans tau (schedule' n v i c)
          (schedule'
             (S n)
             (cons_vec (fun _ => k true) (replace_vec v i (fun _ => k false)))
             (Fin.L_R 1 i)
             c).
  Proof.
    intro. cbn in H. red in H.
    remember (observe (v i c)).
    pose proof (ctree_eta (go (observe (v i c)))).
    rewrite <- Heqc0 in H0 at 1. cbn in H0. clear Heqc0.
    (* remember true as b. clear Heqb.  *)
    pose proof (H true) as Htrue. pose proof (H false) as Hfalse. clear H.
    remember (obs _ true) as lt.
    remember (obs _ false) as lf.
    remember (observe (k true)) as kt.
    remember (observe (k false)) as kf.
    revert n v i c k H0 Heqlt Heqlf Heqkt Heqkf.
    induction Hfalse; induction Htrue; intros; subst; try inv Heqlf; try inv Heqlt.
    - admit.
    - apply inj_pair2 in H4, H3. subst.
    (* - admit. *)


    (* - step in H0. inv H0. apply inj_pair2 in H3. subst. *)
    (* (* eapply IHHfalse; eauto. *) *)
    (*   admit. *)
    (* - step in H0. inv H0. apply inj_pair2 in H3, H4, H5, H6. subst. *)
    (*   rewrite rewrite_schedule'. unfold schedule'_match. rewrite <- H7. *)
    (*   constructor. apply Fin.F1. apply equ_schedule'. apply cons_vec_vec_relation. *)
    (*   + apply replace_vec_vec_relation. repeat intro; auto. *)
    (*     intro. rewrite <- REL. rewrite H. rewrite ctree_eta. rewrite Heqkf. *)
    (*     rewrite <- ctree_eta. reflexivity. *)
    (*   + intro. rewrite <- REL. *)
  Abort.

(*
  Lemma trans_thread_schedule'_yield_cases c c' t (k : thread) :
        trans (obs (inl1 (Yield _ c)) c') t (k c') ->
        (exists X (e : parE config X) k, observe t = VisF e k) \/
          (exists n k, observe t = ChoiceF false n k).
  Proof.
    intros H. inv H.
    - right. do 2 eexists. eauto.
    - left. do 3 eexists. eauto.
  Qed.
*)

  Lemma trans_thread_schedule'_yield_vis (c' : config) n v i i' c e (k k' : thread) :
    observe (v i c) = VisF e k' ->
    (forall c'', trans (obs (inl1 (Yield _ c')) c'') (v i c) (k c'')) ->
    trans tau (schedule' n v i c) (schedule' n (replace_vec v i k) i' c').
  Proof.
    intros. rewrite rewrite_schedule'. unfold schedule'_match. rewrite H.
    (* destruct e. *)
    pose proof (H0 c). cbn in H1. red in H1.
    rewrite H in H1. inv H1. apply inj_pair2 in H4, H5, H6, H7. subst.
    constructor 2 with (x:=i').
    apply equ_schedule'.
    apply replace_vec_vec_relation. repeat intro. reflexivity.
    intro. specialize (H0 x). cbn in H0. red in H0. rewrite H in H0.
    inv H0. apply inj_pair2 in H4, H5, H6, H7. subst. rewrite H2.
    rewrite ctree_eta. rewrite H9. rewrite <- ctree_eta. reflexivity.
  Qed.

  (* Not true, since [v i c] can be something like [choice2 (if true => kc true else nonsense) (if false => kc false else nonsense)], and since [schedule'] behaves syntactically, it will never give us the desired result *)
  Lemma trans_thread_schedule'_yield (c' c'' : config) n v i i' c kc :
    (forall c'', trans (obs (inl1 (Yield _ c')) c'') (v i c) (kc c'')) ->
    trans tau (schedule' n v i c) (schedule' n (replace_vec v i kc) i' c').
  Proof.
    intros. pose proof (H c'') as H0. cbn in H0. red in H0.
    remember (observe (v i c)).
    pose proof (ctree_eta (go (observe (v i c)))).
    rewrite <- Heqc0 in H1 at 1. cbn in H1. clear Heqc0.
    remember (observe (kc c'')).
    pose proof (ctree_eta (go (observe (kc c'')))).
    rewrite <- Heqc1 in H2 at 1. cbn in H2. clear Heqc1.
    remember (obs _ _).
    revert kc v i i' c c' c'' Heql H H1 H2.
    induction H0; intros kc v i i' c c' c'' Heql Htrans Hequ1 Hequ2;
      try solve [inv Heql].
    - step in Hequ1. inv Hequ1. apply inj_pair2 in H3. subst.
      rewrite rewrite_schedule'. unfold schedule'_match. rewrite <- H.
      constructor 1 with (x:=x). rewrite <- (replace_vec_twice n v i (fun _ => k2 x) kc).
      eapply IHtrans_; auto.
      2: { rewrite replace_vec_eq. rewrite REL. reflexivity. }
      intros c'''. rewrite replace_vec_eq. specialize (Htrans c''').
      cbn in Htrans. red in Htrans. rewrite <- H in Htrans.
      inv Htrans. apply inj_pair2 in H4. subst.
      (* apply H5. *)
(*       eapply Htrans.


      eapply IHtrans_; auto.



      pose proof (trans_thread_schedule'_yield_cases _ _ _ _ H0).
      destruct H as [(X & e & k'' & ?) | (? & ? & ?)].
      + clear IHtrans_.
        rewrite H in H0. inv H0. inv HchoiceI.
        apply inj_pair2 in H3, H4, H5, H6, H7. subst.
        (* inv HchoiceI. subst. *)

        step in Hequ. inv Hequ. apply inj_pair2 in H4. subst.
        rewrite rewrite_schedule'. unfold schedule'_match. rewrite <- H5.
        constructor 1 with (x:=x).
        rewrite H in H0. inv H0. apply inj_pair2 in H3, H4, H8, H7. subst.
        specialize (REL x). step in REL. rewrite H in REL. inv REL.
        apply inj_pair2 in H3, H4. subst.
        rewrite rewrite_schedule'. unfold schedule'_match.
        rewrite replace_vec_eq. rewrite <- H6. econstructor; eauto.
        rewrite replace_vec_twice. apply equ_schedule'.
        apply replace_vec_vec_relation. repeat intro; auto.
        intro. rewrite <- REL0.
      (* ok now unfold schedule', and we'll get there I think *)

      (* rewrite H in H0. *)
      eapply trans_thread_schedule'_yield_vis.
*)
      (* step in Hequ. inv Hequ. apply inj_pair2 in H3; subst. *)
      (* rewrite rewrite_schedule'. unfold schedule'_match. rewrite <- H. *)
      (* constructor 1 with (x:=x). *)
      (* rewrite <- (replace_vec_twice n v i (fun _ => k2 x) k'). *)
      (* eapply IHtrans_; auto. *)
      (* 2: { rewrite REL. rewrite replace_vec_eq. reflexivity. } *)

  Abort.

  Require Import Coq.Logic.IndefiniteDescription.

  (* Lemma construct n (v1 v2 : vec n) i c c' k : *)
  (*   (forall c'' : config, trans (obs (inl1 (Yield config c')) c'') (v1 i c) (k c'')) -> *)
  (*   (forall (l : label) (t' : ctree (parE config) (config * ())), *)
  (*       trans l (v1 i c) t' -> *)
  (*       exists2 u' : ctree (parE config) (config * ()), trans l (v2 i c) u' & t' ~ u') -> *)
  (*   {k' : thread | (forall c'', trans (obs (inl1 (Yield config c')) c'') (v2 i c) (k' c'') /\ k c'' ~ k' c'')}. *)
  (* Proof. *)
  (*   intros Ht Hf. *)
  (*   assert *)
  (*        (forall (l : label) (t' : ctree (parE config) (config * ())), *)
  (*            trans l (v1 i c) t' -> *)
  (*            {u' : ctree (parE config) (config * ()) | trans l (v2 i c) u' /\ t' ~ u'}). *)
  (*   { *)
  (*     intros. apply constructive_indefinite_description. *)
  (*     edestruct Hf; eauto. *)
  (*   } clear Hf. rename X into Hf. *)

  (*   eexists. *)
  (*   Unshelve. *)
  (*   2: { *)
  (*     intros c''. destruct (Hf _ _ (Ht c'')). *)
  (*     apply x. *)
  (*   } *)
  (*   intro c''. *)
  (*   split; cbn. *)
  (*   - edestruct Hf. destruct a. apply H. *)
  (*   - edestruct Hf. destruct a. apply H0. *)
  (* Qed. *)

  (* Lemma sbisim_vis_cases {E R X} (t : ctree E R) (e : E X) k : *)
  (*   Vis e k ~ t -> *)
  (*   (exists k', t ≅ Vis e k' /\ forall x, k x ~ k' x). *)

  Lemma sbisim_vis_visible {E R X} (t2 : ctree E R) (e : E X) k1 (Hin: inhabited X) :
    Vis e k1 ~ t2 ->
    exists k2, visible t2 (Vis e k2) /\ (forall x, k1 x ~ k2 x).
  Proof.
    intros.
    step in H. destruct H as [Hf Hb].
    cbn in *. unfold transR in Hf.
    assert
      (forall (l : label) (t' : ctree E R),
          trans_ l (VisF e k1) (observe t') ->
          {u' : ctree E R | trans_ l (observe t2) (observe u') /\ t' ~ u'}).
    {
      intros. apply constructive_indefinite_description.
      edestruct Hf; eauto.
    } clear Hf. rename X0 into Hf.
    destruct Hin as [x].
    edestruct (Hf (obs e x)). constructor. reflexivity.
    destruct a. clear H0 Hb.
    dependent induction H.
    - assert (n = 1%nat) by admit. subst.
      edestruct IHtrans_; try reflexivity.
      intros. rewrite <- x in Hf. edestruct Hf. eauto.
      destruct a.
      exists x3. split. inv H1. apply inj_pair2 in H6. subst.
      assert (x1 = x4).
      admit.
      subst. auto. auto.
      exists x3. split; auto. red. cbn. rewrite <- x. econstructor. apply H0. apply H0.
    - rewrite <- x2 in Hf.
      eexists. Unshelve.
      2: {
        intros x'. edestruct Hf. constructor. reflexivity.
        Unshelve. apply x3. apply x'.
      }
      split.
      + red. cbn. rewrite <- x2. constructor. intros. destruct Hf. destruct a.
        inv H0. apply inj_pair2 in H4, H5, H6, H7. subst.
        rewrite (ctree_eta t0) in H3. rewrite H8 in H3. rewrite <- ctree_eta in H3. auto.
      + intros. destruct Hf. destruct a. cbn. auto.
  Admitted.

  Lemma sbisim_visible {E R X} (t1 t2 : ctree E R) (e : E X) k1 (Hin: inhabited X) :
    t1 ~ t2 ->
    visible t1 (Vis e k1) ->
    exists k2, visible t2 (Vis e k2) /\ (forall x, k1 x ~ k2 x).
  Proof.
    intros. cbn in *. red in H0. remember (observe t1). remember (observe (Vis e k1)).
    revert X t1 e k1 t2 H Heqc Heqc0 Hin.
    induction H0; intros; auto.
    - assert (n = 1%nat) by admit. subst. eapply IHvisible_. 2: reflexivity. all: auto.
      pose proof (ctree_eta t1). rewrite <- Heqc in H1. rewrite H1 in H.
      epose proof (sbisim_ChoiceI_1_inv _ _ _ H); auto. apply H2.
    - inv Heqc0.
    - inv Heqc0. apply inj_pair2 in H3, H4. subst.
      apply sbisim_vis_visible; auto.
      pose proof (ctree_eta t1).  rewrite <- Heqc in H1.
      (* TODO: clean this up *) eapply equ_VisF in H. rewrite H in H1.
      rewrite H1 in H0. auto.
    - inv Heqc0.
  Admitted.

  Lemma visible_yield_trans_schedule' n v i c i' c' k :
    visible (v i c) (Vis (inl1 (Yield config c')) k) ->
    trans tau (schedule' n v i c) (schedule' n (replace_vec v i k) i' c').
  Proof.
    intros. cbn in *. red in H |- *.
    remember (observe (v i c)). remember (observe (Vis _ k)).
    revert v i c i' c' k Heqc0 Heqc1.
    induction H; intros; subst; try inv Heqc1.
    - assert (n0 = 1%nat) by admit. subst.
      rewrite rewrite_schedule' at 1. unfold schedule'_match.
      rewrite <- Heqc0. constructor 1 with (x:=x).
      rewrite <- (replace_vec_twice _ v i (fun _ => k x) k0).
      eapply IHvisible_; auto. rewrite replace_vec_eq. auto.
    - apply inj_pair2 in H2, H3. subst.
      rewrite rewrite_schedule' at 1. unfold schedule'_match.
      rewrite <- Heqc0. econstructor. apply equ_schedule'.
      apply replace_vec_vec_relation; repeat intro; auto.
  Admitted.

  Lemma visible_spawn_trans_schedule' n v i c k :
    visible (v i c) (Vis (inr1 Spawn) k) ->
    trans tau (schedule' n v i c)
          (schedule' (S n)
                     (cons_vec (fun _ => k true)
                               (replace_vec v i (fun _ => k false)))
                     (Fin.L_R 1 i)
                     c).
  Proof.
    intros. cbn in *. red in H |- *.
    remember (observe (v i c)). remember (observe (Vis _ k)).
    revert v i c k Heqc0 Heqc1.
    induction H; intros; subst; try inv Heqc1.
    - assert (n0 = 1%nat) by admit. subst.
      rewrite rewrite_schedule' at 1. unfold schedule'_match.
      rewrite <- Heqc0. constructor 1 with (x:=x).
      rewrite <- (replace_vec_twice _ v i (fun _ => k x) (fun _ => k0 false)).
      eapply IHvisible_; auto. rewrite replace_vec_eq. auto.
    - apply inj_pair2 in H2, H3. subst.
      rewrite rewrite_schedule' at 1. unfold schedule'_match.
      rewrite <- Heqc0. econstructor. apply Fin.F1. apply equ_schedule'.
      apply cons_vec_vec_relation; auto.
      apply replace_vec_vec_relation; repeat intro; auto.
  Admitted.

  #[global] Instance sbisim_schedule' n :
    Proper ((vec_relation sbisim) ==> vec_relation sbisim) (schedule' n).
  Proof.
    repeat intro. revert H. revert n x y i c.
    coinduction r CIH.
    symmetric using intuition.
    intros n v1 v2 i c Hv l t Ht.
    destruct l.
    - apply trans_schedule'_thread_tau in Ht.
      decompose [or] Ht; clear Ht.
      + destruct H as (c' & n' & i' & Ht & Hn & Hequ).
        subst. pose proof (Hv i c) as Hsb. step in Hsb. destruct Hsb as [Hf Hb].
        edestruct Hf as [? ? ?]; eauto.
        eapply trans_thread_schedule'_val_SS in H.
        eexists. apply H. rewrite Hequ. apply CIH.
        cbn. apply remove_vec_vec_relation; auto.      + destruct H0 as (t' & Ht & Hequ).
        pose proof (Hv i c) as Hsb. step in Hsb. destruct Hsb as [Hf Hb].
        edestruct Hf as [? ? ?]; eauto.
        apply trans_thread_schedule'_tau in H.
        eexists; eauto. rewrite Hequ. apply CIH.
        apply replace_vec_vec_relation; auto.
      + destruct H as (c' & k & Hvis & i' & Hequ).
        pose proof (Hv i c) as Hsb.
        eapply sbisim_visible in Hvis; eauto. destruct Hvis as (k' & ? & ?).
        exists (schedule' n (replace_vec v2 i k') i' c').
        2: { rewrite Hequ. apply CIH. apply replace_vec_vec_relation; auto. }
        apply visible_yield_trans_schedule'; auto.
      + destruct H as (k & Hvis & Hequ).
        pose proof (Hv i c) as Hsb.
        eapply sbisim_visible in Hvis; eauto. 2: { constructor. apply true. }
        destruct Hvis as (k' & ? & ?).
        exists (schedule' (S n)
                     (cons_vec (fun _ => k' true)
                               (replace_vec v2 i (fun _ => k' false)))
                     (Fin.L_R 1 i) c).
        2: { rewrite Hequ. apply CIH. apply cons_vec_vec_relation; auto.
             apply replace_vec_vec_relation; auto. }
        apply visible_spawn_trans_schedule'; auto.
    - apply trans_schedule'_obs in Ht. contradiction.
    - pose proof (trans_schedule'_val_1 _ _ _ _ _ _ Ht). subst.
      pose proof (trans_val_inv Ht).
      specialize (Hv i c). step in Hv. destruct Hv as [Hf Hb].
      pose proof (trans_schedule'_thread_val _ _ _ _ _ Ht) as Hv1.
      edestruct Hf; eauto.
      apply trans_thread_schedule'_val_1 in H0. eexists; eauto. rewrite H. reflexivity.
  Qed.

End parallel.
