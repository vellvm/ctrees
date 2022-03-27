From Coq Require Import
     Program
     List
     Logic.FunctionalExtensionality
     micromega.Lia
     Init.Specif.

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

Import ListNotations.
Import CTreeNotations.

Variant yieldE S : Type -> Type :=
| Yield : S -> yieldE S S.

Variant spawnE : Type -> Type :=
| Spawn : spawnE bool.

(* Fixpoint remove_at {A} {n : nat} {H : n > 0} (l : fin n -> A) (i : fin n) : fin (n - 1) -> A := *)
(*   fun (i' : fin (n - 1)) => *)
(*     _ *)
(* . *)


(** return one of the elements in [x :: xs], as well as the complete list of unchosen elements *)
Fixpoint choose' {E} {X} (x : X) (xs : list X) (rest : list X) :
  ctree E (X * list X)
  := match xs with
     | [] => Ret (x, rest)
     | x' :: xs =>
         choiceI2
         (Ret (x, (x' :: xs) ++ rest)) (* [x] *)
         (choose' x' xs (x :: rest)) (* not [x] *)
     end.
Definition choose {E} {X} (x : X) (xs : list X) : ctree E (X * list X) :=
  choose' x xs [].

Section parallel.
  Context {config : Type}.

  Definition parE c := yieldE c +' spawnE.

  Definition thread := Monads.stateT config
                                     (ctree (parE config))
                                     unit.

  Definition completed := Monads.stateT config (ctree void1) unit.

  Definition schedule_match schedule (curr : thread) (rest : list thread)
    : completed :=
    fun (s : config) =>
      match (observe (curr s)) with
      | RetF (s', _) => match rest with
                       | [] => Ret (s', tt)
                       | h :: t => '(curr', rest') <- choose h t;;
                                 TauI (schedule curr' rest' s')
                       end
      | ChoiceF b n k => Choice b n (fun c => (schedule (fun _ => k c) rest s))
      | VisF (inl1 e) k =>
          match e in yieldE _ C return (C -> ctree (parE config) (config * unit)) -> _ with
          | Yield _ s' =>
              fun k =>
                '(curr', rest') <- choose k rest;;
                TauI (schedule curr' rest' s')
          end k
      | VisF (inr1 e) k =>
          match e in spawnE R return (R -> ctree (parE config) (config * unit)) -> _ with
          | Spawn =>
              fun k =>
                TauI (schedule (fun _ => k false) ((fun _ => k true) :: rest) s) (* this s doesn't matter, since the running thread won't use it *)
          end k
      end.
  CoFixpoint schedule := schedule_match schedule.
  Lemma rewrite_schedule curr rest s : schedule curr rest s ≅ schedule_match schedule curr rest s.
  Proof.
    step. eauto.
  Qed.

  Fixpoint list_relation {T} (P : relation T) (l1 l2 : list T) : Prop :=
    match l1, l2 with
    | [], [] => True
    | h1 :: t1, h2 :: t2 => P h1 h2 /\ list_relation P t1 t2
    | _, _ => False
    end.

  #[global] Instance list_relation_refl {T} (P : relation T)
        `{Reflexive _ P} :
    Reflexive (list_relation P).
  Proof.
    repeat intro. induction x; auto. split; auto.
  Qed.

  Lemma list_relation_app {T} (P : relation T) l1 l2 r1 r2 :
    list_relation P l1 l2 ->
    list_relation P r1 r2 ->
    list_relation P (l1 ++ r1) (l2 ++ r2).
  Proof.
    revert l2.
    induction l1; destruct l2; intros Hl Hr; inv Hl; try split; auto.
  Qed.

  Lemma equ_schedule_helper k1 k2 l1 l2 s r
        (CIH : forall (x y : config -> ctree (parE config) (config * ()))
                 (x0 y0 : list (config -> ctree (parE config) (config * ())))
                 (y1 : config),
            pointwise_relation config (equ eq) x y ->
            list_relation (pointwise_relation config (equ eq)) x0 y0 ->
            et eq r (schedule x x0 y1) (schedule y y0 y1)) :
    forall r1 r2,
    pointwise_relation config (equ eq) k1 k2 ->
    list_relation (pointwise_relation _ (equ eq)) l1 l2 ->
    list_relation (pointwise_relation _ (equ eq)) r1 r2 ->
    equF eq (et eq r)
         (observe ('(curr', rest') <- choose' k1 l1 r1;;
                   TauI (schedule curr' rest' s)))
         (observe ('(curr', rest') <- choose' k2 l2 r2;;
                   TauI (schedule curr' rest' s))).
  Proof.
    revert l2 k1 k2.
    induction l1; destruct l2; intros k1 k2 r1 r2 Hk Hl Hr; inv Hl.
    - cbn. constructor. intros; auto.
    - cbn. constructor. intros [].
      + step. cbn. constructor. intros. apply CIH; auto. constructor; auto.
        apply list_relation_app; auto.
      + step. eapply IHl1; eauto. constructor; auto.
  Qed.

  #[global] Instance equ_schedule :
    Proper ((pointwise_relation _ (equ eq)) ==> (list_relation (pointwise_relation _ (equ eq))) ==> eq ==> equ eq)
           schedule.
  Proof.
    repeat intro. subst. revert H H0. revert x y x0 y0 y1.
    coinduction r CIH. intros t1 t2 l1 l2 c Ht Hl.
    do 2 rewrite rewrite_schedule. unfold schedule_match. simpl.
    specialize (Ht c). step in Ht. inv Ht; eauto. 2: destruct e.
    - destruct y. destruct l1, l2; inv Hl; auto.
      apply equ_schedule_helper; auto.
    - clear H H0. destruct y.
      unfold choose.
      apply equ_schedule_helper; auto.
    - destruct s. constructor. intros. apply CIH.
      + intro. apply REL.
      + constructor; auto. intro. auto.
    - cbn. constructor. intros. apply CIH; auto.
      intro. apply REL.
  Qed.

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
    (* this is the one we're removing, so bump [i'] by one *)
    | Fin.F1 => remove_front_vec v
    (* not yet at the index we want to ignore *)
    | Fin.FS j => fun i' =>
                   match i' with
                   | Fin.F1 => v Fin.F1
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

  Lemma remove_vec_replace_vec_eq {n} (v : vec (S n)) i t :
    remove_vec v i = remove_vec (replace_vec v i t) i.
  Proof.
  Admitted.

  Lemma remove_vec_helper_replace_vec_eq {n n'} (v : vec n) i t H :
    remove_vec_helper n n' v i H = remove_vec_helper n n' (replace_vec v i t) i H.
  Proof.
  Admitted.

  Lemma replace_vec_vec_relation n P (v1 v2 : vec n) i t1 t2 :
    vec_relation P v1 v2 ->
    (forall x, P (t1 x) (t2 x)) ->
    vec_relation P (replace_vec v1 i t1) (replace_vec v2 i t2).
  Proof.
    unfold replace_vec. repeat intro. destruct (Fin.eqb i i0); auto.
  Qed.

  (* Lemma replace_vec_sb n (v : vec n) i t : *)

  (*   (replace_vec v i t) i = t. *)
  (* Proof. *)
  (*   unfold replace_vec. *)
  (*   assert (i = i) by reflexivity. apply Fin.eqb_eq in H. rewrite H. *)
  (*   reflexivity. *)
  (* Qed. *)

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
                                       (fun i' => schedule' n' (remove_vec_helper n n' v i _) i' c')
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
    - subst. reflexivity.
  Defined.



  (* Definition k1 : bool -> ctree fooE nat := fun b : bool => (if b then Ret 0%nat else Ret 1%nat). *)
  (* Definition k2 : bool -> ctree fooE nat := fun b : bool => (if b then Ret 2%nat else Ret 3%nat). *)
  (* Definition t1 : ctree fooE nat := choiceI2 (Vis Foo k1) (Vis Foo k2). *)
  (* Definition t2 : ctree fooE nat := *)
  (*   choiceI2 (Vis Foo (fun b: bool => if b then Ret 0%nat else Ret 3%nat)) *)
  (*            (Vis Foo (fun b: bool => if b then Ret 2%nat else Ret 1%nat)). *)

  (* sched [Ret tt; t] 0 c ~  sched [t] 0 c *)

  (* sched [t1] ~~ ChoiceI2 (sched [Spawn 0 1]) (sched [Spawn 2 3]) ~~ChoiceI2 (TauV ( *)
  (* sched [t2] ~~ ChoiceI2 (Spawn 0 3) (Spawn 2 1) *)


  CoFixpoint schedule' := schedule'_match schedule'.

  (* Alternate definition: factoring out the yielding effect *)
  Definition schedule''_match
             (schedule' : forall (n : nat), vec n -> option (fin n) -> thread)
             (n : nat)
             (v: vec n)
    : option (fin n) -> thread.
    refine
      (fun (oi : option (fin n)) c =>
         match oi with
         | None   => match n with
                    | O => Ret (c,tt)
                    | _ => ChoiceV n (fun i' => schedule' n v (Some i') c)
                    end
         | Some i =>
             match (observe (v i c)) with
             | RetF (c', _) =>
                 match n as m return n = m -> _ with
                 | 0 => _
                 | S n' => fun H1 => TauI (schedule' n' (remove_vec_helper n n' v i _) None c')
                 end (eq_refl n)
             | ChoiceF b n' k => Choice b n' (fun i' => schedule' n (replace_vec v i (fun _ => k i')) (Some i) c)
             | VisF (inl1 e) k =>
                 match e in yieldE _ R return (R -> ctree (parE config) (config * unit)) -> _ with
                 | Yield _ s' =>
                     fun k => TauI (schedule' n (replace_vec v i k) None s')
                 end k
             | VisF (inr1 e) k =>
                 match e in spawnE R return (R -> ctree (parE config) (config * unit)) -> _ with
                 | Spawn =>
                     fun k =>
                       TauV (schedule'
                               (S n)
                               (cons_vec (fun _ => k true) (replace_vec v i (fun _ => k false)))
                               (* The [i] here means that we don't yield at a spawn *)
                               (Some (Fin.L_R 1 i)) (* view [i] as a [fin (n + 1)] *)
                               c) (* this [c] doesn't matter, since the running thread won't use it *)
                 end k
             end
         end).
    - intro. subst. inv i.
    - subst. reflexivity.
  Defined.

  CoFixpoint schedule'' := schedule''_match schedule''.

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
      (exists c' k, (forall c'', trans (obs (inl1 (Yield _ c')) c'') (v i c) (k c'')) /\
                 visible (v i c) (Vis (inl1 (Yield _ c')) k) /\
                 exists i', t ≅ schedule' n (replace_vec v i k) i' c') \/
      (exists k, (forall b, trans (obs (inr1 (Spawn)) b) (v i c) (k b)) /\
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
      + right. right. left. destruct H0 as (c' & k'' & Ht & Hvis & i' & Ht').
        rewrite replace_vec_eq in Ht, Hvis.
        exists c', k''. split; [| split].
        * intro. rewrite Hequ. econstructor. apply Ht.
        * rewrite Hequ. econstructor. apply Hvis.
        * exists i'. setoid_rewrite replace_vec_twice in Ht'. apply Ht'.
      + right. right. right. destruct H0 as (kb & Ht & Ht').
        rewrite replace_vec_eq in Ht.
        exists kb. split.
        * intros b. rewrite Hequ. econstructor. apply Ht.
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
        exists c0, k0. split; [| split].
        * intro. cbn. red. rewrite Hv. econstructor. reflexivity.
        * cbn. red. rewrite Hv. constructor.
        * pose proof (ctree_eta t). rewrite Heq in H0. rewrite <- ctree_eta in H0.
          setoid_rewrite <- H0. setoid_rewrite <- H.
          destruct (equ_choice_invT _ _ Hequ); subst. clear H2.
          exists x. pose proof (equ_choice_invE _ _ Hequ). setoid_rewrite H1.
          reflexivity.
      + right. right. right. destruct s. cbn in Hequ.
        destruct (equ_choice_invT _ _ Hequ) as [? _]. subst.
        pose proof (equ_choice_invE _ _ Hequ) as Hk. cbn in Hk.
        eexists. split.
        * intros. cbn. red.
          rewrite Hv. econstructor. reflexivity.
        * rewrite ctree_eta. rewrite <- Heq. rewrite <- ctree_eta. rewrite <- H.
          apply Hk.
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

  (* not actually useful, just for testing *)
  (* if schedule is a ret, then so is (v i s).
     if it's a choiceI, then so is (v i s).
     if it's a choiceV, then (v i s) could be any of ret, vis, or choiceV.
     it's impossible for it to be a vis.
   *)
  Lemma foo l t n v i c :
    trans l (schedule' n v i c) t ->
    exists u' l', trans l' (v i c) u'.
  Proof.
    intro. cbn in H. red in H.
    remember (observe (schedule' n v i c)).
    pose proof (ctree_eta (go (observe (schedule' n v i c)))).
    rewrite <- Heqc0 in H0 at 1. cbn in H0. clear Heqc0. remember (observe t).
    revert t n v i c Heqc1 H0.
    induction H; intros t' n' v i c Heq Hequ.
    - clear H.
      rewrite rewrite_schedule' in Hequ. unfold schedule'_match in Hequ.
      destruct (observe (v i c)) eqn:Hv.
      + destruct r, n'; [inv i |].
        destruct n'; step in Hequ; inv Hequ.
      + destruct e; [destruct y | destruct s]; step in Hequ; inv Hequ.
      + destruct vis; [step in Hequ; inv Hequ |].
        destruct (equ_choice_invT _ _ Hequ); subst. clear H0.
        pose proof (equ_choice_invE _ _ Hequ x).
        setoid_rewrite H in IHtrans_.
        edestruct IHtrans_. reflexivity.
        step. reflexivity.
        rewrite replace_vec_eq in H0. destruct H0.
        do 2 eexists. cbn. red. rewrite Hv. econstructor. apply H0.
    - clear H.
      rewrite rewrite_schedule' in Hequ. unfold schedule'_match in Hequ.
      destruct (observe (v i c)) eqn:Hv.
      + clear Hequ. exists CTree.stuckI. eexists. cbn. red. rewrite Hv. econstructor.
      + destruct e; [destruct y | destruct s]; step in Hequ; inv Hequ.
        * apply inj_pair2 in H2, H4; subst.
          do 2 eexists. cbn. red. rewrite Hv. constructor 3 with (x := c). reflexivity.
        * apply inj_pair2 in H2, H4; subst.
          do 2 eexists. cbn. red. rewrite Hv. constructor 3 with (x := true). reflexivity.
      + destruct vis; [| step in Hequ; inv Hequ].
        destruct (equ_choice_invT _ _ Hequ); subst. clear H0.
        do 2 eexists. cbn. red. rewrite Hv. constructor 2 with (x := x). reflexivity.
    - clear H.
      rewrite rewrite_schedule' in Hequ. unfold schedule'_match in Hequ.
      destruct (observe (v i c)) eqn:Hv.
      + destruct n'. inv i. destruct r. destruct n'; step in Hequ; inv Hequ.
      + destruct e0; [destruct y | destruct s]; step in Hequ; inv Hequ.
      + step in Hequ; inv Hequ.
    - rewrite rewrite_schedule' in Hequ. unfold schedule'_match in Hequ.
      destruct (observe (v i c)) eqn:Hv.
      + clear Hequ. exists CTree.stuckI. eexists. cbn. red. rewrite Hv. econstructor.
      + destruct e; [destruct y | destruct s]; step in Hequ; inv Hequ.
      + step in Hequ; inv Hequ.
  Qed.

  Require Import Coq.Logic.IndefiniteDescription.

  Lemma construct n (v1 v2 : vec n) i c c' k :
    (forall c'' : config, trans (obs (inl1 (Yield config c')) c'') (v1 i c) (k c'')) ->
    (forall (l : label) (t' : ctree (parE config) (config * ())),
        trans l (v1 i c) t' ->
        exists2 u' : ctree (parE config) (config * ()), trans l (v2 i c) u' & t' ~ u') ->
    {k' : thread | (forall c'', trans (obs (inl1 (Yield config c')) c'') (v2 i c) (k' c'') /\ k c'' ~ k' c'')}.
  Proof.
    intros Ht Hf.
    assert
         (forall (l : label) (t' : ctree (parE config) (config * ())),
             trans l (v1 i c) t' ->
             {u' : ctree (parE config) (config * ()) | trans l (v2 i c) u' /\ t' ~ u'}).
    {
      intros. apply constructive_indefinite_description.
      edestruct Hf; eauto.
    } clear Hf. rename X into Hf.

    eexists.
    Unshelve.
    2: {
      intros c''. destruct (Hf _ _ (Ht c'')).
      apply x.
    }
    intro c''.
    split; cbn.
    - edestruct Hf. destruct a. apply H.
    - edestruct Hf. destruct a. apply H0.
  Qed.



  Variant fooE: Type -> Type := | Foo : fooE bool.
  Definition k1 : bool -> ctree fooE nat := fun b : bool => (if b then Ret 0%nat else Ret 1%nat).
  Definition k2 : bool -> ctree fooE nat := fun b : bool => (if b then Ret 2%nat else Ret 3%nat).
  Definition t1 : ctree fooE nat := choiceI2 (Vis Foo k1) (Vis Foo k2).

  Definition u1 : ctree fooE nat :=
    choiceI2 (Vis Foo (fun b: bool => if b then Ret 0%nat else Ret 3%nat))
             (Vis Foo (fun b: bool => if b then Ret 2%nat else Ret 1%nat)).

  Fact are_bisim: t1 ~ u1.
  step.
  split.
  - intros ? ? TR.
    unfold t1 in TR.
    remember 3%nat as x3.
    remember 2%nat as x2.
    remember 1%nat as x1.
    remember 0%nat as x0.
    inv_trans; subst.
    + apply trans_vis_inv in TR as (b & ? & ->).
      unfold u1.
      destruct b.
      * eexists.
        apply trans_choiceI21.
        apply trans_vis.
        rewrite H; reflexivity.
      * eexists.
        apply trans_choiceI22.
        apply trans_vis.
        rewrite H; reflexivity.
    + apply trans_vis_inv in TR as (b & ? & ->).
      unfold u1.
      destruct b.
      * eexists.
        apply trans_choiceI22.
        apply trans_vis.
        rewrite H; reflexivity.
      * eexists.
        apply trans_choiceI21.
        apply trans_vis.
        rewrite H; reflexivity.
  - cbn; intros ? ? TR.
    unfold u1 in TR.
    remember 3%nat as x3.
    remember 2%nat as x2.
    remember 1%nat as x1.
    remember 0%nat as x0.
    inv_trans; subst.
    + apply trans_vis_inv in TR as (b & ? & ->).
      unfold t1.
      destruct b.
      * eexists.
        apply trans_choiceI21.
        apply trans_vis.
        rewrite H; reflexivity.
      * eexists.
        apply trans_choiceI22.
        apply trans_vis.
        rewrite H; reflexivity.
    + apply trans_vis_inv in TR as (b & ? & ->).
      unfold u1.
      destruct b.
      * eexists.
        apply trans_choiceI22.
        apply trans_vis.
        rewrite H; reflexivity.
      * eexists.
        apply trans_choiceI21.
        apply trans_vis.
        rewrite H; reflexivity.
Qed.

Fact is_vis : visible t1 (Vis Foo k1).
Proof.
  eapply VisibleI with (x := Fin.F1); econstructor.
Qed.

Fact abs : forall k2, visible u1 (Vis Foo k2) -> exists x, ~ (k1 x ~ k2 x).
Proof.
  intros ? VIS.
  red in VIS; cbn in VIS.
  unfold u1 in VIS.
  red in VIS.
  cbn in VIS.
  dependent destruction VIS.
  dependent destruction x.
  - dependent destruction VIS.
    exists false.
    cbn.
    intros abs; apply sbisim_ret_ret_inv in abs; lia.
  - dependent destruction VIS.
    exists true.
    cbn.
    intros abs; apply sbisim_ret_ret_inv in abs; lia.
Qed.


  Lemma sbism_visible {E R X} (t1 t2 : ctree E R) (e : E X) k1 :
    t1 ~ t2 ->
    visible t1 (Vis e k1) ->
    exists k2, visible t2 (Vis e k2) /\ (forall x, k1 x ~ k2 x).
  Proof.
    intros * bis VIS. cbn in *.
    revert t2 bis.
    red in VIS; cbn in VIS.
    dependent induction VIS; intros; auto.
    - destruct (observe t1) eqn:EQ; dependent induction x.

    (*
    visible t1 (Vis e k1)
    ->
    (forall x, trans (obs e x) t1 (k x))


t1 == ChoiceI2 (Vis e k1) (Vis e k1')
t2 == choiceI2 (Vis e k2) (Vis e k2')

k2 true   = k1 true
k2 false  = k1' false

k2' true  = k1' true
k2' false = k1 false




     ChoiceI 2
     Vis e                  Vis e
     false —> k1 false      false -> k2 false
     true -> k2 true        true  -> k1 true


k1' k1 false k2 true

     *)


  (*   - admit. *)
  (*   - admit. *)
  (*   red in H0. remember (observe t1). remember (observe (Vis e k1)). *)
  (*   revert X t1 e k1 t2 H Heqc Heqc0. *)
  (*   induction H0; intros; auto. *)
  (*   - eapply IHvisible_. 2: reflexivity. 2: auto. admit. *)
  (*   - inv Heqc0. *)
  (*   - inv Heqc0. apply inj_pair2 in H2, H3. subst. admit. *)
  (*   - inv Heqc0. *)
  Abort.

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
      + destruct H as (c' & k & Ht & Hvis & i' & Hequ).
        pose proof (Hv i c) as Hsb. step in Hsb. destruct Hsb as [Hf Hb].
        simpl in Hf.
        destruct (construct _ _ _ _ _ _ _ Ht Hf) as (k' & ?).
        exists (schedule' n (replace_vec v2 i k') i' c').
        2: { rewrite Hequ. apply CIH; auto. apply replace_vec_vec_relation; auto.
             intros.
             apply a.
        }
        admit.
        (* eapply trans_thread_schedule'_yield. apply a. *)

    (* so problem: on the tau lemma, if we try to change from k to t, then it becomes too specific. the schedule step could have chosen another thread to run. Conversely, For the yield lemma, if we change from t to k, then it becomes too specific too. The bisimulation won't go to another k c, it'll go to a t. *)
      + destruct H as (k & Ht & Hequ).
(* TODO: do something similar to above
        assert (forall b, trans (obs (inr1 Spawn) b) (v2 i c) (k b)).
        {
          intro. specialize (Ht b). specialize (Hv i c). step in Hv. destruct Hv.
          edestruct H; eauto.
        apply trans_thread_schedule'_spawn in Ht.
        eexists. 2: { rewrite Hequ. reflexivity. }
 *)
        admit.

    - apply trans_schedule'_obs in Ht. contradiction.
    - pose proof (trans_schedule'_val_1 _ _ _ _ _ _ Ht). subst.
      pose proof (trans_val_inv Ht).
      specialize (Hv i c). step in Hv. destruct Hv as [Hf Hb].
      pose proof (trans_schedule'_thread_val _ _ _ _ _ Ht) as Hv1.
      edestruct Hf; eauto.
      apply trans_thread_schedule'_val_1 in H0. eexists; eauto. rewrite H. reflexivity.
  Abort.

End parallel.
