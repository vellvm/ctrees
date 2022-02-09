From Coq Require Import
     Program
     List
     Logic.FunctionalExtensionality.

Require Import Coq.micromega.Lia.

From CTree Require Import
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
            t_equ eq r (schedule x x0 y1) (schedule y y0 y1)) :
    forall r1 r2,
    pointwise_relation config (equ eq) k1 k2 ->
    list_relation (pointwise_relation _ (equ eq)) l1 l2 ->
    list_relation (pointwise_relation _ (equ eq)) r1 r2 ->
    equF eq (t_equ eq r)
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

  Definition replace_vec {n : nat} (v : vec n) (i : fin n) (t : thread) : vec n :=
    fun i' => if Fin.eqb i i' then t else v i'.

  Lemma replace_vec_vec_relation n P (v1 v2 : vec n) i t1 t2 :
    vec_relation P v1 v2 ->
    (forall x, P (t1 x) (t2 x)) ->
    vec_relation P (replace_vec v1 i t1) (replace_vec v2 i t2).
  Proof.
    unfold replace_vec. repeat intro. destruct (Fin.eqb i i0); auto.
  Qed.

  Lemma replace_vec_eq n (v : vec n) i t :
    (replace_vec v i t) i = t.
  Proof.
    unfold replace_vec.
    assert (i = i) by reflexivity. apply Fin.eqb_eq in H. rewrite H.
    reflexivity.
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
                                       (fun i' => schedule' n' (remove_vec _ _) i' c')
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
    - subst. apply v.
    - subst. apply i.
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

  #[global] Instance equ_schedule' n :
    Proper ((vec_relation sbisim) ==> vec_relation sbisim) (schedule' n).
  Proof.
    repeat intro. revert H. revert n x y i c.
    coinduction r CIH.
    symmetric using intuition.
    intros n v1 v2 i c Hv. (* Unset Printing Notations. *)
    pose proof (Hv i c) as H.
    destruct (observe (v1 i c)) eqn:Hv1; [| | destruct vis];
      (destruct (observe (v2 i c)) eqn:Hv2; [| | destruct vis]);
      rewrite ctree_eta, (ctree_eta (v2 i c)) in H; rewrite Hv1, Hv2 in H.
    (* Ret *)
    - pose proof (sbisim_ret_ret_inv _ _ H). subst.
      do 2 rewrite rewrite_schedule'. unfold schedule'_match.
      rewrite Hv1, Hv2. destruct r1. destruct n. inv i.
      destruct n; repeat intro.
      + apply trans_ret_inv in H0. destruct H0; subst.
        eexists; eauto. rewrite H1. constructor.
      + apply trans_ChoiceV_inv in H0. destruct H0 as [? [? ?]]. subst.
        eexists. econstructor; eauto.
        rewrite H0. apply CIH. apply remove_vec_vec_relation; eauto.
    - contradiction (sbisim_ret_vis_inv _ _ _ H).
    - contradiction (sbisim_ret_ChoiceV_inv _ _ _ H).
    - (* ChoiceI *)
      step in H. destruct H as [H H'].
      cbn in H. specialize (H _ _ (trans_ret _)).
      destruct H.
      do 2 rewrite rewrite_schedule'. unfold schedule'_match.
      rewrite Hv1, Hv2. destruct r0, u. destruct n. inv i.
      (* repeat intro. *)
      (* eexists. *)
      (* 2: { apply CIH. *)


      remember (ChoiceI _ _); remember (val _). revert n0 k H' Hv1 Hv2 Heqc1 Heql.
      induction H.
      + auto.
      + intros. inv Heql.
      + intros. inv Heql.
      + intros. inv Heql.
        apply inj_pair2 in H1. subst.

      (* do 2 rewrite rewrite_schedule'. unfold schedule'_match. *)
      (* rewrite Hv1, Hv2. destruct r0, u. destruct n. inv i. *)
      (* destruct n. *)
      (* + repeat intro. apply trans_ret_inv in H. destruct H. subst. *)
      (*   assert (exists i', k i' ~ Ret (c0, ())) by admit. destruct H0. *)
      (*   eexists. *)
      (*   2: { rewrite H1. reflexivity. } *)
      (*   apply (Stepchoice x). *)

      (*   (* eapply (trans_ChoiceI _ _); eauto. *) *)
      (*   rewrite rewrite_schedule'. unfold schedule'_match. *)
      (*   rewrite replace_vec_eq. *)
        admit.
      (* + repeat intro. *)
      (*   apply trans_ChoiceV_inv in H0. destruct H0 as [? [? ?]]. subst. *)
      (*   eexists. *)
      (*   2: { rewrite H0. apply CIH. apply remove_vec_vec_relation; eauto. } *)
      (*   econstructor; eauto. *)
    (* Vis *)
    - symmetry in H. contradiction (sbisim_ret_vis_inv _ _ _ H).
    - assert (x : X).
      { destruct e. destruct y; auto. destruct s; auto. apply false. }
      pose proof (sbisim_vis_vis_inv_type _ _ _ _ x H). subst.
      pose proof (sbisim_vis_vis_inv _ _ _ _ x H). destruct H0 as [? Hk]; subst.
      clear x. rename e0 into e.
      do 2 rewrite rewrite_schedule'. unfold schedule'_match.
      rewrite Hv1, Hv2. destruct e; [destruct y | destruct s].
      + intros l s Ht. apply trans_ChoiceV_inv in Ht.
        destruct Ht as [i' [Hs ?]]; subst.
        eexists. econstructor; eauto. rewrite Hs.
        apply CIH; auto. apply replace_vec_vec_relation; auto.
      + intros l s Ht. apply trans_TauV_inv in Ht.
        destruct Ht as [Hs ?]; subst.
        eexists. econstructor; eauto. apply Fin.F1. rewrite Hs.
        apply CIH; auto.
        apply cons_vec_vec_relation; auto.
        apply replace_vec_vec_relation; auto.
    - assert (x : X) by admit.
      contradiction (sbisim_vis_ChoiceV_inv _ _ _ _ x H).
    - admit.
    (* ChoiceV *)
    - symmetry in H.
      contradiction (sbisim_ret_ChoiceV_inv _ _ _ H).
    - assert (x : X) by admit. symmetry in H.
      contradiction (sbisim_vis_ChoiceV_inv _ _ _ _ x H).
    - pose proof (sbisim_ChoiceV_ChoiceV_inv _ _ _ _ H).
      do 2 rewrite rewrite_schedule'. unfold schedule'_match.
      rewrite Hv1, Hv2.
      intros l s Ht. apply trans_ChoiceV_inv in Ht. destruct Ht as [i' [Hs ?]]; subst.
      destruct (H0 i').
      eexists. econstructor; eauto. rewrite Hs; auto. apply CIH.
      apply replace_vec_vec_relation; auto. intro. eauto.
    - (* ChoiceI *) admit.
    (* ChoiceI *)
    - admit.
    - admit.
    - admit.
    - do 2 rewrite rewrite_schedule'. unfold schedule'_match.
      rewrite Hv1, Hv2.
      repeat intro.
      remember (ChoiceI n0 _) in H0. revert Heqc0.
      induction H0; auto.
      + intros. subst.
  (*   - clear H1 H2. destruct y. destruct n; cbn in *; auto. *)
  (*     destruct n; cbn; auto. constructor. intros. apply CIH. *)
  (*     apply remove_vec_vec_relation; auto. *)
  (*   - clear H1 H2. destruct y. cbn. *)
  (*     constructor. intros. eapply CIH. *)
  (*     apply replace_vec_vec_relation; auto. *)
  (*   - destruct s. constructor. intros. eapply CIH. *)
  (*     apply cons_vec_vec_relation; auto. *)
  (*     apply replace_vec_vec_relation; auto. *)
  (*   - cbn. constructor. intros. apply CIH. *)
  (*     apply replace_vec_vec_relation; auto. *)
  (* Qed. *)
  Abort.

End parallel.
