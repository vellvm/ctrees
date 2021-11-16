From Coq Require Import
     Program
     List
     Logic.FunctionalExtensionality.

From CTree Require Import
	Utils
	CTrees
 	Interp
	Equ
	Bisim
    Shallow.

From ITree Require Import
     Sum.

From Coinduction Require Import
	coinduction rel tactics.

Import ListNotations.
Import CTreeNotations.

Variant yieldE S : Type -> Type :=
| Yield : S -> yieldE S S.

Inductive spawnE C (E : Type -> Type) : Type -> Type :=
| Spawn : forall (t: C -> ctree (E +' spawnE C E) (C * unit)), spawnE C E unit.

(** return one of the elements in [x :: xs], as well as the complete list of unchosen elements *)
Fixpoint choose' {E} {X} (x : X) (xs : list X) (rest : list X) :
  ctree E (X * list X)
  := match xs with
     | [] => Ret (x, rest)
     | x' :: xs =>
       Sanity.choice2
         (Ret (x, (x' :: xs) ++ rest)) (* [x] *)
         (choose' x' xs (x :: rest)) (* not [x] *)
     end.
Definition choose {E} {X} x xs : ctree E (X * list X) :=
  choose' x xs [].

Section parallel.
  Context {config : Type}.

  Definition E c := yieldE c +' spawnE c (yieldE c).

  Definition thread := config -> ctree
                                  (E config)
                                  (config * unit).

  Definition par_match par (curr : thread) (rest : list thread)
    : thread :=
    fun (s : config) =>
      match (observe (curr s)) with
      | RetF (s', _) => match rest with
                       | [] => Ret (s', tt)
                       | h :: t => Tau (par h t s')
                       end
      | ChoiceF b n k => Choice b n (fun c => (par (fun _ => k c) rest s))
      | VisF (inl1 e) k =>
        match e in yieldE _ C return (C -> ctree (E config) (config * unit)) -> _ with
        | Yield _ s' =>
          fun k =>
            '(curr', rest') <- choose k rest;;
            Vis (inl1 (Yield _ s')) (fun s' => (par curr' rest' s'))
        end k
      | VisF (inr1 e) k =>
        match e in spawnE _ _ R return (R -> ctree (E config) (config * unit)) -> _ with
        | Spawn _ _ t =>
          fun k =>
            Tau (par (fun _ => k tt) (t :: rest) s) (* this s doesn't matter, since the running thread won't use it *)
        end k
      end.
  CoFixpoint par := par_match par.
  Lemma rewrite_par curr rest s : par curr rest s ≅ par_match par curr rest s.
  Proof.
    step. eauto.
  Qed.

  (* no longer true with the new spawn events *)
  Lemma par_empty :
    forall t c, par t [] c ≅ t c.
  Proof.
    coinduction r CIH. intros. cbn.
    destruct (observe (t c)) eqn:?.
    - rewrite rewrite_par. unfold par_match. rewrite Heqc0.
      destruct r0, u. constructor; auto.
    - rewrite rewrite_par. unfold par_match. rewrite Heqc0. destruct e.
      + destruct y. unfold choose, choose'. cbn. constructor; apply CIH.
      + destruct s.
  (*   - eapply equ_equF. apply rewrite_par. eauto. *)
  (*     unfold par_match. rewrite Heqc0. *)
  (*     cbn. constructor; intros; eapply CIH. *)
        (* Qed. *)
  Abort.

  Fixpoint list_relation {T} (P : relation T) (l1 l2 : list T) : Prop :=
    match l1, l2 with
    | [], [] => True
    | h1 :: t1, h2 :: t2 => P h1 h2 /\ list_relation P t1 t2
    | _, _ => False
    end.

  Lemma list_relation_app {T} (P : relation T) l1 l2 r1 r2 :
    list_relation P l1 l2 ->
    list_relation P r1 r2 ->
    list_relation P (l1 ++ r1) (l2 ++ r2).
  Proof.
    revert l2.
    induction l1; destruct l2; intros Hl Hr; inv Hl; try split; auto.
  Qed.

  Lemma equ_par_helper k1 k2 l1 l2 s r
        (CIH : forall (x y : config -> ctree (E config) (config * ()))
                 (x0 y0 : list (config -> ctree (E config) (config * ())))
                 (y1 : config),
            pointwise_relation config (equ eq) x y ->
            list_relation (pointwise_relation config (equ eq)) x0 y0 ->
            t_equ eq r (par x x0 y1) (par y y0 y1)) :
    forall r1 r2,
    pointwise_relation config (equ eq) k1 k2 ->
    list_relation (pointwise_relation _ (equ eq)) l1 l2 ->
    list_relation (pointwise_relation _ (equ eq)) r1 r2 ->
    equF eq (t_equ eq r)
         (observe ('(curr', rest') <- choose' k1 l1 r1;;
                   Vis (inl1 (Yield _ s)) (fun s' => (par curr' rest' s'))))
         (observe ('(curr', rest') <- choose' k2 l2 r2;;
                   Vis (inl1 (Yield _ s)) (fun s' => (par curr' rest' s')))).
  Proof.
    revert l2 k1 k2.
    induction l1; destruct l2; intros k1 k2 r1 r2 Hk Hl Hr; inv Hl.
    - cbn. constructor. intros; auto.
    - cbn. constructor. intros [].
      + step. cbn. constructor. intros. apply CIH; auto. constructor; auto.
        apply list_relation_app; auto.
      + step. eapply IHl1; eauto. constructor; auto.
  Qed.

  #[global] Instance equ_par :
    Proper ((pointwise_relation _ (equ eq)) ==> (list_relation (pointwise_relation _ (equ eq))) ==> eq ==> equ eq)
           par.
  Proof.
    repeat intro. subst. revert H H0. revert x y x0 y0 y1. coinduction r CIH. intros t1 t2 l1 l2 c Ht Hl.
    do 2 rewrite rewrite_par. unfold par_match. simpl.
    specialize (Ht c). step in Ht. inv Ht; eauto. 2: destruct e.
    - destruct y. destruct l1, l2; inv Hl; auto.
      constructor; eauto.
    - clear H H0. destruct y.
      unfold choose.
      apply equ_par_helper; auto.
    - destruct s. constructor. intros. apply CIH.
      + intro. apply REL.
      + constructor; auto.
    - cbn. constructor. intros. apply CIH; auto.
      intro. apply REL.
  Qed.

  (* Lemma observe_par t s r : *)
  (*   t s ≅ Ret r -> *)
  (*   observe (par t [] s) = RetF r. *)
  (* Proof. *)
  (*   intros. destruct r, u. step in H. inv H. *)
  (*   intros. rewrite rewrite_par'. unfold par_match. rewrite H. destruct r, u; auto. *)
  (* Qed. *)

  (* Lemma par_empty : *)
  (*   forall t s, par (fun s' : config => par t [] s') [] s ≅ par t [] s. *)
  (* Proof. *)
  (*   coinduction r CIH. intros t s. *)
  (*   pose proof rewrite_par. specialize (H t [] s). step in H. unfold par_match in H. *)
  (*   do 2 rewrite rewrite_par. unfold par_match. *)
  (*   destruct (observe (t s)) eqn:?. 2: destruct e. *)
  (*   - destruct r0, u. inv H; auto. *)
  (*   - destruct y. cbn in H. inv H. apply inj_pair2 in H3, H4. subst. *)
  (*     unfold choose, choose'. cbn. constructor; auto. intros. admit. *)
  (*   - destruct s0. inv H. apply inj_pair2 in H3. subst. *)
  (* Qed. *)

  Lemma schedule_par_assoc :
    forall t1 t2 t3 c t, schedule (par t1 [par t2 [t3]] c) t ->
                  schedule (par (par t1 [t2]) [t3] c) t.
  Proof.
    intros.
    rewrite rewrite_par in H |- *.
    unfold schedule in *. unfold par_match.
    pose proof (rewrite_par t1 [t2] c). step in H0. inv H0.
    - destruct y, u. unfold par_match in *. destruct (observe (t1 c)); inv H3.
      + destruct r. inv H1.
      + destruct e; [destruct y | destruct s]; inv H1.
    - unfold par_match in *. destruct (observe (t1 c)) eqn:?; inv H3.
      + destruct r. inv H1.
      + destruct e; [destruct y | destruct s]; (destruct e0; [destruct y | destruct s]; inv H1).
    - cbn in *. unfold par_match in *. destruct (observe (t1 c)) eqn:?; inv H3.
      + destruct r.
        cbn in H1. inv H2.
      (* + destruct e; [destruct y | destruct s]; (destruct e0; [destruct y | destruct s]; inv H1). *)
  Abort.

  Lemma par_assoc :
    forall t1 t2 t3 c, par t1 [par t2 [t3]] c ≈ par (par t1 [t2]) [t3] c.
  Proof.
    red. coinduction r CIH.
    intros. cbn.
(*
    unfold bisim. coinduction r CIH. constructor.
    - intros. rewrite rewrite_par' in H |- *. unfold par_match in *.
      destruct (observe (t1 c)) eqn:?.
      + destruct r0, u. inv H. apply inj_pair2 in H2. subst.
        rewrite rewrite_par'. unfold par_match. rewrite Heqc0. cbn.
        exists u'. split. 2: admit.
        constructor; auto. eapply CIH.
  Qed.

  Lemma par_assoc :
    forall t1 t2 t3 c, par t1 [par t2 [t3]] c ≅ par (par t1 [t2]) [t3] c.
  Proof.
    coinduction r CIH. intros.
    (* intros. cbn. *)
    do 2 rewrite rewrite_par. unfold par_match.
    (* eapply equ_equF. apply rewrite_par. eauto. *)
    (* eapply equ_equF'. 2: { apply rewrite_par. } eauto. *)
    (* unfold par_match. *)
    destruct (observe (t1 c)) eqn:?.
    - destruct r0 as [? []]. cbn.
      pose proof rewrite_par as Hr. specialize (Hr t1 [t2] c).
      step in Hr. unfold par_match in Hr. rewrite Heqc0 in Hr. inv Hr.
      apply inj_pair2 in H2. subst.
      constructor. intros. rewrite REL. apply CIH.

      step. do 2 rewrite rewrite_par'. unfold par_match.
      do 2 rewrite rewrite_par'. unfold par_match.

      destruct (observe (t2 c0)) eqn:?; cbn.
      + destruct r0. cbn.
        constructor. intros. step. destruct u.
        do 2 rewrite rewrite_par'. unfold par_match.
        destruct (observe (t3 c1)) eqn:?.
        * destruct r0. cbn. constructor; auto.
        * admit.
        * destruct e.
          -- destruct y. unfold choose, choose'. cbn. constructor.
             intros. step. simpl.
        constructor.
      cbn.
      (* eapply equ_equF. apply par_empty. eauto. *)
      eapply equ_equF'. 2: { apply par_empty. eauto.
*)
  Admitted.

End parallel.
