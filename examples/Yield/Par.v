From Coq Require Import
     Program
     List
     Logic.FunctionalExtensionality.

From CTree Require Import
	Utils
	CTrees
 	Interp
	Equ
	Bisim.

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
      | ChoiceF n k => Choice n (fun c => (par (fun _ => k c) rest s))
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
    coinduction r CIH.
    unfold par. cbn. reflexivity.
  Qed.

  Lemma par_empty :
    forall t c, par t [] c ≅ t c.
  Proof.
    coinduction r CIH. intros. cbn.
    destruct (observe (t c)) eqn:?.
    (* TODO: get proper instance to work *)
    - eapply equ_equF. apply rewrite_par. eauto.
      unfold par_match. rewrite Heqc0. destruct r0, u. constructor; auto.
    - eapply equ_equF. apply rewrite_par. eauto.
      unfold par_match. rewrite Heqc0. destruct e. destruct y.

      unfold choose, choose'. cbn. constructor; apply CIH.
    - eapply equ_equF. apply rewrite_par. eauto.
      unfold par_match. rewrite Heqc0.
      cbn. constructor; intros; eapply CIH.
  Qed.

  (* TODO: I think we need something like [observing] from itrees to make this work properly *)
  #[global] Instance equ_equF' {E R r} :
    Proper (eq ==> gfp (@fequ E R R eq) ==> flip impl)
	       (fun x y => equF eq (t_equ eq r) x (observe y)).
  Proof.
    unfold Proper, respectful, flip, impl. intros x y ?. subst. intros.
    step in H. inv H; rewrite <- H3 in H0; inv H0; auto.
    - apply inj_pair2 in H5, H6.
      subst. constructor. intros. rewrite REL. auto.
    - apply inj_pair2 in H5.
      subst. constructor. intros. rewrite REL. auto.
  Qed.

  Lemma rewrite_par' curr rest s : par curr rest s = par_match par curr rest s.
  Admitted.

  Lemma par_assoc :
    forall t1 t2 t3 c, par t1 [par t2 [t3]] c ≅ par (par t1 [t2]) [t3] c.
  Proof.
    coinduction r CIH.
    intros. cbn.
    do 2 rewrite rewrite_par'. unfold par_match.
    rewrite rewrite_par'. unfold par_match.

    (* eapply equ_equF. apply rewrite_par. eauto. *)
    (* eapply equ_equF'. 2: { apply rewrite_par. } eauto. *)
    (* unfold par_match. *)
    destruct (observe (t1 c)) eqn:?.
    - destruct r0 as [? []]. simpl.
      constructor. intros.

      step. do 2 rewrite rewrite_par'. unfold par_match.
      (* eapply equ_equF. apply par_empty. eauto. *)
      eapply equ_equF'. 2: { apply par_empty. eauto.

  Qed.
End parallel.
