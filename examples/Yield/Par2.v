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

Import ListNotations.
Import CTreeNotations.

Variant choiceI_boundF {E R} b (choiceI_bound : ctree E R -> Prop) :
  ctree' E R -> Prop :=
  | bound_Ret r : choiceI_boundF b choiceI_bound (RetF r)
  | bound_Vis {X} (e : E X) k : (forall x, choiceI_bound (k x)) ->
                                choiceI_boundF b choiceI_bound (VisF e k)
  | bound_choiceF {n} k : (forall i, choiceI_bound (k i)) ->
                          choiceI_boundF b choiceI_bound (ChoiceF true n k)
  | bound_choiceI {n} k : (forall i, choiceI_bound (k i)) ->
                          (n <= b)%nat ->
                          choiceI_boundF b choiceI_bound (ChoiceF false n k)
.
#[global] Hint Constructors choiceI_boundF: core.

Definition choiceI_bound_ {E R} b choiceI_bound : ctree E R -> Prop :=
  fun t => choiceI_boundF b choiceI_bound (observe t).

Obligation Tactic := idtac.
Program Definition fchoiceI_bound {E R} (b : nat) : mon (ctree E R -> Prop) :=
  {| body := choiceI_bound_ b |}.
Next Obligation.
  intros E R b ?? INC t H. inversion H; unfold choiceI_bound_ in *.
  - rewrite <- H1 in *. constructor.
  - rewrite <- H0 in *. constructor. intros. apply INC; auto.
  - rewrite <- H0 in *. constructor. intros. apply INC; auto.
  - rewrite <- H0 in *. constructor; auto. intros. apply INC; auto.
Qed.

Definition choiceI_bound {E R} b := (gfp (@fchoiceI_bound E R b)).
#[global] Hint Unfold choiceI_bound: core.

Notation ct Q := (t (fchoiceI_bound Q)).
Notation cT Q := (T (fchoiceI_bound Q)).
Notation cbt Q := (bt (fchoiceI_bound Q)).
Notation cbT Q := (bT (fchoiceI_bound Q)).

#[global] Instance equ_choiceI_bound {E R} b :
  Proper (equ eq ==> impl) (@choiceI_bound E R b).
Proof.
  unfold Proper, respectful, impl. intros ? ?. subst. revert b.
  red. intros. revert x y H H0. coinduction r CIH. intros x y Hequ H.
  step in Hequ. step in H. cbn*.
  cbn in H. red in H |- *. inversion Hequ; auto. 2: destruct b0.
  - rewrite <- H1 in H. inv H. invert.
    constructor. intros. eapply CIH. apply REL. apply H3.
  - rewrite <- H1 in H. inv H. invert.
    constructor. intros. eapply CIH. apply REL. apply H3.
  - rewrite <- H1 in H. inv H. invert.
    constructor; auto. intros. eapply CIH. apply REL. apply H4.
Qed.

#[global] Instance equ_choiceI_bound' {E R} b :
  Proper (equ eq ==> flip impl) (@choiceI_bound E R b).
Proof.
  unfold Proper, respectful, flip, impl. intros ? ?. subst. revert b.
  red. intros. revert x y H H0. coinduction r CIH. intros x y Hequ H.
  step in Hequ. step in H. cbn*.
  cbn in H. red in H |- *. inversion Hequ; auto. 2: destruct b0.
  - rewrite <- H2 in H. inv H. invert.
    constructor. intros. eapply CIH. apply REL. apply H3.
  - rewrite <- H2 in H. inv H. invert.
    constructor. intros. eapply CIH. apply REL. apply H3.
  - rewrite <- H2 in H. inv H. invert.
    constructor; auto. intros. eapply CIH. apply REL. apply H4.
Qed.

Lemma choiceI_step {E R} n k x :
  choiceI_bound 1 (ChoiceI n k : ctree E R) ->
  n = 1%nat /\ choiceI_bound 1 (k x).
Proof.
  intros Hbound.
  step in Hbound.
  inversion Hbound.
  destruct n.
  - inversion x.
  - split. lia. invert. apply H1.
Qed.

Lemma trans_choiceI_bound E R (t t' : ctree E R) l :
  choiceI_bound 1 t ->
  trans l t t' ->
  choiceI_bound 1 t'.
Proof.
  intros Hbound Htrans. revert Hbound.
  unfold trans in *.
  cbn in *. red in Htrans. dependent induction Htrans; intros.
  - eapply IHHtrans; auto.
    assert (t ≅ ChoiceI n k). { rewrite ctree_eta. rewrite <- x. reflexivity. }
    rewrite H in Hbound. step in Hbound. inv Hbound. invert. auto.
  - assert (t' ≅ k x0).
    { rewrite ctree_eta. rewrite <- x. rewrite H. rewrite <- ctree_eta. reflexivity. }
    assert (t ≅ ChoiceV n k).
    { rewrite ctree_eta. rewrite <- x1. reflexivity. }
    rewrite H1 in Hbound. rewrite H0. step in Hbound. inv Hbound. invert. auto.
  - assert (t' ≅ k x0).
    { rewrite ctree_eta. rewrite <- x. rewrite H. rewrite <- ctree_eta. reflexivity. }
    assert (t ≅ Vis e k).
    { rewrite ctree_eta. rewrite <- x1. reflexivity. }
    rewrite H1 in Hbound. rewrite H0. step in Hbound. inv Hbound. invert. auto.
  - rewrite ctree_eta. rewrite <- x. step. constructor; auto. intros. inv i.
Qed.

Lemma visible_choiceI_bound E R n (t t' : ctree E R) :
  choiceI_bound n t ->
  visible t t' ->
  choiceI_bound n t'.
Proof.
  intros Hbound Hvisible. revert n Hbound.
  cbn in *. red in Hvisible. dependent induction Hvisible; intros.
  - eapply IHHvisible; auto.
    assert (t ≅ ChoiceI n k). { rewrite ctree_eta. rewrite <- x. reflexivity. }
    rewrite H in Hbound.
    step in Hbound. inv Hbound. invert. auto.
  - assert (t ≅ ChoiceV n k1). { rewrite ctree_eta. rewrite <- x1. reflexivity. }
    assert (t' ≅ ChoiceV n k2). { rewrite ctree_eta. rewrite <- x. reflexivity. }
    rewrite H0 in Hbound. rewrite H1. clear H0 H1 x x1.
    step in Hbound. inv Hbound. invert.
    (* TODO: fix step in the coinduction library to work on unary relations *)
    red. apply (proj2 (gfp_fp (fchoiceI_bound n0) (ChoiceV n k2))). cbn.
    constructor. intros. specialize (H1 i). fold (@choiceI_bound E R n0) in *.
    rewrite H in H1. auto.
  - assert (t ≅ Vis e k1). { rewrite ctree_eta. rewrite <- x0. reflexivity. }
    assert (t' ≅ Vis e k2). { rewrite ctree_eta. rewrite <- x. reflexivity. }
    rewrite H0 in Hbound. rewrite H1. clear H0 H1 x x0.
    step in Hbound. inv Hbound. invert.
    red. apply (proj2 (gfp_fp (fchoiceI_bound n) (Vis e k2))). cbn.
    constructor. intros. specialize (H1 x). fold (@choiceI_bound E R n) in *.
    rewrite H in H1. auto.
  - assert (t ≅ Ret r). { rewrite ctree_eta. rewrite <- x0. reflexivity. }
    assert (t' ≅ Ret r). { rewrite ctree_eta. rewrite <- x. reflexivity. }
    rewrite H in Hbound. rewrite H0. auto.
Qed.

(* TODO: move to ctree library *)
Variant equ_clos1_body {E X} (R : ctree E X -> Prop) : (ctree E X -> Prop) :=
  | Equ_clos1 : forall t t'
                 (Equt : t ≅ t')
                 (HR : R t'),
      equ_clos1_body R t.

Program Definition equ_clos1 {E X} : mon (ctree E X -> Prop) :=
  {| body := @equ_clos1_body E X |}.
Next Obligation.
  intros * ?? LE t EQ; inv EQ.
  econstructor; eauto.
  apply LE; auto.
Qed.

Lemma equ_clos1_ct {E R} n : @equ_clos1 E R <= ct n.
Proof.
  apply Coinduction.
  intros r t EQ; inv EQ.
  cbn. red. step in Equt. inv Equt; auto.
  2: destruct b.
  all: cbn in HR; red in HR; rewrite <- H in HR; inv HR; invert;
    constructor; intros; auto; apply (f_Tf (fchoiceI_bound n)); econstructor; eauto.
Qed.

#[global] Instance equ_ct {E R} {r : ctree E R -> Prop} n :
  Proper ((equ eq) ==> flip impl) (ct n r).
Proof.
  unfold Proper, respectful, flip, impl. intros.
  apply (ft_t (equ_clos1_ct n)); econstructor; eauto.
Qed.

#[global] Instance equ_choiceI_boundF {E R r} n :
  Proper (going (equ eq) ==> flip impl) (@choiceI_boundF E R n (ct n r)).
Proof.
  unfold Proper, respectful, flip, impl. intros.
  inv H. step in H1. inv H0; inv H1; auto; invert; constructor; intros; auto.
  rewrite REL; auto.
  rewrite REL; auto.
  rewrite REL; auto.
Qed.

#[global] Instance equ_choiceI_bound_ {E R r} n :
  Proper (equ eq ==> flip impl) (@choiceI_bound_ E R n (ct n r)).
Proof.
  cbn. red. intros. rewrite H. auto.
Qed.

Definition bind_ctx1 {E X Y}
           (R: ctree E X -> Prop)
           (S: (X -> ctree E Y) -> Prop) :
  ctree E Y -> Prop :=
  (sup R
       (fun x => sup S
                  (fun k => (fun t => t = CTree.bind x k)))).

Lemma leq_bind_ctx1 {E X Y} :
  forall R S S', @bind_ctx1 E X Y R S <= S' <->
              (forall x, R x -> forall k, S k -> S' (CTree.bind x k)).
Proof.
  intros. unfold bind_ctx1.
  setoid_rewrite sup_spec.
  setoid_rewrite sup_spec.
  firstorder congruence.
Qed.

Lemma in_bind_ctx1 {E X Y} (R : ctree E X -> Prop) (S : (X -> ctree E Y) -> Prop) x f :
  R x -> S f -> @bind_ctx1 E X Y R S (CTree.bind x f).
Proof. intros. epose proof (proj1 (leq_bind_ctx1 R S _)). apply H1; auto. Qed.
#[global] Opaque bind_ctx1.

Program Definition bind_ctx1_equ {E X Y} n : mon (ctree E Y -> Prop) :=
  {| body := fun R => @bind_ctx1 E X Y (choiceI_bound n) (fun f => forall x, R (f x)) |}.
Next Obligation.
  intros E X Y n R R' Hleq x.
  apply leq_bind_ctx1. intros x' H' k H''.
  apply in_bind_ctx1; auto. intros. apply Hleq; auto.
Qed.

Lemma bind_ctx1_ct {E X Y} n : @bind_ctx1_equ E X Y n <= ct n.
Proof.
  apply Coinduction. intros r. apply (leq_bind_ctx1 _).
  intros x Hx k Hk.
  cbn. red. unfold observe. cbn.
  step in Hx.
  inversion Hx.
  - cbn in *.
    generalize (Hk r0).
    apply (fchoiceI_bound n).
    apply id_T.
  - constructor; intros ?. apply (fTf_Tf (fchoiceI_bound n)).
    apply in_bind_ctx1; auto.
    intros. apply (b_T (fchoiceI_bound n)). apply Hk.
  - constructor; intros ?. apply (fTf_Tf (fchoiceI_bound n)).
    apply in_bind_ctx1; auto.
    intros. apply (b_T (fchoiceI_bound n)). apply Hk.
  - constructor; auto; intros ?. apply (fTf_Tf (fchoiceI_bound n)).
    apply in_bind_ctx1; auto.
    intros. apply (b_T (fchoiceI_bound n)). apply Hk.
Qed.

Lemma ct_clo_bind {E R1 R2} n r (t : ctree E R1) (k : R1 -> ctree E R2) :
  choiceI_bound n t ->
  (forall x, ct n r (k x)) ->
  ct n r (CTree.bind t k).
Proof.
  intros.
  apply (ft_t (@bind_ctx1_ct E R1 R2 n)).
  eapply in_bind_ctx1; auto.
Qed.

Lemma bind_choiceI_bound {E R1 R2} n (t : ctree E R1) (k : R1 -> ctree E R2) :
  choiceI_bound n t ->
  (forall x, choiceI_bound n (k x)) ->
  choiceI_bound n (CTree.bind t k).

Proof.
  red. intros. revert t k H H0. coinduction r CIH. intros.
  cbn*. step in H. cbn in H. red in H |- *.
  rewrite unfold_bind.
  desobs t. 3: destruct vis.
  2, 3, 4: inv H; invert; constructor; auto.
  specialize (H0 r0). step in H0. red in H0.
  inv H0; constructor; auto; intros; apply (gfp_t (fchoiceI_bound n)); auto.
Qed.

Lemma iter_choiceI_bound {E R I} n (k : I -> ctree E (I + R)) (Hn : n > 0):
  (forall i, choiceI_bound n (k i)) ->
  forall i, choiceI_bound n (iter k i).
Proof.
  unfold choiceI_bound. coinduction r CIH. intros.
  cbn*. unfold iter, MonadIter_ctree. rewrite unfold_iter.
  rewrite unfold_bind.
  destruct (observe (k i)) eqn:?. 3: destruct vis.
  2, 3, 4: pose proof (H i) as H'; step in H'; cbn in H'; red in H';
  rewrite Heqc in H'; inversion H'; invert;
  constructor; auto; intros;
  eapply ct_clo_bind; auto; intros y; destruct y; step; econstructor; eauto.
  destruct r0; constructor; auto; intros; apply CIH; auto.
Qed.

(* TODO move this *)
Lemma sbisim_vis_visible {E R X} (t2 : ctree E R) (e : E X) k1 (Hin: inhabited X) (Hbound : choiceI_bound 1 t2) :
  Vis e k1 ~ t2 ->
  exists k2, visible t2 (Vis e k2) /\ (forall x, k1 x ~ k2 x).
Proof.
  unfold trans in *; intros.
  step in H. destruct H as [Hf Hb].
  cbn in *. unfold transR in Hf.
  assert
    (forall (l : label) (t' : ctree E R),
        trans_ l (VisF e k1) (observe t') ->
        {u' : ctree E R | trans_ l (observe t2) (observe u') /\ t' ~ u'}).
  {
    unfold trans in *.
    intros. apply constructive_indefinite_description.
    edestruct Hf; eauto.
  } clear Hf. rename X0 into Hf.
  destruct Hin as [x].
  edestruct (Hf (obs e x)). constructor. reflexivity.
  destruct a. clear H0 Hb.
  dependent induction H.
  - edestruct @choiceI_step as (? & Hbound').
    {
      assert (t2 ≅ ChoiceI n k).
      rewrite ctree_eta. rewrite <- x. reflexivity.
      rewrite H0 in Hbound. apply Hbound.
    }
    subst.
    edestruct IHtrans_; try reflexivity; eauto.
    intros. rewrite <- x in Hf. edestruct Hf. eauto.
    destruct a.
    exists x3. split. inv H1. apply inj_pair2 in H6. subst.
    assert (x1 = x4).
    {
      remember 1%nat.
      destruct x1.
      - dependent destruction x4; auto.
        inversion Heqn. subst. inv x4.
      - inv Heqn. inv x1.
    }
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
Qed.

Lemma sbisim_visible {E R X} (t1 t2 : ctree E R) (e : E X) k1 (Hin: inhabited X) (Hbound1 : choiceI_bound 1 t1) (Hbound2 : choiceI_bound 1 t2):
  t1 ~ t2 ->
  visible t1 (Vis e k1) ->
  exists k2, visible t2 (Vis e k2) /\ (forall x, k1 x ~ k2 x).
Proof.
  unfold trans; intros. cbn in *. red in H0. remember (observe t1). remember (observe (Vis e k1)).
  revert X t1 e k1 t2 H Heqc Heqc0 Hin Hbound1 Hbound2.
  induction H0; intros; auto.
  - edestruct @choiceI_step as (? & Hbound1').
    {
      assert (t1 ≅ ChoiceI n k).
      rewrite ctree_eta. rewrite <- Heqc. reflexivity.
      rewrite H1 in Hbound1. apply Hbound1.
    }
    subst. eapply IHvisible_. 2: reflexivity. all: eauto.
    pose proof (ctree_eta t1). rewrite <- Heqc in H1. rewrite H1 in H.
    epose proof (sbisim_ChoiceI_1_inv _ H); auto. apply H2.
  - inv Heqc0.
  - inv Heqc0. apply inj_pair2 in H3, H4. subst.
    apply sbisim_vis_visible; auto.
    pose proof (ctree_eta t1).  rewrite <- Heqc in H1.
    (* TODO: clean this up *) eapply equ_VisF in H. rewrite H in H1.
    rewrite H1 in H0. auto.
  - inv Heqc0.
Qed.


Variant yieldE : Type -> Type :=
| Yield : yieldE unit.

Variant spawnE : Type -> Type :=
| Spawn : spawnE bool.

Section parallel.
  Context {config : Type}.

  Definition parE s := yieldE +' spawnE +' stateE s.

  Definition thread := ctree (parE config) unit.

  Definition completed := ctree (stateE config) unit.

  Definition vec n := fin n -> thread.

  Definition vec_relation {n : nat} (P : rel _ _) (v1 v2 : vec n) : Prop :=
    forall i, P (v1 i) (v2 i).

  Instance vec_relation_symmetric n (P : rel _ _) `{@Symmetric _ P} :
    Symmetric (@vec_relation n P).
  Proof. repeat intro. auto. Qed.

  Definition remove_front_vec {n : nat} (v : vec (S n)) : vec n :=
    fun i => v (FS i).

  Lemma remove_front_vec_vec_relation n P (v1 v2 : vec (S n)) :
    vec_relation P v1 v2 ->
    vec_relation P (remove_front_vec v1) (remove_front_vec v2).
  Proof.
    repeat intro. apply H.
  Qed.

  Lemma remove_front_vec_choiceI_bound n n' (v : vec (S n)) :
    (forall i, choiceI_bound n' (v i)) ->
    forall i, choiceI_bound n' (remove_front_vec v i).
  Proof.
    repeat intro. apply H.
  Qed.

  Equations remove_vec {n : nat} (v : vec (S n)) (i : fin (S n)) : vec n :=
    remove_vec v F1     i'      := remove_front_vec v i';
    remove_vec v (FS i) F1      := v F1;
    remove_vec v (FS i) (FS i') := remove_vec (remove_front_vec v) i i'.
  Transparent remove_vec.

  Lemma remove_vec_vec_relation n P (v1 v2 : vec (S n)) i :
    vec_relation P v1 v2 ->
    vec_relation P (remove_vec v1 i) (remove_vec v2 i).
  Proof.
    intros.
    depind i; [apply remove_front_vec_vec_relation; auto |].
    repeat intro. destruct i0; cbn; auto.
    apply IHi; auto.
    repeat intro. apply remove_front_vec_vec_relation; auto.
  Qed.

  Lemma remove_vec_choiceI_bound n n' (v : vec (S n)) i' :
    (forall i, choiceI_bound n' (v i)) ->
    forall i, choiceI_bound n' (remove_vec v i' i).
  Proof.
    intros. depind i'.
    - apply remove_front_vec_choiceI_bound; auto.
    - destruct i; cbn; auto.
      apply IHi'; auto. intros. apply remove_front_vec_choiceI_bound; auto.
  Qed.

  Lemma remove_vec_remove_vec_front n (v : vec (S (S n))) i i' :
    remove_vec (remove_front_vec v) i i' = remove_front_vec (remove_vec v (FS i)) i'.
  Proof.
    depind i; cbn; auto.
  Qed.

  (* Lemma of_nat_lt_S n j (Hj : j < S n) (Hj' : j < n) : *)
  (*   of_nat_lt Hj = FS (of_nat_lt Hj'). *)
  (* Proof. *)
  (*   revert n Hj Hj'. *)
  (*   induction j; intros; auto. *)
  (*   - cbn. destruct n; auto. inv Hj'. *)
  (* Qed. *)

  (* before the element removed, the same index works *)
  Lemma remove_vec_index_before {n} (v : vec (S n)) i j
        (Hi : i < S n) (Hji : j < i) (Hj : j < S n) (Hj' : j < n) :
    v (of_nat_lt Hj) = (remove_vec v (of_nat_lt Hi)) (of_nat_lt Hj').
  Proof.
    revert n v j Hi Hj Hj' Hji. induction i; intros; auto. inv Hji.
    destruct n. inv Hj'. destruct j; auto. cbn.
    erewrite <- IHi; auto. lia.
  Qed.

  (* after the element removed, we need to subtract one from the index *)
  Lemma remove_vec_index_after {n} (v : vec (S n)) i j
        (Hi : i < S n) (Hji : j > i) (Hj : S j < S n) (Hj' : j < n) (* S j to j *) :
    v (of_nat_lt Hj) = (remove_vec v (of_nat_lt Hi)) (of_nat_lt Hj').
  Proof.
    revert n v i Hi Hji Hj Hj'. induction j; intros. inv Hji.
    destruct i.
    - destruct n. inv Hj'. cbn. unfold remove_front_vec. erewrite of_nat_ext. reflexivity.
    - destruct n. inv Hj'. cbn. erewrite <- IHj; eauto. lia.
  Qed.

  (* at the element removed, we also subtract one. TODO: can we unify this with prev lemma? *)
  Lemma remove_vec_index_eq {n} (v : vec (S n)) i j
        (Hi : i < S n) (Hji : j = i) (Hj : S j < S n) (Hj' : j < n) :
    v (of_nat_lt Hj) = (remove_vec v (of_nat_lt Hi)) (of_nat_lt Hj').
  Proof.
    revert n v j Hi Hj Hj' Hji. induction i; intros; auto.
    - destruct n. inv Hj'. subst. reflexivity.
    - destruct n. inv Hj'. subst. cbn.
      erewrite <- IHi; auto.
  Qed.

  (* Definition remove_vec_index {n} (v : vec (S n)) (i i' : fin (S n)) (H : i <> i') : *)
  (*   { j : fin n | v i' = (remove_vec v i) j }. *)
  (*   revert v. depind i; cbn; intros. *)
  (*   - dependent destruction i'. contradiction. *)
  (*     exists i'. reflexivity. *)
  (*   - destruct n; [inv i |]. *)
  (*     dependent destruction i'; auto. *)
  (*     + exists F1. reflexivity. *)
  (*     + assert (i <> i'). { intro. subst. contradiction. } *)
  (*       edestruct IHi as (j & Hj); eauto. exists (FS j). rewrite <- Hj. reflexivity. *)
  (* Defined. *)

  (* Lemma remove_vec_index_foo {n} (v : vec (S n)) i j1 j2 Hj1 Hj2 : *)
  (*   (* TODO: figure out why this doesn't work with ` notation *) *)

  (*   (proj1_sig (remove_vec_index v i (FS j1) Hj1)) <> *)
  (*     (proj1_sig (remove_vec_index v i (FS j2) Hj2)) -> *)
  (*   (proj1_sig (remove_vec_index v i j1 Hj1)) <> *)
  (*     (proj1_sig (remove_vec_index v i j2 Hj2)). *)

  (* Lemma remove_vec_index_injective {n} (v : vec (S n)) i j1 j2 Hj1 Hj2 : *)
  (*   (* TODO: figure out why this doesn't work with ` notation *) *)
  (*   j1 <> j2 -> *)
  (*   (proj1_sig (remove_vec_index v i j1 Hj1)) <> (proj1_sig (remove_vec_index v i j2 Hj2)). *)
  (* Proof. *)
  (*   revert v. depind i. *)
  (*   - intro. intro. revert j2 Hj2 H v. depind j1; [contradiction |]; intros. *)
  (*     dependent destruction j2; [contradiction |]. destruct n. inv j1. *)
  (*     apply IHj1. *)
  (* Qed. *)

  (* Lemma remove_vec_index {n} (v : vec (S n)) i : *)
  (*   forall i', i <> i' -> exists j, v i' = remove_vec v i j. *)
  (* Proof. *)
  (*   revert v. depind i; cbn; intros. *)
  (*   - dependent destruction i'. contradiction. *)
  (*     exists i'. reflexivity. *)
  (*   - destruct n; [inv i |]. *)
  (*     dependent destruction i'; auto. *)
  (*     + exists F1. reflexivity. *)
  (*     + assert (i <> i'). { intro. subst. contradiction. } *)
  (*       edestruct IHi as (j & Hj); eauto. exists (FS j). rewrite <- Hj. reflexivity. *)
  (* Qed. *)

  Definition remove_vec_helper n n' (v : vec n) (i : fin n) (H : n = S n')
    : vec n'.
    subst. apply remove_vec; eauto.
  Defined.

  Definition replace_vec {n : nat} (v : vec n) (i : fin n) (t : thread) : vec n :=
    fun i' => if Fin.eqb i i' then t else v i'.

  Lemma remove_front_vec_replace_vec n (v : vec (S n)) i t :
    remove_front_vec (replace_vec v (FS i) t) =
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
    P t1 t2 ->
    vec_relation P (replace_vec v1 i t1) (replace_vec v2 i t2).
  Proof.
    unfold replace_vec. repeat intro. destruct (Fin.eqb i i0); auto.
  Qed.

  Lemma replace_vec_choiceI_bound n n' (v : vec n) i' t :
    (forall i, choiceI_bound n' (v i)) ->
    choiceI_bound n' t ->
    forall i, choiceI_bound n' (replace_vec v i' t i).
  Proof.
    unfold replace_vec. repeat intro. destruct (Fin.eqb i' i); auto.
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

  Lemma replace_vec_neq n (v : vec n) i1 i2 t :
    i1 <> i2 ->
    (replace_vec v i1 t) i2 = v i2.
  Proof.
    intros.
    unfold replace_vec.
    destruct (Fin.eqb i1 i2) eqn:?.
    - apply Fin.eqb_eq in Heqb. contradiction.
    - reflexivity.
  Qed.

  (* Lemma replace_vec_same n (v : vec n) i : *)
  (*   replace_vec v i (v i) = v. *)
  (* Proof. *)
  (*   unfold replace_vec. apply functional_extensionality. intro. *)
  (*   destruct (Fin.eqb i x) eqn:?; auto. *)
  (*   apply Fin.eqb_eq in Heqb. subst. auto. *)
  (* Qed. *)

  Equations cons_vec {n : nat} (t : thread) (v : vec n) : vec (S n) :=
    cons_vec t v F1      := t;
    cons_vec t v (FS i)  := v i.
  Transparent cons_vec.

  Lemma cons_vec_vec_relation n P (v1 v2 : vec n) t1 t2 :
    vec_relation P v1 v2 ->
    P t1 t2 ->
    vec_relation P (cons_vec t1 v1) (cons_vec t2 v2).
  Proof.
    unfold cons_vec. repeat intro. depind i; cbn; auto.
  Qed.

  Lemma cons_vec_choiceI_bound n n' (v : vec n) t :
    (forall i, choiceI_bound n' (v i)) ->
    choiceI_bound n' t ->
    forall i, choiceI_bound n' (cons_vec t v i).
  Proof.
    unfold cons_vec. repeat intro. depind i; cbn; auto.
  Qed.

  Lemma remove_vec_cons_1 t1 t2 :
    (remove_vec (cons_vec t1 (fun _ : fin 1 => t2)) F1) = (fun _ => t2).
  Proof.
    apply functional_extensionality. intros i. dependent destruction i; [| inv i].
    simp remove_vec. unfold remove_front_vec. simp cons_vec. reflexivity.
  Qed.

  Lemma remove_vec_cons_2 t1 t2 :
    (remove_vec (cons_vec t1 (fun _ : fin 1 => t2)) (FS F1)) = (fun _ => t1).
  Proof.
    apply functional_extensionality. intros i. dependent destruction i; [| inv i].
    simp remove_vec. simp cons_vec. reflexivity.
  Qed.

  Lemma replace_vec_cons_1 t1 t2 t :
    (replace_vec (cons_vec t1 (fun _ : fin 1 => t2)) F1 t) =
      (cons_vec t (fun _ : fin 1 => t2)).
  Proof.
    apply functional_extensionality. intros i. dependent destruction i; reflexivity.
  Qed.

  Lemma replace_vec_cons_2 t1 t2 t :
    (replace_vec (cons_vec t1 (fun _ : fin 1 => t2)) (FS F1) t) =
      (cons_vec t1 (fun _ : fin 1 => t)).
  Proof.
    apply functional_extensionality. intros i. dependent destruction i; cbn.
    - reflexivity.
    - dependent destruction i; [| inv i]. cbn. simp cons_vec. reflexivity.
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

  Equations schedule_match
             (schedule : forall (n : nat), vec n -> option (fin n) -> thread)
             (n : nat)
             (v: vec n)
    : option (fin n) -> thread :=
    (* If no thread is focused, and there are none left in the pool, we are done *)
    schedule_match schedule 0 v None :=
      Ret tt;

    (* If no thread is focused, but there are some left in the pool, we pick one *)
    schedule_match schedule (S n) v None :=
      ChoiceV (S n) (fun i' => schedule (S n) v (Some i'));

    (* If a thread is focused on, we analyze its head constructor *)
    schedule_match schedule (S n) v (Some i) with observe (v i) =>
      {
        (* If it's a [Ret], we simply remove it from the pool and focus *)
        schedule_match _ _ _ _ (RetF _) :=
          TauI (schedule n (remove_vec v i) None);

        (* If it's a [Choice], we propagate the choice and update the thread *)
        schedule_match _ _ _ _ (ChoiceF b n' k) :=
          Choice b n' (fun i' => schedule (S n) (replace_vec v i (k i')) (Some i));

        (* If it's a [Yield], we remove the focus *)
        schedule_match _ _ _ _ (VisF (inl1 Yield) k) :=
          TauI (schedule (S n) (replace_vec v i (k tt)) None);

        (* If it's a [Spawn], we extend the pool *)
        schedule_match _ _ _ _ (VisF (inr1 (inl1 Spawn)) k) :=
          TauV (schedule
                  (S (S n))
                  (* Note that [cons_vec] puts the new thread on the front of the vector *)
                  (cons_vec (k true) (replace_vec v i (k false)))
                  (* The [i] here means that we don't yield at a spawn *)
                  (Some (FS i))); (* view [i] as a [fin (n + 1)] *)

        (* todo *)
        schedule_match _ _ _ _ (VisF (inr1 (inr1 s)) k) :=
        (Vis (inr1 (inr1 s)) (fun x => (schedule (S n) (replace_vec v i (k x)) (Some i))));

      }.
  (* Transparent schedule_match. *)
  CoFixpoint schedule := schedule_match schedule.

  Lemma rewrite_schedule n v i : schedule n v i ≅ schedule_match schedule n v i.
  Proof.
    step. eauto.
  Qed.

  #[global] Instance equ_schedule n :
    Proper ((vec_relation (equ eq)) ==> pwr (equ eq)) (schedule n).
  Proof.
    cbn. revert n.
    coinduction r CIH. intros n v1 v2 Hv i.
    do 2 rewrite rewrite_schedule.
    destruct i as [i |].
    2: { destruct n; auto. constructor. intros. apply CIH; auto. }
    destruct n as [| n]; auto.
    pose proof (Hv i).
    simp schedule_match.
    step in H. cbn. inv H; eauto. 2: destruct e. 3: destruct s. all: cbn.
    - clear H1 H2. destruct y; cbn in *; auto.
      constructor. intros. apply CIH.
      apply remove_vec_vec_relation; auto.
    - clear H1 H2. destruct y.
      constructor. intros. eapply CIH.
      apply replace_vec_vec_relation; auto.
    - destruct s. constructor. intros. eapply CIH.
      apply cons_vec_vec_relation; auto.
      apply replace_vec_vec_relation; auto.
    - constructor. intros. apply CIH.
      apply replace_vec_vec_relation; auto.
    - constructor. intros. apply CIH.
      apply replace_vec_vec_relation; auto.
  Qed.

  (** Helper lemmas for dealing with [schedule] *)

  Lemma ChoiceI_schedule_inv n1 k n2 (v : vec n2) i :
    ChoiceI n1 k ≅ schedule n2 v (Some i) ->
    (exists k', v i ≅ ChoiceI n1 k' /\
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
      right. right. step in Hequ. pose proof (equb_choice_invT _ _ Hequ) as [? _]. subst.
      pose proof (equb_choice_invE _ _ Hequ).
      exists n2, eq_refl. split; auto. step. rewrite Heqc. reflexivity.
    - destruct e; [destruct y | destruct s; [destruct s |]; step in Hequ; inv Hequ].
      step in Hequ. pose proof (equb_choice_invT _ _ Hequ) as [? _]. subst.
      pose proof (equb_choice_invE _ _ Hequ).
      right. left. eexists. split; auto. step. rewrite Heqc. reflexivity.
    - destruct vis; [step in Hequ; inv Hequ |].
      pose proof (equ_choice_invT _ _ Hequ) as [? _]; subst.
      pose proof (equ_choice_invE _ _ Hequ).
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
    revert t v i x Heql Heqc0 H0.
    induction H; intros t' v i x' Heql Heq Hequ; try inv Heql; subst.
    - rewrite <- ctree_eta in Hequ.
      apply ChoiceI_schedule_inv in Hequ. destruct Hequ as [? | [? | ?]].
      + destruct H0 as (k' & Hvic & Hk).
        eapply IHtrans_; eauto.
        rewrite Hk. auto.
      + destruct H0 as (k' & Hvic & Hn & Hk). subst.
        rewrite Hk in H. rewrite rewrite_schedule in H.
        destruct n; [inv i | inv H].
      + destruct H0 as (n' & Hn2' & Hvic & Hn & Hk).
        rewrite Hk in H. rewrite rewrite_schedule in H.
        destruct n'; auto. inv H.
    - invert. rewrite rewrite_schedule in Hequ.
      destruct n; [inv i |].
      simp schedule_match in Hequ.
      destruct (observe (v i)) eqn:Hv; cbn in Hequ.
      + destruct r; step in Hequ; inv Hequ.
      + destruct e; [destruct y | destruct s; [destruct s |]]; step in Hequ; inv Hequ.
      + step in Hequ; inv Hequ.
  Qed.

  Lemma trans_schedule_thread_val {X} v i (x : X) t :
    trans (val x) (schedule 1 v (Some i)) t ->
    trans (val x) (v i) CTree.stuckI.
  Proof.
    intro. unfold trans in *; cbn in H. red in H.
    remember (observe (schedule 1 v (Some i))).
    pose proof (ctree_eta (go (observe (schedule 1 v (Some i))))).
    rewrite <- Heqc in H0 at 1. cbn in H0. clear Heqc.
    remember (observe t). remember (val x).
    revert t v i x Heql Heqc0 H0.
    induction H; intros t' v i x' Heql Heq Hequ; try inv Heql; subst.
    - rewrite <- ctree_eta in Hequ. cbn.
      apply ChoiceI_schedule_inv in Hequ. destruct Hequ as [? | [? | ?]].
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
      + destruct e; [destruct y | destruct s; [destruct s |]]; step in Hequ; inv Hequ.
      + step in Hequ; inv Hequ.
  Qed.

  (** [schedule] transitions with an [obs] *)
  Lemma trans_schedule_obs {X} n v o (e : parE config X) (x : X) t :
    trans (obs e x) (schedule n v o) t ->
    (exists k i s, o = Some i /\
                e = inr1 (inr1 s) /\
                visible (v i) (Vis (inr1 (inr1 s)) k) /\
                t ≅ schedule n (replace_vec v i (k x)) o).
  Proof.
    unfold trans; intro. destruct o as [i |].
    2: {
      rewrite rewrite_schedule in H. destruct n; inv H.
    }
    cbn in H. red in H.
    remember (observe (schedule n v (Some i))).
    pose proof (ctree_eta (go (observe (schedule n v (Some i))))).
    rewrite <- Heqc in H0 at 1. cbn in H0. clear Heqc.
    remember (observe t). remember (obs _ _).
    revert t n v i e x Heql Heqc0 H0.
    induction H; intros t' n' v i e' x' Heql Heq Hequ; try inv Heql; subst.
    - rewrite <- ctree_eta in Hequ.
      apply ChoiceI_schedule_inv in Hequ. destruct Hequ as [? | [? | ?]].
      + destruct H0 as (k' & Hvic & Hk).
        edestruct IHtrans_ as (k'' & i' & se & ? & ? & ? & ?); auto.
        * rewrite Hk. reflexivity.
        * inv H0.
          exists k'', i', se. split; [| split; [| split]]; auto.
          -- rewrite Hvic. cbn. red. cbn. econstructor.
             rewrite replace_vec_eq in H2. apply H2.
          -- rewrite replace_vec_twice in H3. apply H3.
      + destruct H0 as (k' & Hvic & ? & Hk). subst.
        setoid_rewrite Hk in H.
        destruct n'; inv H.
      + destruct H0 as (n'' & ? & Hvic & ? & Hk). subst.
        setoid_rewrite Hk in H.
        destruct n''; inv H.
    - invert. destruct n'; [inv i |].
      rewrite rewrite_schedule in Hequ.
      simp schedule_match in Hequ.
      destruct (observe (v i)) eqn:Hv.
      + destruct r. destruct n'; step in Hequ; inv Hequ.
      + destruct e; [destruct y | destruct s; [destruct s |]]; try solve [step in Hequ; inv Hequ].
        cbn in *.
        pose proof (equ_vis_invT _ _ _ _ Hequ). subst.
        destruct (equ_vis_invE _ _ _ _ Hequ). subst.
        exists k0, i, s. split; [| split; [| split]]; auto.
        * cbn. red. rewrite Hv. constructor. reflexivity.
        * rewrite ctree_eta. rewrite <- Heq. rewrite <- ctree_eta. rewrite <- H. apply H1.
      + step in Hequ; inv Hequ.
  Qed.

  (** schedule transitions with a tau and it's selecting a new index *)
  Lemma trans_schedule_thread_tau_none n v t :
    trans tau (schedule n v None) t ->
    exists n' i, n = S n' /\ t ≅ schedule n v (Some i).
  Proof.
    intros Ht.
    unfold trans in Ht. cbn in Ht. red in Ht. destruct n; try solve [inv Ht].
    rewrite rewrite_schedule in Ht. simp schedule_match in Ht.
    inv Ht. invert.
    exists n, x. split; auto. rewrite H2. rewrite ctree_eta.
    rewrite <- H1. rewrite <- ctree_eta. reflexivity.
  Qed.

  (* spawn or choice *)
  Lemma trans_schedule_thread_tau_some n v i t (Hbound : choiceI_bound 1 (v i)) :
    trans tau (schedule n v (Some i)) t ->
    (exists n' i',
        trans (val ()) (v i) CTree.stuckI /\
          {H: n = S (S n') &
                t ≅ schedule (S n') (remove_vec_helper n (S n') v i H) (Some i')}) \/
      (exists t', trans tau (v i) t' /\
               choiceI_bound 1 t' /\
               t ≅ schedule n (replace_vec v i t') (Some i)) \/
      (exists k, visible (v i) (Vis (inl1 Yield) k) /\
                 exists i', t ≅ schedule n (replace_vec v i (k tt)) (Some i')) \/
      (exists k, visible (v i) (Vis (inr1 (inl1 Spawn)) k) /\
              t ≅ schedule
                (S n)
                (cons_vec (k true) (replace_vec v i (k false)))
                (Some (FS i))).
  Proof.
    unfold trans. intros. cbn in H. red in H. (* destruct n; try inv i. *)
    remember (observe (schedule n v (Some i))).
    pose proof (ctree_eta (go (observe (schedule n v (Some i))))).
    rewrite <- Heqc in H0 at 1. cbn in H0. clear Heqc.
    remember (observe t). remember tau.
    revert t n v i Heqc0 Heql H0 Hbound.
    induction H; intros t' n' v i Heq Heql Hequ Hbound; subst; try inv Heql.
    {
      rewrite <- ctree_eta in Hequ.
      apply ChoiceI_schedule_inv in Hequ. destruct Hequ as [? | [? | ?]].
      - destruct H0 as (k' & Hvi & Hk).
        edestruct IHtrans_ as [? | [? | [? | ?]]]; auto; clear IHtrans_.
        rewrite Hk. reflexivity.
        rewrite replace_vec_eq. rewrite Hvi in Hbound.
        step in Hbound. inv Hbound. invert. apply H2. all: cbn in *.
        + destruct H0 as (n'' & o & Ht & ? & Hequ). subst. left.
          rewrite replace_vec_eq in Ht.
          cbn in Hequ. erewrite <- remove_vec_replace_vec_eq in Hequ.
          exists n'', o. split; [| exists eq_refl].
          * rewrite Hvi. red. econstructor. apply Ht.
          * apply Hequ.
        + destruct H0 as (t'' & Ht & Hbound' & Hequ).
          right. left.
          rewrite replace_vec_eq in Ht. rewrite replace_vec_twice in Hequ.
          exists t''. split; [| split]; auto.
          rewrite Hvi. red. econstructor. eauto.
        + edestruct H0 as (k'' & Hvis & o & Hequ).
          right. right. left.
          rewrite replace_vec_eq in Hvis. rewrite replace_vec_twice in Hequ.
          exists k''. split; eauto.
          rewrite Hvi. red. econstructor. eauto.
        + edestruct H0 as (k'' & Hvis & Hequ).
          right. right. right.
          rewrite replace_vec_eq in Hvis. rewrite replace_vec_twice in Hequ.
          exists k''. split; auto.
          rewrite Hvi. red. econstructor; eauto.
      - clear IHtrans_. destruct H0 as (k' & Hequ & ? & Hk). subst.
        right. right. left. exists k'. split.
        + rewrite Hequ. constructor. reflexivity.
        + rewrite Hk in H. apply trans_schedule_thread_tau_none in H.
          destruct H as (? & ? & ? & ?). subst. eauto.
      - clear IHtrans_. destruct H0 as (n'' & ? & Hvi & ? & Hk). subst. cbn in *.
        left. rewrite Hk in H. apply trans_schedule_thread_tau_none in H.
        destruct H as (n' & i' & ? & Hequ). subst.
        exists n', i'.
        split.
        + rewrite Hvi. constructor.
        + exists eq_refl; cbn; auto.
    }
    {
      destruct n'; try inv i.
      rewrite rewrite_schedule in Hequ. simp schedule_match in Hequ.
      destruct (observe (v i)) eqn:?; cbn in Hequ.
      - step in Hequ. inv Hequ.
      - destruct e; [destruct y | destruct s; [destruct s |]]; cbn in Hequ.
        + step in Hequ. inv Hequ.
        + destruct (equ_choice_invT _ _ Hequ) as (? & _). subst.
          pose proof (equ_choice_invE _ _ Hequ).
          right. right. right.
          exists k0. split.
          * cbn. red. rewrite Heqc. constructor. reflexivity.
          * rewrite ctree_eta. rewrite <- Heq. rewrite <- ctree_eta. rewrite <- H.
            rewrite H0. auto.
        + step in Hequ. inv Hequ.
      - destruct (equ_choice_invT _ _ Hequ). subst.
        pose proof (equ_choice_invE _ _ Hequ). right. left. cbn.
        exists (k0 x). split; [| split]; auto.
        + red. rewrite Heqc. econstructor; eauto.
        + step in Hbound. pose proof (ctree_eta (v i)). erewrite Heqc in H1.
          rewrite H1 in Hbound. inv Hbound. invert. auto.
        + rewrite ctree_eta. rewrite <- Heq. rewrite <- ctree_eta. rewrite <- H.
          rewrite H0. auto.
     }
  Qed.

  (** how the thread transitions affects the scheduler *)

  Lemma trans_thread_schedule_val_1 {X} v i (x : X) t :
    trans (val x) (v i) t ->
    trans (val x) (schedule 1 v (Some i)) CTree.stuckI.
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
    forall i', trans tau (schedule (S (S n)) v (Some i)) (schedule (S n) (remove_vec v i) (Some i')).
  Proof.
    unfold trans; intro. cbn in *. red in H.
    remember (observe (v i)).
    pose proof (ctree_eta (go (observe (v i)))).
    rewrite <- Heqc in H0 at 1. cbn in H0. clear Heqc.
    remember (observe t). remember (val ()).
    revert t v i Heql Heqc0 H0.
    induction H; intros t' v i Heql Heq Hequ i'; try inv Heql.
    - step in Hequ. inv Hequ. invert.
      epose proof (IHtrans_ t' (replace_vec v i (k2 x)) i eq_refl eq_refl _).
      Unshelve.
      2: { rewrite REL. rewrite replace_vec_eq. reflexivity. }
      specialize (H0 i').
      setoid_rewrite rewrite_schedule. simp schedule_match. rewrite <- H4. cbn.
      econstructor. erewrite <- remove_vec_replace_vec_eq in H0. apply H0.
    - invert. step in Hequ. inv Hequ.
      setoid_rewrite rewrite_schedule at 1. simp schedule_match. rewrite <- H. cbn.
      constructor. constructor.
      rewrite rewrite_schedule at 1. simp schedule_match. econstructor.
      reflexivity.
  Qed.

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
      apply replace_vec_vec_relation; repeat intro; try reflexivity.
      rewrite <- Heq. rewrite <- REL. auto.
  Qed.

  (** [visible] lemmas *)
  Lemma visible_yield_trans_schedule n v i i' k (Hbound : choiceI_bound 1 (v i)) :
    visible (v i) (Vis (inl1 Yield) k) ->
    trans tau (schedule (S n) v (Some i)) (schedule (S n) (replace_vec v i (k tt)) (Some i')).
  Proof.
    intros. cbn in *. red in H |- *. red.
    remember (observe (v i)). remember (observe (Vis _ k)).
    revert v i i' k Heqc Heqc0 Hbound.
    induction H; intros; subst; try inv Heqc0.
    - edestruct @choiceI_step as (? & Hbound').
      {
        assert (v i ≅ ChoiceI n0 k).
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
      econstructor. eapply equ_schedule.
      apply replace_vec_vec_relation; repeat intro; auto.
  Qed.

  Lemma visible_spawn_trans_schedule n v i k (Hbound : choiceI_bound 1 (v i)) :
    visible (v i) (Vis (inr1 (inl1 Spawn)) k) ->
    trans tau (schedule (S n) v (Some i))
          (schedule (S (S n))
                    (cons_vec (k true)
                              (replace_vec v i (k false)))
                    (Some (FS i))).
  Proof.
    intros. cbn in *. red in H |- *. red.
    remember (observe (v i)). remember (observe (Vis _ k)).
    revert v i k Heqc Heqc0 Hbound.
    induction H; intros; subst; try inv Heqc0.
    - edestruct @choiceI_step as (? & Hbound').
      {
        assert (v i ≅ ChoiceI n0 k).
        rewrite ctree_eta. rewrite <- Heqc. reflexivity.
        rewrite H0 in Hbound. apply Hbound.
      } subst.
      rewrite rewrite_schedule at 1. simp schedule_match.
      rewrite <- Heqc. constructor 1 with (x:=x).
      rewrite <- (replace_vec_twice _ v i (k x) (k0 false)).
      eapply IHvisible_; auto; rewrite replace_vec_eq; eauto.
    - invert.
      rewrite rewrite_schedule at 1. simp schedule_match.
      rewrite <- Heqc. econstructor. apply F1. apply equ_schedule.
      apply cons_vec_vec_relation; auto.
      apply replace_vec_vec_relation; repeat intro; auto.
  Qed.

  Lemma visible_stateE_trans_schedule {X} n v i (s : stateE config X) k x (Hbound : choiceI_bound 1 (v i)) :
    visible (v i) (Vis (inr1 (inr1 s)) k) ->
    trans (obs (inr1 (inr1 s)) x) (schedule (S n) v (Some i))
          (schedule (S n) (replace_vec v i (k x)) (Some i)).
  Proof.
    intros. cbn in *. red in H |- *. red.
    remember (observe (v i)). remember (observe (Vis _ k)).
    revert v i k Heqc Heqc0 Hbound.
    induction H; intros; subst; try inv Heqc0.
    - edestruct @choiceI_step as (? & Hbound').
      {
        assert (v i ≅ ChoiceI n0 k).
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
      apply replace_vec_vec_relation; repeat intro; auto.
  Qed.

  #[global] Instance sbisim_schedule n :
    Proper (vec_relation (fun x y => sbisim x y /\ choiceI_bound 1 x /\ choiceI_bound 1 y) ==> eq ==> sbisim) (schedule n).
  Proof.
    repeat intro. subst. revert n x y y0 H. cbn in *.
    coinduction r CIH.
    symmetric using idtac.
    {
      intros. apply H. repeat intro. split; [symmetry | split]; apply H0.
    }
    intros n v1 v2 o Hv l t Ht. cbn in *.
    destruct l.
    - destruct o as [i |].
      + apply trans_schedule_thread_tau_some in Ht. 2: apply Hv.
        decompose [or] Ht; clear Ht.
        * destruct H as (n' & o & Ht & ? & Hequ). subst.
          pose proof (Hv i) as (Hsb & _). step in Hsb. destruct Hsb as [Hf _].
          edestruct Hf as [? ? ?]; eauto.
          eapply trans_thread_schedule_val_SS in H.
          eexists. apply H. rewrite Hequ. eapply CIH.
          cbn. apply remove_vec_vec_relation; auto.
        * destruct n; try inv i.
          destruct H0 as (t' & Ht & Hbound & Hequ).
          pose proof (Hv i) as (Hsb & Hbound1 & Hbound2). step in Hsb. destruct Hsb as [Hf _].
          edestruct Hf as [? ? ?]; eauto.
          pose proof (trans_choiceI_bound _ _ _ _ _ Hbound2 H).
          apply trans_thread_schedule_tau in H.
          eexists; eauto. rewrite Hequ. apply CIH.
          apply replace_vec_vec_relation; auto.
        * destruct H as (k & Hvis & i' & Hequ).
          pose proof (Hv i) as (Hsb & Hbound1 & Hbound2).
          pose proof Hvis as Hvis'.
          eapply sbisim_visible in Hvis'; eauto. destruct Hvis' as (k' & ? & ?).
          exists (schedule n (replace_vec v2 i (k' tt)) (Some i')).
          2: {
            rewrite Hequ. apply CIH. apply replace_vec_vec_relation; auto.
            intros; split; [| split]; auto.
            - pose proof (visible_choiceI_bound _ _ _ _ _ Hbound1 Hvis).
              step in H1. inv H1. invert. auto.
            - pose proof (visible_choiceI_bound _ _ _ _ _ Hbound2 H).
              step in H1. inv H1. invert. auto.
          }
          destruct n; try inv i.
          apply visible_yield_trans_schedule; auto.
        * destruct H as (k & Hvis & Hequ).
          pose proof (Hv i) as (Hsb & Hbound1 & Hbound2).
          pose proof Hvis as Hvis'.
          eapply sbisim_visible in Hvis'; eauto.
          2: { constructor. apply true. }
          destruct Hvis' as (k' & ? & ?).
          exists (schedule (S n)
                      (cons_vec (k' true)
                                (replace_vec v2 i (k' false)))
                      (Some (FS i))).
          2: { rewrite Hequ. apply CIH. apply cons_vec_vec_relation; auto.
               - apply replace_vec_vec_relation; auto; split; auto. split.
                 + pose proof (visible_choiceI_bound _ _ _ _ _ Hbound1 Hvis).
                   step in H1. inv H1. invert. auto.
                 + pose proof (visible_choiceI_bound _ _ _ _ _ Hbound2 H).
                   step in H1. inv H1. invert. auto.
               - split; auto. split.
                 + pose proof (visible_choiceI_bound _ _ _ _ _ Hbound1 Hvis).
                   step in H1. inv H1. invert. auto.
                 + pose proof (visible_choiceI_bound _ _ _ _ _ Hbound2 H).
                   step in H1. inv H1. invert. auto.
          }
          destruct n; try inv i.
          apply visible_spawn_trans_schedule; auto.
      + apply trans_schedule_thread_tau_none in Ht.
        destruct Ht as (n' & i & ? & Hequ). subst.
        exists (schedule (S n') v2 (Some i)).
        * rewrite rewrite_schedule. simp schedule_match. econstructor; eauto.
        * rewrite Hequ. apply CIH; auto.
    - apply trans_schedule_obs in Ht.
      destruct Ht as (k & i & s & ? & ? & Hvis & Hequ). subst.
      destruct n; try inv i.
      pose proof (Hv i) as (Hsb & Hbound1 & Hbound2).
      pose proof Hvis as Hvis'.
      eapply sbisim_visible in Hvis'; eauto.
      destruct Hvis' as (k' & ? & ?).
      exists (schedule (S n) (replace_vec v2 i (k' v)) (Some i)).
      2: { rewrite Hequ. apply CIH. apply replace_vec_vec_relation; auto.
           split; [| split]; auto.
           - pose proof (visible_choiceI_bound _ _ _ _ _ Hbound1 Hvis).
             step in H1. inv H1. invert. auto.
           - pose proof (visible_choiceI_bound _ _ _ _ _ Hbound2 H).
             step in H1. inv H1. invert. auto.
      }
      eapply visible_stateE_trans_schedule in H; eauto.
    - destruct o as [i |].
      + pose proof (trans_schedule_val_1 _ _ _ _ _ Ht). subst.
        pose proof (trans_val_inv Ht).
        specialize (Hv i). destruct Hv as (Hsb & _). step in Hsb. destruct Hsb as [Hf Hb].
        pose proof (trans_schedule_thread_val _ _ _ _ Ht) as Hv1.
        edestruct Hf; eauto.
        apply trans_thread_schedule_val_1 in H0. eexists; eauto. rewrite H. reflexivity.
      + rewrite rewrite_schedule in Ht.
        destruct n; [| inv Ht].
        destruct (trans_ret_inv Ht). inv H0. apply inj_pair2 in H3. subst.
        exists CTree.stuckI.
        * rewrite rewrite_schedule. constructor.
        * rewrite H. reflexivity.
  Qed.

  Lemma of_nat_lt_sig1_neq_1 n1 n2 n (H1 : n1 < n) (H2 : n2 < n) :
    of_nat_lt H1 <> of_nat_lt H2 ->
    n1 <> n2.
  Proof.
    repeat intro. subst. apply H. apply of_nat_ext.
  Qed.

  Lemma of_nat_lt_sig1_neq_2 n1 n2 n (H1 : n1 < n) (H2 : n2 < n) :
    n1 <> n2 ->
    of_nat_lt H1 <> of_nat_lt H2.
  Proof.
    revert n2 n H1 H2. induction n1; intros; auto.
    - destruct n2; auto. destruct n; [inv H2 |]. intro. inv H0.
    - destruct n; [inv H2 |]. destruct n2.
      + intro. inv H0.
      + cbn. intro. inv H0. invert. eapply (IHn1 n2).
        * intro. subst. contradiction.
        * apply x.
  Qed.

  Lemma of_nat_lt_sig1_neq n1 n2 n (H1 : n1 < n) (H2 : n2 < n) :
    n1 <> n2 <->
      of_nat_lt H1 <> of_nat_lt H2.
  Proof.
    split. apply of_nat_lt_sig1_neq_2. apply of_nat_lt_sig1_neq_1.
  Qed.

  (* Definition permutation_from_nat {n} (p q : nat -> nat) *)
  (*            (Hp : forall i, i < n -> p i < n) *)
  (*            (Hq : forall i, i < n -> q i < n) *)
  (*            (Hpq : forall i, i < n -> p (q i) = i) *)
  (*            (Hqp : forall i, i < n -> q (p i) = i) : *)
  (*   { x : (fin n -> fin n) * (fin n -> fin n) & *)
  (*           (forall i, (fst x) ((snd x) i) = i) & *)
  (*           (forall i, (snd x) ((fst x) i) = i) }. *)
  (* Proof. *)
  (*   eexists. Unshelve. *)
  (*   3: { *)
  (*     split. *)
  (*     - intro i. destruct (to_nat i). *)
  (*       pose proof (Hp x l). *)
  (*       apply (of_nat_lt H). *)
  (*     - intro i. destruct (to_nat i). *)
  (*       pose proof (Hq x l). *)
  (*       apply (of_nat_lt H). *)
  (*   } *)
  (*   - cbn. intros. destruct (to_nat i). *)
  (*     rewrite to_nat_of_nat. *)
  (*     erewrite of_nat_ext. *)
  (*     unfold of_nat_lt. *)
  (*     (* generalize dependent x. *) *)
  (*     rewrite (Hpq x l). *)
  (*     revert (p (q x)). erewrite (Hpq x). *)
  (* Qed. *)

  (*
  Definition permutation_to_nat {n} (p q : fin n -> fin n)
        (Hpq : forall i, p (q i) = i)
        (Hqp : forall i, q (p i) = i) :
    { x : (nat -> nat) * (nat -> nat) &
            (forall i, i < n -> (fst x) i < n) /\ (forall i, i < n -> (snd x) i < n) /\
            (forall i, i < n -> (fst x) ((snd x) i) = i) /\ (forall i, i < n -> (snd x) ((fst x) i) = i) }.
  Proof.
    eexists. Unshelve.
    2: {
      split.
      - clear q Hpq Hqp. intro i'.
        destruct (Compare_dec.lt_dec i' n).
        + pose proof (of_nat_lt l) as i.
          pose proof (p i) as pi.
          destruct (to_nat pi). apply x.
        + apply i'.
      - clear p Hpq Hqp. intro i'.
        destruct (Compare_dec.lt_dec i' n).
        + pose proof (of_nat_lt l) as i.
          pose proof (q i) as qi.
          destruct (to_nat qi). apply x.
        + apply i'.
    }
    cbn. split; [| split; [| split]].
    - intros.
      destruct (Compare_dec.lt_dec i n); try contradiction.
      destruct (to_nat (q (of_nat_lt l))) eqn:?.
      destruct (to_nat (p (of_nat_lt l))) eqn:?. auto.
    - intros.
      destruct (Compare_dec.lt_dec i n); try contradiction.
      destruct (to_nat (q (of_nat_lt l))) eqn:?.
      destruct (to_nat (p (of_nat_lt l))) eqn:?. auto.
    - intros i Hi.
      destruct (Compare_dec.lt_dec i n); try contradiction. clear Hi. rename l into Hi.
      destruct (to_nat (q (of_nat_lt Hi))) as (qi' & Hqi) eqn:?.
      destruct (Compare_dec.lt_dec qi' n); try contradiction.
      rewrite (of_nat_ext _ Hqi). clear l.
      destruct (to_nat (p (of_nat_lt Hqi))) as (pqi' & Hpqi) eqn:?.

      pose proof Heqs as ?. apply (f_equal from_nat_) in H.
      (* unfold to_nat in Heqs. *)
      pose proof (Hpq (of_nat_lt Hi)). rewrite <- H in Heqs.
  Qed. *)

  Definition cons_permutation {n} (p : fin n -> fin n) :
    {
      p' : (fin (S n) -> fin (S n)) &
             p' F1 = F1 /\ forall i, p' (FS i) = FS (p i)
    }.
    eexists. Unshelve.
    2: {
      intro i.
      dependent destruction i.
      - apply F1.
      - apply (FS (p i)).
    }
    split; auto.
  Defined.

  Lemma cons_permutation_correct {n} (p q : fin n -> fin n)
        (Hpq : forall i, p (q i) = i)
        (Hqp : forall i, q (p i) = i) :
    let p' := projT1 (cons_permutation p) in
    let q' := projT1 (cons_permutation q) in
    (forall i, p' (q' i) = i) /\ (forall i, q' (p' i) = i).
  Proof.
    destruct (cons_permutation p) as (p' & Hp1 & Hp2).
    destruct (cons_permutation q) as (q' & Hq1 & Hq2).
    cbn in *. split.
    - intro i. dependent destruction i.
      + rewrite Hq1, Hp1. auto.
      + rewrite Hq2, Hp2, Hpq. auto.
    - intro i. dependent destruction i.
      + rewrite Hp1, Hq1. auto.
      + rewrite Hp2, Hq2, Hqp. auto.
  Qed.

  (* Inductive lt {m n} : fin (S m) -> fin (S n) -> Prop := *)
  (* | lt_base : forall i, lt F1 (FS i) *)
  (* | lt_ind : forall i j, lt i j -> lt (FS i) (FS j) *)
  (* . *)

  Variant ordering := LT | EQ | GT.

  Fixpoint order {m n} (p : fin m) (q : fin n) : ordering :=
    match p, q with
    | F1, F1 => EQ
    | F1, _ => LT
    | _, F1 => GT
    | FS p', FS q' => order p' q'
    end.

  (** General order lemmas *)

  Lemma order_reflexive {n} (p : fin n) :
    order p p = EQ.
  Proof.
    depind p; auto.
  Qed.

  Lemma order_transitive {m n o} (p : fin m) (q : fin n) (r : fin o) l :
    order p q = l ->
    order q r = l ->
    order p r = l.
  Proof.
    destruct l.
    {
      revert n o q r.
      depind p; intros; auto.
      - dependent destruction q; auto. dependent destruction r; auto. inv H0.
      - dependent destruction q; auto; [inv H |].
        dependent destruction r; auto. cbn in *. eapply IHp; eauto.
    }
    {
      revert n o q r.
      depind p; intros; auto.
      - dependent destruction q; auto. dependent destruction r; auto.
      - dependent destruction q; auto; [inv H |].
        dependent destruction r; auto. cbn in *. eapply IHp; eauto.
    }
    {
      revert n o q r.
      depind p; intros; auto.
      - dependent destruction q; auto. dependent destruction r; auto. inv H.
      - dependent destruction q.
        + dependent destruction r; auto; inv H0.
        + dependent destruction r; auto. cbn in *. eapply IHp; eauto.
    }
  Qed.

  Lemma order_flip {m n} (p : fin m) (q : fin n) :
    order p q = LT <-> order q p = GT.
  Proof.
    split.
    {
      revert n q.
      depind p; dependent destruction q; auto.
      - intros. inv H.
      - cbn. eapply IHp.
    }
    {
      revert n q.
      depind p; dependent destruction q; auto.
      - intros. inv H.
      - cbn. eapply IHp.
    }
  Qed.

  Lemma order_eq {n} (p q : fin n) :
    order p q = EQ -> p = q.
  Proof.
    depind p; intros; dependent destruction q; inv H; auto.
    f_equal. auto.
  Qed.


  Lemma order_EQ_FS {m n} (p : fin m) (q : fin n) :
    order p q = EQ -> order (FS p) q = GT.
  Proof.
    revert n q.
    depind p.
    - intros. dependent destruction q; inv H; auto.
    - intros. dependent destruction q. inv H. cbn in H. apply IHp; auto.
  Qed.

  Lemma order_GT_FS {m n} (p : fin m) (q : fin n) :
    order p q = GT -> order (FS p) q = GT.
  Proof.
    revert n q.
    depind p.
    - intros. dependent destruction q; inv H; auto.
    - intros. dependent destruction q; auto. cbn in H. apply IHp; auto.
  Qed.

  Lemma order_FS_LT {n} (i : fin n) :
    order i (FS i) = LT.
  Proof.
    induction i; auto.
  Qed.

  (* Lemma order_FS' {n} (i : fin n) : *)
  (*   order (FS i) i = g. *)
  (* Proof. *)
  (*   apply order_flip; apply order_FS. *)
  (* Qed. *)

  Lemma order_FS_GT_inv {m n} (p : fin m) (q : fin n) :
    order (FS p) q = GT ->
    order p q = EQ \/ order p q = GT.
  Proof.
    intros. generalize dependent n. depind p; intros.
    - dependent destruction q.
      + left; auto.
      + dependent destruction q; inv H.
    - dependent destruction q.
      + right; auto.
      + cbn in H. destruct (IHp _ q H); auto.
  Qed.

  Lemma order_cases {m n} (p : fin m) (q : fin n) :
    {order p q = LT} + {order p q = EQ} + {order p q = GT}.
  Proof.
    destruct (order p q); intuition.
  Qed.

  (** For converting a value of type [fin (S (S n))] into one of type [fin (S n)] *)
  Equations not_highest {n} (p q : fin (S (S n))) (H: order p q = LT) : fin (S n) :=
    not_highest F1 q H := F1 ;
    not_highest (FS p') F1 H := _;
    @not_highest 0 (FS p') (FS q') H := _;
    @not_highest (S n) (FS p') (FS q') H := FS (not_highest p' q' _).
  Next Obligation.
    intros. inv H.
  Defined.
  Next Obligation.
    intros. cbn in *. dependent destruction p'. 2: inv p'.
    dependent destruction q'. inv H. inv q'.
  Defined.
  Next Obligation.
    auto.
  Defined.

  (* not used *)
  Lemma not_highest_FS {n} (p q : fin (S (S n))) H H' :
    (not_highest (FS p) (FS q) H) = FS (not_highest p q H').
  Proof.
    simp not_highest. f_equal. f_equal. apply proof_irrelevance.
  Qed.

  Lemma order_not_highest {n} (p q r : fin (S (S n))) H :
    order p r = order (not_highest p q H) r.
  Proof.
    depind p.
    - simp not_highest. reflexivity.
    - dependent destruction q. inv H.
      destruct n.
      + cbn in *. depind p. depind q. inv H. inv q. inv p.
      + cbn in H. rewrite not_highest_FS with (H':=H).
        cbn in *. dependent destruction r; auto.
  Qed.

  Lemma order_not_highest_EQ {n} (p q : fin (S (S n))) H :
    order (not_highest p q H) p = EQ.
  Proof.
    depind p; auto.
    - simp not_highest. auto.
    - dependent destruction q. inv H.
      destruct n.
      + cbn in H.
        dependent destruction p. 2: inv p.
        dependent destruction q. inv H. inv q.
      + simp not_highest. cbn. apply IHp; auto.
  Qed.

  (** view a [fin n] as a [fin (S n)] *)
  Equations fin_S {n} (i : fin n) : fin (S n) :=
    fin_S F1 := F1;
    fin_S (FS i') := FS (fin_S i').

  Lemma order_fin_S_EQ {n} (i : fin n) : order i (fin_S i) = EQ.
  Proof.
    depind i; auto.
  Qed.

  Lemma order_fin_S m n (p : fin m) (q : fin n) : order p q = order (fin_S p) q.
  Proof.
    intros. revert n q. depind p.
    - reflexivity.
    - dependent destruction q.
      + reflexivity.
      + cbn. rewrite IHp. reflexivity.
  Qed.

  Lemma fin_S_not_highest {n} (p q : fin (S (S n))) H : fin_S (not_highest p q H) = p.
  Proof.
    depind p; cbn; auto.
    - simp not_highest. simp fin_S. reflexivity.
    - dependent destruction q. inv H.
      destruct n. cbn in H.
      dependent destruction p. dependent destruction q. inv H. inv q. inv p.
      simp not_highest. simp fin_S. f_equal. apply IHp; auto.
  Qed.

  Lemma not_highest_fin_S {n} (p : fin (S n)) q H : (not_highest (fin_S p) q H) = p.
  Proof.
    destruct n.
    { dependent destruction p. auto. inv p. }
    depind p; auto.
    dependent destruction q. inv H.
    revert H. simp fin_S. intro.
    destruct n; auto.
    - cbn in *. dependent destruction p. 2: inv p. auto.
    - simp not_highest. f_equal. auto.
  Qed.

  (** p is greater than another value, so we can subtract one *)
  Equations subtract_one {n} (p q : fin (S n)) (H: order p q = GT) : fin n :=
  subtract_one F1 q H := _;
  subtract_one (FS p') q H := p'.
  Next Obligation.
    intros. dependent destruction q; inv H.
  Defined.

  Lemma subtract_one_FS {n} p (q : fin (S n)) H :
    subtract_one (FS p) q H = p.
  Proof.
    reflexivity.
  Qed.

  Lemma FS_subtract_one {n} (p q : fin (S n)) H :
    FS (subtract_one p q H) = p.
  Proof.
    dependent destruction p.
    - dependent destruction q; inv H.
    - reflexivity.
  Qed.

  Lemma order_subtract_one_GT {n} (p q : fin (S n)) (H : order p q = GT) :
    order p (subtract_one p q H) = GT.
  Proof.
    dependent destruction p.
    - dependent destruction q; inv H.
    - destruct n. inv p. rewrite subtract_one_FS. apply order_flip. apply order_FS_LT.
  Qed.

  Lemma order_subtract_one_GT_inv {n} (p q r : fin (S n)) H :
    order p q = GT ->
    order (subtract_one p r H) q = EQ \/ order (subtract_one p r H) q = GT.
  Proof.
    intros.
    dependent destruction p.
    - dependent destruction q; inv H0.
    - destruct n. inv p.
      rewrite subtract_one_FS. apply order_FS_GT_inv; auto.
  Qed.

  Lemma order_subtract_one_LT_inv {n} (p q r : fin (S n)) H :
     order (subtract_one p r H) q = LT ->
     order p q = EQ \/ order p q = LT.
  Proof.
    intros.
    depind p. dependent destruction r; inv H.
    destruct n. inv p. specialize (IHp n p eq_refl JMeq_refl).
    rewrite subtract_one_FS in H0.
    dependent destruction q. dependent destruction p; inv H0. cbn.
    dependent destruction p. dependent destruction q; auto.
    cbn in H0.
    eapply (IHp q (fin_S p) _ _). Unshelve.
    - rewrite <- order_flip. rewrite <- order_fin_S. apply order_FS_LT.
    - rewrite subtract_one_FS. auto.
  Qed.

  (** lemmas about remove_vec and order *)
  Lemma remove_vec_index_before' {n} (v : vec (S n)) i j
    (Hj : order j i = LT) :
    v (fin_S j) = remove_vec v i j.
  Proof.
    revert v j Hj. depind i; intros; auto. dependent destruction j; inv Hj.
    destruct n. inv j. dependent destruction j; auto. cbn. simp fin_S.
    erewrite <- IHi; auto.
  Qed.

  (* after the element removed, we need to subtract one from the index *)
  Lemma remove_vec_index_after' {n} (v : vec (S n)) i j
        (Hj : order j i = GT) :
    v (FS j) = remove_vec v i j.
  Proof.
    revert v i Hj. depind j; intros. dependent destruction i; auto; inv Hj.
    dependent destruction i.
    - destruct n. inv j. reflexivity.
    - destruct n. inv j. cbn in *. rewrite <- IHj; auto.
  Qed.

  (* at the element removed, we also subtract one. TODO: can we unify this with prev lemma? *)
  Lemma remove_vec_index_eq' {n} (v : vec (S n)) i j
        (Hj : order j i = EQ) :
    v (FS j) = remove_vec v i j.
  Proof.
    revert v i Hj. depind j; intros. dependent destruction i; auto; inv Hj.
    dependent destruction i. inv Hj.
    destruct n. inv j. cbn in *. rewrite <- IHj; auto.
  Qed.

  (* why.. *)
  Instance test: subrelation eq (flip impl).
  Proof.
    repeat intro. subst. auto.
  Qed.

  Ltac cases a b name := destruct (order_cases a b) as [[name | name] | name].


  (* Definition remove_at_permutation {n} (p : fin (S (S n)) -> fin (S (S n))) *)
  (*            (r : fin (S (S n))) *)
  (*            (Hp : Injective p) *)
  (*   : fin (S n) -> fin (S n). *)
  (*   intro i. *)
  (*   destruct (order_cases' i r) as [[Hi | Hi] | Hi]. *)
  (*   - (* i < r *) *)
  (*     remember (p (fin_S i)) as pi. *)
  (*     destruct (order_cases' pi r) as [[Hpi | Hpi] | Hpi]. *)
  (*     + (* p i < r *) *)
  (*       apply (not_highest _ _ Hpi). *)
  (*     + (* p i = r, return p (p i) *) *)
  (*       remember (p pi) as ppi. *)
  (*       destruct (order_cases' ppi r) as [[Hppi | Hppi] | Hppi]. *)
  (*       * apply (not_highest _ _ Hppi). *)
  (*       * (* impossible since p should be an injection: p i = r = p (p i), but i < p i *) *)
  (*         apply order_eq in Hpi, Hppi. subst. apply Hp in Hppi. rewrite Hppi in Hi. *)
  (*         rewrite order_fin_S_equal in Hi. inv Hi. *)
  (*       * apply (subtract_one _ _ Hppi). *)
  (*     + (* p i > r *) *)
  (*       apply (subtract_one _ _ Hpi). *)
  (*   - apply F1. *)
  (*   - apply F1. *)
  (* Defined. *)

  Definition remove_at_permutation {n} (p : fin (S (S n)) -> fin (S (S n)))
             (r : fin (S (S n)))
             (Hp : Injective p)
    :
    { p' : (fin (S n) -> fin (S n)) &
             (forall i, match (order_cases i r) with
                   | inleft (left Hi) =>
                       (* i < r *)
                       let pi := p (fin_S i) in
                       match (order_cases pi (p r)) with
                       | inleft (left Hpi) => (* p i < p r *)
                           p' i = not_highest _ _ Hpi
                       | inleft (right Hpi) => (* p i = p r *)
                           False
                       | inright Hpi => (* p i > p r *)
                           p' i = subtract_one _ _ Hpi
                       end
                   | _(* inleft (right Hi) *) =>
                       (* i >= r *)
                       let pi := p (FS i) in
                       match (order_cases pi (p r)) with
                       | inleft (left Hpi) => (* p (i + 1) < p r *)
                           p' i = not_highest _ _ Hpi
                       | inleft (right Hpi) => (* p (i + 1) = p r *)
                           False
                       | inright Hpi => (* p (i + 1) > p r *)
                           p' i = subtract_one _ _ Hpi
                       end
                   end)
    }.
  Proof.
    eexists. Unshelve.
    2: {
      intro i.
      cases i r Hi.
      - (* i < r *)
        remember (p (fin_S i)) as pi.
        cases pi (p r) Hpi.
        + (* p i < p r *)
          apply (not_highest _ _ Hpi).
        + (* p i = p r, contradiction *)
          apply order_eq in Hpi. subst. apply Hp in Hpi. rewrite <- Hpi in Hi.
          rewrite order_fin_S_EQ in Hi. inv Hi.
        + (* p i > p r *)
          apply (subtract_one _ _ Hpi).
      - (* i = r *)
        remember (p (FS i)) as pi.
        cases pi (p r) Hpi.
        + (* p (i + 1) < p r *)
          apply (not_highest _ _ Hpi).
        + (* p (i + 1) = p r, contradiction *)
          apply order_eq in Hpi. subst. apply Hp in Hpi. rewrite <- Hpi in Hi.
          rewrite order_FS_LT in Hi. inv Hi.
        + (* p i > p r *)
          apply (subtract_one _ _ Hpi).
      - (* i > r *)
        remember (p (FS i)) as pi.
        cases pi (p r) Hpi.
        + (* p (i + 1) < p r *)
          apply (not_highest _ _ Hpi).
        + (* p (i + 1) = p r, contradiction *)
          apply order_eq in Hpi. subst. apply Hp in Hpi. rewrite <- Hpi in Hi.
          rewrite order_FS_LT in Hi. inv Hi.
        + (* p i > p r *)
          apply (subtract_one _ _ Hpi).
    }
    intro i. cbn.
    cases i r Hi.
    - (* i < r *)
      set (pi := p (fin_S i)).
      cases pi (p r) Hpi; auto.
      (* equals case is a contradiction *)
      apply order_eq in Hpi. subst. apply Hp in Hpi. rewrite <- Hpi in Hi.
      rewrite order_fin_S_EQ in Hi. inv Hi.
    - (* i = r *)
      set (pi := p (FS i)).
      cases pi (p r) Hpi; auto.
      (* equals case is a contradiction *)
      apply order_eq in Hpi. subst pi. apply Hp in Hpi. rewrite <- Hpi in Hi.
      rewrite order_FS_LT in Hi. inv Hi.
    - (* i > r *)
      set (pi := p (FS i)).
      cases pi (p r) Hpi; auto.
      (* equals case is a contradiction *)
      apply order_eq in Hpi. subst pi. apply Hp in Hpi. rewrite <- Hpi in Hi.
      rewrite order_FS_LT in Hi. inv Hi.
  Qed.

  Lemma bijective_injective {n} (p q : fin n -> fin n)
        (Hqp: forall i, q (p i) = i) :
    Injective p.
  Proof.
    intros i1 i2 ?. apply (f_equal q) in H. do 2 rewrite Hqp in H. auto.
  Qed.

  (*
  Lemma remove_at_permutation_correct {n} (p q : fin (S (S n)) -> fin (S (S n))) r
        (Hpq : forall i, p (q i) = i)
        (Hqp : forall i, q (p i) = i) :
    let p' := projT1 (remove_at_permutation p r (bijective_injective _ _ Hqp)) in
    let q' := projT1 (remove_at_permutation q r (bijective_injective _ _ Hpq)) in
    (forall i, p' (q' i) = i) /\ (forall i, q' (p' i) = i).
  Proof.
    destruct (remove_at_permutation p r _) as (p' & Hp).
    destruct (remove_at_permutation q r _) as (q' & Hq).
    cbn in *. split.
    {
      intro i.
      specialize (Hq i).
      destruct (order_cases' i r) as [[Hi | Hi] | Hi].
      - (* i < r *)
        destruct (order_cases' (q (fin_S i)) r) as [[Hqi | Hqi] | Hqi].
        + (* q i < r *)
          rewrite Hq. specialize (Hp (q' i)). rewrite Hq in Hp.
          rewrite fin_S_not_highest in Hp. rewrite Hpq in Hp.
          destruct (order_cases' (not_highest (q (fin_S i)) r Hqi) r) as [[Hqi' | Hqi'] | Hqi'].
          2, 3: erewrite <- order_not_highest_equal in Hqi'; rewrite Hqi in Hqi'; inv Hqi'.
          destruct (order_cases' (fin_S i) r) as [[Hi' | Hi'] | Hi'].
          2, 3: rewrite order_fin_S in Hi; rewrite Hi' in Hi; inv Hi.
          rewrite Hp. rewrite not_highest_fin_S. reflexivity.
        + (* q i = r, so we apply q again *)
          destruct (order_cases' (q (q (fin_S i))) r) as [[Hqqi | Hqqi] | Hqqi].
          * (* q (q i) < r *)
            rewrite Hq. specialize (Hp (q' i)). rewrite Hq in Hp.
            rewrite fin_S_not_highest in Hp. do 2 rewrite Hpq in Hp.
            destruct (order_cases' (not_highest (q (q (fin_S i))) r Hqqi) r) as
              [[Hqqi' | Hqqi'] | Hqqi'].
            2, 3: erewrite <- order_not_highest_equal in Hqqi'; rewrite Hqqi in Hqqi'; inv Hqqi'.
            destruct (order_cases' (q (fin_S i)) r) as [[Hqi' | Hqi'] | Hqi'].
            1, 3: rewrite Hqi' in Hqi; inv Hqi.
            destruct (order_cases' (fin_S i) r) as [[Hi' | Hi'] | Hi'].
            2, 3: rewrite order_fin_S in Hi; rewrite Hi' in Hi; inv Hi.
            rewrite Hp. rewrite not_highest_fin_S. reflexivity.
          * (* q (q i) = r *)
            contradiction.
          * (* q (q i) > r *)
            rewrite Hq. specialize (Hp (q' i)). rewrite Hq in Hp.
            rewrite FS_subtract_one in Hp. do 2 rewrite Hpq in Hp.
            destruct (order_cases' (subtract_one (q (q (fin_S i))) r Hqqi) r) as
              [[Hqqis | Hqqis] | Hqqis].
            -- (* q (q i) - 1 < r *)
              (* contradiction *)
              apply (subtract_one_l) in Hqqis.
              destruct Hqqis as [Hqqis | Hqqis]; rewrite Hqqi in Hqqis; inv Hqqis.
            -- (* q (q i) - 1 = r *)
              destruct (order_cases' (q (fin_S i)) r) as [[Hqi' | Hqi'] | Hqi'].
              1, 3: rewrite Hqi' in Hqi; inv Hqi. clear Hqi'.
              destruct (order_cases' (fin_S i) r) as [[Hi' | Hi'] | Hi'].
              2, 3: rewrite order_fin_S in Hi; rewrite Hi' in Hi; inv Hi.
              rewrite Hp. rewrite not_highest_fin_S. reflexivity.
            -- (* q (q i) - 1 > r, same as above *)
              destruct (order_cases' (q (fin_S i)) r) as [[Hqi' | Hqi'] | Hqi'].
              1, 3: rewrite Hqi' in Hqi; inv Hqi. clear Hqi'.
              destruct (order_cases' (fin_S i) r) as [[Hi' | Hi'] | Hi'].
              2, 3: rewrite order_fin_S in Hi; rewrite Hi' in Hi; inv Hi.
              rewrite Hp. rewrite not_highest_fin_S. reflexivity.
        + (* q i > r *)
          rewrite Hq. specialize (Hp (q' i)). rewrite Hq in Hp.
          rewrite FS_subtract_one in Hp. rewrite Hpq in Hp.
          destruct (order_cases' (subtract_one (q (fin_S i)) r Hqi) r) as
            [[Hqis | Hqis] | Hqis].
          * (* q i - 1 < r *)
            (* contradiction *)
            apply (subtract_one_l) in Hqis.
            destruct Hqis as [Hqis | Hqis]; rewrite Hqi in Hqis; inv Hqis.
          * (* q i - 1 = r *)
            destruct (order_cases' (fin_S i) r) as [[Hi' | Hi'] | Hi'].
            2, 3: rewrite order_fin_S in Hi; rewrite Hi' in Hi; inv Hi.
            rewrite Hp. rewrite not_highest_fin_S. reflexivity.
          * (* q i - 1 > r *)
            destruct (order_cases' (fin_S i) r) as [[Hi' | Hi'] | Hi'].
            2, 3: rewrite order_fin_S in Hi; rewrite Hi' in Hi; inv Hi.
            rewrite Hp. rewrite not_highest_fin_S. reflexivity.
      - (* i = r *)
        destruct (order_cases' (q (FS i)) r) as [[Hqi | Hqi] | Hqi].
        + (* q (i + 1) < r *)
          rewrite Hq. specialize (Hp (q' i)). rewrite Hq in Hp.
          rewrite fin_S_not_highest in Hp. rewrite Hpq in Hp.
          destruct (order_cases' (not_highest (q (FS i)) r Hqi) r) as [[Hqi' | Hqi'] | Hqi'].
          2, 3: erewrite <- order_not_highest_equal in Hqi'; rewrite Hqi in Hqi'; inv Hqi'.
          destruct (order_cases' (FS i) r) as [[Hi' | Hi'] | Hi'].
          1, 2: apply order_e_FS in Hi; rewrite Hi' in Hi; inv Hi.
          rewrite Hp. rewrite subtract_one_FS. reflexivity.
        + (* q (i + 1) = r *)
          destruct (order_cases' (q (q (FS i))) r) as [[Hqqi | Hqqi] | Hqqi].
          * (* q (q (i + 1)) < r *)
            rewrite Hq. specialize (Hp (q' i)). rewrite Hq in Hp.
            rewrite fin_S_not_highest in Hp. do 2 rewrite Hpq in Hp.
            destruct (order_cases' (not_highest (q (q (FS i))) r Hqqi) r) as
              [[Hqqi' | Hqqi'] | Hqqi'].
            2, 3: erewrite <- order_not_highest_equal in Hqqi'; rewrite Hqqi in Hqqi'; inv Hqqi'.
            destruct (order_cases' (q (FS i)) r) as [[Hqi' | Hqi'] | Hqi'].
            1, 3: rewrite Hqi' in Hqi; inv Hqi.
            destruct (order_cases' (FS i) r) as [[Hio | Hio] | Hio].
            { apply order_e_FS in Hi. rewrite Hio in Hi. inv Hi. }
            { contradiction. }
            rewrite Hp. rewrite subtract_one_FS. reflexivity.
          * (* q (q (i + 1)) = r *)
            contradiction.
          * (* q (q (i + 1)) > r *)
            rewrite Hq. specialize (Hp (q' i)). rewrite Hq in Hp.
            rewrite FS_subtract_one in Hp. do 2 rewrite Hpq in Hp.
            destruct (order_cases' (subtract_one (q (q (FS i))) r Hqqi) r) as
              [[Hqqis | Hqqis] | Hqqis].
            -- (* (q (q (i + 1))) - 1 < r *)
              apply (subtract_one_l) in Hqqis.
              destruct Hqqis as [Hqqis | Hqqis]; rewrite Hqqi in Hqqis; inv Hqqis.
            -- (* (q (q (i + 1))) - 1 = r *)
              destruct (order_cases' (q (FS i)) r) as [[Hqi' | Hqi'] | Hqi'].
              1, 3: rewrite Hqi' in Hqi; inv Hqi. clear Hqi'.
              destruct (order_cases' (FS i) r) as [[Hi' | Hi'] | Hi'].
              { apply order_e_FS in Hi. rewrite Hi' in Hi. inv Hi. }
              { contradiction. }
              rewrite Hp. rewrite subtract_one_FS. reflexivity.
            -- (* (q (q (i + 1))) - 1 > r *)
              destruct (order_cases' (q (FS i)) r) as [[Hqi' | Hqi'] | Hqi'].
              1, 3: rewrite Hqi' in Hqi; inv Hqi. clear Hqi'.
              destruct (order_cases' (FS i) r) as [[Hi' | Hi'] | Hi'].
              { apply order_e_FS in Hi. rewrite Hi' in Hi. inv Hi. }
              { contradiction. }
              rewrite Hp. rewrite subtract_one_FS. reflexivity.
        + (* q (i + 1) > r *)
          rewrite Hq. specialize (Hp (q' i)). rewrite Hq in Hp.
          rewrite FS_subtract_one in Hp. rewrite Hpq in Hp.
          destruct (order_cases' (subtract_one (q (FS i)) r Hqi) r) as
            [[Hqis | Hqis] | Hqis].
          * (* (q (i + 1)) - 1 < r *)
            (* contradiction *)
            apply subtract_one_l in Hqis.
            destruct Hqis as [Hqis | Hqis]; rewrite Hqi in Hqis; inv Hqis.
          * (* (q (i + 1)) - 1 = r *)
            destruct (order_cases' (FS i) r) as [[Hi' | Hi'] | Hi'].
            1, 2: apply order_e_FS in Hi; rewrite Hi' in Hi; inv Hi.
            rewrite Hp. rewrite subtract_one_FS. reflexivity.
          * (* (q (i + 1)) - 1 > r *)
            destruct (order_cases' (FS i) r) as [[Hi' | Hi'] | Hi'].
            1, 2: apply order_e_FS in Hi; rewrite Hi' in Hi; inv Hi.
            rewrite Hp. rewrite subtract_one_FS. reflexivity.
      - (* i > r *)
        (* exactly the same as prev case *)
        destruct (order_cases' (q (FS i)) r) as [[Hqi | Hqi] | Hqi].
        + (* q (i + 1) < r *)
          rewrite Hq. specialize (Hp (q' i)). rewrite Hq in Hp.
          rewrite fin_S_not_highest in Hp. rewrite Hpq in Hp.
          destruct (order_cases' (not_highest (q (FS i)) r Hqi) r) as [[Hqi' | Hqi'] | Hqi'].
          2, 3: erewrite <- order_not_highest_equal in Hqi'; rewrite Hqi in Hqi'; inv Hqi'.
          destruct (order_cases' (FS i) r) as [[Hi' | Hi'] | Hi'].
          1, 2: apply order_g_FS in Hi; rewrite Hi' in Hi; inv Hi.
          rewrite Hp. rewrite subtract_one_FS. reflexivity.
        + (* q (i + 1) = r *)
          destruct (order_cases' (q (q (FS i))) r) as [[Hqqi | Hqqi] | Hqqi].
          * (* q (q (i + 1)) < r *)
            rewrite Hq. specialize (Hp (q' i)). rewrite Hq in Hp.
            rewrite fin_S_not_highest in Hp. do 2 rewrite Hpq in Hp.
            destruct (order_cases' (not_highest (q (q (FS i))) r Hqqi) r) as
              [[Hqqi' | Hqqi'] | Hqqi'].
            2, 3: erewrite <- order_not_highest_equal in Hqqi'; rewrite Hqqi in Hqqi'; inv Hqqi'.
            destruct (order_cases' (q (FS i)) r) as [[Hqi' | Hqi'] | Hqi'].
            1, 3: rewrite Hqi' in Hqi; inv Hqi.
            destruct (order_cases' (FS i) r) as [[Hio | Hio] | Hio].
            { apply order_g_FS in Hi. rewrite Hio in Hi. inv Hi. }
            { contradiction. }
            rewrite Hp. rewrite subtract_one_FS. reflexivity.
          * (* q (q (i + 1)) = r *)
            contradiction.
          * (* q (q (i + 1)) > r *)
            rewrite Hq. specialize (Hp (q' i)). rewrite Hq in Hp.
            rewrite FS_subtract_one in Hp. do 2 rewrite Hpq in Hp.
            destruct (order_cases' (subtract_one (q (q (FS i))) r Hqqi) r) as
              [[Hqqis | Hqqis] | Hqqis].
            -- (* (q (q (i + 1))) - 1 < r *)
              apply (subtract_one_l) in Hqqis.
              destruct Hqqis as [Hqqis | Hqqis]; rewrite Hqqi in Hqqis; inv Hqqis.
            -- (* (q (q (i + 1))) - 1 = r *)
              destruct (order_cases' (q (FS i)) r) as [[Hqi' | Hqi'] | Hqi'].
              1, 3: rewrite Hqi' in Hqi; inv Hqi. clear Hqi'.
              destruct (order_cases' (FS i) r) as [[Hi' | Hi'] | Hi'].
              { apply order_g_FS in Hi. rewrite Hi' in Hi. inv Hi. }
              { contradiction. }
              rewrite Hp. rewrite subtract_one_FS. reflexivity.
            -- (* (q (q (i + 1))) - 1 > r *)
              destruct (order_cases' (q (FS i)) r) as [[Hqi' | Hqi'] | Hqi'].
              1, 3: rewrite Hqi' in Hqi; inv Hqi. clear Hqi'.
              destruct (order_cases' (FS i) r) as [[Hi' | Hi'] | Hi'].
              { apply order_g_FS in Hi. rewrite Hi' in Hi. inv Hi. }
              { contradiction. }
              rewrite Hp. rewrite subtract_one_FS. reflexivity.
        + (* q (i + 1) > r *)
          rewrite Hq. specialize (Hp (q' i)). rewrite Hq in Hp.
          rewrite FS_subtract_one in Hp. rewrite Hpq in Hp.
          destruct (order_cases' (subtract_one (q (FS i)) r Hqi) r) as
            [[Hqis | Hqis] | Hqis].
          * (* (q (i + 1)) - 1 < r *)
            (* contradiction *)
            apply subtract_one_l in Hqis.
            destruct Hqis as [Hqis | Hqis]; rewrite Hqi in Hqis; inv Hqis.
          * (* (q (i + 1)) - 1 = r *)
            destruct (order_cases' (FS i) r) as [[Hi' | Hi'] | Hi'].
            1, 2: apply order_g_FS in Hi; rewrite Hi' in Hi; inv Hi.
            rewrite Hp. rewrite subtract_one_FS. reflexivity.
          * (* (q (i + 1)) - 1 > r *)
            destruct (order_cases' (FS i) r) as [[Hi' | Hi'] | Hi'].
            1, 2: apply order_g_FS in Hi; rewrite Hi' in Hi; inv Hi.
            rewrite Hp. rewrite subtract_one_FS. reflexivity.
    }
    {
      intro i.
      specialize (Hp i).
      destruct (order_cases' i r) as [[Hi | Hi] | Hi].
      - (* i < r *)
        destruct (order_cases' (p (fin_S i)) r) as [[Hpi | Hpi] | Hpi].
        + (* p i < r *)
          rewrite Hp. specialize (Hq (p' i)). rewrite Hp in Hq.
          rewrite fin_S_not_highest in Hq. rewrite Hqp in Hq.
          destruct (order_cases' (not_highest (p (fin_S i)) r Hpi) r) as [[Hpi' | Hpi'] | Hpi'].
          2, 3: erewrite <- order_not_highest_equal in Hpi'; rewrite Hpi in Hpi'; inv Hpi'.
          destruct (order_cases' (fin_S i) r) as [[Hi' | Hi'] | Hi'].
          2, 3: rewrite order_fin_S in Hi; rewrite Hi' in Hi; inv Hi.
          rewrite Hq. rewrite not_highest_fin_S. reflexivity.
        + (* p i = r, so we apply p again *)
          destruct (order_cases' (p (p (fin_S i))) r) as [[Hppi | Hppi] | Hppi].
          * (* p (p i) < r *)
            rewrite Hp. specialize (Hq (p' i)). rewrite Hp in Hq.
            rewrite fin_S_not_highest in Hq. do 2 rewrite Hqp in Hq.
            destruct (order_cases' (not_highest (p (p (fin_S i))) r Hppi) r) as
              [[Hppi' | Hppi'] | Hppi'].
            2, 3: erewrite <- order_not_highest_equal in Hppi'; rewrite Hppi in Hppi'; inv Hppi'.
            destruct (order_cases' (p (fin_S i)) r) as [[Hpi' | Hpi'] | Hpi'].
            1, 3: rewrite Hpi' in Hpi; inv Hpi.
            destruct (order_cases' (fin_S i) r) as [[Hi' | Hi'] | Hi'].
            2, 3: rewrite order_fin_S in Hi; rewrite Hi' in Hi; inv Hi.
            rewrite Hq. rewrite not_highest_fin_S. reflexivity.
          * (* p (p i) = r *)
            contradiction.
          * (* p (p i) > r *)
            rewrite Hp. specialize (Hq (p' i)). rewrite Hp in Hq.
            rewrite FS_subtract_one in Hq. do 2 rewrite Hqp in Hq.
            destruct (order_cases' (subtract_one (p (p (fin_S i))) r Hppi) r) as
              [[Hppis | Hppis] | Hppis].
            -- (* p (p i) - 1 < r *)
              (* contradiction *)
              apply (subtract_one_l) in Hppis.
              destruct Hppis as [Hppis | Hppis]; rewrite Hppi in Hppis; inv Hppis.
            -- (* p (p i) - 1 = r *)
              destruct (order_cases' (p (fin_S i)) r) as [[Hpi' | Hpi'] | Hpi'].
              1, 3: rewrite Hpi' in Hpi; inv Hpi. clear Hpi'.
              destruct (order_cases' (fin_S i) r) as [[Hi' | Hi'] | Hi'].
              2, 3: rewrite order_fin_S in Hi; rewrite Hi' in Hi; inv Hi.
              rewrite Hq. rewrite not_highest_fin_S. reflexivity.
            -- (* p (p i) - 1 > r, same as above *)
              destruct (order_cases' (p (fin_S i)) r) as [[Hpi' | Hpi'] | Hpi'].
              1, 3: rewrite Hpi' in Hpi; inv Hpi. clear Hpi'.
              destruct (order_cases' (fin_S i) r) as [[Hi' | Hi'] | Hi'].
              2, 3: rewrite order_fin_S in Hi; rewrite Hi' in Hi; inv Hi.
              rewrite Hq. rewrite not_highest_fin_S. reflexivity.
        + (* p i > r *)
          rewrite Hp. specialize (Hq (p' i)). rewrite Hp in Hq.
          rewrite FS_subtract_one in Hq. rewrite Hqp in Hq.
          destruct (order_cases' (subtract_one (p (fin_S i)) r Hpi) r) as
            [[Hpis | Hpis] | Hpis].
          * (* p i - 1 < r *)
            (* contradiction *)
            apply (subtract_one_l) in Hpis.
            destruct Hpis as [Hpis | Hpis]; rewrite Hpi in Hpis; inv Hpis.
          * (* p i - 1 = r *)
            destruct (order_cases' (fin_S i) r) as [[Hi' | Hi'] | Hi'].
            2, 3: rewrite order_fin_S in Hi; rewrite Hi' in Hi; inv Hi.
            rewrite Hq. rewrite not_highest_fin_S. reflexivity.
          * (* p i - 1 > r *)
            destruct (order_cases' (fin_S i) r) as [[Hi' | Hi'] | Hi'].
            2, 3: rewrite order_fin_S in Hi; rewrite Hi' in Hi; inv Hi.
            rewrite Hq. rewrite not_highest_fin_S. reflexivity.
      - (* i = r *)
        destruct (order_cases' (p (FS i)) r) as [[Hpi | Hpi] | Hpi].
        + (* p (i + 1) < r *)
          rewrite Hp. specialize (Hq (p' i)). rewrite Hp in Hq.
          rewrite fin_S_not_highest in Hq. rewrite Hqp in Hq.
          destruct (order_cases' (not_highest (p (FS i)) r Hpi) r) as [[Hpi' | Hpi'] | Hpi'].
          2, 3: erewrite <- order_not_highest_equal in Hpi'; rewrite Hpi in Hpi'; inv Hpi'.
          destruct (order_cases' (FS i) r) as [[Hi' | Hi'] | Hi'].
          1, 2: apply order_e_FS in Hi; rewrite Hi' in Hi; inv Hi.
          rewrite Hq. rewrite subtract_one_FS. reflexivity.
        + (* p (i + 1) = r *)
          destruct (order_cases' (p (p (FS i))) r) as [[Hppi | Hppi] | Hppi].
          * (* p (p (i + 1)) < r *)
            rewrite Hp. specialize (Hq (p' i)). rewrite Hp in Hq.
            rewrite fin_S_not_highest in Hq. do 2 rewrite Hqp in Hq.
            destruct (order_cases' (not_highest (p (p (FS i))) r Hppi) r) as
              [[Hppi' | Hppi'] | Hppi'].
            2, 3: erewrite <- order_not_highest_equal in Hppi'; rewrite Hppi in Hppi'; inv Hppi'.
            destruct (order_cases' (p (FS i)) r) as [[Hpi' | Hpi'] | Hpi'].
            1, 3: rewrite Hpi' in Hpi; inv Hpi.
            destruct (order_cases' (FS i) r) as [[Hio | Hio] | Hio].
            { apply order_e_FS in Hi. rewrite Hio in Hi. inv Hi. }
            { contradiction. }
            rewrite Hq. rewrite subtract_one_FS. reflexivity.
          * (* p (p (i + 1)) = r *)
            contradiction.
          * (* p (p (i + 1)) > r *)
            rewrite Hp. specialize (Hq (p' i)). rewrite Hp in Hq.
            rewrite FS_subtract_one in Hq. do 2 rewrite Hqp in Hq.
            destruct (order_cases' (subtract_one (p (p (FS i))) r Hppi) r) as
              [[Hppis | Hppis] | Hppis].
            -- (* (p (p (i + 1))) - 1 < r *)
              apply (subtract_one_l) in Hppis.
              destruct Hppis as [Hppis | Hppis]; rewrite Hppi in Hppis; inv Hppis.
            -- (* (p (p (i + 1))) - 1 = r *)
              destruct (order_cases' (p (FS i)) r) as [[Hpi' | Hpi'] | Hpi'].
              1, 3: rewrite Hpi' in Hpi; inv Hpi. clear Hpi'.
              destruct (order_cases' (FS i) r) as [[Hi' | Hi'] | Hi'].
              { apply order_e_FS in Hi. rewrite Hi' in Hi. inv Hi. }
              { contradiction. }
              rewrite Hq. rewrite subtract_one_FS. reflexivity.
            -- (* (p (p (i + 1))) - 1 > r *)
              destruct (order_cases' (p (FS i)) r) as [[Hpi' | Hpi'] | Hpi'].
              1, 3: rewrite Hpi' in Hpi; inv Hpi. clear Hpi'.
              destruct (order_cases' (FS i) r) as [[Hi' | Hi'] | Hi'].
              { apply order_e_FS in Hi. rewrite Hi' in Hi. inv Hi. }
              { contradiction. }
              rewrite Hq. rewrite subtract_one_FS. reflexivity.
        + (* p (i + 1) > r *)
          rewrite Hp. specialize (Hq (p' i)). rewrite Hp in Hq.
          rewrite FS_subtract_one in Hq. rewrite Hqp in Hq.
          destruct (order_cases' (subtract_one (p (FS i)) r Hpi) r) as
            [[Hpis | Hpis] | Hpis].
          * (* (p (i + 1)) - 1 < r *)
            (* contradiction *)
            apply subtract_one_l in Hpis.
            destruct Hpis as [Hpis | Hpis]; rewrite Hpi in Hpis; inv Hpis.
          * (* (p (i + 1)) - 1 = r *)
            destruct (order_cases' (FS i) r) as [[Hi' | Hi'] | Hi'].
            1, 2: apply order_e_FS in Hi; rewrite Hi' in Hi; inv Hi.
            rewrite Hq. rewrite subtract_one_FS. reflexivity.
          * (* (p (i + 1)) - 1 > r *)
            destruct (order_cases' (FS i) r) as [[Hi' | Hi'] | Hi'].
            1, 2: apply order_e_FS in Hi; rewrite Hi' in Hi; inv Hi.
            rewrite Hq. rewrite subtract_one_FS. reflexivity.
      - (* i > r *)
        (* exactly the same as prev case *)
        destruct (order_cases' (p (FS i)) r) as [[Hpi | Hpi] | Hpi].
        + (* p (i + 1) < r *)
          rewrite Hp. specialize (Hq (p' i)). rewrite Hp in Hq.
          rewrite fin_S_not_highest in Hq. rewrite Hqp in Hq.
          destruct (order_cases' (not_highest (p (FS i)) r Hpi) r) as [[Hpi' | Hpi'] | Hpi'].
          2, 3: erewrite <- order_not_highest_equal in Hpi'; rewrite Hpi in Hpi'; inv Hpi'.
          destruct (order_cases' (FS i) r) as [[Hi' | Hi'] | Hi'].
          1, 2: apply order_g_FS in Hi; rewrite Hi' in Hi; inv Hi.
          rewrite Hq. rewrite subtract_one_FS. reflexivity.
        + (* p (i + 1) = r *)
          destruct (order_cases' (p (p (FS i))) r) as [[Hppi | Hppi] | Hppi].
          * (* p (p (i + 1)) < r *)
            rewrite Hp. specialize (Hq (p' i)). rewrite Hp in Hq.
            rewrite fin_S_not_highest in Hq. do 2 rewrite Hqp in Hq.
            destruct (order_cases' (not_highest (p (p (FS i))) r Hppi) r) as
              [[Hppi' | Hppi'] | Hppi'].
            2, 3: erewrite <- order_not_highest_equal in Hppi'; rewrite Hppi in Hppi'; inv Hppi'.
            destruct (order_cases' (p (FS i)) r) as [[Hpi' | Hpi'] | Hpi'].
            1, 3: rewrite Hpi' in Hpi; inv Hpi.
            destruct (order_cases' (FS i) r) as [[Hio | Hio] | Hio].
            { apply order_g_FS in Hi. rewrite Hio in Hi. inv Hi. }
            { contradiction. }
            rewrite Hq. rewrite subtract_one_FS. reflexivity.
          * (* p (p (i + 1)) = r *)
            contradiction.
          * (* p (p (i + 1)) > r *)
            rewrite Hp. specialize (Hq (p' i)). rewrite Hp in Hq.
            rewrite FS_subtract_one in Hq. do 2 rewrite Hqp in Hq.
            destruct (order_cases' (subtract_one (p (p (FS i))) r Hppi) r) as
              [[Hppis | Hppis] | Hppis].
            -- (* (p (p (i + 1))) - 1 < r *)
              apply (subtract_one_l) in Hppis.
              destruct Hppis as [Hppis | Hppis]; rewrite Hppi in Hppis; inv Hppis.
            -- (* (p (p (i + 1))) - 1 = r *)
              destruct (order_cases' (p (FS i)) r) as [[Hpi' | Hpi'] | Hpi'].
              1, 3: rewrite Hpi' in Hpi; inv Hpi. clear Hpi'.
              destruct (order_cases' (FS i) r) as [[Hi' | Hi'] | Hi'].
              { apply order_g_FS in Hi. rewrite Hi' in Hi. inv Hi. }
              { contradiction. }
              rewrite Hq. rewrite subtract_one_FS. reflexivity.
            -- (* (p (p (i + 1))) - 1 > r *)
              destruct (order_cases' (p (FS i)) r) as [[Hpi' | Hpi'] | Hpi'].
              1, 3: rewrite Hpi' in Hpi; inv Hpi. clear Hpi'.
              destruct (order_cases' (FS i) r) as [[Hi' | Hi'] | Hi'].
              { apply order_g_FS in Hi. rewrite Hi' in Hi. inv Hi. }
              { contradiction. }
              rewrite Hq. rewrite subtract_one_FS. reflexivity.
        + (* p (i + 1) > r *)
          rewrite Hp. specialize (Hq (p' i)). rewrite Hp in Hq.
          rewrite FS_subtract_one in Hq. rewrite Hqp in Hq.
          destruct (order_cases' (subtract_one (p (FS i)) r Hpi) r) as
            [[Hpis | Hpis] | Hpis].
          * (* (p (i + 1)) - 1 < r *)
            (* contradiction *)
            apply subtract_one_l in Hpis.
            destruct Hpis as [Hpis | Hpis]; rewrite Hpi in Hpis; inv Hpis.
          * (* (p (i + 1)) - 1 = r *)
            destruct (order_cases' (FS i) r) as [[Hi' | Hi'] | Hi'].
            1, 2: apply order_g_FS in Hi; rewrite Hi' in Hi; inv Hi.
            rewrite Hq. rewrite subtract_one_FS. reflexivity.
          * (* (p (i + 1)) - 1 > r *)
            destruct (order_cases' (FS i) r) as [[Hi' | Hi'] | Hi'].
            1, 2: apply order_g_FS in Hi; rewrite Hi' in Hi; inv Hi.
            rewrite Hq. rewrite subtract_one_FS. reflexivity.
    }
  Qed.
*)

  Lemma remove_at_permutation_correct' {n} (p q : fin (S (S n)) -> fin (S (S n))) r
        (Hpq : forall i, p (q i) = i)
        (Hqp : forall i, q (p i) = i)
        Hinjp Hinjq :
    let p' := projT1 (remove_at_permutation p r Hinjp) in
    let q' := projT1 (remove_at_permutation q (p r) Hinjq) in
    (forall i, p' (q' i) = i) /\ (forall i, q' (p' i) = i).
  Proof.
    destruct (remove_at_permutation p r _) as (p' & Hp).
    destruct (remove_at_permutation q (p r) _) as (q' & Hq).
    cbn in *. split.
    {
      intro i.
      specialize (Hq i). rewrite Hqp in Hq.
      cases i (p r) Hi.
      - (* i < p r *)
        cases (q (fin_S i)) r Hqi; try contradiction.
        + (* q i < r *)
          specialize (Hp (q' i)). rewrite Hq in *.
          rewrite fin_S_not_highest, Hpq in Hp.
          cases (not_highest (q (fin_S i)) r Hqi) r Hqi'.
          2, 3: rewrite <- order_not_highest in Hqi'; rewrite Hqi in Hqi'; inv Hqi'.
          cases (fin_S i) (p r) Hi'.
          2, 3: rewrite order_fin_S in Hi; rewrite Hi' in Hi; inv Hi.
          rewrite Hp. rewrite not_highest_fin_S. reflexivity.
        + (* q i > r *)
          specialize (Hp (q' i)). rewrite Hq in *.
          rewrite FS_subtract_one in Hp. rewrite Hpq in Hp.
          cases (subtract_one (q (fin_S i)) r Hqi) r Hqi'.
          1: { (* q i - 1 < r not possible *)
            pose proof Hqi as Hqi''. eapply order_subtract_one_GT_inv in Hqi''.
            destruct Hqi'' as [Hqi'' | Hqi'']; rewrite Hqi' in Hqi''; inv Hqi''.
          }
          * (* q i - 1 = r *)
            cases (fin_S i) (p r) Hi'.
            2, 3: rewrite order_fin_S in Hi; rewrite Hi' in Hi; inv Hi.
            rewrite Hp. rewrite not_highest_fin_S. reflexivity.
          * (* q i - 1 > r *)
            cases (fin_S i) (p r) Hi'.
            2, 3: rewrite order_fin_S in Hi; rewrite Hi' in Hi; inv Hi.
            rewrite Hp. rewrite not_highest_fin_S. reflexivity.
      - (* i = p r *)
        cases (q (FS i)) r Hqi; try contradiction.
        + (* q (i + 1) < r *)
          specialize (Hp (q' i)). rewrite Hq in *.
          rewrite fin_S_not_highest, Hpq in Hp.
          cases (not_highest (q (FS i)) r Hqi) r Hqi'.
          2, 3: rewrite <- order_not_highest in Hqi'; rewrite Hqi in Hqi'; inv Hqi'.
          cases (FS i) (p r) Hi'; try contradiction.
          1: { (* i + 1 < p r is not possible *)
            rewrite order_fin_S in Hi. apply order_eq in Hi. pose proof Hi' as Hi''.
            rewrite <- Hi in Hi''. rewrite order_flip in Hi''. rewrite <- order_fin_S in Hi''.
            rewrite order_FS_LT in Hi''. inv Hi''.
          }
          (* i + 1 > p r *)
          rewrite Hp. rewrite subtract_one_FS. reflexivity.
        + (* q (i + 1) > r *)
          specialize (Hp (q' i)). rewrite Hq in *.
          rewrite FS_subtract_one, Hpq in Hp.
          cases (subtract_one (q (FS i)) r Hqi) r Hqi'.
          1: { (* q (i + 1) - 1 < r not possible *)
            apply order_subtract_one_LT_inv in Hqi'.
            destruct Hqi' as [Hqi' | Hqi']; rewrite Hqi in Hqi'; inv Hqi'.
          }
          * (* q (i + 1) - 1 = r *)
            cases (FS i) (p r) Hi'; try contradiction.
            1: { (* i + 1 < p r not possible *)
              rewrite order_fin_S in Hi. apply order_eq in Hi. pose proof Hi' as Hi''.
              rewrite <- Hi in Hi''. rewrite order_flip in Hi''.
              rewrite <- order_fin_S in Hi''. rewrite order_FS_LT in Hi''. inv Hi''.
            }
            (* i + 1 > p r *)
            rewrite Hp. rewrite subtract_one_FS. reflexivity.
          * (* q (i + 1) - 1 > r *)
            cases (FS i) (p r) Hi'; try contradiction.
            1: { (* i + 1 < p r not possible *)
              rewrite order_fin_S in Hi. apply order_eq in Hi. pose proof Hi' as Hi''.
              rewrite <- Hi in Hi''. rewrite order_flip in Hi''.
              rewrite <- order_fin_S in Hi''. rewrite order_FS_LT in Hi''. inv Hi''.
            }
            (* i + 1 > p r *)
            rewrite Hp. rewrite subtract_one_FS. reflexivity.
      - (* i > p r *)
        cases (q (FS i)) r Hqi; try contradiction.
        + (* q (i + 1) < r *)
          specialize (Hp (q' i)). rewrite Hq in *.
          rewrite fin_S_not_highest, Hpq in Hp.
          cases (not_highest (q (FS i)) r Hqi) r Hqi'.
          2, 3: rewrite <- order_not_highest in Hqi'; rewrite Hqi in Hqi'; inv Hqi'.
          cases (FS i) (p r) Hi'; try contradiction.
          1: { (* i + 1 < p r is not possible *)
            pose proof Hi' as Hi''. apply order_flip in Hi''.
            apply order_GT_FS in Hi''. cbn in Hi''.
            pose proof (order_transitive _ _ _ _ Hi Hi'').
            rewrite order_reflexive in H. inv H.
          }
          (* i + 1 > p r *)
          rewrite Hp. rewrite subtract_one_FS. reflexivity.
        + (* q (i + 1) > r *)
          specialize (Hp (q' i)). rewrite Hq in *.
          rewrite FS_subtract_one, Hpq in Hp.
          cases (subtract_one (q (FS i)) r Hqi) r Hqi'.
          1: { (* q (i + 1) - 1 < r not possible *)
            apply order_subtract_one_LT_inv in Hqi'.
            destruct Hqi' as [Hqi' | Hqi']; rewrite Hqi in Hqi'; inv Hqi'.
          }
          * (* q (i + 1) - 1 = r *)
            cases (FS i) (p r) Hi'; try contradiction.
            1: { (* i + 1 < p r not possible *)
              pose proof Hi' as Hi''. apply order_flip in Hi''.
              apply order_GT_FS in Hi''. cbn in Hi''.
              pose proof (order_transitive _ _ _ _ Hi Hi'').
              rewrite order_reflexive in H. inv H.
            }
            (* i + 1 > p r *)
            rewrite Hp. rewrite subtract_one_FS. reflexivity.
          * (* q (i + 1) - 1 > r *)
            cases (FS i) (p r) Hi'; try contradiction.
            1: { (* i + 1 < p r not possible *)
              pose proof Hi' as Hi''. apply order_flip in Hi''.
              apply order_GT_FS in Hi''. cbn in Hi''.
              pose proof (order_transitive _ _ _ _ Hi Hi'').
              rewrite order_reflexive in H. inv H.
            }
            (* i + 1 > p r *)
            rewrite Hp. rewrite subtract_one_FS. reflexivity.
    }
    {
      intro i.
      specialize (Hp i).
      cases i r Hi.
      - (* i < r *)
        cases (p (fin_S i)) (p r) Hpi; try contradiction.
        + (* p i < p r *)
          specialize (Hq (p' i)). rewrite Hp in *.
          rewrite fin_S_not_highest in Hq. do 2 rewrite Hqp in Hq.
          cases (not_highest (p (fin_S i)) (p r) Hpi) (p r) Hpi'.
          2, 3: rewrite <- order_not_highest in Hpi'; rewrite Hpi in Hpi'; inv Hpi'.
          cases (fin_S i) r Hi'.
          2, 3: rewrite order_fin_S in Hi; rewrite Hi' in Hi; inv Hi.
          rewrite Hq. rewrite not_highest_fin_S. reflexivity.
        + (* p i > p r *)
          specialize (Hq (p' i)). rewrite Hp in *.
          rewrite FS_subtract_one in Hq. do 2 rewrite Hqp in Hq.
          cases (subtract_one (p (fin_S i)) (p r) Hpi) (p r) Hpi'.
          1: { (* p i - 1 < p r not possible *)
            pose proof Hpi as Hpi''. eapply order_subtract_one_GT_inv in Hpi''.
            destruct Hpi'' as [Hpi'' | Hpi'']; rewrite Hpi' in Hpi''; inv Hpi''.
          }
          * (* p i - 1 = r *)
            cases (fin_S i) r Hi'.
            2, 3: rewrite order_fin_S in Hi; rewrite Hi' in Hi; inv Hi.
            rewrite Hq. rewrite not_highest_fin_S. reflexivity.
          * (* p i - 1 > r *)
            cases (fin_S i) r Hi'.
            2, 3: rewrite order_fin_S in Hi; rewrite Hi' in Hi; inv Hi.
            rewrite Hq. rewrite not_highest_fin_S. reflexivity.
      - (* i = r *)
        cases (p (FS i)) (p r) Hpi; try contradiction.
        + (* p (i + 1) < p r *)
          specialize (Hq (p' i)). rewrite Hp in *.
          rewrite fin_S_not_highest in Hq. do 2 rewrite Hqp in Hq.
          cases (not_highest (p (FS i)) (p r) Hpi) (p r) Hpi'.
          2, 3: rewrite <- order_not_highest in Hpi'; rewrite Hpi in Hpi'; inv Hpi'.
          cases (FS i) r Hi'; try contradiction.
          1: { (* i + 1 < r is not possible *)
            rewrite order_fin_S in Hi. apply order_eq in Hi. pose proof Hi' as Hi''.
            rewrite <- Hi in Hi''. rewrite order_flip in Hi''. rewrite <- order_fin_S in Hi''.
            rewrite order_FS_LT in Hi''. inv Hi''.
          }
          (* i + 1 > r *)
          rewrite Hq. rewrite subtract_one_FS. reflexivity.
        + (* p (i + 1) > r *)
          specialize (Hq (p' i)). rewrite Hp in *.
          rewrite FS_subtract_one in Hq. do 2 rewrite Hqp in Hq.
          cases (subtract_one (p (FS i)) (p r) Hpi) (p r) Hpi'.
          1: { (* p (i + 1) - 1 < p r not possible *)
            apply order_subtract_one_LT_inv in Hpi'.
            destruct Hpi' as [Hpi' | Hpi']; rewrite Hpi in Hpi'; inv Hpi'.
          }
          * (* p (i + 1) - 1 = p r *)
            cases (FS i) r Hi'; try contradiction.
            1: { (* i + 1 < r not possible *)
              rewrite order_fin_S in Hi. apply order_eq in Hi. pose proof Hi' as Hi''.
              rewrite <- Hi in Hi''. rewrite order_flip in Hi''.
              rewrite <- order_fin_S in Hi''. rewrite order_FS_LT in Hi''. inv Hi''.
            }
            (* i + 1 > r *)
            rewrite Hq. rewrite subtract_one_FS. reflexivity.
          * (* p (i + 1) - 1 > p r *)
            cases (FS i) r Hi'; try contradiction.
            1: { (* i + 1 < r not possible *)
              rewrite order_fin_S in Hi. apply order_eq in Hi. pose proof Hi' as Hi''.
              rewrite <- Hi in Hi''. rewrite order_flip in Hi''.
              rewrite <- order_fin_S in Hi''. rewrite order_FS_LT in Hi''. inv Hi''.
            }
            (* i + 1 > r *)
            rewrite Hq. rewrite subtract_one_FS. reflexivity.
      - (* i > r *)
        cases (p (FS i)) (p r) Hpi; try contradiction.
        + (* p (i + 1) < p r *)
          specialize (Hq (p' i)). rewrite Hp in *.
          rewrite fin_S_not_highest in Hq. do 2 rewrite Hqp in Hq.
          cases (not_highest (p (FS i)) (p r) Hpi) (p r) Hpi'.
          2, 3: rewrite <- order_not_highest in Hpi'; rewrite Hpi in Hpi'; inv Hpi'.
          cases (FS i) r Hi'; try contradiction.
          1: { (* i + 1 < r is not possible *)
            pose proof Hi' as Hi''. apply order_flip in Hi''.
            apply order_GT_FS in Hi''. cbn in Hi''.
            pose proof (order_transitive _ _ _ _ Hi Hi'').
            rewrite order_reflexive in H. inv H.
          }
          (* i + 1 > r *)
          rewrite Hq. rewrite subtract_one_FS. reflexivity.
        + (* p (i + 1) > p r *)
          specialize (Hq (p' i)). rewrite Hp in *.
          rewrite FS_subtract_one in Hq. do 2 rewrite Hqp in Hq.
          cases (subtract_one (p (FS i)) (p r) Hpi) (p r) Hpi'.
          1: { (* p (i + 1) - 1 < p r not possible *)
            apply order_subtract_one_LT_inv in Hpi'.
            destruct Hpi' as [Hpi' | Hpi']; rewrite Hpi in Hpi'; inv Hpi'.
          }
          * (* p (i + 1) - 1 = p r *)
            cases (FS i) r Hi'; try contradiction.
            1: { (* i + 1 < r not possible *)
              pose proof Hi' as Hi''. apply order_flip in Hi''.
              apply order_GT_FS in Hi''. cbn in Hi''.
              pose proof (order_transitive _ _ _ _ Hi Hi'').
              rewrite order_reflexive in H. inv H.
            }
            (* i + 1 > r *)
            rewrite Hq. rewrite subtract_one_FS. reflexivity.
          * (* p (i + 1) - 1 > p r *)
            cases (FS i) r Hi'; try contradiction.
            1: { (* i + 1 < r not possible *)
              pose proof Hi' as Hi''. apply order_flip in Hi''.
              apply order_GT_FS in Hi''. cbn in Hi''.
              pose proof (order_transitive _ _ _ _ Hi Hi'').
              rewrite order_reflexive in H. inv H.
            }
            (* i + 1 > r *)
            rewrite Hq. rewrite subtract_one_FS. reflexivity.
    }
  Qed.

  Lemma remove_at_permutation_vectors {n} (v1 v2 : vec (S (S n))) i p q Hp Hq p' q'
        (Hp' : p' = projT1 (remove_at_permutation p i Hp))
        (Hq' : q' = projT1 (remove_at_permutation q (p i) Hq))
        (Hpq : forall i, p (q i) = i)
        (Hqp : forall i, q (p i) = i)
        (Hpq' : forall i, p' (q' i) = i)
        (Hqp' : forall i, q' (p' i) = i)
        (Hsb1 : forall i, v1 i ~ v2 (p i))
        (Hsb2 : forall i, v2 i ~ v1 (q i)) :
    (forall j, remove_vec v1 i j ~ remove_vec v2 (p i) (p' j)) /\
    (forall j, remove_vec v2 (p i) j ~ remove_vec v1 i (q' j)).
  Proof.
    split; intros j.
    {
      subst. destruct (remove_at_permutation p) as (p' & Hp'). cbn in *.
      destruct (remove_at_permutation q) as (q' & Hq'). cbn in *. clear Hq'.
      specialize (Hp' j).
      cases j i Hj.
      - (* j < i *)
        rewrite <- remove_vec_index_before'; auto.
        cases (p (fin_S j)) (p i) Hpj; try contradiction.
        + (* p j < p i *)
          rewrite <- remove_vec_index_before'; rewrite Hp'.
          2: rewrite <- order_not_highest; auto.
          rewrite fin_S_not_highest. auto.
        + (* p j > p i *)
          pose proof Hpj as Hpj'.
          apply (order_subtract_one_GT_inv _ _ _ Hpj) in Hpj'.
          destruct Hpj'; [rewrite <- remove_vec_index_eq' | rewrite <- remove_vec_index_after'];
            rewrite Hp'; auto; rewrite FS_subtract_one; auto.
      - (* j = i *)
        rewrite <- remove_vec_index_eq'; auto.
        cases (p (FS j)) (p i) Hpj; try contradiction.
        + (* p (j + 1) < p i *)
          rewrite <- remove_vec_index_before'; rewrite Hp'.
          2: rewrite <- order_not_highest; auto.
          rewrite fin_S_not_highest. auto.
        + (* p (j + 1) > p i *)
          pose proof Hpj as Hpj'.
          apply (order_subtract_one_GT_inv _ _ _ Hpj) in Hpj'.
          destruct Hpj'; [rewrite <- remove_vec_index_eq' | rewrite <- remove_vec_index_after'];
            rewrite Hp'; auto; rewrite FS_subtract_one; auto.
      - (* j > i *)
        rewrite <- remove_vec_index_after'; auto.
        cases (p (FS j)) (p i) Hpj; try contradiction.
        + (* p (j + 1) < p i *)
          rewrite <- remove_vec_index_before'; rewrite Hp'.
          2: rewrite <- order_not_highest; auto.
          rewrite fin_S_not_highest. auto.
        + (* p (j + 1) > p i *)
          pose proof Hpj as Hpj'.
          apply (order_subtract_one_GT_inv _ _ _ Hpj) in Hpj'.
          destruct Hpj'; [rewrite <- remove_vec_index_eq' | rewrite <- remove_vec_index_after'];
            rewrite Hp'; auto; rewrite FS_subtract_one; auto.
    }
    {
      subst. destruct (remove_at_permutation p) as (p' & Hp'). cbn in *. clear Hp'.
      destruct (remove_at_permutation q) as (q' & Hq'). cbn in *.
      specialize (Hq' j). rewrite Hqp in Hq'.
      cases j (p i) Hj.
      - (* j < p i *)
        rewrite <- remove_vec_index_before'; auto.
        cases (q (fin_S j)) i Hqj; try contradiction.
        + (* q j < i *)
          rewrite <- remove_vec_index_before'; rewrite Hq'.
          2: rewrite <- order_not_highest; auto.
          rewrite fin_S_not_highest. auto.
        + (* q j > i *)
          pose proof Hqj as Hqj'.
          apply (order_subtract_one_GT_inv _ _ _ Hqj) in Hqj'.
          destruct Hqj'; [rewrite <- remove_vec_index_eq' | rewrite <- remove_vec_index_after'];
            rewrite Hq'; auto; rewrite FS_subtract_one; auto.
      - (* j = p i *)
        rewrite <- remove_vec_index_eq'; auto.
        cases (q (FS j)) i Hqj; try contradiction.
        + (* q (j + 1) < i *)
          rewrite <- remove_vec_index_before'; rewrite Hq'.
          2: rewrite <- order_not_highest; auto.
          rewrite fin_S_not_highest. auto.
        + (* q (j + 1) > i *)
          pose proof Hqj as Hqj'.
          apply (order_subtract_one_GT_inv _ _ _ Hqj) in Hqj'.
          destruct Hqj'; [rewrite <- remove_vec_index_eq' | rewrite <- remove_vec_index_after'];
            rewrite Hq'; auto; rewrite FS_subtract_one; auto.
      - (* j > p i *)
        rewrite <- remove_vec_index_after'; auto.
        cases (q (FS j)) i Hqj; try contradiction.
        + (* q (j + 1) < i *)
          rewrite <- remove_vec_index_before'; rewrite Hq'.
          2: rewrite <- order_not_highest; auto.
          rewrite fin_S_not_highest. auto.
        + (* q (j + 1) > i *)
          pose proof Hqj as Hqj'.
          apply (order_subtract_one_GT_inv _ _ _ Hqj) in Hqj'.
          destruct Hqj'; [rewrite <- remove_vec_index_eq' | rewrite <- remove_vec_index_after'];
            rewrite Hq'; auto; rewrite FS_subtract_one; auto.
    }
  Qed.

  Lemma schedule_permutation n (v1 v2 : vec n) i (p q : fin n -> fin n)
        (Hbound1 : forall i, choiceI_bound 1 (v1 i))
        (Hbound2 : forall i, choiceI_bound 1 (v2 i))
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
      decompose [or] Ht; clear Ht.
      + (* thread is finished *)
        assert (Hinjp : Injective p) by (eapply bijective_injective; eauto).
        assert (Hinjq : Injective q) by (eapply bijective_injective; eauto).
        destruct H as (n' & i' & Ht & ? & Hequ). subst.
        pose proof (remove_at_permutation_correct' _ _ i Hpq Hqp Hinjp Hinjq) as (Hpq' & Hqp').
        edestruct (@remove_at_permutation_vectors) as (Hpq'' & Hqp''); eauto.

        pose proof (Hsb1 i). step in H. destruct H as [Hf _].
        edestruct Hf as [? ? ?]; eauto.
        eapply trans_thread_schedule_val_SS in H.
        eexists. apply H. rewrite Hequ.

        (* pose proof (remove_at_permutation_correct' _ _ (p i) Hqp Hpq Hinjq Hinjp) as Hqp'. *)
        (* rewrite (Hqp i) in Hqp'. *)
        (* destruct (remove_at_permutation p i _) as (p' & Hp') eqn:?. *)
        (* destruct (remove_at_permutation q (p i) _) as (q' & Hq'). cbn in *. *)
        (* rewrite (Hqp i) in Hqp'. rewrite Heqs in Hpq'. cbn in Hqp'. *)

        eapply CIH; clear CIH; cbn; try solve [apply remove_vec_choiceI_bound; auto].
        * apply Hpq'.
        * apply Hqp'.
        * apply Hpq''.
        * apply Hqp''.
      + (* tau step *)
        destruct n; try inv i.
        destruct H0 as (t' & Ht & Hbound & Hequ).
        pose proof (Hsb1 i). step in H. destruct H as [Hf _].
        edestruct Hf as [? ? ?]; eauto.
        pose proof (trans_choiceI_bound _ _ _ _ _ (Hbound2 _) H) as Hbound'.
        apply trans_thread_schedule_tau in H.
        eexists; eauto. rewrite Hequ.
        eapply CIH; clear CIH; eauto; try solve [apply replace_vec_choiceI_bound; auto].
        * intros. destruct (Fin.eq_dec i i0).
          -- subst. do 2 (rewrite replace_vec_eq; auto).
          -- do 2 (rewrite replace_vec_neq; auto). intro.
             apply (f_equal q) in H1. do 2 rewrite Hqp in H1. contradiction.
        * intros. destruct (Fin.eq_dec (p i) i0).
          -- subst. rewrite Hqp. do 2 (rewrite replace_vec_eq; auto). symmetry; auto.
          -- do 2 (rewrite replace_vec_neq; auto). intro.
             apply (f_equal p) in H1. rewrite Hpq in H1. contradiction.
      + (* The thread yields *)
        destruct n; try inv i.
        destruct H as (k & Hvis & i' & Hequ).
        pose proof Hvis as Hvis'.
        eapply sbisim_visible in Hvis'. 5: apply Hsb1. all: auto.
        destruct Hvis' as (k' & Hvis' & Hk).
        exists (schedule (S n) (replace_vec v2 (p i) (k' tt)) (Some (p i'))).
        2: { rewrite Hequ.
             eapply CIH; clear CIH; eauto.
             - intro. apply replace_vec_choiceI_bound; auto.
               eapply visible_choiceI_bound in Hvis; eauto.
               eapply trans_choiceI_bound; eauto. constructor. reflexivity.
             - intro. apply replace_vec_choiceI_bound; auto.
               eapply visible_choiceI_bound in Hvis'; eauto.
               eapply trans_choiceI_bound; eauto. constructor. reflexivity.
             - intros. destruct (Fin.eq_dec i i0).
               + subst. do 2 rewrite replace_vec_eq; auto.
               + do 2 (rewrite replace_vec_neq; auto). intro.
                 apply (f_equal q) in H. do 2 rewrite Hqp in H. contradiction.
             - intros. destruct (Fin.eq_dec (p i) i0).
               + subst. rewrite Hqp. do 2 rewrite replace_vec_eq; auto. symmetry; auto.
               + do 2 (rewrite replace_vec_neq; auto). intro.
                 apply (f_equal p) in H. rewrite Hpq in H. contradiction.
        }
        apply visible_yield_trans_schedule; auto.
      + (* the thread spawns a new thread *)
        destruct H as (k & Hvis & Hequ).
        destruct n; try inv i.
        pose proof Hvis as Hvis'.
        eapply sbisim_visible in Hvis'. 5: apply Hsb1. all: eauto.
        2: { constructor. apply true. }
        destruct Hvis' as (k' & Hvis' & ?).
        pose proof (cons_permutation_correct _ _ Hpq Hqp).
        destruct (cons_permutation p) as (p' & Hp1 & Hp2).
        destruct (cons_permutation q) as (q' & Hq1 & Hq2). cbn in *.
        destruct H0 as (Hpq' & Hqp').
        exists (schedule (S (S n))
                    (cons_vec (k' true)
                              (replace_vec v2 (p i) (k' false)))
                    (Some (p' (FS i)))).
        2: {
          assert (Hbound: forall b, choiceI_bound 1 (k b)). {
            intros. eapply visible_choiceI_bound in Hvis; eauto.
            eapply trans_choiceI_bound; eauto. constructor. reflexivity.
          }
          assert (Hbound': forall b, choiceI_bound 1 (k' b)). {
            intros. eapply visible_choiceI_bound in Hvis'; eauto.
            eapply trans_choiceI_bound; eauto. constructor. reflexivity.
          }
          rewrite Hequ. eapply CIH; auto;
            try solve [apply cons_vec_choiceI_bound; auto;
                       apply replace_vec_choiceI_bound; auto].
          - intros. dependent destruction i0.
            + rewrite Hp1. cbn. auto.
            + rewrite Hp2. cbn. destruct (Fin.eq_dec i i0).
              * subst. do 2 (rewrite replace_vec_eq; auto).
              * do 2 (rewrite replace_vec_neq; auto). intro.
                apply (f_equal q) in H0. do 2 rewrite Hqp in H0. contradiction.
          - intros. dependent destruction i0.
            + rewrite Hq1. cbn. symmetry. auto.
            + rewrite Hq2. cbn. destruct (Fin.eq_dec (p i) i0).
              * subst. rewrite Hqp. do 2 (rewrite replace_vec_eq; auto). symmetry; auto.
              * do 2 (rewrite replace_vec_neq; auto). intro.
                apply (f_equal p) in H0. rewrite Hpq in H0. contradiction.
        }
        rewrite Hp2. apply visible_spawn_trans_schedule; auto.
    - apply trans_schedule_obs in Ht.
      destruct Ht as (k & i' & s & ? & ? & Hvis & Hequ). inv H. rename i' into i.
      destruct n; try inv i.
      pose proof Hvis as Hvis'.
      eapply sbisim_visible in Hvis'. 5: apply Hsb1. all: eauto.
      destruct Hvis' as (k' & Hvis' & ?).
      exists (schedule (S n) (replace_vec v2 (p i) (k' v)) (Some (p i))).
      2: {
        assert (Hbound: forall x, choiceI_bound 1 (k x)). {
          intros. eapply visible_choiceI_bound in Hvis; eauto.
          eapply trans_choiceI_bound; eauto. constructor. reflexivity.
        }
        assert (Hbound': forall x, choiceI_bound 1 (k' x)). {
          intros. eapply visible_choiceI_bound in Hvis'; eauto.
          eapply trans_choiceI_bound; eauto. constructor. reflexivity.
        }
        rewrite Hequ. eapply CIH; clear CIH; eauto;
          try solve [apply replace_vec_choiceI_bound; auto].
        - intros. destruct (Fin.eq_dec i i0).
          + subst. do 2 rewrite replace_vec_eq; auto.
          + do 2 (rewrite replace_vec_neq; auto). intro.
            apply (f_equal q) in H0. do 2 rewrite Hqp in H0. contradiction.
        - intros. destruct (Fin.eq_dec (p i) i0).
          + subst. rewrite Hqp. do 2 rewrite replace_vec_eq; auto. symmetry; auto.
          + do 2 (rewrite replace_vec_neq; auto). intro.
            apply (f_equal p) in H0. rewrite Hpq in H0. contradiction.
      }
      apply visible_stateE_trans_schedule; auto.
    - pose proof (trans_schedule_val_1 _ _ _ _ _ Ht). subst.
      pose proof (trans_val_inv Ht).
      pose proof (Hsb1 i). step in H0. destruct H0 as [Hf _].
      pose proof (trans_schedule_thread_val _ _ _ _ Ht) as Hv1.
      edestruct Hf; eauto.
      apply trans_thread_schedule_val_1 in H0. eexists; eauto. rewrite H. reflexivity.
  Qed.

  (*
  Lemma schedule_perm_2 n (v1 v2 : vec n) i1 i2
        (Hbound1 : forall i, choiceI_bound 1 (v1 i))
        (Hbound2 : forall i, choiceI_bound 1 (v2 i)) :
    (i1 = i2 /\ forall i, v1 i ~ v2 i) \/
      (i1 = i2 /\
         exists i3 i4,
           i3 <> i4 /\
             i1 <> i3 /\
             i1 <> i4 /\
             v1 i3 ~ v2 i4 /\
             v2 i3 ~ v1 i4 /\
             (forall i, i <> i3 -> i <> i4 -> v1 i ~ v2 i)) \/
      (i1 <> i2 /\
         v1 i1 ~ v2 i2 /\
         v2 i1 ~ v1 i2 /\
         (forall i, i <> i1 -> i <> i2 -> v1 i ~ v2 i)) ->
    schedule n v1 (Some i1) ~ schedule n v2 (Some i2).
  Proof.
    revert n v1 v2 i1 i2 Hbound1 Hbound2.
    coinduction r CIH.
    symmetric using idtac.
    {
      intros. apply H; auto. decompose [or] H0; clear H0.
      - left. destruct H1. split; auto. symmetry. auto.
      - right. left. destruct H2 as (? & i3 & i4 & ? & ? & ? & ? & ? & ?). subst.
        split; auto. exists i4, i3. split; [| split; [| split]]; auto.
        split; [| split]; symmetry; auto.
      - right. right. destruct H2 as (? & ? & ? & ?).
        split; auto. split; [| split]; symmetry; auto.
    }
    intros n v1 v2 i1 i2 Hbound1 Hbound2 Hi l t Ht. cbn in *.
    destruct l.
    - apply trans_schedule_thread_tau_some in Ht; auto.
      decompose [or] Ht; clear Ht.
      + (* thread is finished *)
        destruct H as (n' & i & Ht & ? & Hequ). subst.
        destruct Hi as [
            (? & Hv) | [
              (? & i3 & i4 & Hneq1 & Hneq2 & Hneq3 & Hi1sb & Hi2sb & Hothers) |
              (Hneq & Hi1sb & Hi2sb & Hothers)]].
        * (* no swapped elements *)
          subst. pose proof (Hv i2). step in H. destruct H as [Hf _].
          edestruct Hf as [? ? ?]; eauto.
          eapply trans_thread_schedule_val_SS in H.
          eexists. apply H. rewrite Hequ. apply CIH; cbn.
          admit. admit.
          left. split; eauto.
          intros. apply remove_vec_vec_relation; auto.
        * (* swapped elements are elsewhere in v: i3 and i4 *)
          subst. pose proof (Hothers i2 Hneq2 Hneq3).
          step in H. destruct H as [Hf _].
          edestruct Hf as [? ? ?]; eauto.
          rewrite <- (of_nat_to_nat_inv i) in Hequ. rewrite <- (of_nat_to_nat_inv i2) in Hequ.
          destruct (to_nat i) as [i' Hi'] eqn:Hi.
          destruct (to_nat i2) as [i2' Hi2'] eqn:Hi2. cbn in Hequ.
          destruct (to_nat i3) as [i3' Hi3'] eqn:Hi3.
          destruct (to_nat i4) as [i4' Hi4'] eqn:Hi4.
          assert (i3' < i2' \/ i3' > i2').
          {
            rewrite <- (of_nat_to_nat_inv i3) in Hneq2. rewrite Hi3 in Hneq2.
            rewrite <- (of_nat_to_nat_inv i2) in Hneq2. rewrite Hi2 in Hneq2. cbn in Hneq2.
            rewrite <- of_nat_lt_sig1_neq in Hneq2. lia.
          }
          assert (i4' < i2' \/ i4' > i2').
          {
            rewrite <- (of_nat_to_nat_inv i4) in Hneq3. rewrite Hi4 in Hneq3.
            rewrite <- (of_nat_to_nat_inv i2) in Hneq3. rewrite Hi2 in Hneq3. cbn in Hneq3.
            rewrite <- of_nat_lt_sig1_neq in Hneq3. lia.
          }
          destruct H1, H2.
          (* TODO: clean up all this copy and paste *)
          (* i3' < i2', i4' < i2' *)
          {
            assert (Hneq4: i3' <> i4').
            {
              rewrite of_nat_lt_sig1_neq.
              rewrite <- (of_nat_to_nat_inv i3) in Hneq1. rewrite Hi3 in Hneq1.
              rewrite <- (of_nat_to_nat_inv i4) in Hneq1. rewrite Hi4 in Hneq1.
              apply Hneq1.
            }
            destruct (PeanoNat.Nat.eq_dec i' i3'); [| destruct (PeanoNat.Nat.eq_dec i' i4')].
            {
              (* we are going to i3' next *)
              subst. rename Hi' into Hi3''.
              assert (Hi4'' : i4' < S n') by lia.
              apply trans_thread_schedule_val_SS with (i':=(of_nat_lt Hi4'')) in H.
              eexists. apply H. rewrite Hequ. apply CIH; clear CIH. admit. admit.
              right. right. split.
              {
                intro. eapply f_equal in H3. do 2 rewrite to_nat_of_nat in H3.
                inv H3. contradiction.
              }
              split; [| split].
              - rewrite <- (of_nat_to_nat_inv i2). rewrite Hi2. cbn.
                do 2 (erewrite <- remove_vec_index_before; eauto).
                rewrite <- (of_nat_to_nat_inv i3) in Hi1sb.
                rewrite <- (of_nat_to_nat_inv i4) in Hi1sb.
                rewrite Hi3, Hi4 in Hi1sb. cbn in Hi1sb.
                apply Hi1sb.
              - rewrite <- (of_nat_to_nat_inv i2). rewrite Hi2. cbn.
                do 2 (erewrite <- remove_vec_index_before; eauto).
                rewrite <- (of_nat_to_nat_inv i3) in Hi2sb.
                rewrite <- (of_nat_to_nat_inv i4) in Hi2sb.
                rewrite Hi3, Hi4 in Hi2sb. cbn in Hi2sb.
                apply Hi2sb.
              - intros.
                destruct (to_nat i0) as [i0' Hi0'] eqn:Hi0.
                rewrite <- (of_nat_to_nat_inv i2). rewrite Hi2.
                rewrite <- (of_nat_to_nat_inv i0). rewrite Hi0. cbn.
                rewrite <- (of_nat_to_nat_inv i0) in H3, H4. rewrite Hi0 in H3, H4. cbn in *.
                assert (i0' < i2' \/ i0' = i2' \/ i0' > i2') by lia.
                destruct H5 as [? | [? | ?]].
                + assert (Hi0'' : i0' < S (S n')) by lia.
                  specialize (Hothers (of_nat_lt Hi0'')).
                  rewrite <- of_nat_lt_sig1_neq in H3.
                  rewrite <- of_nat_lt_sig1_neq in H4.
                  do 2 (erewrite <- remove_vec_index_before; eauto).
                  eapply Hothers; eauto.
                  * rewrite <- (of_nat_to_nat_inv i3). rewrite Hi3. cbn.
                    rewrite <- of_nat_lt_sig1_neq. auto.
                  * rewrite <- (of_nat_to_nat_inv i4). rewrite Hi4. cbn.
                    rewrite <- of_nat_lt_sig1_neq. auto.
                + subst. rename i2' into i0'.
                  assert (Hi0'' : S i0' < S (S n')) by lia.
                  specialize (Hothers (of_nat_lt Hi0'')).
                  do 2 (erewrite <- remove_vec_index_eq; eauto).
                  eapply Hothers; eauto.
                  * rewrite <- (of_nat_to_nat_inv i3). rewrite Hi3.
                    rewrite <- of_nat_lt_sig1_neq. cbn. lia.
                  * rewrite <- (of_nat_to_nat_inv i4). rewrite Hi4.
                    rewrite <- of_nat_lt_sig1_neq. cbn. lia.
                + assert (Hi0'' : S i0' < S (S n')) by lia.
                  specialize (Hothers (of_nat_lt Hi0'')).
                  do 2 (erewrite <- remove_vec_index_after; eauto).
                  eapply Hothers; eauto.
                  * rewrite <- (of_nat_to_nat_inv i3). rewrite Hi3.
                    rewrite <- of_nat_lt_sig1_neq. cbn. lia.
                  * rewrite <- (of_nat_to_nat_inv i4). rewrite Hi4.
                    rewrite <- of_nat_lt_sig1_neq. cbn. lia.
            }
            {
              (* we are going to i4' next *)
              subst. rename Hi' into Hi4''.
              assert (Hi3'' : i3' < S n') by lia.
              apply trans_thread_schedule_val_SS with (i':=(of_nat_lt Hi3'')) in H.
              eexists. apply H. rewrite Hequ. apply CIH; clear CIH. admit. admit.
              right. right. split.
              {
                intro. eapply f_equal in H3. do 2 rewrite to_nat_of_nat in H3.
                inv H3. contradiction.
              }
              split; [| split].
              - rewrite <- (of_nat_to_nat_inv i2). rewrite Hi2. cbn.
                do 2 (erewrite <- remove_vec_index_before; eauto).
                rewrite <- (of_nat_to_nat_inv i3) in Hi2sb.
                rewrite <- (of_nat_to_nat_inv i4) in Hi2sb.
                rewrite Hi3, Hi4 in Hi2sb. cbn in Hi2sb.
                symmetry. apply Hi2sb.
              - rewrite <- (of_nat_to_nat_inv i2). rewrite Hi2. cbn.
                do 2 (erewrite <- remove_vec_index_before; eauto).
                rewrite <- (of_nat_to_nat_inv i3) in Hi1sb.
                rewrite <- (of_nat_to_nat_inv i4) in Hi1sb.
                rewrite Hi3, Hi4 in Hi1sb. cbn in Hi1sb.
                symmetry. apply Hi1sb.
              - intros.
                destruct (to_nat i0) as [i0' Hi0'] eqn:Hi0.
                rewrite <- (of_nat_to_nat_inv i2). rewrite Hi2.
                rewrite <- (of_nat_to_nat_inv i0). rewrite Hi0. cbn.
                rewrite <- (of_nat_to_nat_inv i0) in H3, H4. rewrite Hi0 in H3, H4. cbn in *.
                assert (i0' < i2' \/ i0' = i2' \/ i0' > i2') by lia.
                destruct H5 as [? | [? | ?]].
                + assert (Hi0'' : i0' < S (S n')) by lia.
                  specialize (Hothers (of_nat_lt Hi0'')).
                  rewrite <- of_nat_lt_sig1_neq in H3.
                  rewrite <- of_nat_lt_sig1_neq in H4.
                  do 2 (erewrite <- remove_vec_index_before; eauto).
                  eapply Hothers; eauto.
                  * rewrite <- (of_nat_to_nat_inv i3). rewrite Hi3. cbn.
                    rewrite <- of_nat_lt_sig1_neq. auto.
                  * rewrite <- (of_nat_to_nat_inv i4). rewrite Hi4. cbn.
                    rewrite <- of_nat_lt_sig1_neq. auto.
                + subst. rename i2' into i0'.
                  assert (Hi0'' : S i0' < S (S n')) by lia.
                  specialize (Hothers (of_nat_lt Hi0'')).
                  do 2 (erewrite <- remove_vec_index_eq; eauto).
                  eapply Hothers; eauto.
                  * rewrite <- (of_nat_to_nat_inv i3). rewrite Hi3.
                    rewrite <- of_nat_lt_sig1_neq. cbn. lia.
                  * rewrite <- (of_nat_to_nat_inv i4). rewrite Hi4.
                    rewrite <- of_nat_lt_sig1_neq. cbn. lia.
                + assert (Hi0'' : S i0' < S (S n')) by lia.
                  specialize (Hothers (of_nat_lt Hi0'')).
                  do 2 (erewrite <- remove_vec_index_after; eauto).
                  eapply Hothers; eauto.
                  * rewrite <- (of_nat_to_nat_inv i3). rewrite Hi3.
                    rewrite <- of_nat_lt_sig1_neq. cbn. lia.
                  * rewrite <- (of_nat_to_nat_inv i4). rewrite Hi4.
                    rewrite <- of_nat_lt_sig1_neq. cbn. lia.
            }
            {
              (* we are going to i', which is not one of the swapped elements *)
              assert (Hi3'' : i3' < S n') by lia.
              assert (Hi4'' : i4' < S n') by lia.
              apply trans_thread_schedule_val_SS with (i':=(of_nat_lt Hi')) in H.
              eexists. apply H. rewrite Hequ. apply CIH; clear CIH. admit. admit.
              right. left. split; auto.
              exists (of_nat_lt Hi3''), (of_nat_lt Hi4'').
              split; [| split; [| split]]; try solve [rewrite <- of_nat_lt_sig1_neq; auto].
              split; [| split].
              - rewrite <- (of_nat_to_nat_inv i2). rewrite Hi2. cbn.
                do 2 (erewrite <- remove_vec_index_before; eauto).
                rewrite <- (of_nat_to_nat_inv i3) in Hi1sb.
                rewrite <- (of_nat_to_nat_inv i4) in Hi1sb.
                rewrite Hi3, Hi4 in Hi1sb. cbn in Hi1sb.
                apply Hi1sb.
              - rewrite <- (of_nat_to_nat_inv i2). rewrite Hi2. cbn.
                do 2 (erewrite <- remove_vec_index_before; eauto).
                rewrite <- (of_nat_to_nat_inv i3) in Hi2sb.
                rewrite <- (of_nat_to_nat_inv i4) in Hi2sb.
                rewrite Hi3, Hi4 in Hi2sb. cbn in Hi2sb.
                apply Hi2sb.
              - intros.
                destruct (to_nat i0) as [i0' Hi0'] eqn:Hi0.
                rewrite <- (of_nat_to_nat_inv i2). rewrite Hi2.
                rewrite <- (of_nat_to_nat_inv i0). rewrite Hi0. cbn.
                rewrite <- (of_nat_to_nat_inv i0) in H3, H4. rewrite Hi0 in H3, H4. cbn in *.
                assert (i0' < i2' \/ i0' = i2' \/ i0' > i2') by lia.
                destruct H5 as [? | [? | ?]].
                + assert (Hi0'' : i0' < S (S n')) by lia.
                  specialize (Hothers (of_nat_lt Hi0'')).
                  rewrite <- of_nat_lt_sig1_neq in H3.
                  rewrite <- of_nat_lt_sig1_neq in H4.
                  do 2 (erewrite <- remove_vec_index_before; eauto).
                  eapply Hothers; eauto.
                  * rewrite <- (of_nat_to_nat_inv i3). rewrite Hi3. cbn.
                    rewrite <- of_nat_lt_sig1_neq. auto.
                  * rewrite <- (of_nat_to_nat_inv i4). rewrite Hi4. cbn.
                    rewrite <- of_nat_lt_sig1_neq. auto.
                + subst. rename i2' into i0'.
                  assert (Hi0'' : S i0' < S (S n')) by lia.
                  specialize (Hothers (of_nat_lt Hi0'')).
                  do 2 (erewrite <- remove_vec_index_eq; eauto).
                  eapply Hothers; eauto.
                  * rewrite <- (of_nat_to_nat_inv i3). rewrite Hi3.
                    rewrite <- of_nat_lt_sig1_neq. cbn. lia.
                  * rewrite <- (of_nat_to_nat_inv i4). rewrite Hi4.
                    rewrite <- of_nat_lt_sig1_neq. cbn. lia.
                + assert (Hi0'' : S i0' < S (S n')) by lia.
                  specialize (Hothers (of_nat_lt Hi0'')).
                  do 2 (erewrite <- remove_vec_index_after; eauto).
                  eapply Hothers; eauto.
                  * rewrite <- (of_nat_to_nat_inv i3). rewrite Hi3.
                    rewrite <- of_nat_lt_sig1_neq. cbn. lia.
                  * rewrite <- (of_nat_to_nat_inv i4). rewrite Hi4.
                    rewrite <- of_nat_lt_sig1_neq. cbn. lia.
            }
          }
          (* i3' < i2', i4' > i2' *)
          {
            destruct i4'. inv H2.
            assert (Hneq4: i3' <> i4').
            {
              rewrite <- (of_nat_to_nat_inv i3) in Hneq1. rewrite Hi3 in Hneq1.
              rewrite <- (of_nat_to_nat_inv i4) in Hneq1. rewrite Hi4 in Hneq1.
              rewrite <- of_nat_lt_sig1_neq in Hneq1. cbn in Hneq1. lia.
            }

            destruct (PeanoNat.Nat.eq_dec i' i3'); [| destruct (PeanoNat.Nat.eq_dec i' i4')].
            {
              (* we are going to i3' next *)
              subst. rename Hi' into Hi3''.
              (* destruct i4'. inv H2. (* subtract i4' by one *) *)
              assert (Hi4'' : i4' < S n') by lia.
              apply trans_thread_schedule_val_SS with (i':=(of_nat_lt Hi4'')) in H.
              eexists. apply H. rewrite Hequ. apply CIH; clear CIH. admit. admit.
              right. right. split.
              {
                intro. eapply f_equal in H3. do 2 rewrite to_nat_of_nat in H3.
                inv H3. contradiction.
              }
              split; [| split].
              - rewrite <- (of_nat_to_nat_inv i2). rewrite Hi2. cbn.
                erewrite <- remove_vec_index_before; eauto.
                assert (i4' = i2' \/ i4' > i2') by lia. destruct H3.
                + subst. erewrite <- remove_vec_index_eq; eauto.
                  rewrite <- (of_nat_to_nat_inv i3) in Hi1sb.
                  rewrite <- (of_nat_to_nat_inv i4) in Hi1sb.
                  rewrite Hi3, Hi4 in Hi1sb. cbn in Hi1sb.
                  apply Hi1sb.
                + erewrite <- remove_vec_index_after; eauto.
                  rewrite <- (of_nat_to_nat_inv i3) in Hi1sb.
                  rewrite <- (of_nat_to_nat_inv i4) in Hi1sb.
                  rewrite Hi3, Hi4 in Hi1sb. cbn in Hi1sb.
                  apply Hi1sb.
              - rewrite <- (of_nat_to_nat_inv i2). rewrite Hi2. cbn.
                erewrite <- remove_vec_index_before; eauto.
                assert (i4' = i2' \/ i4' > i2') by lia. destruct H3.
                + subst. erewrite <- remove_vec_index_eq; eauto.
                  rewrite <- (of_nat_to_nat_inv i3) in Hi2sb.
                  rewrite <- (of_nat_to_nat_inv i4) in Hi2sb.
                  rewrite Hi3, Hi4 in Hi2sb. cbn in Hi2sb.
                  apply Hi2sb.
                + erewrite <- remove_vec_index_after; eauto.
                  rewrite <- (of_nat_to_nat_inv i3) in Hi2sb.
                  rewrite <- (of_nat_to_nat_inv i4) in Hi2sb.
                  rewrite Hi3, Hi4 in Hi2sb. cbn in Hi2sb.
                  apply Hi2sb.
              - intros.
                destruct (to_nat i0) as [i0' Hi0'] eqn:Hi0.
                rewrite <- (of_nat_to_nat_inv i2). rewrite Hi2.
                rewrite <- (of_nat_to_nat_inv i0). rewrite Hi0. cbn.
                rewrite <- (of_nat_to_nat_inv i0) in H3, H4. rewrite Hi0 in H3, H4. cbn in *.
                assert (i0' < i2' \/ i0' = i2' \/ i0' > i2') by lia.
                destruct H5 as [? | [? | ?]].
                + assert (Hi0'' : i0' < S (S n')) by lia.
                  specialize (Hothers (of_nat_lt Hi0'')).
                  rewrite <- of_nat_lt_sig1_neq in H3.
                  rewrite <- of_nat_lt_sig1_neq in H4.
                  do 2 (erewrite <- remove_vec_index_before; eauto).
                  eapply Hothers; eauto.
                  * rewrite <- (of_nat_to_nat_inv i3). rewrite Hi3. cbn.
                    rewrite <- of_nat_lt_sig1_neq. auto.
                  * rewrite <- (of_nat_to_nat_inv i4). rewrite Hi4.
                    rewrite <- of_nat_lt_sig1_neq. cbn. lia.
                + subst. rename i2' into i0'.
                  assert (Hi0'' : S i0' < S (S n')) by lia.
                  specialize (Hothers (of_nat_lt Hi0'')).
                  do 2 (erewrite <- remove_vec_index_eq; eauto).
                  eapply Hothers; eauto.
                  * rewrite <- (of_nat_to_nat_inv i3). rewrite Hi3.
                    rewrite <- of_nat_lt_sig1_neq. cbn. lia.
                  * rewrite <- (of_nat_to_nat_inv i4). rewrite Hi4.
                    rewrite <- of_nat_lt_sig1_neq in H4.
                    rewrite <- of_nat_lt_sig1_neq. cbn. lia.
                + assert (Hi0'' : S i0' < S (S n')) by lia.
                  specialize (Hothers (of_nat_lt Hi0'')).
                  do 2 (erewrite <- remove_vec_index_after; eauto).
                  eapply Hothers; eauto.
                  * rewrite <- (of_nat_to_nat_inv i3). rewrite Hi3.
                    rewrite <- of_nat_lt_sig1_neq. cbn. lia.
                  * rewrite <- (of_nat_to_nat_inv i4). rewrite Hi4.
                    rewrite <- of_nat_lt_sig1_neq in H4.
                    rewrite <- of_nat_lt_sig1_neq. cbn. lia.
            }
            {
              (* we are going to i4' next *)
              subst. rename Hi' into Hi4''.
              assert (Hi3'' : i3' < S n') by lia.
              apply trans_thread_schedule_val_SS with (i':=(of_nat_lt Hi3'')) in H.
              eexists. apply H. rewrite Hequ. apply CIH; clear CIH. admit. admit.
              right. right. split.
              {
                intro. eapply f_equal in H3. do 2 rewrite to_nat_of_nat in H3.
                inv H3. contradiction.
              }
              split; [| split].
              - rewrite <- (of_nat_to_nat_inv i2). rewrite Hi2.
                assert (i4' = i2' \/ i4' > i2') by lia. destruct H3.
                + subst. erewrite <- remove_vec_index_eq; eauto.
                  erewrite <- remove_vec_index_before; eauto.
                  rewrite <- (of_nat_to_nat_inv i3) in Hi2sb.
                  rewrite <- (of_nat_to_nat_inv i4) in Hi2sb.
                  rewrite Hi3, Hi4 in Hi2sb. cbn in Hi2sb.
                  symmetry. eapply Hi2sb.
                + erewrite <- remove_vec_index_after; eauto.
                  erewrite <- remove_vec_index_before; eauto.
                  rewrite <- (of_nat_to_nat_inv i3) in Hi2sb.
                  rewrite <- (of_nat_to_nat_inv i4) in Hi2sb.
                  rewrite Hi3, Hi4 in Hi2sb. cbn in Hi2sb.
                  symmetry. apply Hi2sb.
              - rewrite <- (of_nat_to_nat_inv i2). rewrite Hi2. cbn.
                assert (i4' = i2' \/ i4' > i2') by lia. destruct H3.
                + subst. erewrite <- remove_vec_index_eq; eauto.
                  erewrite <- remove_vec_index_before; eauto.
                  rewrite <- (of_nat_to_nat_inv i3) in Hi1sb.
                  rewrite <- (of_nat_to_nat_inv i4) in Hi1sb.
                  rewrite Hi3, Hi4 in Hi1sb. cbn in Hi1sb.
                  symmetry. eapply Hi1sb.
                + erewrite <- remove_vec_index_after; eauto.
                  erewrite <- remove_vec_index_before; eauto.
                  rewrite <- (of_nat_to_nat_inv i3) in Hi1sb.
                  rewrite <- (of_nat_to_nat_inv i4) in Hi1sb.
                  rewrite Hi3, Hi4 in Hi1sb. cbn in Hi1sb.
                  symmetry. eapply Hi1sb.
              - intros.
                destruct (to_nat i0) as [i0' Hi0'] eqn:Hi0.
                rewrite <- (of_nat_to_nat_inv i2). rewrite Hi2.
                rewrite <- (of_nat_to_nat_inv i0). rewrite Hi0. cbn.
                rewrite <- (of_nat_to_nat_inv i0) in H3, H4. rewrite Hi0 in H3, H4. cbn in *.
                assert (i0' < i2' \/ i0' = i2' \/ i0' > i2') by lia.
                destruct H5 as [? | [? | ?]].
                + assert (Hi0'' : i0' < S (S n')) by lia.
                  specialize (Hothers (of_nat_lt Hi0'')).
                  rewrite <- of_nat_lt_sig1_neq in H3.
                  rewrite <- of_nat_lt_sig1_neq in H4.
                  do 2 (erewrite <- remove_vec_index_before; eauto).
                  eapply Hothers; eauto.
                  * rewrite <- (of_nat_to_nat_inv i3). rewrite Hi3. cbn.
                    rewrite <- of_nat_lt_sig1_neq. auto.
                  * rewrite <- (of_nat_to_nat_inv i4). rewrite Hi4.
                    rewrite <- of_nat_lt_sig1_neq. cbn. lia.
                + subst. rename i2' into i0'.
                  assert (Hi0'' : S i0' < S (S n')) by lia.
                  specialize (Hothers (of_nat_lt Hi0'')).
                  do 2 (erewrite <- remove_vec_index_eq; eauto).
                  eapply Hothers; eauto.
                  * rewrite <- (of_nat_to_nat_inv i3). rewrite Hi3.
                    rewrite <- of_nat_lt_sig1_neq. cbn. lia.
                  * rewrite <- (of_nat_to_nat_inv i4). rewrite Hi4.
                    rewrite <- of_nat_lt_sig1_neq in H3.
                    rewrite <- of_nat_lt_sig1_neq. cbn. lia.
                + assert (Hi0'' : S i0' < S (S n')) by lia.
                  specialize (Hothers (of_nat_lt Hi0'')).
                  do 2 (erewrite <- remove_vec_index_after; eauto).
                  eapply Hothers; eauto.
                  * rewrite <- (of_nat_to_nat_inv i3). rewrite Hi3.
                    rewrite <- of_nat_lt_sig1_neq. cbn. lia.
                  * rewrite <- (of_nat_to_nat_inv i4). rewrite Hi4.
                    rewrite <- of_nat_lt_sig1_neq in H3.
                    rewrite <- of_nat_lt_sig1_neq. cbn. lia.
            }
            {
              (* we are going to i', which is not one of the swapped elements *)
              assert (Hi3'' : i3' < S n') by lia.
              assert (Hi4'' : i4' < S n') by lia.
              apply trans_thread_schedule_val_SS with (i':=(of_nat_lt Hi')) in H.
              eexists. apply H. rewrite Hequ. apply CIH; clear CIH. admit. admit.
              right. left. split; auto.
              exists (of_nat_lt Hi3''), (of_nat_lt Hi4'').
              split; [| split; [| split]]; try solve [rewrite <- of_nat_lt_sig1_neq; auto].
              split; [| split].
              - rewrite <- (of_nat_to_nat_inv i2). rewrite Hi2. cbn.
                erewrite <- remove_vec_index_before; eauto.
                assert (i4' = i2' \/ i4' > i2') by lia. destruct H3.
                + subst. erewrite <- remove_vec_index_eq; eauto.
                  rewrite <- (of_nat_to_nat_inv i3) in Hi1sb.
                  rewrite <- (of_nat_to_nat_inv i4) in Hi1sb.
                  rewrite Hi3, Hi4 in Hi1sb. cbn in Hi1sb.
                  apply Hi1sb.
                + erewrite <- remove_vec_index_after; eauto.
                  rewrite <- (of_nat_to_nat_inv i3) in Hi1sb.
                  rewrite <- (of_nat_to_nat_inv i4) in Hi1sb.
                  rewrite Hi3, Hi4 in Hi1sb. cbn in Hi1sb.
                  apply Hi1sb.
              - rewrite <- (of_nat_to_nat_inv i2). rewrite Hi2. cbn.
                erewrite <- remove_vec_index_before; eauto.
                assert (i4' = i2' \/ i4' > i2') by lia. destruct H3.
                + subst. erewrite <- remove_vec_index_eq; eauto.
                  rewrite <- (of_nat_to_nat_inv i3) in Hi2sb.
                  rewrite <- (of_nat_to_nat_inv i4) in Hi2sb.
                  rewrite Hi3, Hi4 in Hi2sb. cbn in Hi2sb.
                  apply Hi2sb.
                + subst. erewrite <- remove_vec_index_after; eauto.
                  rewrite <- (of_nat_to_nat_inv i3) in Hi2sb.
                  rewrite <- (of_nat_to_nat_inv i4) in Hi2sb.
                  rewrite Hi3, Hi4 in Hi2sb. cbn in Hi2sb.
                  apply Hi2sb.
              - intros.
                destruct (to_nat i0) as [i0' Hi0'] eqn:Hi0.
                rewrite <- (of_nat_to_nat_inv i2). rewrite Hi2.
                rewrite <- (of_nat_to_nat_inv i0). rewrite Hi0. cbn.
                rewrite <- (of_nat_to_nat_inv i0) in H3, H4. rewrite Hi0 in H3, H4. cbn in *.
                assert (i0' < i2' \/ i0' = i2' \/ i0' > i2') by lia.
                destruct H5 as [? | [? | ?]].
                + assert (Hi0'' : i0' < S (S n')) by lia.
                  specialize (Hothers (of_nat_lt Hi0'')).
                  rewrite <- of_nat_lt_sig1_neq in H3.
                  rewrite <- of_nat_lt_sig1_neq in H4.
                  do 2 (erewrite <- remove_vec_index_before; eauto).
                  eapply Hothers; eauto.
                  * rewrite <- (of_nat_to_nat_inv i3). rewrite Hi3. cbn.
                    rewrite <- of_nat_lt_sig1_neq. auto.
                  * rewrite <- (of_nat_to_nat_inv i4). rewrite Hi4.
                    rewrite <- of_nat_lt_sig1_neq. cbn. lia.
                + subst. rename i2' into i0'.
                  assert (Hi0'' : S i0' < S (S n')) by lia.
                  specialize (Hothers (of_nat_lt Hi0'')).
                  do 2 (erewrite <- remove_vec_index_eq; eauto).
                  eapply Hothers; eauto.
                  * rewrite <- (of_nat_to_nat_inv i3). rewrite Hi3.
                    rewrite <- of_nat_lt_sig1_neq. cbn. lia.
                  * rewrite <- (of_nat_to_nat_inv i4). rewrite Hi4.
                    rewrite <- of_nat_lt_sig1_neq in H4.
                    rewrite <- of_nat_lt_sig1_neq. cbn. lia.
                + assert (Hi0'' : S i0' < S (S n')) by lia.
                  specialize (Hothers (of_nat_lt Hi0'')).
                  do 2 (erewrite <- remove_vec_index_after; eauto).
                  eapply Hothers; eauto.
                  * rewrite <- (of_nat_to_nat_inv i3). rewrite Hi3.
                    rewrite <- of_nat_lt_sig1_neq. cbn. lia.
                  * rewrite <- (of_nat_to_nat_inv i4). rewrite Hi4.
                    rewrite <- of_nat_lt_sig1_neq in H4.
                    rewrite <- of_nat_lt_sig1_neq. cbn. lia.
            }
          }
          (* i3' > i2', i4' < i2' *)
          {
            destruct i3'. inv H1.
            assert (Hneq4: i3' <> i4').
            {
              rewrite <- (of_nat_to_nat_inv i3) in Hneq1. rewrite Hi3 in Hneq1.
              rewrite <- (of_nat_to_nat_inv i4) in Hneq1. rewrite Hi4 in Hneq1.
              rewrite <- of_nat_lt_sig1_neq in Hneq1. cbn in Hneq1. lia.
            }
            destruct (PeanoNat.Nat.eq_dec i' i3'); [| destruct (PeanoNat.Nat.eq_dec i' i4')].
            {
              (* we are going to i3' next *)
              subst. rename Hi' into Hi3''.
              assert (Hi4'' : i4' < S n') by lia.
              apply trans_thread_schedule_val_SS with (i':=(of_nat_lt Hi4'')) in H.
              eexists. apply H. rewrite Hequ. apply CIH; clear CIH. admit. admit.
              right. right. split.
              {
                intro. eapply f_equal in H3. do 2 rewrite to_nat_of_nat in H3.
                inv H3. contradiction.
              }
              split; [| split].
              - rewrite <- (of_nat_to_nat_inv i2). rewrite Hi2. cbn.
                assert (i3' = i2' \/ i3' > i2') by lia. destruct H3.
                + erewrite <- remove_vec_index_eq; eauto.
                  erewrite <- remove_vec_index_before; eauto.
                  rewrite <- (of_nat_to_nat_inv i3) in Hi1sb.
                  rewrite <- (of_nat_to_nat_inv i4) in Hi1sb.
                  rewrite Hi3, Hi4 in Hi1sb. cbn in Hi1sb.
                  apply Hi1sb.
                + erewrite <- remove_vec_index_after; eauto.
                  erewrite <- remove_vec_index_before; eauto.
                  rewrite <- (of_nat_to_nat_inv i3) in Hi1sb.
                  rewrite <- (of_nat_to_nat_inv i4) in Hi1sb.
                  rewrite Hi3, Hi4 in Hi1sb. cbn in Hi1sb.
                  apply Hi1sb.
              - rewrite <- (of_nat_to_nat_inv i2). rewrite Hi2. cbn.
                assert (i3' = i2' \/ i3' > i2') by lia. destruct H3.
                + erewrite <- remove_vec_index_eq; eauto.
                  erewrite <- remove_vec_index_before; eauto.
                  rewrite <- (of_nat_to_nat_inv i3) in Hi2sb.
                  rewrite <- (of_nat_to_nat_inv i4) in Hi2sb.
                  rewrite Hi3, Hi4 in Hi2sb. cbn in Hi2sb.
                  apply Hi2sb.
                + erewrite <- remove_vec_index_after; eauto.
                  erewrite <- remove_vec_index_before; eauto.
                  rewrite <- (of_nat_to_nat_inv i3) in Hi2sb.
                  rewrite <- (of_nat_to_nat_inv i4) in Hi2sb.
                  rewrite Hi3, Hi4 in Hi2sb. cbn in Hi2sb.
                  apply Hi2sb.
              - intros.
                destruct (to_nat i0) as [i0' Hi0'] eqn:Hi0.
                rewrite <- (of_nat_to_nat_inv i2). rewrite Hi2.
                rewrite <- (of_nat_to_nat_inv i0). rewrite Hi0. cbn.
                rewrite <- (of_nat_to_nat_inv i0) in H3, H4. rewrite Hi0 in H3, H4. cbn in *.
                assert (i0' < i2' \/ i0' = i2' \/ i0' > i2') by lia.
                destruct H5 as [? | [? | ?]].
                + assert (Hi0'' : i0' < S (S n')) by lia.
                  specialize (Hothers (of_nat_lt Hi0'')).
                  rewrite <- of_nat_lt_sig1_neq in H3.
                  rewrite <- of_nat_lt_sig1_neq in H4.
                  do 2 (erewrite <- remove_vec_index_before; eauto).
                  eapply Hothers; eauto.
                  * rewrite <- (of_nat_to_nat_inv i3). rewrite Hi3.
                    rewrite <- of_nat_lt_sig1_neq. cbn. lia.
                  * rewrite <- (of_nat_to_nat_inv i4). rewrite Hi4. cbn.
                    rewrite <- of_nat_lt_sig1_neq. auto.
                + subst. rename i2' into i0'.
                  assert (Hi0'' : S i0' < S (S n')) by lia.
                  specialize (Hothers (of_nat_lt Hi0'')).
                  do 2 (erewrite <- remove_vec_index_eq; eauto).
                  eapply Hothers; eauto.
                  * rewrite <- (of_nat_to_nat_inv i3). rewrite Hi3.
                    rewrite <- of_nat_lt_sig1_neq in H3.
                    rewrite <- of_nat_lt_sig1_neq. cbn. lia.
                  * rewrite <- (of_nat_to_nat_inv i4). rewrite Hi4.
                    rewrite <- of_nat_lt_sig1_neq in H3.
                    rewrite <- of_nat_lt_sig1_neq. cbn. lia.
                + assert (Hi0'' : S i0' < S (S n')) by lia.
                  specialize (Hothers (of_nat_lt Hi0'')).
                  do 2 (erewrite <- remove_vec_index_after; eauto).
                  eapply Hothers; eauto.
                  * rewrite <- (of_nat_to_nat_inv i3). rewrite Hi3.
                    rewrite <- of_nat_lt_sig1_neq in H3.
                    rewrite <- of_nat_lt_sig1_neq. cbn. lia.
                  * rewrite <- (of_nat_to_nat_inv i4). rewrite Hi4.
                    rewrite <- of_nat_lt_sig1_neq. cbn. lia.
            }
            {
              (* we are going to i4' next *)
              subst. rename Hi' into Hi4''.
              assert (Hi3'' : i3' < S n') by lia.
              apply trans_thread_schedule_val_SS with (i':=(of_nat_lt Hi3'')) in H.
              eexists. apply H. rewrite Hequ. apply CIH; clear CIH. admit. admit.
              right. right. split.
              {
                intro. eapply f_equal in H3. do 2 rewrite to_nat_of_nat in H3.
                inv H3. contradiction.
              }
              split; [| split].
              - rewrite <- (of_nat_to_nat_inv i2). rewrite Hi2.
                erewrite <- remove_vec_index_before; eauto.
                assert (i3' = i2' \/ i3' > i2') by lia. destruct H3.
                + subst. erewrite <- remove_vec_index_eq; eauto.
                  rewrite <- (of_nat_to_nat_inv i3) in Hi2sb.
                  rewrite <- (of_nat_to_nat_inv i4) in Hi2sb.
                  rewrite Hi3, Hi4 in Hi2sb. cbn in Hi2sb.
                  symmetry. apply Hi2sb.
                + erewrite <- remove_vec_index_after; eauto.
                  rewrite <- (of_nat_to_nat_inv i3) in Hi2sb.
                  rewrite <- (of_nat_to_nat_inv i4) in Hi2sb.
                  rewrite Hi3, Hi4 in Hi2sb. cbn in Hi2sb.
                  symmetry. apply Hi2sb.
              - rewrite <- (of_nat_to_nat_inv i2). rewrite Hi2. cbn.
                erewrite <- remove_vec_index_before; eauto.
                assert (i3' = i2' \/ i3' > i2') by lia. destruct H3.
                + subst. erewrite <- remove_vec_index_eq; eauto.
                  rewrite <- (of_nat_to_nat_inv i3) in Hi1sb.
                  rewrite <- (of_nat_to_nat_inv i4) in Hi1sb.
                  rewrite Hi3, Hi4 in Hi1sb. cbn in Hi1sb.
                  symmetry. apply Hi1sb.
                + erewrite <- remove_vec_index_after; eauto.
                  rewrite <- (of_nat_to_nat_inv i3) in Hi1sb.
                  rewrite <- (of_nat_to_nat_inv i4) in Hi1sb.
                  rewrite Hi3, Hi4 in Hi1sb. cbn in Hi1sb.
                  symmetry. apply Hi1sb.
              - intros.
                destruct (to_nat i0) as [i0' Hi0'] eqn:Hi0.
                rewrite <- (of_nat_to_nat_inv i2). rewrite Hi2.
                rewrite <- (of_nat_to_nat_inv i0). rewrite Hi0. cbn.
                rewrite <- (of_nat_to_nat_inv i0) in H3, H4. rewrite Hi0 in H3, H4. cbn in *.
                assert (i0' < i2' \/ i0' = i2' \/ i0' > i2') by lia.
                destruct H5 as [? | [? | ?]].
                + assert (Hi0'' : i0' < S (S n')) by lia.
                  specialize (Hothers (of_nat_lt Hi0'')).
                  rewrite <- of_nat_lt_sig1_neq in H3.
                  rewrite <- of_nat_lt_sig1_neq in H4.
                  do 2 (erewrite <- remove_vec_index_before; eauto).
                  eapply Hothers; eauto.
                  * rewrite <- (of_nat_to_nat_inv i3). rewrite Hi3.
                    rewrite <- of_nat_lt_sig1_neq. cbn. lia.
                  * rewrite <- (of_nat_to_nat_inv i4). rewrite Hi4. cbn.
                    rewrite <- of_nat_lt_sig1_neq. auto.
                + subst. rename i2' into i0'.
                  assert (Hi0'' : S i0' < S (S n')) by lia.
                  specialize (Hothers (of_nat_lt Hi0'')).
                  do 2 (erewrite <- remove_vec_index_eq; eauto).
                  eapply Hothers; eauto.
                  * rewrite <- (of_nat_to_nat_inv i3). rewrite Hi3.
                    rewrite <- of_nat_lt_sig1_neq in H4.
                    rewrite <- of_nat_lt_sig1_neq. cbn. lia.
                  * rewrite <- (of_nat_to_nat_inv i4). rewrite Hi4.
                    rewrite <- of_nat_lt_sig1_neq. cbn. lia.
                + assert (Hi0'' : S i0' < S (S n')) by lia.
                  specialize (Hothers (of_nat_lt Hi0'')).
                  do 2 (erewrite <- remove_vec_index_after; eauto).
                  eapply Hothers; eauto.
                  * rewrite <- (of_nat_to_nat_inv i3). rewrite Hi3.
                    rewrite <- of_nat_lt_sig1_neq in H4.
                    rewrite <- of_nat_lt_sig1_neq. cbn. lia.
                  * rewrite <- (of_nat_to_nat_inv i4). rewrite Hi4.
                    rewrite <- of_nat_lt_sig1_neq. cbn. lia.
            }
            {
              (* we are going to i', which is not one of the swapped elements *)
              assert (Hi3'' : i3' < S n') by lia.
              assert (Hi4'' : i4' < S n') by lia.
              apply trans_thread_schedule_val_SS with (i':=(of_nat_lt Hi')) in H.
              eexists. apply H. rewrite Hequ. apply CIH; clear CIH. admit. admit.
              right. left. split; auto.
              exists (of_nat_lt Hi3''), (of_nat_lt Hi4'').
              split; [| split; [| split]]; try solve [rewrite <- of_nat_lt_sig1_neq; auto].
              split; [| split].
              - rewrite <- (of_nat_to_nat_inv i2). rewrite Hi2. cbn.
                assert (i3' = i2' \/ i3' > i2') by lia. destruct H3.
                + subst. erewrite <- remove_vec_index_eq; eauto.
                  erewrite <- remove_vec_index_before; eauto.
                  rewrite <- (of_nat_to_nat_inv i3) in Hi1sb.
                  rewrite <- (of_nat_to_nat_inv i4) in Hi1sb.
                  rewrite Hi3, Hi4 in Hi1sb. cbn in Hi1sb.
                  apply Hi1sb.
                + erewrite <- remove_vec_index_after; eauto.
                  erewrite <- remove_vec_index_before; eauto.
                  rewrite <- (of_nat_to_nat_inv i3) in Hi1sb.
                  rewrite <- (of_nat_to_nat_inv i4) in Hi1sb.
                  rewrite Hi3, Hi4 in Hi1sb. cbn in Hi1sb.
                  apply Hi1sb.
              - rewrite <- (of_nat_to_nat_inv i2). rewrite Hi2. cbn.
                assert (i3' = i2' \/ i3' > i2') by lia. destruct H3.
                + subst. erewrite <- remove_vec_index_eq; eauto.
                  erewrite <- remove_vec_index_before; eauto.
                  rewrite <- (of_nat_to_nat_inv i3) in Hi2sb.
                  rewrite <- (of_nat_to_nat_inv i4) in Hi2sb.
                  rewrite Hi3, Hi4 in Hi2sb. cbn in Hi2sb.
                  apply Hi2sb.
                + erewrite <- remove_vec_index_after; eauto.
                  erewrite <- remove_vec_index_before; eauto.
                  rewrite <- (of_nat_to_nat_inv i3) in Hi2sb.
                  rewrite <- (of_nat_to_nat_inv i4) in Hi2sb.
                  rewrite Hi3, Hi4 in Hi2sb. cbn in Hi2sb.
                  apply Hi2sb.
              - intros.
                destruct (to_nat i0) as [i0' Hi0'] eqn:Hi0.
                rewrite <- (of_nat_to_nat_inv i2). rewrite Hi2.
                rewrite <- (of_nat_to_nat_inv i0). rewrite Hi0. cbn.
                rewrite <- (of_nat_to_nat_inv i0) in H3, H4. rewrite Hi0 in H3, H4. cbn in *.
                assert (i0' < i2' \/ i0' = i2' \/ i0' > i2') by lia.
                destruct H5 as [? | [? | ?]].
                + assert (Hi0'' : i0' < S (S n')) by lia.
                  specialize (Hothers (of_nat_lt Hi0'')).
                  rewrite <- of_nat_lt_sig1_neq in H3.
                  rewrite <- of_nat_lt_sig1_neq in H4.
                  do 2 (erewrite <- remove_vec_index_before; eauto).
                  eapply Hothers; eauto.
                  * rewrite <- (of_nat_to_nat_inv i3). rewrite Hi3.
                    rewrite <- of_nat_lt_sig1_neq. cbn. lia.
                  * rewrite <- (of_nat_to_nat_inv i4). rewrite Hi4. cbn.
                    rewrite <- of_nat_lt_sig1_neq. auto.
                + subst. rename i2' into i0'.
                  assert (Hi0'' : S i0' < S (S n')) by lia.
                  specialize (Hothers (of_nat_lt Hi0'')).
                  do 2 (erewrite <- remove_vec_index_eq; eauto).
                  eapply Hothers; eauto.
                  * rewrite <- (of_nat_to_nat_inv i3). rewrite Hi3.
                    rewrite <- of_nat_lt_sig1_neq in H3.
                    rewrite <- of_nat_lt_sig1_neq. cbn. lia.
                  * rewrite <- (of_nat_to_nat_inv i4). rewrite Hi4.
                    rewrite <- of_nat_lt_sig1_neq. cbn. lia.
                + assert (Hi0'' : S i0' < S (S n')) by lia.
                  specialize (Hothers (of_nat_lt Hi0'')).
                  do 2 (erewrite <- remove_vec_index_after; eauto).
                  eapply Hothers; eauto.
                  * rewrite <- (of_nat_to_nat_inv i3). rewrite Hi3.
                    rewrite <- of_nat_lt_sig1_neq in H3.
                    rewrite <- of_nat_lt_sig1_neq. cbn. lia.
                  * rewrite <- (of_nat_to_nat_inv i4). rewrite Hi4.
                    rewrite <- of_nat_lt_sig1_neq. cbn. lia.
            }
          }
          (* i3' > i2', i4' > i2' *)
          {
            destruct i3'. inv H1.
            destruct i4'. inv H2.
            assert (Hneq4: i3' <> i4').
            {
              rewrite <- (of_nat_to_nat_inv i3) in Hneq1. rewrite Hi3 in Hneq1.
              rewrite <- (of_nat_to_nat_inv i4) in Hneq1. rewrite Hi4 in Hneq1.
              rewrite <- of_nat_lt_sig1_neq in Hneq1. cbn in Hneq1. lia.
            }

            destruct (PeanoNat.Nat.eq_dec i' i3'); [| destruct (PeanoNat.Nat.eq_dec i' i4')].
            {
              (* we are going to i3' next *)
              subst. rename Hi' into Hi3''.
              (* destruct i4'. inv H2. (* subtract i4' by one *) *)
              assert (Hi4'' : i4' < S n') by lia.
              apply trans_thread_schedule_val_SS with (i':=(of_nat_lt Hi4'')) in H.
              eexists. apply H. rewrite Hequ. apply CIH; clear CIH. admit. admit.
              right. right. split.
              {
                intro. eapply f_equal in H3. do 2 rewrite to_nat_of_nat in H3.
                inv H3. contradiction.
              }
              split; [| split].
              - rewrite <- (of_nat_to_nat_inv i2). rewrite Hi2. cbn.
                assert (i3' = i2' \/ i3' > i2') by lia.
                assert (i4' = i2' \/ i4' > i2') by lia. destruct H3, H4.
                + do 2 (erewrite <- remove_vec_index_eq; eauto).
                  rewrite <- (of_nat_to_nat_inv i3) in Hi1sb.
                  rewrite <- (of_nat_to_nat_inv i4) in Hi1sb.
                  rewrite Hi3, Hi4 in Hi1sb. cbn in Hi1sb.
                  apply Hi1sb.
                + erewrite <- remove_vec_index_eq; eauto.
                  erewrite <- remove_vec_index_after; eauto.
                  rewrite <- (of_nat_to_nat_inv i3) in Hi1sb.
                  rewrite <- (of_nat_to_nat_inv i4) in Hi1sb.
                  rewrite Hi3, Hi4 in Hi1sb. cbn in Hi1sb.
                  apply Hi1sb.
                + erewrite <- remove_vec_index_after; eauto.
                  erewrite <- remove_vec_index_eq; eauto.
                  rewrite <- (of_nat_to_nat_inv i3) in Hi1sb.
                  rewrite <- (of_nat_to_nat_inv i4) in Hi1sb.
                  rewrite Hi3, Hi4 in Hi1sb. cbn in Hi1sb.
                  apply Hi1sb.
                + do 2 (erewrite <- remove_vec_index_after; eauto).
                  rewrite <- (of_nat_to_nat_inv i3) in Hi1sb.
                  rewrite <- (of_nat_to_nat_inv i4) in Hi1sb.
                  rewrite Hi3, Hi4 in Hi1sb. cbn in Hi1sb.
                  apply Hi1sb.
              - rewrite <- (of_nat_to_nat_inv i2). rewrite Hi2. cbn.
                assert (i3' = i2' \/ i3' > i2') by lia.
                assert (i4' = i2' \/ i4' > i2') by lia. destruct H3, H4.
                + do 2 (erewrite <- remove_vec_index_eq; eauto).
                  rewrite <- (of_nat_to_nat_inv i3) in Hi2sb.
                  rewrite <- (of_nat_to_nat_inv i4) in Hi2sb.
                  rewrite Hi3, Hi4 in Hi2sb. cbn in Hi2sb.
                  apply Hi2sb.
                + erewrite <- remove_vec_index_eq; eauto.
                  erewrite <- remove_vec_index_after; eauto.
                  rewrite <- (of_nat_to_nat_inv i3) in Hi2sb.
                  rewrite <- (of_nat_to_nat_inv i4) in Hi2sb.
                  rewrite Hi3, Hi4 in Hi2sb. cbn in Hi2sb.
                  apply Hi2sb.
                + erewrite <- remove_vec_index_after; eauto.
                  erewrite <- remove_vec_index_eq; eauto.
                  rewrite <- (of_nat_to_nat_inv i3) in Hi2sb.
                  rewrite <- (of_nat_to_nat_inv i4) in Hi2sb.
                  rewrite Hi3, Hi4 in Hi2sb. cbn in Hi2sb.
                  apply Hi2sb.
                + do 2 (erewrite <- remove_vec_index_after; eauto).
                  rewrite <- (of_nat_to_nat_inv i3) in Hi2sb.
                  rewrite <- (of_nat_to_nat_inv i4) in Hi2sb.
                  rewrite Hi3, Hi4 in Hi2sb. cbn in Hi2sb.
                  apply Hi2sb.
              - intros.
                destruct (to_nat i0) as [i0' Hi0'] eqn:Hi0.
                rewrite <- (of_nat_to_nat_inv i2). rewrite Hi2.
                rewrite <- (of_nat_to_nat_inv i0). rewrite Hi0. cbn.
                rewrite <- (of_nat_to_nat_inv i0) in H3, H4. rewrite Hi0 in H3, H4. cbn in *.
                assert (i0' < i2' \/ i0' = i2' \/ i0' > i2') by lia.
                destruct H5 as [? | [? | ?]].
                + assert (Hi0'' : i0' < S (S n')) by lia.
                  specialize (Hothers (of_nat_lt Hi0'')).
                  rewrite <- of_nat_lt_sig1_neq in H3.
                  rewrite <- of_nat_lt_sig1_neq in H4.
                  do 2 (erewrite <- remove_vec_index_before; eauto).
                  eapply Hothers; eauto.
                  * rewrite <- (of_nat_to_nat_inv i3). rewrite Hi3.
                    rewrite <- of_nat_lt_sig1_neq. cbn. lia.
                  * rewrite <- (of_nat_to_nat_inv i4). rewrite Hi4.
                    rewrite <- of_nat_lt_sig1_neq. cbn. lia.
                + subst. rename i2' into i0'.
                  assert (Hi0'' : S i0' < S (S n')) by lia.
                  specialize (Hothers (of_nat_lt Hi0'')).
                  do 2 (erewrite <- remove_vec_index_eq; eauto).
                  eapply Hothers; eauto.
                  * rewrite <- (of_nat_to_nat_inv i3). rewrite Hi3.
                    rewrite <- of_nat_lt_sig1_neq in H3.
                    rewrite <- of_nat_lt_sig1_neq. cbn. lia.
                  * rewrite <- (of_nat_to_nat_inv i4). rewrite Hi4.
                    rewrite <- of_nat_lt_sig1_neq in H4.
                    rewrite <- of_nat_lt_sig1_neq. cbn. lia.
                + assert (Hi0'' : S i0' < S (S n')) by lia.
                  specialize (Hothers (of_nat_lt Hi0'')).
                  do 2 (erewrite <- remove_vec_index_after; eauto).
                  eapply Hothers; eauto.
                  * rewrite <- (of_nat_to_nat_inv i3). rewrite Hi3.
                    rewrite <- of_nat_lt_sig1_neq in H3.
                    rewrite <- of_nat_lt_sig1_neq. cbn. lia.
                  * rewrite <- (of_nat_to_nat_inv i4). rewrite Hi4.
                    rewrite <- of_nat_lt_sig1_neq in H4.
                    rewrite <- of_nat_lt_sig1_neq. cbn. lia.
            }
            {
              (* we are going to i4' next *)
              subst. rename Hi' into Hi4''.
              assert (Hi3'' : i3' < S n') by lia.
              apply trans_thread_schedule_val_SS with (i':=(of_nat_lt Hi3'')) in H.
              eexists. apply H. rewrite Hequ. apply CIH; clear CIH. admit. admit.
              right. right. split.
              {
                intro. eapply f_equal in H3. do 2 rewrite to_nat_of_nat in H3.
                inv H3. contradiction.
              }
              split; [| split].
              - rewrite <- (of_nat_to_nat_inv i2). rewrite Hi2.
                assert (i4' = i2' \/ i4' > i2') by lia.
                assert (i3' = i2' \/ i3' > i2') by lia. destruct H3, H4.
                + do 2 (erewrite <- remove_vec_index_eq; eauto).
                  rewrite <- (of_nat_to_nat_inv i3) in Hi2sb.
                  rewrite <- (of_nat_to_nat_inv i4) in Hi2sb.
                  rewrite Hi3, Hi4 in Hi2sb. cbn in Hi2sb.
                  symmetry. eapply Hi2sb.
                + erewrite <- remove_vec_index_eq; eauto.
                  erewrite <- remove_vec_index_after; eauto.
                  rewrite <- (of_nat_to_nat_inv i3) in Hi2sb.
                  rewrite <- (of_nat_to_nat_inv i4) in Hi2sb.
                  rewrite Hi3, Hi4 in Hi2sb. cbn in Hi2sb.
                  symmetry. eapply Hi2sb.
                + erewrite <- remove_vec_index_after; eauto.
                  erewrite <- remove_vec_index_eq; eauto.
                  rewrite <- (of_nat_to_nat_inv i3) in Hi2sb.
                  rewrite <- (of_nat_to_nat_inv i4) in Hi2sb.
                  rewrite Hi3, Hi4 in Hi2sb. cbn in Hi2sb.
                  symmetry. eapply Hi2sb.
                + do 2 (erewrite <- remove_vec_index_after; eauto).
                  rewrite <- (of_nat_to_nat_inv i3) in Hi2sb.
                  rewrite <- (of_nat_to_nat_inv i4) in Hi2sb.
                  rewrite Hi3, Hi4 in Hi2sb. cbn in Hi2sb.
                  symmetry. eapply Hi2sb.
              - rewrite <- (of_nat_to_nat_inv i2). rewrite Hi2. cbn.
                assert (i4' = i2' \/ i4' > i2') by lia.
                assert (i3' = i2' \/ i3' > i2') by lia. destruct H3, H4.
                + do 2 (erewrite <- remove_vec_index_eq; eauto).
                  rewrite <- (of_nat_to_nat_inv i3) in Hi1sb.
                  rewrite <- (of_nat_to_nat_inv i4) in Hi1sb.
                  rewrite Hi3, Hi4 in Hi1sb. cbn in Hi1sb.
                  symmetry. eapply Hi1sb.
                + erewrite <- remove_vec_index_eq; eauto.
                  erewrite <- remove_vec_index_after; eauto.
                  rewrite <- (of_nat_to_nat_inv i3) in Hi1sb.
                  rewrite <- (of_nat_to_nat_inv i4) in Hi1sb.
                  rewrite Hi3, Hi4 in Hi1sb. cbn in Hi1sb.
                  symmetry. eapply Hi1sb.
                + erewrite <- remove_vec_index_after; eauto.
                  erewrite <- remove_vec_index_eq; eauto.
                  rewrite <- (of_nat_to_nat_inv i3) in Hi1sb.
                  rewrite <- (of_nat_to_nat_inv i4) in Hi1sb.
                  rewrite Hi3, Hi4 in Hi1sb. cbn in Hi1sb.
                  symmetry. eapply Hi1sb.
                + do 2 (erewrite <- remove_vec_index_after; eauto).
                  rewrite <- (of_nat_to_nat_inv i3) in Hi1sb.
                  rewrite <- (of_nat_to_nat_inv i4) in Hi1sb.
                  rewrite Hi3, Hi4 in Hi1sb. cbn in Hi1sb.
                  symmetry. eapply Hi1sb.
              - intros.
                destruct (to_nat i0) as [i0' Hi0'] eqn:Hi0.
                rewrite <- (of_nat_to_nat_inv i2). rewrite Hi2.
                rewrite <- (of_nat_to_nat_inv i0). rewrite Hi0. cbn.
                rewrite <- (of_nat_to_nat_inv i0) in H3, H4. rewrite Hi0 in H3, H4. cbn in *.
                assert (i0' < i2' \/ i0' = i2' \/ i0' > i2') by lia.
                destruct H5 as [? | [? | ?]].
                + assert (Hi0'' : i0' < S (S n')) by lia.
                  specialize (Hothers (of_nat_lt Hi0'')).
                  rewrite <- of_nat_lt_sig1_neq in H3.
                  rewrite <- of_nat_lt_sig1_neq in H4.
                  do 2 (erewrite <- remove_vec_index_before; eauto).
                  eapply Hothers; eauto.
                  * rewrite <- (of_nat_to_nat_inv i3). rewrite Hi3.
                    rewrite <- of_nat_lt_sig1_neq. cbn. lia.
                  * rewrite <- (of_nat_to_nat_inv i4). rewrite Hi4.
                    rewrite <- of_nat_lt_sig1_neq. cbn. lia.
                + subst. rename i2' into i0'.
                  assert (Hi0'' : S i0' < S (S n')) by lia.
                  specialize (Hothers (of_nat_lt Hi0'')).
                  do 2 (erewrite <- remove_vec_index_eq; eauto).
                  eapply Hothers; eauto.
                  * rewrite <- (of_nat_to_nat_inv i3). rewrite Hi3.
                    rewrite <- of_nat_lt_sig1_neq in H4.
                    rewrite <- of_nat_lt_sig1_neq. cbn. lia.
                  * rewrite <- (of_nat_to_nat_inv i4). rewrite Hi4.
                    rewrite <- of_nat_lt_sig1_neq in H3.
                    rewrite <- of_nat_lt_sig1_neq. cbn. lia.
                + assert (Hi0'' : S i0' < S (S n')) by lia.
                  specialize (Hothers (of_nat_lt Hi0'')).
                  do 2 (erewrite <- remove_vec_index_after; eauto).
                  eapply Hothers; eauto.
                  * rewrite <- (of_nat_to_nat_inv i3). rewrite Hi3.
                    rewrite <- of_nat_lt_sig1_neq in H4.
                    rewrite <- of_nat_lt_sig1_neq. cbn. lia.
                  * rewrite <- (of_nat_to_nat_inv i4). rewrite Hi4.
                    rewrite <- of_nat_lt_sig1_neq in H3.
                    rewrite <- of_nat_lt_sig1_neq. cbn. lia.
            }
            {
              (* we are going to i', which is not one of the swapped elements *)
              assert (Hi3'' : i3' < S n') by lia.
              assert (Hi4'' : i4' < S n') by lia.
              apply trans_thread_schedule_val_SS with (i':=(of_nat_lt Hi')) in H.
              eexists. apply H. rewrite Hequ. apply CIH; clear CIH. admit. admit.
              right. left. split; auto.
              exists (of_nat_lt Hi3''), (of_nat_lt Hi4'').
              split; [| split; [| split]]; try solve [rewrite <- of_nat_lt_sig1_neq; auto].
              split; [| split].
              - rewrite <- (of_nat_to_nat_inv i2). rewrite Hi2. cbn.
                assert (i3' = i2' \/ i3' > i2') by lia.
                assert (i4' = i2' \/ i4' > i2') by lia. destruct H3, H4.
                + do 2 (erewrite <- remove_vec_index_eq; eauto).
                  rewrite <- (of_nat_to_nat_inv i3) in Hi1sb.
                  rewrite <- (of_nat_to_nat_inv i4) in Hi1sb.
                  rewrite Hi3, Hi4 in Hi1sb. cbn in Hi1sb.
                  apply Hi1sb.
                + erewrite <- remove_vec_index_eq; eauto.
                  erewrite <- remove_vec_index_after; eauto.
                  rewrite <- (of_nat_to_nat_inv i3) in Hi1sb.
                  rewrite <- (of_nat_to_nat_inv i4) in Hi1sb.
                  rewrite Hi3, Hi4 in Hi1sb. cbn in Hi1sb.
                  apply Hi1sb.
                + erewrite <- remove_vec_index_after; eauto.
                  erewrite <- remove_vec_index_eq; eauto.
                  rewrite <- (of_nat_to_nat_inv i3) in Hi1sb.
                  rewrite <- (of_nat_to_nat_inv i4) in Hi1sb.
                  rewrite Hi3, Hi4 in Hi1sb. cbn in Hi1sb.
                  apply Hi1sb.
                + do 2 (erewrite <- remove_vec_index_after; eauto).
                  rewrite <- (of_nat_to_nat_inv i3) in Hi1sb.
                  rewrite <- (of_nat_to_nat_inv i4) in Hi1sb.
                  rewrite Hi3, Hi4 in Hi1sb. cbn in Hi1sb.
                  apply Hi1sb.
              - rewrite <- (of_nat_to_nat_inv i2). rewrite Hi2. cbn.
                assert (i3' = i2' \/ i3' > i2') by lia.
                assert (i4' = i2' \/ i4' > i2') by lia. destruct H3, H4.
                + do 2 (erewrite <- remove_vec_index_eq; eauto).
                  rewrite <- (of_nat_to_nat_inv i3) in Hi2sb.
                  rewrite <- (of_nat_to_nat_inv i4) in Hi2sb.
                  rewrite Hi3, Hi4 in Hi2sb. cbn in Hi2sb.
                  apply Hi2sb.
                + erewrite <- remove_vec_index_eq; eauto.
                  erewrite <- remove_vec_index_after; eauto.
                  rewrite <- (of_nat_to_nat_inv i3) in Hi2sb.
                  rewrite <- (of_nat_to_nat_inv i4) in Hi2sb.
                  rewrite Hi3, Hi4 in Hi2sb. cbn in Hi2sb.
                  apply Hi2sb.
                + erewrite <- remove_vec_index_after; eauto.
                  erewrite <- remove_vec_index_eq; eauto.
                  rewrite <- (of_nat_to_nat_inv i3) in Hi2sb.
                  rewrite <- (of_nat_to_nat_inv i4) in Hi2sb.
                  rewrite Hi3, Hi4 in Hi2sb. cbn in Hi2sb.
                  apply Hi2sb.
                + do 2 (erewrite <- remove_vec_index_after; eauto).
                  rewrite <- (of_nat_to_nat_inv i3) in Hi2sb.
                  rewrite <- (of_nat_to_nat_inv i4) in Hi2sb.
                  rewrite Hi3, Hi4 in Hi2sb. cbn in Hi2sb.
                  apply Hi2sb.
              - intros.
                destruct (to_nat i0) as [i0' Hi0'] eqn:Hi0.
                rewrite <- (of_nat_to_nat_inv i2). rewrite Hi2.
                rewrite <- (of_nat_to_nat_inv i0). rewrite Hi0. cbn.
                rewrite <- (of_nat_to_nat_inv i0) in H3, H4. rewrite Hi0 in H3, H4. cbn in *.
                assert (i0' < i2' \/ i0' = i2' \/ i0' > i2') by lia.
                destruct H5 as [? | [? | ?]].
                + assert (Hi0'' : i0' < S (S n')) by lia.
                  specialize (Hothers (of_nat_lt Hi0'')).
                  rewrite <- of_nat_lt_sig1_neq in H3.
                  rewrite <- of_nat_lt_sig1_neq in H4.
                  do 2 (erewrite <- remove_vec_index_before; eauto).
                  eapply Hothers; eauto.
                  * rewrite <- (of_nat_to_nat_inv i3). rewrite Hi3.
                    rewrite <- of_nat_lt_sig1_neq. cbn. lia.
                  * rewrite <- (of_nat_to_nat_inv i4). rewrite Hi4.
                    rewrite <- of_nat_lt_sig1_neq. cbn. lia.
                + subst. rename i2' into i0'.
                  assert (Hi0'' : S i0' < S (S n')) by lia.
                  specialize (Hothers (of_nat_lt Hi0'')).
                  do 2 (erewrite <- remove_vec_index_eq; eauto).
                  eapply Hothers; eauto.
                  * rewrite <- (of_nat_to_nat_inv i3). rewrite Hi3.
                    rewrite <- of_nat_lt_sig1_neq in H3.
                    rewrite <- of_nat_lt_sig1_neq. cbn. lia.
                  * rewrite <- (of_nat_to_nat_inv i4). rewrite Hi4.
                    rewrite <- of_nat_lt_sig1_neq in H4.
                    rewrite <- of_nat_lt_sig1_neq. cbn. lia.
                + assert (Hi0'' : S i0' < S (S n')) by lia.
                  specialize (Hothers (of_nat_lt Hi0'')).
                  do 2 (erewrite <- remove_vec_index_after; eauto).
                  eapply Hothers; eauto.
                  * rewrite <- (of_nat_to_nat_inv i3). rewrite Hi3.
                    rewrite <- of_nat_lt_sig1_neq in H3.
                    rewrite <- of_nat_lt_sig1_neq. cbn. lia.
                  * rewrite <- (of_nat_to_nat_inv i4). rewrite Hi4.
                    rewrite <- of_nat_lt_sig1_neq in H4.
                    rewrite <- of_nat_lt_sig1_neq. cbn. lia.
            }
          }
        * (* the finished thread is one of the swapped threads. this can lead to there still being 2 swapped threads, or no swapped threads, depending on the positions of the two threads *)
          rewrite <- (of_nat_to_nat_inv i) in Hequ. rewrite <- (of_nat_to_nat_inv i1) in Hequ.
          destruct (to_nat i) as [i' Hi'] eqn:Hi.
          destruct (to_nat i1) as [i1' Hi1'] eqn:Hi1. cbn in Hequ.
          destruct (to_nat i2) as [i2' Hi2'] eqn:Hi2.
          pose proof Hi1sb.
          step in H. destruct H as [Hf _].
          edestruct Hf as [? ? ?]; eauto.
          assert (i1' <> i2') by admit.
          assert (i1' = S i2' \/ i2' =  S i1' \/ S i1' < i2' \/ S i2' < i1') by lia.
          destruct H2 as [? | [? | [? | ?]]].
          -- (* | i2 | i1 |, no more swapped elements *)
            subst.
            assert (i' < i2' \/ i' = i2' \/ i' > i2') by lia. destruct H2.
            ++ eapply trans_thread_schedule_val_SS with (i':=(of_nat_lt Hi')) in H.
               eexists. apply H. rewrite Hequ. apply CIH; clear CIH. admit. admit.
               left. split; auto.
               intros. rewrite <- (of_nat_to_nat_inv i2). rewrite Hi2.
             assert (i4' < i2' \/ i4' > i2').
             cbn.
          -- (* | i1 | i2 |, no more swapped elements *)
          -- (* | i1 | ... | i2 |, still swapped elements *)
          -- (* | i2 | ... | i1 | *)

          (* copy struct from prev case, do case analysis on top level, then
             do case analysis here on what i is *)

          eapply trans_thread_schedule_val_SS with (i':=(of_nat_lt Hi')) in H.
          eexists. apply H. rewrite Hequ. apply CIH; clear CIH. admit. admit.


          (* we just removed one of the swapped ones, so now it can either be all in order or there can still be one swapped.... *)
          (* right. left. split; auto.  *)
          left. split; eauto.
          intros. admit.
      + (* tau step *)
        destruct n; try inv i1.
        destruct H0 as (t' & Ht & Hbound & Hequ).
        destruct Hi as [
            (? & Hv) | [
              (? & i3 & i4 & Hneq1 & Hneq2 & Hneq3 & Hi1sb & Hi2sb & Hothers) |
              (Hneq & Hi1sb & Hi2sb & Hothers)]].
        * subst. pose proof (Hv i2). step in H. destruct H as [Hf _].
          edestruct Hf as [? ? ?]; eauto.
          epose proof (trans_choiceI_bound _ _ _ _ _ H).
          apply trans_thread_schedule_tau in H.
          eexists; eauto. rewrite Hequ. apply CIH. admit. admit.
          left. split; auto.
          intros. destruct (Fin.eq_dec i i2).
          -- subst. do 2 rewrite replace_vec_eq. auto.
          -- do 2 (rewrite replace_vec_neq; auto).
        * subst. epose proof (Hothers i2 _ _); eauto. step in H. destruct H as [Hf _].
          edestruct Hf as [? ? ?]; eauto.
          epose proof (trans_choiceI_bound _ _ _ _ _ H).
          apply trans_thread_schedule_tau in H.
          eexists; eauto. rewrite Hequ. apply CIH. admit. admit.
          right. left. split; auto. exists i3, i4. split; [| split; [| split]]; auto.
          split; [| split].
          -- do 2 (rewrite replace_vec_neq; auto).
          -- do 2 (rewrite replace_vec_neq; auto).
          -- intros. destruct (Fin.eq_dec i i2).
             ++ subst. do 2 rewrite replace_vec_eq; auto.
             ++ do 2 (rewrite replace_vec_neq; auto); auto.
        * step in Hi1sb. destruct Hi1sb as [Hf _].
          edestruct Hf as [? ? ?]; eauto.
          epose proof (trans_choiceI_bound _ _ _ _ _ H).
          apply trans_thread_schedule_tau in H.
          eexists; eauto. rewrite Hequ. apply CIH. admit. admit.
          right. right. split; auto.
          split; [| split].
          -- do 2 rewrite replace_vec_eq; auto.
          -- do 2 (rewrite replace_vec_neq; auto).
          -- intros. do 2 (rewrite replace_vec_neq; auto).
      + (* The thread yields *)
        destruct H as (k & Hvis & i' & Hequ).
        destruct Hi as [
            (? & Hv) | [
              (? & i3 & i4 & Hneq1 & Hneq2 & Hneq3 & Hi1sb & Hi2sb & Hothers) |
              (Hneq & Hi1sb & Hi2sb & Hothers)]].
        * subst. destruct n; try inv i2.
          pose proof Hvis as Hvis'.
          eapply sbisim_visible in Hvis'. 5: apply Hv. all: auto.
          destruct Hvis' as (k' & Hvis' & Hk).
          exists (schedule (S n) (replace_vec v2 i2 (k' tt)) (Some i')).
          2: { rewrite Hequ. apply CIH. admit. admit.
               left. split; auto. intros.
               apply replace_vec_vec_relation; auto.
          }
          apply visible_yield_trans_schedule; auto.
        * subst. destruct n; try inv i2.
          pose proof Hvis as Hvis'.
          eapply sbisim_visible in Hvis'. 5: apply Hothers; auto. all: auto.
          destruct Hvis' as (k' & Hvis' & Hk).
          destruct (Fin.eq_dec i' i3); [| destruct (Fin.eq_dec i' i4)]; subst.
          -- (* we are going to i3 *)
            exists (schedule (S n) (replace_vec v2 i2 (k' tt)) (Some i4)).
            2: { rewrite Hequ. apply CIH. admit. admit.
                 right. right. split; auto. split; [| split]; auto.
                 - do 2 (rewrite replace_vec_neq; auto).
                 - do 2 (rewrite replace_vec_neq; auto).
                 - intros. destruct (Fin.eq_dec i2 i).
                   + subst. do 2 (rewrite replace_vec_eq; auto).
                   + do 2 (rewrite replace_vec_neq; auto).
            }
          apply visible_yield_trans_schedule; auto.
          -- (* we are going to i4 *)
            exists (schedule (S n) (replace_vec v2 i2 (k' tt)) (Some i3)).
            2: { rewrite Hequ. apply CIH. admit. admit.
                 right. right. split; auto. split; [| split]; auto.
                 - do 2 (rewrite replace_vec_neq; auto). symmetry; auto.
                 - do 2 (rewrite replace_vec_neq; auto). symmetry; auto.
                 - intros. destruct (Fin.eq_dec i2 i).
                   + subst. do 2 (rewrite replace_vec_eq; auto).
                   + do 2 (rewrite replace_vec_neq; auto).
            }
            apply visible_yield_trans_schedule; auto.
          -- (* we are not going to a swapped element *)
            exists (schedule (S n) (replace_vec v2 i2 (k' tt)) (Some i')).
            2: { rewrite Hequ. apply CIH. admit. admit.
                 right. left. split; auto. exists i3, i4. split; [| split; [| split]]; auto.
                 split; [| split]; auto.
                 - do 2 (rewrite replace_vec_neq; auto).
                 - do 2 (rewrite replace_vec_neq; auto).
                 - intros. destruct (Fin.eq_dec i2 i).
                   + subst. do 2 (rewrite replace_vec_eq; auto).
                   + do 2 (rewrite replace_vec_neq; auto).
            }
            apply visible_yield_trans_schedule; auto.
        * destruct n; try inv i2.
          pose proof Hvis as Hvis'.
          eapply sbisim_visible in Hvis'. 5: apply Hi1sb. all: auto.
          destruct Hvis' as (k' & Hvis' & Hk).
          destruct (Fin.eq_dec i' i1); [| destruct (Fin.eq_dec i' i2)]; subst.
          -- (* going to i1 *)
            exists (schedule (S n) (replace_vec v2 i2 (k' tt)) (Some i2)).
            2: { rewrite Hequ. apply CIH. admit. admit.
                 right. right. split; auto. split; [| split]; auto.
                 - do 2 (rewrite replace_vec_eq; auto).
                 - do 2 (rewrite replace_vec_neq; auto).
                 - intros. do 2 (rewrite replace_vec_neq; auto).
            }
            apply visible_yield_trans_schedule; auto.
          -- (* going to i2 *)
            exists (schedule (S n) (replace_vec v2 i2 (k' tt)) (Some i1)).
            2: { rewrite Hequ. apply CIH. admit. admit.
                 right. right. split; auto. split; [| split]; auto.
                 - do 2 (rewrite replace_vec_neq; auto). symmetry; auto.
                 - do 2 (rewrite replace_vec_eq; auto). symmetry; auto.
                 - intros. do 2 (rewrite replace_vec_neq; auto).
            }
            apply visible_yield_trans_schedule; auto.
          -- (* not going to a swapped element *)
            exists (schedule (S n) (replace_vec v2 i2 (k' tt)) (Some i')).
            2: { rewrite Hequ. apply CIH. admit. admit.
                 right. left. split; auto. exists i1, i2. split; [| split; [| split]]; auto.
                 split; [| split]; auto.
                 - do 2 (rewrite replace_vec_eq; auto).
                 - do 2 (rewrite replace_vec_neq; auto).
                 - intros. do 2 (rewrite replace_vec_neq; auto).
            }
            apply visible_yield_trans_schedule; auto.
      + (* the thread spawns a new thread *)
        destruct H as (k & Hvis & Hequ).
        destruct Hi as [
            (? & Hv) | [
              (? & i3 & i4 & Hneq1 & Hneq2 & Hneq3 & Hi1sb & Hi2sb & Hothers) |
              (Hneq & Hi1sb & Hi2sb & Hothers)]].
        * subst.
          destruct n; try inv i2.
          pose proof Hvis as Hvis'.
          eapply sbisim_visible in Hvis'. 5: apply Hv. all: eauto.
          2: { constructor. apply true. }
          destruct Hvis' as (k' & ? & ?).
          exists (schedule (S (S n))
                      (cons_vec (k' true)
                                (replace_vec v2 i2 (k' false)))
                      (Some (Fin.FS i2))).
          2: { rewrite Hequ. apply CIH. admit. admit.
               left. split; auto. intros.
               apply cons_vec_vec_relation; auto.
               apply replace_vec_vec_relation; auto.
          }
          apply visible_spawn_trans_schedule; auto.
        * subst.
          destruct n; try inv i2.
          pose proof Hvis as Hvis'.
          eapply sbisim_visible in Hvis'. 5: apply Hothers; auto. all: eauto.
          2: { constructor. apply true. }
          destruct Hvis' as (k' & ? & ?).
          exists (schedule (S (S n))
                      (cons_vec (k' true)
                                (replace_vec v2 i2 (k' false)))
                      (Some (Fin.FS i2))).
          2: { rewrite Hequ. apply CIH. admit. admit.
               right. left. split; auto. exists (FS i3), (FS i4).
               split; [| split; [| split]]; auto. admit. admit. admit.
               split; [| split].
               - simp cons_vec. do 2 (rewrite replace_vec_neq; auto).
               - simp cons_vec. do 2 (rewrite replace_vec_neq; auto).
               - intros. dependent destruction i; simp cons_vec.
                 destruct (Fin.eq_dec i2 i).
                 + subst. do 2 (rewrite replace_vec_eq; auto).
                 + do 2 (rewrite replace_vec_neq; auto). apply Hothers. admit. admit.
          }
          apply visible_spawn_trans_schedule; auto.
        * destruct n; try inv i2.
          pose proof Hvis as Hvis'.
          eapply sbisim_visible in Hvis'. 5: apply Hi1sb. all: eauto.
          2: { constructor. apply true. }
          destruct Hvis' as (k' & ? & ?).
          exists (schedule (S (S n))
                      (cons_vec (k' true)
                                (replace_vec v2 i2 (k' false)))
                      (Some (Fin.FS i2))).
          2: { rewrite Hequ. apply CIH. admit. admit.
               right. right. split. admit.
               split; [| split].
               - simp cons_vec. do 2 (rewrite replace_vec_eq; auto).
               - simp cons_vec. do 2 (rewrite replace_vec_neq; auto).
               - intros. dependent destruction i; simp cons_vec.
                 assert (i <> i1) by admit.
                 assert (i <> i2) by admit.
                 do 2 (rewrite replace_vec_neq; auto).
          }
          apply visible_spawn_trans_schedule; auto.
    - apply trans_schedule_obs in Ht.
      destruct Ht as (k & i & s & ? & ? & Hvis & Hequ). inv H.
      destruct n; try inv i.
      pose proof Hvis as Hvis'.
      destruct Hi as [
          (? & Hv) | [
            (? & i3 & i4 & Hneq1 & Hneq2 & Hneq3 & Hi1 & Hi2 & Hothers) |
            (Hneq & Hi1 & Hi2 & Hothers)]].
      + subst. pose proof (Hv i2).
        eapply sbisim_visible in Hvis'. 5: apply Hv. all: eauto.
        destruct Hvis' as (k' & ? & ?).
        exists (schedule (S n) (replace_vec v2 i2 (k' v)) (Some i2)).
        2: { rewrite Hequ. apply CIH; clear CIH. admit. admit.
             left. split; auto.
             intros. destruct (Fin.eq_dec i2 i).
             - subst. do 2 rewrite replace_vec_eq; auto.
             - do 2 (rewrite replace_vec_neq; auto).
        }
        eapply visible_stateE_trans_schedule in H0; eauto.
      + subst. eapply sbisim_visible in Hvis'. 5: apply Hothers; auto. all: auto.
        destruct Hvis' as (k' & ? & ?).
        exists (schedule (S n) (replace_vec v2 i2 (k' v)) (Some i2)).
        2: { rewrite Hequ. apply CIH; clear CIH. admit. admit.
             right. left. split; auto.
             exists i3, i4. split; [| split; [| split]]; auto.
             split; [| split].
             - do 2 (rewrite replace_vec_neq; auto).
             - do 2 (rewrite replace_vec_neq; auto).
             - intros. destruct (Fin.eq_dec i2 i).
               + subst. do 2 rewrite replace_vec_eq; auto.
               + do 2 (rewrite replace_vec_neq; auto).
        }
        eapply visible_stateE_trans_schedule in H; eauto.
      + eapply sbisim_visible in Hvis'. 5: apply Hi1. all: auto.
        destruct Hvis' as (k' & ? & ?).
        exists (schedule (S n) (replace_vec v2 i2 (k' v)) (Some i2)).
        2: { rewrite Hequ. apply CIH; clear CIH. admit. admit.
             right. right. split; auto. split; [| split].
             - do 2 rewrite replace_vec_eq; auto.
             - do 2 (rewrite replace_vec_neq; auto).
             - intros. do 2 (rewrite replace_vec_neq; auto).
        }
        eapply visible_stateE_trans_schedule in H; eauto.
    - pose proof (trans_schedule_val_1 _ _ _ _ _ Ht). subst.
      pose proof (trans_val_inv Ht).
      destruct Hi as [
          (? & Hv) | [
            (? & i3 & i4 & Hneq1 & Hneq2 & Hneq3 & Hi1 & Hi2 & Hothers) |
            (Hneq & Hi1 & Hi2 & Hothers)]].
      + subst. pose proof (Hv i2). step in H0.
        destruct H0 as [Hf _].
        pose proof (trans_schedule_thread_val _ _ _ _ Ht) as Hv1.
        edestruct Hf; eauto.
        apply trans_thread_schedule_val_1 in H0. eexists; eauto. rewrite H. reflexivity.
      + subst. specialize (Hothers i2 Hneq2 Hneq3). step in Hothers.
        destruct Hothers as [Hf _].
        pose proof (trans_schedule_thread_val _ _ _ _ Ht) as Hv1.
        edestruct Hf; eauto.
        apply trans_thread_schedule_val_1 in H0. eexists; eauto. rewrite H. reflexivity.
      + step in Hi1. destruct Hi1 as [Hf _].
        pose proof (trans_schedule_thread_val _ _ _ _ Ht) as Hv1.
        edestruct Hf; eauto.
        apply trans_thread_schedule_val_1 in H0. eexists; eauto. rewrite H. reflexivity.
  Admitted.


  Lemma schedule_perm_2 n (v1 v2 : vec n) i1 i2 :
    v1 i1 ~ v2 i2 ->
    v2 i1 ~ v1 i2 ->
    (forall i, i <> i1 -> i <> i2 -> v1 i ~ v2 i) ->
    schedule n v1 (Some i1) ~ schedule n v2 (Some i2).
  Proof.
    revert n v1 v2 i1 i2.
    coinduction r CIH.
    symmetric using idtac. { intros. apply H; symmetry; auto. }
    intros n v1 v2 i1 i2 Hi1 Hi2 Hothers l t Ht. cbn in *.
    destruct l.
    - apply trans_schedule_thread_tau_some in Ht. 2: admit.
      decompose [or] Ht; clear Ht.
      + destruct H as (n' & i & Ht & ? & Hequ). subst.
        step in Hi1. destruct Hi1 as [Hf _].
        edestruct Hf as [? ? ?]; eauto.
        eapply trans_thread_schedule_val_SS in H.
        eexists. apply H. rewrite Hequ. apply CIH; cbn.
        * admit.
        * admit.
        * intros. admit.
      + destruct n; try inv i1.
        destruct H0 as (t' & Ht & Hbound & Hequ).
        step in Hi1. destruct Hi1 as [Hf _].
        edestruct Hf as [? ? ?]; eauto.
        epose proof (trans_choiceI_bound _ _ _ _ _ H).
        apply trans_thread_schedule_tau in H.
        eexists; eauto. rewrite Hequ. apply CIH.
        * do 2 rewrite replace_vec_eq. auto.
        * destruct (Fin.eq_dec i1 i2).
          -- subst. do 2 rewrite replace_vec_eq. symmetry. auto.
          -- do 2 (rewrite replace_vec_neq; auto).
        * intros. do 2 (rewrite replace_vec_neq; auto).
      + destruct H as (k & Hvis & i' & Hequ).
        pose proof Hvis as Hvis'.
        eapply sbisim_visible in Hvis'; eauto. 2, 3: admit.
        destruct Hvis' as (k' & ? & ?).
        destruct (Fin.eq_dec i' i1); [| destruct (Fin.eq_dec i' i2)]; subst.
        { (* i1 = i' *)
          exists (schedule n (replace_vec v2 i2 (k' tt)) (Some i2)).
          2: {
            rewrite Hequ. apply CIH.
            - do 2 rewrite replace_vec_eq; auto.
            - destruct (Fin.eq_dec i1 i2); subst.
              + do 2 rewrite replace_vec_eq. symmetry; auto.
              + do 2 (rewrite replace_vec_neq; auto).
            - intros. do 2 (rewrite replace_vec_neq; auto).
          }
          destruct n; try inv i1.
          apply visible_yield_trans_schedule; auto. admit.
        }
        { (* i1 <> i' = i2 *)
          exists (schedule n (replace_vec v2 i2 (k' tt)) (Some i1)).
          2: {
            rewrite Hequ. apply CIH.
            - do 2 (rewrite replace_vec_neq; auto). symmetry; auto.
            - do 2 rewrite replace_vec_eq. symmetry; auto.
            - intros. do 2 (rewrite replace_vec_neq; auto).
          }
          destruct n; try inv i1.
          apply visible_yield_trans_schedule; auto. admit.
        }
        { (* i1 <> i' <> i2 *)
          exists (schedule n (replace_vec v2 i2 (k' tt)) (Some i')).
          2: {
            rewrite Hequ. apply CIH.
            - do 2 (rewrite replace_vec_neq; auto).
            - do 2 (rewrite replace_vec_neq; auto). symmetry; auto.
            - intros. destruct (Fin.eq_dec i i1); destruct (Fin.eq_dec i i2); subst.
              + do 2 (rewrite replace_vec_eq; auto).
              + rewrite replace_vec_eq. rewrite replace_vec_neq; auto.
              + do 2 (rewrite replace_vec_eq; auto).
              + do 2 (rewrite replace_vec_eq; auto).
          }
          destruct n; try inv i1.
          apply visible_yield_trans_schedule; auto. admit.

        }
        destruct n; try inv i1.
        apply visible_yield_trans_schedule; auto. admit.
      +  destruct H as (k & Hvis & Hequ).
         pose proof Hvis as Hvis'.
         eapply sbisim_visible in Hvis'; eauto.
         2: { constructor. apply true. }
         2, 3: admit.
         destruct Hvis' as (k' & ? & ?).
         exists (schedule (S n)
                     (cons_vec (k' true)
                               (replace_vec v2 i2 (k' false)))
                     (Some (Fin.FS i2))).
         2: { rewrite Hequ. apply CIH.
              - admit.
              - admit.
              - intros. admit.
         }
         destruct n; try inv i1.
         apply visible_spawn_trans_schedule; auto. admit.
    - apply trans_schedule_obs in Ht.
      destruct Ht as (k & i & s & ? & ? & Hvis & Hequ). inv H.
      destruct n; try inv i.
      pose proof Hvis as Hvis'.
      eapply sbisim_visible in Hvis'; eauto. 2, 3: admit.
      destruct Hvis' as (k' & ? & ?).
      exists (schedule (S n) (replace_vec v2 i2 (k' v)) (Some i2)).
      2: { rewrite Hequ. apply CIH.
           admit. admit. admit.
      }
      eapply visible_stateE_trans_schedule in H; eauto. admit.
    - pose proof (trans_schedule_val_1 _ _ _ _ _ Ht). subst.
      pose proof (trans_val_inv Ht).
      step in Hi1. destruct Hi1 as [Hf _].
      pose proof (trans_schedule_thread_val _ _ _ _ Ht) as Hv1.
      edestruct Hf; eauto.
      apply trans_thread_schedule_val_1 in H0. eexists; eauto. rewrite H. reflexivity.
  Admitted.
*)
End parallel.
