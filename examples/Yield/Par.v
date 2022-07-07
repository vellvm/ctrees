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


(** [brD_bound] gives a bound on the arity of BrD nodes.
    To be replaced eventually with generalized br types. *)

Variant brD_boundF {E R} b (brD_bound : ctree E R -> Prop) :
  ctree' E R -> Prop :=
  | bound_Ret r : brD_boundF b brD_bound (RetF r)
  | bound_Vis {X} (e : E X) k : (forall x, brD_bound (k x)) ->
                                brD_boundF b brD_bound (VisF e k)
  | bound_brF {n} k : (forall i, brD_bound (k i)) ->
                          brD_boundF b brD_bound (BrF true n k)
  | bound_brD {n} k : (forall i, brD_bound (k i)) ->
                          (n <= b)%nat ->
                          brD_boundF b brD_bound (BrF false n k)
.
#[global] Hint Constructors brD_boundF: core.

Definition brD_bound_ {E R} b brD_bound : ctree E R -> Prop :=
  fun t => brD_boundF b brD_bound (observe t).

Obligation Tactic := idtac.
Program Definition fbrD_bound {E R} (b : nat) : mon (ctree E R -> Prop) :=
  {| body := brD_bound_ b |}.
Next Obligation.
  intros E R b ?? INC t H. inversion H; unfold brD_bound_ in *.
  - rewrite <- H1 in *. constructor.
  - rewrite <- H0 in *. constructor. intros. apply INC; auto.
  - rewrite <- H0 in *. constructor. intros. apply INC; auto.
  - rewrite <- H0 in *. constructor; auto. intros. apply INC; auto.
Qed.

Definition brD_bound {E R} b := (gfp (@fbrD_bound E R b)).
#[global] Hint Unfold brD_bound: core.

Notation ct Q := (t (fbrD_bound Q)).
Notation cT Q := (T (fbrD_bound Q)).
Notation cbt Q := (bt (fbrD_bound Q)).
Notation cbT Q := (bT (fbrD_bound Q)).

#[global] Instance equ_brD_bound {E R} b :
  Proper (equ eq ==> impl) (@brD_bound E R b).
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

#[global] Instance equ_brD_bound' {E R} b :
  Proper (equ eq ==> flip impl) (@brD_bound E R b).
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

Lemma brD_bound_1_inv {E R} n k x :
  brD_bound 1 (BrD n k : ctree E R) ->
  n = 1%nat /\ brD_bound 1 (k x).
Proof.
  intros Hbound.
  step in Hbound.
  inversion Hbound.
  destruct n.
  - inversion x.
  - split. lia. invert. apply H1.
Qed.

Lemma trans_brD_bound E R (t t' : ctree E R) l :
  brD_bound 1 t ->
  trans l t t' ->
  brD_bound 1 t'.
Proof.
  intros Hbound Htrans. revert Hbound.
  unfold trans in *.
  cbn in *. red in Htrans. dependent induction Htrans; intros.
  - eapply IHHtrans; auto.
    assert (t ≅ BrD n k). { rewrite ctree_eta. rewrite <- x. reflexivity. }
    rewrite H in Hbound. step in Hbound. inv Hbound. invert. auto.
  - assert (t' ≅ k x0).
    { rewrite ctree_eta. rewrite <- x. rewrite H. rewrite <- ctree_eta. reflexivity. }
    assert (t ≅ BrS n k).
    { rewrite ctree_eta. rewrite <- x1. reflexivity. }
    rewrite H1 in Hbound. rewrite H0. step in Hbound. inv Hbound. invert. auto.
  - assert (t' ≅ k x0).
    { rewrite ctree_eta. rewrite <- x. rewrite H. rewrite <- ctree_eta. reflexivity. }
    assert (t ≅ Vis e k).
    { rewrite ctree_eta. rewrite <- x1. reflexivity. }
    rewrite H1 in Hbound. rewrite H0. step in Hbound. inv Hbound. invert. auto.
  - rewrite ctree_eta. rewrite <- x. step. constructor; auto. intros. inv i.
Qed.

Lemma visible_brD_bound E R n (t t' : ctree E R) :
  brD_bound n t ->
  visible t t' ->
  brD_bound n t'.
Proof.
  intros Hbound Hvisible. revert n Hbound.
  cbn in *. red in Hvisible. dependent induction Hvisible; intros.
  - eapply IHHvisible; auto.
    assert (t ≅ BrD n k). { rewrite ctree_eta. rewrite <- x. reflexivity. }
    rewrite H in Hbound.
    step in Hbound. inv Hbound. invert. auto.
  - assert (t ≅ BrS n k1). { rewrite ctree_eta. rewrite <- x1. reflexivity. }
    assert (t' ≅ BrS n k2). { rewrite ctree_eta. rewrite <- x. reflexivity. }
    rewrite H0 in Hbound. rewrite H1. clear H0 H1 x x1.
    step in Hbound. inv Hbound. invert.
    red. apply (proj2 (gfp_fp (fbrD_bound n0) (BrS n k2))). cbn.
    constructor. intros. specialize (H1 i). fold (@brD_bound E R n0) in *.
    rewrite H in H1. auto.
  - assert (t ≅ Vis e k1). { rewrite ctree_eta. rewrite <- x0. reflexivity. }
    assert (t' ≅ Vis e k2). { rewrite ctree_eta. rewrite <- x. reflexivity. }
    rewrite H0 in Hbound. rewrite H1. clear H0 H1 x x0.
    step in Hbound. inv Hbound. invert.
    red. apply (proj2 (gfp_fp (fbrD_bound n) (Vis e k2))). cbn.
    constructor. intros. specialize (H1 x). fold (@brD_bound E R n) in *.
    rewrite H in H1. auto.
  - assert (t ≅ Ret r). { rewrite ctree_eta. rewrite <- x0. reflexivity. }
    assert (t' ≅ Ret r). { rewrite ctree_eta. rewrite <- x. reflexivity. }
    rewrite H in Hbound. rewrite H0. auto.
Qed.

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
    constructor; intros; auto; apply (f_Tf (fbrD_bound n)); econstructor; eauto.
Qed.

#[global] Instance equ_ct {E R} {r : ctree E R -> Prop} n :
  Proper ((equ eq) ==> flip impl) (ct n r).
Proof.
  unfold Proper, respectful, flip, impl. intros.
  apply (ft_t (equ_clos1_ct n)); econstructor; eauto.
Qed.

#[global] Instance equ_brD_boundF {E R r} n :
  Proper (going (equ eq) ==> flip impl) (@brD_boundF E R n (ct n r)).
Proof.
  unfold Proper, respectful, flip, impl. intros.
  inv H. step in H1. inv H0; inv H1; auto; invert; constructor; intros; auto.
  rewrite REL; auto.
  rewrite REL; auto.
  rewrite REL; auto.
Qed.

#[global] Instance equ_brD_bound_ {E R r} n :
  Proper (equ eq ==> flip impl) (@brD_bound_ E R n (ct n r)).
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
  {| body := fun R => @bind_ctx1 E X Y (brD_bound n) (fun f => forall x, R (f x)) |}.
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
    apply (fbrD_bound n).
    apply id_T.
  - constructor; intros ?. apply (fTf_Tf (fbrD_bound n)).
    apply in_bind_ctx1; auto.
    intros. apply (b_T (fbrD_bound n)). apply Hk.
  - constructor; intros ?. apply (fTf_Tf (fbrD_bound n)).
    apply in_bind_ctx1; auto.
    intros. apply (b_T (fbrD_bound n)). apply Hk.
  - constructor; auto; intros ?. apply (fTf_Tf (fbrD_bound n)).
    apply in_bind_ctx1; auto.
    intros. apply (b_T (fbrD_bound n)). apply Hk.
Qed.

Lemma ct_clo_bind {E R1 R2} n r (t : ctree E R1) (k : R1 -> ctree E R2) :
  brD_bound n t ->
  (forall x, ct n r (k x)) ->
  ct n r (CTree.bind t k).
Proof.
  intros.
  apply (ft_t (@bind_ctx1_ct E R1 R2 n)).
  eapply in_bind_ctx1; auto.
Qed.

Lemma bind_brD_bound {E R1 R2} n (t : ctree E R1) (k : R1 -> ctree E R2) :
  brD_bound n t ->
  (forall x, brD_bound n (k x)) ->
  brD_bound n (CTree.bind t k).

Proof.
  red. intros. revert t k H H0. coinduction r CIH. intros.
  cbn*. step in H. cbn in H. red in H |- *.
  rewrite unfold_bind.
  desobs t. 3: destruct vis.
  2, 3, 4: inv H; invert; constructor; auto.
  specialize (H0 r0). step in H0. red in H0.
  inv H0; constructor; auto; intros; apply (gfp_t (fbrD_bound n)); auto.
Qed.

Lemma iter_brD_bound {E R I} n (k : I -> ctree E (I + R)) (Hn : n > 0):
  (forall i, brD_bound n (k i)) ->
  forall i, brD_bound n (iter k i).
Proof.
  unfold brD_bound. coinduction r CIH. intros.
  cbn*. unfold iter, MonadIter_ctree. rewrite unfold_iter.
  rewrite unfold_bind.
  destruct (observe (k i)) eqn:?. 3: destruct vis.
  2, 3, 4: pose proof (H i) as H'; step in H'; cbn in H'; red in H';
  rewrite Heqc in H'; inversion H'; invert;
  constructor; auto; intros;
  eapply ct_clo_bind; auto; intros y; destruct y; step; econstructor; eauto.
  destruct r0; constructor; auto; intros; apply CIH; auto.
Qed.

Lemma sbisim_vis_visible {E R X} (t2 : ctree E R) (e : E X) k1
      (Hin: inhabited X)
      (Hbound : brD_bound 1 t2) :
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
  - edestruct @brD_bound_1_inv as (? & Hbound').
    {
      assert (t2 ≅ BrD n k).
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

Lemma sbisim_visible {E R X} (t1 t2 : ctree E R) (e : E X) k1
      (Hin: inhabited X)
      (Hbound1 : brD_bound 1 t1)
      (Hbound2 : brD_bound 1 t2):
  t1 ~ t2 ->
  visible t1 (Vis e k1) ->
  exists k2, visible t2 (Vis e k2) /\ (forall x, k1 x ~ k2 x).
Proof.
  unfold trans; intros. cbn in *. red in H0. remember (observe t1). remember (observe (Vis e k1)).
  revert X t1 e k1 t2 H Heqc Heqc0 Hin Hbound1 Hbound2.
  induction H0; intros; auto.
  - edestruct @brD_bound_1_inv as (? & Hbound1').
    {
      assert (t1 ≅ BrD n k).
      rewrite ctree_eta. rewrite <- Heqc. reflexivity.
      rewrite H1 in Hbound1. apply Hbound1.
    }
    subst. eapply IHvisible_. 2: reflexivity. all: eauto.
    pose proof (ctree_eta t1). rewrite <- Heqc in H1. rewrite H1 in H.
    epose proof (sbisim_BrD_1_inv _ H); auto. apply H2.
  - inv Heqc0.
  - inv Heqc0. apply inj_pair2 in H3, H4. subst.
    apply sbisim_vis_visible; auto.
    pose proof (ctree_eta t1).  rewrite <- Heqc in H1.
    eapply equ_VisF in H. rewrite H in H1.
    rewrite H1 in H0. auto.
  - inv Heqc0.
Qed.

(** Events used to model yields and spawns in our language *)
Variant yieldE : Type -> Type :=
  | Yield : yieldE unit.

Variant spawnE : Type -> Type :=
  | Spawn : spawnE bool.

Section parallel.
  Context {E : Type -> Type}.

  Definition parE := yieldE +' spawnE +' E.

  Definition thread := ctree parE unit.

  Definition completed := ctree E unit.

  Definition vec n := fin n -> thread.

  (** Removing an element from a [vec] *)
  Definition remove_front_vec {n : nat} (v : vec (S n)) : vec n :=
    fun i => v (FS i).

  #[global] Instance remove_front_vec_relation n P :
    Proper (pwr P ==> pwr P) (@remove_front_vec n).
  Proof.
    repeat intro. apply H.
  Qed.

  Lemma remove_front_vec_brD_bound n n' (v : vec (S n)) :
    (forall i, brD_bound n' (v i)) ->
    forall i, brD_bound n' (remove_front_vec v i).
  Proof.
    repeat intro. apply H.
  Qed.

  Equations remove_vec {n : nat} (v : vec (S n)) (i : fin (S n)) : vec n :=
    remove_vec v F1     i'      := remove_front_vec v i';
    remove_vec v (FS i) F1      := v F1;
    remove_vec v (FS i) (FS i') := remove_vec (remove_front_vec v) i i'.
  Transparent remove_vec.

  #[global] Instance remove_vec_relation n P :
    Proper (pwr P ==> eq ==> pwr P) (@remove_vec n).
  Proof.
    intros v1 v2 Pv ? i ?. subst.
    depind i; [apply remove_front_vec_relation; auto |].
    intro i'. destruct i'; cbn; auto.
    apply IHi; auto.
    repeat intro. apply remove_front_vec_relation; auto.
  Qed.

  Lemma remove_vec_brD_bound n n' (v : vec (S n)) i' :
    (forall i, brD_bound n' (v i)) ->
    forall i, brD_bound n' (remove_vec v i' i).
  Proof.
    intros. depind i'.
    - apply remove_front_vec_brD_bound; auto.
    - destruct i; cbn; auto.
      apply IHi'; auto. intros. apply remove_front_vec_brD_bound; auto.
  Qed.

  Lemma remove_vec_remove_vec_front n (v : vec (S (S n))) i i' :
    remove_vec (remove_front_vec v) i i' = remove_front_vec (remove_vec v (FS i)) i'.
  Proof.
    depind i; cbn; auto.
  Qed.

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

  (* at the element removed, we also subtract one. *)
  Lemma remove_vec_index_eq {n} (v : vec (S n)) i j
        (Hi : i < S n) (Hji : j = i) (Hj : S j < S n) (Hj' : j < n) :
    v (of_nat_lt Hj) = (remove_vec v (of_nat_lt Hi)) (of_nat_lt Hj').
  Proof.
    revert n v j Hi Hj Hj' Hji. induction i; intros; auto.
    - destruct n. inv Hj'. subst. reflexivity.
    - destruct n. inv Hj'. subst. cbn.
      erewrite <- IHi; auto.
  Qed.

  Definition remove_vec_helper n n' (v : vec n) (i : fin n) (H : n = S n')
    : vec n'.
    subst. apply remove_vec; eauto.
  Defined.


  (** Replacing an element in a [vec] *)
  Definition replace_vec {n : nat} (v : vec n) (i : fin n) (t : thread) : vec n :=
    fun i' => if Fin.eqb i i' then t else v i'.

  Lemma replace_vec_unary t1 t2 :
    replace_vec (fun _: fin 1 => t1) F1 t2 = (fun _ => t2).
  Proof.
    apply functional_extensionality. intros. dependent destruction x; auto. inv x.
  Qed.

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

  #[global] Instance replace_vec_relation n P :
    Proper (pwr P ==> eq ==> P ==> pwr P) (@replace_vec n).
  Proof.
    unfold replace_vec. repeat intro. subst. destruct (Fin.eqb y0 a); auto.
  Qed.

  Lemma replace_vec_brD_bound n n' (v : vec n) i' t :
    (forall i, brD_bound n' (v i)) ->
    brD_bound n' t ->
    forall i, brD_bound n' (replace_vec v i' t i).
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

  (** Adding an element to the front of a [vec] *)
  Equations cons_vec {n : nat} (t : thread) (v : vec n) : vec (S n) :=
    cons_vec t v F1      := t;
    cons_vec t v (FS i)  := v i.
  Transparent cons_vec.

  #[global] Instance cons_vec_relation n P :
    Proper (P ==> pwr P ==> pwr P) (@cons_vec n).
  Proof.
    unfold cons_vec. repeat intro. depind a; cbn; auto.
  Qed.

  Lemma cons_vec_brD_bound n n' (v : vec n) t :
    (forall i, brD_bound n' (v i)) ->
    brD_bound n' t ->
    forall i, brD_bound n' (cons_vec t v i).
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
      BrS (S n) (fun i' => schedule (S n) v (Some i'));

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

        (* If it's a [Spawn], we extend the pool *)
        schedule_match _ _ _ _ (VisF (inr1 (inl1 Spawn)) k) :=
          Step (schedule
                  (S (S n))
                  (* Note that [cons_vec] puts the new thread on the front of the vector *)
                  (cons_vec (k true) (replace_vec v i (k false)))
                  (* We stay with the old thread; we don't yield at a spawn *)
                  (Some (FS i)));

        (* State events are not touched in scheduling *)
        schedule_match _ _ _ _ (VisF (inr1 (inr1 s)) k) :=
        (Vis s (fun x => (schedule (S n) (replace_vec v i (k x)) (Some i))));

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
    2: { destruct n; auto. constructor. intros. apply CIH; auto. }
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
    - destruct s. constructor. intros. eapply CIH.
      apply cons_vec_relation; auto.
      apply replace_vec_relation; auto.
    - constructor. intros. apply CIH.
      apply replace_vec_relation; auto.
    - constructor. intros. apply CIH.
      apply replace_vec_relation; auto.
  Qed.

  (** Helper lemmas for dealing with [schedule] *)

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
    - destruct e; [destruct y | destruct s; [destruct s |]; step in Hequ; inv Hequ].
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
    revert t v i x Heql Heqc0 H0.
    induction H; intros t' v i x' Heql Heq Hequ; try inv Heql; subst.
    - rewrite <- ctree_eta in Hequ.
      apply BrD_schedule_inv in Hequ. destruct Hequ as [? | [? | ?]].
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
      + destruct e; [destruct y | destruct s; [destruct s |]]; step in Hequ; inv Hequ.
      + step in Hequ; inv Hequ.
  Qed.

  (** [schedule] transitions with an [obs] *)
  Lemma trans_schedule_obs {X} n v o (e : E X) (x : X) t :
    trans (obs e x) (schedule n v o) t ->
    (exists k i, o = Some i /\
                visible (v i) (Vis (inr1 (inr1 e)) k) /\
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
      apply BrD_schedule_inv in Hequ. destruct Hequ as [? | [? | ?]].
      + destruct H0 as (k' & Hvic & Hk).
        edestruct IHtrans_ as (k'' & i' & ? & ? & ?); auto.
        * rewrite Hk. reflexivity.
        * inv H0.
          exists k'', i'. split; [| split]; auto.
          -- rewrite Hvic. cbn. red. cbn. econstructor.
             rewrite replace_vec_eq in H1. apply H1.
          -- rewrite replace_vec_twice in H2. apply H2.
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
      + destruct e; [destruct y | destruct s; [destruct s |]];
          try solve [step in Hequ; inv Hequ].
        cbn in *.
        pose proof (equ_vis_invT _ _ _ _ Hequ). subst.
        destruct (equ_vis_invE _ _ _ _ Hequ). subst.
        exists k0, i. split; [| split]; auto.
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

  Lemma trans_schedule_thread_tau_some n v i t (Hbound : brD_bound 1 (v i)) :
    trans tau (schedule n v (Some i)) t ->
    (exists n' i',
        trans (val ()) (v i) CTree.stuckD /\
          {H: n = S (S n') &
                t ≅ schedule (S n') (remove_vec_helper n (S n') v i H) (Some i')}) \/
      (exists t', trans tau (v i) t' /\
               brD_bound 1 t' /\
               t ≅ schedule n (replace_vec v i t') (Some i)) \/
      (exists k, visible (v i) (Vis (inl1 Yield) k) /\
                 exists i', t ≅ schedule n (replace_vec v i (k tt)) (Some i')) \/
      (exists k, visible (v i) (Vis (inr1 (inl1 Spawn)) k) /\
              t ≅ schedule
                (S n)
                (cons_vec (k true) (replace_vec v i (k false)))
                (Some (FS i))).
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
        + destruct (equ_br_invT _ _ Hequ) as (? & _). subst.
          pose proof (equ_br_invE _ _ Hequ).
          right. right. right.
          exists k0. split.
          * cbn. red. rewrite Heqc. constructor. reflexivity.
          * rewrite ctree_eta. rewrite <- Heq. rewrite <- ctree_eta. rewrite <- H.
            rewrite H0. auto.
        + step in Hequ. inv Hequ.
      - destruct (equ_br_invT _ _ Hequ). subst.
        pose proof (equ_br_invE _ _ Hequ). right. left. cbn.
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
      apply equ_schedule.
      apply replace_vec_relation; repeat intro; try reflexivity.
      rewrite <- Heq. rewrite <- REL. auto.
  Qed.

  (** [visible] lemmas *)
  Lemma visible_yield_trans_schedule n v i i' k (Hbound : brD_bound 1 (v i)) :
    visible (v i) (Vis (inl1 Yield) k) ->
    trans tau (schedule (S n) v (Some i)) (schedule (S n) (replace_vec v i (k tt)) (Some i')).
  Proof.
    intros. cbn in *. red in H |- *. red.
    remember (observe (v i)). remember (observe (Vis _ k)).
    revert v i i' k Heqc Heqc0 Hbound.
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
      econstructor. apply equ_schedule.
      apply replace_vec_relation; repeat intro; auto.
  Qed.

  Lemma visible_spawn_trans_schedule n v i k (Hbound : brD_bound 1 (v i)) :
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
      rewrite <- Heqc. econstructor. apply F1. apply equ_schedule.
      apply cons_vec_relation; auto.
      apply replace_vec_relation; repeat intro; auto.
  Qed.

  Lemma visible_stateE_trans_schedule {X} n v i (s : E X) k x
        (Hbound : brD_bound 1 (v i)) :
    visible (v i) (Vis (inr1 (inr1 s)) k) ->
    trans (obs s x) (schedule (S n) v (Some i))
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

  Variant ordering := LT | EQ | GT.

  Fixpoint order {m n} (p : fin m) (q : fin n) : ordering :=
    match p, q with
    | F1, F1 => EQ
    | F1, _ => LT
    | _, F1 => GT
    | FS p', FS q' => order p' q'
    end.

  (** General [order] lemmas *)

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

  (* at the element removed, we also subtract one. *)
  Lemma remove_vec_index_eq' {n} (v : vec (S n)) i j
        (Hj : order j i = EQ) :
    v (FS j) = remove_vec v i j.
  Proof.
    revert v i Hj. depind j; intros. dependent destruction i; auto; inv Hj.
    dependent destruction i. inv Hj.
    destruct n. inv j. cbn in *. rewrite <- IHj; auto.
  Qed.

  Ltac cases a b name := destruct (order_cases a b) as [[name | name] | name].

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
                   | _ =>
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

  Lemma remove_at_permutation_correct {n} (p q : fin (S (S n)) -> fin (S (S n))) r
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
      decompose [or] Ht; clear Ht.
      + (* thread is finished *)
        assert (Hinjp : Injective p) by (eapply bijective_injective; eauto).
        assert (Hinjq : Injective q) by (eapply bijective_injective; eauto).
        destruct H as (n' & i' & Ht & ? & Hequ). subst.
        pose proof (remove_at_permutation_correct _ _ i Hpq Hqp Hinjp Hinjq) as (Hpq' & Hqp').
        edestruct (@remove_at_permutation_vectors) as (Hpq'' & Hqp''); eauto.

        pose proof (Hsb1 i). step in H. destruct H as [Hf _].
        edestruct Hf as [? ? ?]; eauto.
        eapply trans_thread_schedule_val_SS in H.
        eexists. apply H. rewrite Hequ.
        eapply CIH; clear CIH; cbn; try solve [apply remove_vec_brD_bound; auto].
        * apply Hpq'.
        * apply Hqp'.
        * apply Hpq''.
        * apply Hqp''.
      + (* tau step *)
        destruct n; try inv i.
        destruct H0 as (t' & Ht & Hbound & Hequ).
        pose proof (Hsb1 i). step in H. destruct H as [Hf _].
        edestruct Hf as [? ? ?]; eauto.
        pose proof (trans_brD_bound _ _ _ _ _ (Hbound2 _) H) as Hbound'.
        apply trans_thread_schedule_tau in H.
        eexists; eauto. rewrite Hequ.
        eapply CIH; clear CIH; eauto; try solve [apply replace_vec_brD_bound; auto].
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
          assert (Hbound: forall b, brD_bound 1 (k b)). {
            intros. eapply visible_brD_bound in Hvis; eauto.
            eapply trans_brD_bound; eauto. constructor. reflexivity.
          }
          assert (Hbound': forall b, brD_bound 1 (k' b)). {
            intros. eapply visible_brD_bound in Hvis'; eauto.
            eapply trans_brD_bound; eauto. constructor. reflexivity.
          }
          rewrite Hequ. eapply CIH; auto;
            try solve [apply cons_vec_brD_bound; auto;
                       apply replace_vec_brD_bound; auto].
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
      destruct Ht as (k & i' & ? & Hvis & Hequ). inv H. rename i' into i.
      destruct n; try inv i.
      pose proof Hvis as Hvis'.
      eapply sbisim_visible in Hvis'. 5: apply Hsb1. all: eauto.
      destruct Hvis' as (k' & Hvis' & ?).
      exists (schedule (S n) (replace_vec v2 (p i) (k' v)) (Some (p i))).
      2: {
        assert (Hbound: forall x, brD_bound 1 (k x)). {
          intros. eapply visible_brD_bound in Hvis; eauto.
          eapply trans_brD_bound; eauto. constructor. reflexivity.
        }
        assert (Hbound': forall x, brD_bound 1 (k' x)). {
          intros. eapply visible_brD_bound in Hvis'; eauto.
          eapply trans_brD_bound; eauto. constructor. reflexivity.
        }
        rewrite Hequ. eapply CIH; clear CIH; eauto;
          try solve [apply replace_vec_brD_bound; auto].
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
