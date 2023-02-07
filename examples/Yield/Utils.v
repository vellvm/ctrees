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
    (* TODO: fix step in the coinduction library to work on unary relations *)
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

(* TODO move this *)
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
    (* TODO: clean this up *) eapply equ_VisF in H. rewrite H in H1.
    rewrite H1 in H0. auto.
  - inv Heqc0.
Qed.

Section Vectors.
  Context {thread : Type}.
  Context (vec := fun n => fin n -> thread).

  (** Removing an element from a [vec] *)
  Definition remove_front_vec {n : nat} (v : vec (S n)) : vec n :=
    fun i => v (FS i).

  #[global] Instance remove_front_vec_relation n P :
    Proper (pwr P ==> pwr P) (@remove_front_vec n).
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




End Vectors.

Section Vector_brD_bound.
  Context {E : Type -> Type}.
  Context {R : Type}.
  Context (vec := fun n => fin n -> ctree E R).

  Lemma remove_front_vec_brD_bound n n' (v : vec (S n)) :
    (forall i, brD_bound n' (v i)) ->
    forall i, brD_bound n' (remove_front_vec v i).
  Proof.
    repeat intro. apply H.
  Qed.

  Lemma remove_vec_brD_bound n n' (v : vec (S n)) i' :
    (forall i, brD_bound n' (v i)) ->
    forall i, brD_bound n' (remove_vec v i' i).
  Proof.
    intros. depind i'.
    - simp remove_vec.
    - destruct i; cbn; simp remove_vec.
      eapply IHi'; auto. intros. apply remove_front_vec_brD_bound; auto.
  Qed.

  Lemma replace_vec_brD_bound n n' (v : vec n) i' t :
    (forall i, brD_bound n' (v i)) ->
    brD_bound n' t ->
    forall i, brD_bound n' (replace_vec v i' t i).
  Proof.
    unfold replace_vec. repeat intro. destruct (Fin.eqb i' i); auto.
  Qed.

  Lemma cons_vec_brD_bound n n' (v : vec n) t :
    (forall i, brD_bound n' (v i)) ->
    brD_bound n' t ->
    forall i, brD_bound n' (cons_vec t v i).
  Proof.
    repeat intro. depind i; cbn; auto. simp cons_vec.
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
    revert v j Hj. depind i; intros; auto.
    - dependent destruction j; inv Hj.
    - destruct n; [inv j |]. dependent destruction j; auto. cbn. simp fin_S.
      simp remove_vec. erewrite <- IHi; auto.
  Qed.

  (* after the element removed, we need to subtract one from the index *)
  Lemma remove_vec_index_after' {n} (v : vec (S n)) i j
        (Hj : order j i = GT) :
    v (FS j) = remove_vec v i j.
  Proof.
    revert v i Hj. depind j; intros. dependent destruction i; auto; inv Hj.
    dependent destruction i.
    - destruct n. inv j. reflexivity.
    - destruct n. inv j. simp remove_vec. rewrite <- IHj; auto.
  Qed.

  (* at the element removed, we also subtract one. TODO: can we unify this with prev lemma? *)
  Lemma remove_vec_index_eq' {n} (v : vec (S n)) i j
        (Hj : order j i = EQ) :
    v (FS j) = remove_vec v i j.
  Proof.
    revert v i Hj. depind j; intros. dependent destruction i; auto; inv Hj.
    dependent destruction i. inv Hj.
    destruct n. inv j. simp remove_vec. rewrite <- IHj; auto.
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
End Vector_brD_bound.
