From Coq Require Import
     Program
     List
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
  red in H |- *. inversion Hequ; auto. 2: destruct b0.
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
  red in H |- *. inversion Hequ; auto. 2: destruct b0.
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

Lemma trans_choiceI_bound E R (t t' : ctree E R) :
  choiceI_bound 1 t ->
  trans tau t t' ->
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
  cbn*. step in H. red in H |- *.
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
  2, 3, 4: pose proof (H i) as H'; step in H'; red in H';
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
    P t1 t2 ->
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
                  (cons_vec (k true) (replace_vec v i (k false)))
                  (* The [i] here means that we don't yield at a spawn *)
                  (Some (Fin.L_R 1 i))); (* view [i] as a [fin (n + 1)] *)

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
                (Some (Fin.L_R 1 i))).
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
                    (Some (Fin.L_R 1 i))).
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
      rewrite <- Heqc. econstructor. apply Fin.F1. apply equ_schedule.
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
          pose proof (trans_choiceI_bound _ _ _ _ Hbound2 H).
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
                      (Some (Fin.L_R 1 i))).
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

End parallel.
