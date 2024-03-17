From Coq Require Import Basics Fin.

From Coinduction Require Import
     coinduction rel tactics.

From ITree Require Import
     Basics.CategoryTheory
     Basics.CategoryKleisli.

From CTree Require Import
     CTree
     Utils
     Eq
     Eq.SSimAlt
     Eq.SBisimAlt.

Import CTree.
Import CTreeNotations.

Definition iter_gen {E B X I} `{B1 -< B}
    (step : I -> ctree E B (I + X)) (t : ctree E B (I + X)) :=
  r <- t;;
  match r with
  | inl i => Guard (iter step i)
  | inr x => Ret x
  end.

Lemma iter_iter_gen {E B X I} `{B1 -< B} :
  forall (i : I) (step : I -> ctree E B (I + X)),
  iter step i ≅ iter_gen step (step i).
Proof.
  intros. unfold iter_gen.
  rewrite unfold_iter.
  reflexivity.
Qed.

#[global] Instance iter_gen_equ {E B X I} `{HasB1: B1 -< B} :
  Proper ((pointwise eq (equ eq)) ==> equ eq ==> equ eq) (@iter_gen E B X I _).
Proof.
  cbn. intros step step' ? t t' EQ.
  unfold iter_gen.
  revert t t' EQ. coinduction R CH. intros.
  subs. upto_bind_eq. red in H.
  destruct x; [| reflexivity].
  constructor. intros _.
  rewrite !iter_iter_gen. apply CH. now apply H.
Qed.

Section TransIter.

Context {E B : Type -> Type} {X : Type} {I : Type}.
Context `{HasB0 : B0 -< B} `{HasB1 : B1 -< B}.
Context (step : I -> ctree E B (I + X)).

Inductive trans_it (step : I -> ctree E B (I + X)) (t : ctree E B (I + X)) l T : Prop :=
| it_next i :
    trans (val (inl i : I + X)) t stuckD ->
    trans_it step (step i) l T ->
    trans_it step t l T
| it_ex t' :
    trans l t t' /\ T ≅ iter_gen step t' /\ ~is_val l ->
    trans_it step t l T
| it_val r :
    trans (val (inr r : I + X)) t stuckD ->
    l = val r ->
    T ≅ stuckD ->
    trans_it step t l T.

Lemma trans_it_brD : forall {Y} t l (c : B Y) k x T,
  t ≅ BrD c k ->
  trans_it step (k x) l T ->
  trans_it step t l T.
Proof.
  intros.
  remember (k x) as kx. assert (kx ≅ k x). { now subst. } clear Heqkx.
  revert t k x H H1. induction H0; intros; subst.
  - eapply it_next. rewrite H1. eapply trans_brD with (x := x).
    apply H. now rewrite H2. apply H0.
  - eapply it_ex. split. rewrite H0. eapply trans_brD.
    apply H. now rewrite H1. apply H.
  - eapply it_val; auto. rewrite H2. eapply trans_brD.
    apply H. now rewrite H3.
Qed.

Lemma iter_gen_brS : forall {Y} t (c : B Y) K,
  iter_gen step t ≅ BrS c K ->
  exists k, t ≅ BrS c k /\ forall x, iter_gen step (k x) ≅ K x.
Proof.
  intros.
  unfold iter_gen in H.
  setoid_rewrite (ctree_eta t) in H.
  setoid_rewrite (ctree_eta t).
  desobs t.
  - rewrite bind_ret_l in H.
    destruct r; step in H; inv H.
  - step in H. inv H.
  - rewrite bind_br in H.
    inv_equ.
    exists k. split; auto.
Qed.

Lemma iter_gen_vis {Y} : forall t (e : E Y) K,
  iter_gen step t ≅ Vis e K ->
  exists k, t ≅ Vis e k /\ forall x, iter_gen step (k x) ≅ K x.
Proof.
  intros.
  unfold iter_gen in H.
  setoid_rewrite (ctree_eta t) in H.
  setoid_rewrite (ctree_eta t).
  desobs t.
  - rewrite bind_ret_l in H.
    destruct r; step in H; inv H.
  - rewrite bind_vis in H.
    inv_equ.
    exists k. split. reflexivity. intros.
    apply EQ.
  - step in H. inv H.
Qed.

Theorem trans_iter_gen : forall l t T, trans l (iter_gen step t) T -> trans_it step t l T.
Proof.
  intros. do 3 red in H.
  remember (observe (iter_gen step t)) as oi.
  genobs T oT.
  assert (go oi ≅ iter_gen step t \/ go oi ≅ Guard (iter_gen step t)).
  { left. now rewrite Heqoi, <- ctree_eta. } clear Heqoi.
  revert t H0 T HeqoT. induction H; intros; subst.
  - destruct H0.
    + unfold iter_gen in H0.
      symmetry in H0. apply br_equ_bind in H0 as ?. destruct H1.
      * destruct H1. rewrite H1, bind_ret_l in H0. destruct x0.
        2: { step in H0. inv H0. }
        eapply it_next.
        --rewrite H1. etrans.
        --apply IHtrans_; auto.
           inv_equ.
          left. rewrite <- EQ, <- ctree_eta. apply iter_iter_gen.
      * destruct H1 as (? & ? & ?).
        eapply trans_it_brD. apply H1.
        apply IHtrans_. left. rewrite <- ctree_eta. apply H2. reflexivity.
    + inv_equ.
      apply IHtrans_; auto. left. rewrite <- ctree_eta. apply EQ.
  - destruct H0. 2: { step in H0. inv H0. }
    symmetry in H0. apply iter_gen_brS in H0 as (? & ? & ?).
    eapply it_ex. split. { rewrite H0. etrans. }
    split.
    now rewrite ctree_eta, <- HeqoT, <- ctree_eta, <- H, <- H1.
    intro. inv H2.
  - destruct H0. 2: { step in H0. inv H0. }
    symmetry in H0. apply iter_gen_vis in H0 as (? & ? & ?).
    eapply it_ex. split. { rewrite H0. etrans. }
    split.
    now rewrite ctree_eta, <- HeqoT, <- ctree_eta, <- H, <- H1.
    intro. inv H2.
  - destruct H0. 2: { step in H. inv H. }
    unfold iter_gen in H.
    symmetry in H. apply ret_equ_bind in H as (? & ? & ?).
    destruct x. step in H0. inv H0. step in H0. inv H0.
    eapply it_val. rewrite H. etrans. reflexivity. rewrite ctree_eta, <- HeqoT.
    apply br0_always_stuck.
Qed.

End TransIter.

(* Thanks to SSimAlt, this proof does not need trans_iter_gen. *)
Theorem ssim_iter_gen {E F C D A A' B B'}
  `{HasB0 : B0 -< C} `{HasB1 : B1 -< C} `{HasB0' : B0 -< D} `{HasB1' : B1 -< D}
  (L : rel (@label E) (@label F)) (Ra : rel A A') (Rb : rel B B') L0
  (HL0 : is_update_val_rel L (sum_rel Ra Rb) L0)
  (HRb : forall b b', Rb b b' <-> L (val b) (val b')) :
  forall (step : A -> ctree E C (A + B)) (step' : A' -> ctree F D (A' + B')),
  (forall a a', Ra a a' -> step a (≲L0) step' a') ->
  forall (t : ctree E C (A + B)) (t' : ctree F D (A' + B')),
  t (≲L0) t' ->
  iter_gen step t (≲L) iter_gen step' t'.
Proof.
  repeat intro.
  setoid_rewrite ssim_ssim'.
  revert step step' t t' H H0.
  red. coinduction R CH. intros.
  unfold iter_gen.
  rewrite (ctree_eta t) in * |- *. destruct (observe t); [| | destruct vis].
  - (* Ret *)
    eapply ssbt'_clo_bind_gen; eauto.
    intros. destruct x, y; try destruct H1.
    + apply step_ss'_guard. rewrite !iter_iter_gen. apply CH; auto.
    + apply step_ssbt'_ret. now apply HRb.
  - (* Vis *)
    rewrite bind_vis. apply step_ss'_vis_l. intros.
    step in H0. simple eapply ss_vis_l_inv in H0.
    destruct H0 as (l' & u' & TR & SIM & Hl').
    apply HL0 in Hl'; etrans.
    apply update_val_rel_nonval_l in Hl' as []; etrans.
    eauto 7 with trans.
  - (* BrS *)
    rewrite bind_br. apply step_ss'_brS_l. intros.
    step in H0. simple eapply ss_brS_l_inv in H0.
    edestruct H0 as (l' & u' & TR & SIM & Hl').
    apply HL0 in Hl'; etrans.
    apply update_val_rel_nonval_l in Hl' as []; etrans.
    eauto 7 with trans.
  - (* BrD *)
    rewrite bind_br. apply step_ss'_brD_l. intros.
    apply ssim_brD_l_inv with (x := x) in H0.
    apply CH; auto.
Qed.

#[global] Instance ssim_iter_gen_eq {E B X Y} `{HasB0 : B0 -< B} `{HasB1 : B1 -< B} :
  @Proper ((X -> ctree E B (X + Y)) -> ctree E B (X + Y) -> ctree E B Y)
    (pointwise_relation _ (ssim eq) ==> (ssim eq) ==> (ssim eq))
    iter_gen.
Proof.
  repeat intro.
  eapply ssim_iter_gen with (L := eq) (L0 := eq) (Ra := eq) (Rb := eq).
  - eassert (@weq (relation (X + Y)) _ (sum_rel eq eq) eq).
    { cbn. intros [] []; cbn; split; intro; subst; try easy. now inv H1. now inv H1. }
    rewrite H1; auto. apply update_val_rel_eq.
  - split; intro. now subst. now apply val_eq_inv in H1.
  - intros. subst. apply H.
  - apply H0.
Qed.

Theorem ssim_iter {E F C D A A' B B'} `{B0 -< C} `{B1 -< C} `{B0 -< D} `{B1 -< D}
  (L : rel (@label E) (@label F)) (Ra : rel A A') (Rb : rel B B') L0
  (HL0 : is_update_val_rel L (sum_rel Ra Rb) L0)
  (HRb : forall b b', Rb b b' <-> L (val b) (val b')) :
  forall (step : A -> ctree E C (A + B)) (step' : A' -> ctree F D (A' + B')),
  (forall a a', Ra a a' -> step a (≲L0) step' a') ->
  forall a a', Ra a a' -> iter step a (≲L) iter step' a'.
Proof.
  repeat intro.
  rewrite !iter_iter_gen.
  eapply ssim_iter_gen; eauto.
Qed.

#[global] Instance ssim_iter_eq {E B X Y} `{HasB0 : B0 -< B} `{HasB1 : B1 -< B} :
  @Proper ((X -> ctree E B (X + Y)) -> X -> ctree E B Y)
    (pointwise_relation _ (ssim eq) ==> pointwise_relation _ (ssim eq))
    iter.
Proof.
  repeat intro.
  rewrite !iter_iter_gen.
  apply ssim_iter_gen_eq; auto.
Qed.

#[global] Instance sbisim_iter_gen {E B X Y} `{HasB0 : B0 -< B} `{HasB1 : B1 -< B} :
  @Proper ((X -> ctree E B (X + Y)) -> ctree E B (X + Y) -> ctree E B Y)
    (pointwise_relation _ (sbisim eq) ==> (sbisim eq) ==> (sbisim eq))
    iter_gen.
Proof.
  repeat intro.
  rename x into step. rename y into step'.
  revert step step' x0 y0 H H0.
  coinduction R CH.
  symmetric using idtac.
     { intros. apply H. symmetry. apply H0. symmetry. apply H1. }
  cbn. intros.
  apply trans_iter_gen in H1.
  revert y0 H0. induction H1; intros.
  - step in H2. apply H2 in H0 as (? & ? & ? & ? & ?). subst.
    apply trans_val_inv in H0 as ?. rewrite H4 in H0. clear x0 H3 H4.
    apply IHtrans_it in H as (? & ? & ? & ? & ?). subst. clear IHtrans_it.
    exists x, x0; auto. split; auto.
    unfold iter_gen.
    apply trans_bind_r with (x := inl i); auto.
    apply trans_guard. apply H.
  - destruct H0 as (? & ? & ?).
    step in H1. apply H1 in H0 as (? & ? & ? & ? & ?). subst.
    exists x, (iter_gen step' x0). split; [| split]; auto.
    + apply trans_bind_l; auto.
    + rewrite H2. apply CH; auto.
  - subst.
    step in H3. apply H3 in H0 as (? & ? & ? & ? & ?). subst.
    apply trans_val_inv in H0 as ?. rewrite H4 in H0. clear x0 H1 H4.
    exists (val r), stuckD. split. 2: { split. now rewrite H2. reflexivity. }
    eapply trans_bind_r. apply H0. cbn. etrans.
Qed.

#[global] Instance sbisim_iter {E B X Y} `{HasB0 : B0 -< B} `{HasB1 : B1 -< B} :
  @Proper ((X -> ctree E B (X + Y)) -> X -> ctree E B Y)
    (pointwise_relation _ (sbisim eq) ==> pointwise_relation _ (sbisim eq))
    iter.
Proof.
  repeat intro.
  rewrite !iter_iter_gen.
  apply sbisim_iter_gen. apply H. apply H.
Qed.

Lemma iter_natural_ctree {E C X Y Z} `{HasB1 : B1 -< C} :
  forall (f : X -> ctree E C (X + Y)) (g : Y -> ctree E C Z) (a : X),
  CTree.bind (CTree.iter f a) (fun y : Y => g y)
  ≅ CTree.iter
    (fun x : X =>
     CTree.bind (f x)
       (fun ab : X + Y =>
        match ab with
        | inl a => CTree.bind (Ret a) (fun x : X => Ret (inl x))
        | inr b => CTree.bind (g b) (fun z : Z => Ret (inr z))
        end)) a.
Proof.
  intros until g. unfold equ. coinduction R CH. intros.
  setoid_rewrite unfold_iter.
  rewrite !bind_bind. upto_bind_eq.
  destruct x.
  - rewrite !bind_ret_l, bind_guard. constructor. intros _.
    apply CH.
  - rewrite bind_bind. setoid_rewrite bind_ret_l. rewrite bind_ret_r.
    reflexivity.
Qed.

Lemma iter_dinatural_ctree_inner {E C X Y Z} `{HasB0 : B0 -< C} `{HasB1 : B1 -< C} :
  forall (f : X -> ctree E C (Y + Z)) (g : Y -> ctree E C (X + Z)) (x : X),
  iter
    (fun x : X =>
     CTree.bind (f x)
       (fun yz : Y + Z =>
        match yz with
        | inl y => g y
        | inr z => Ret (inr z)
        end)) x
  ~ CTree.bind (f x)
      (fun yz : Y + Z =>
       match yz with
       | inl y =>
           Guard (iter
             (fun y : Y =>
              CTree.bind (g y)
                (fun xz : X + Z =>
                 match xz with
                 | inl x => f x
                 | inr z => Ret (inr z)
                 end)) y)
       | inr z => Ret z
       end).
Proof.
  intros. apply sbisim_sbisim'. red. revert x. coinduction R CH. intros.
  rewrite unfold_iter, bind_bind.
  apply sbt'_clo_bind_eq. { reflexivity. }
  intros. destruct x0.
  2: { rewrite bind_ret_l. reflexivity. }
  destruct (observe (g y)) eqn:?.
  - setoid_rewrite (ctree_eta (g y)). rewrite Heqc.
    rewrite bind_ret_l. destruct r.
    + apply step_sb'_guard. intros.
      setoid_rewrite unfold_iter at 2.
      rewrite (ctree_eta (g y)), Heqc, bind_ret_l.
      apply CH.
    + apply step_sb'_guard_r. intros.
      rewrite unfold_iter, bind_bind.
      rewrite (ctree_eta (g y)), Heqc, !bind_ret_l. reflexivity.
  - setoid_rewrite (ctree_eta (g y)). rewrite Heqc, bind_vis.
    apply step_sb'_guard_r. intros.
    rewrite unfold_iter, bind_bind, (ctree_eta (g y)), Heqc, bind_vis.
    apply step_sb'_vis_id. intros.
    split; auto. intros.
    apply st'_clo_bind_eq. { reflexivity. }
    intros. destruct x1.
    + apply step_sb'_guard_l'. apply CH.
    + rewrite bind_ret_l. reflexivity.
  - setoid_rewrite (ctree_eta (g y)). rewrite Heqc, bind_br.
    apply step_sb'_guard_r. intros.
    rewrite unfold_iter, bind_bind, (ctree_eta (g y)), Heqc, bind_br.
    apply step_sb'_br_id; auto. intros.
    apply st'_clo_bind_eq. { reflexivity. }
    intros. destruct x1.
    + apply step_sb'_guard_l'. intros. apply CH.
    + rewrite bind_ret_l. reflexivity.
Qed.

Lemma iter_dinatural_ctree {E C X Y Z} `{HasB0 : B0 -< C} `{HasB1 : B1 -< C} :
  forall (f : X -> ctree E C (Y + Z)) (g : Y -> ctree E C (X + Z)) (x : X),
  iter
    (fun x : X =>
     CTree.bind (f x)
     (fun yz : Y + Z =>
        match yz with
        | inl y => g y
        | inr z => Ret (inr z)
        end)) x
  ~ CTree.bind (f x)
      (fun yz : Y + Z =>
       match yz with
       | inl y =>
           iter
             (fun y : Y =>
              CTree.bind (g y)
                (fun xz : X + Z =>
                 match xz with
                 | inl x => f x
                 | inr z => Ret (inr z)
                 end)) y
       | inr z => Ret z
       end).
Proof.
  intros.
  rewrite unfold_iter, bind_bind. upto_bind_eq.
  destruct x0.
  2: { rewrite bind_ret_l. reflexivity. }
  rewrite unfold_iter, bind_bind. upto_bind_eq.
  destruct x0.
  2: { rewrite bind_ret_l. reflexivity. }
  rewrite sb_guard. apply iter_dinatural_ctree_inner.
Qed.

Theorem iter_codiagonal_ctree {E C A B} `{HasB1: B1 -< C} :
  forall (f : A -> ctree E C (A + (A + B))) (a : A),
  iter (iter f) a
  ≅ iter
    (fun x : A =>
     CTree.bind (f x)
       (fun y : A + (A + B) =>
        match y with
        | inl a => Ret (inl a)
        | inr b => Ret b
        end)) a.
Proof.
  intro. unfold equ. coinduction R CH. intros.
  rewrite !unfold_iter.
  rewrite !bind_bind. upto_bind_eq.
  destruct x.
  - rewrite bind_ret_l, bind_guard. constructor. intros _.
    rewrite <- unfold_iter. apply CH.
  - rewrite !bind_ret_l. destruct s; [| reflexivity ].
    constructor. intros _. apply CH.
Qed.
