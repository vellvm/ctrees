From Stdlib Require Import Basics Fin.

From Coinduction Require Import all.

From ITree Require Import
     Basics.CategoryTheory
     Basics.CategoryKleisli.

From CTree Require Import
     CTree
     Utils
     Eq
     Eq.SSimAlt
     Eq.OldAltEquiv.TransEquiv
     Eq.OldAltEquiv.SSimEquiv
     Eq.OldAltEquiv.SBisimEquiv
     Eq.SBisimAlt.

Import CTree.
Import CTreeNotations.

Definition iter_gen {E B X I}
    (step : I -> ctree E B (I + X)) (t : ctree E B (I + X)) :=
  r <- t;;
  match r with
  | inl i => Guard (iter step i)
  | inr x => Ret x
  end.

Lemma iter_iter_gen {E B X I} :
  forall (i : I) (step : I -> ctree E B (I + X)),
  iter step i ≅ iter_gen step (step i).
Proof.
  intros. unfold iter_gen.
  rewrite unfold_iter.
  reflexivity.
Qed.

#[global] Instance iter_gen_equ {E B X I R} `{REFL: Reflexive _ R} :
  Proper ((pointwise R (equ eq)) ==> equ eq ==> equ eq)
    (@iter_gen E B X I).
Proof.
  cbn. intros step step' ? t t' EQ.
  unfold iter_gen.
  revert t t' EQ.
  coinduction CR CH. intros.
  subs. 
  upto_bind_eq. red in H.
  destruct x; [| reflexivity].
  constructor.
  rewrite !iter_iter_gen. apply CH. now apply H.
Qed.

#[global] Instance iter_equ {E B X I R} `{REFL: Reflexive _ R} :
  Proper ((pointwise R (equ eq)) ==> R ==> equ eq) (@iter E B X I).
Proof.
  cbn. intros step step' ? i i' EQ.
  rewrite !iter_iter_gen. apply iter_gen_equ; auto.
Qed.
(* Thanks to SSimAlt, this proof does not need an helper inductive. *)
Theorem ssim_iter {E F C D A A' B B'}
  (L : lrel E F _ _) (Ra : rel A A') (Rb : rel B B')
  (HRb : forall b b', Rb b b' <-> L (val b) (val b')) :
  forall (step : A -> ctree E C (A + B)) (step' : A' -> ctree F D (A' + B')),
  (forall a a', Ra a a' -> step a (≲(upd_rel L (sum_rel Ra Rb))) step' a') ->
  forall a a', Ra a a' ->
  iter step a (≲L) iter step' a'.
Proof.
  intros. apply (ssim_ssim').
  revert step a a' H H0.
  red. coinduction R CH. intros.
  rewrite !unfold_iter.  
  eapply SSimAlt.bind_chain_gen with (SS:=(sum_rel Ra Rb)).
  - cbn -[ss']. 
    (* coinduction library: want [base] tactic that does this and always works *)
    apply (gfp_chain (chain_b R)).
    apply H in H0. now apply ssim_ssim' in H0.  
  - intros. destruct x, x'; try destruct H1.
    + apply step_ss'_guard. apply CH; auto.
    + apply step_ssbt'_ret. 
    change (TransAlt.val b) with (@o2n_label E _ (val b)). 
    change (TransAlt.val b0) with (@o2n_label F _ (val b0)). 
    eapply TransEquiv.lift_L_o2n.
    now apply HRb.
Qed.

#[global] Instance ssim_eq_iter {E B X Y} :
  @Proper ((X -> ctree E B (X + Y)) -> X -> ctree E B Y)
    (pointwise_relation _ (fun t u => ssim Leq (α t) (α u)) ==> eq ==>
       (fun t u => ssim Leq (α t) (α u)))
    iter.
Proof.
  repeat intro. subst.
  eapply ssim_iter with (L := Leq) (Ra := eq) (Rb := eq).
  - intros b b'. split; [intros ->; reflexivity | intros EQ; apply Leq_eq in EQ; now apply val_eq_inv in EQ].
  - intros a ? <-.
    assert (LEQ : lequiv (upd_rel (@Leq E Y) (sum_rel (@eq X) (@eq Y))) (@Leq E (X + Y))).
    { split3; cbn; try reflexivity.
      intros [] []; cbn; split; intro EQ; subst; try easy; now inv EQ. }
    apply (weq_ssim LEQ). apply H.
  - reflexivity.
Qed.

Theorem sbisim_iter {E F C D A A' B B'}
  (L : lrel E F _ _) (Ra : rel A A') (Rb : rel B B')
  (HRb : forall b b', Rb b b' <-> L (val b) (val b')) :
  forall (step : A -> ctree E C (A + B)) (step' : A' -> ctree F D (A' + B')),
  (forall a a', Ra a a' -> step a (≃(upd_rel L (sum_rel Ra Rb))) step' a') ->
  forall a a', Ra a a' ->
  iter step a (≃L) iter step' a'.
Proof.
  intros. apply sbisim_sbisim'.
  revert step a a' H H0.
  red. coinduction R CH. intros.
  cbn [o2n_S]. rewrite !unfold_iter.
  eapply (@SBisimAlt.bind_chain_gen _ _ _ _ _ _ _ _ _ (chain_b R)) with (SS := sum_rel Ra Rb).
  - apply (gfp_chain (chain_b R)).
    change (gfp sb' side _ _ (lift_L (Trans.upd_rel L (sum_rel Ra Rb)))
              (o2n_S (α step a)) (o2n_S (α step' a'))).
    apply sbisim_gfp_sb'. now apply H.
  - intros side0 x x' Hx. destruct x, x'; try destruct Hx.
    + apply step_sb'_guard. apply CH; auto.
    + apply step_sbt'_ret.
      change (TransAlt.val b) with (@o2n_label E _ (val b)).
      change (TransAlt.val b0) with (@o2n_label F _ (val b0)).
      eapply TransEquiv.lift_L_o2n.
      now apply HRb.
Qed.

#[global] Instance sbisim_eq_iter {E B X Y} :
  @Proper ((X -> ctree E B (X + Y)) -> X -> ctree E B Y)
    (pointwise_relation _ (fun t u => sbisim Leq (α t) (α u)) ==>
       pointwise_relation _ (fun t u => sbisim Leq (α t) (α u)))
    iter.
Proof.
  repeat intro.
  eapply sbisim_iter with (L := Leq) (Ra := eq) (Rb := eq).
  - intros b b'. split; [intros ->; reflexivity | intros EQ; apply Leq_eq in EQ; now apply val_eq_inv in EQ].
  - intros ? ? <-.
    assert (LEQ : lequiv (upd_rel (@Leq E Y) (sum_rel (@eq X) (@eq Y))) (@Leq E (X + Y))).
    { split3; cbn; try reflexivity.
      intros [] []; cbn; split; intro EQ; subst; try easy; now inv EQ. }
    apply (weq_sbisim LEQ). apply H.
  - reflexivity.
Qed.

Lemma iter_natural_ctree {E C X Y Z} :
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
  - rewrite !bind_ret_l, bind_guard. constructor.
    apply CH.
  - rewrite bind_bind. setoid_rewrite bind_ret_l. rewrite bind_ret_r.
    reflexivity.
Qed.

Lemma iter_dinatural_ctree_inner {E C X Y Z} :
  forall (f : X -> ctree E C (Y + Z)) (g : Y -> ctree E C (X + Z)) (x : X),
  iter
    (fun x : X =>
     CTree.bind (f x)
       (fun yz : Y + Z =>
        match yz with
        | inl y => g y
        | inr z => Ret (inr z)
        end)) x
  ≃ CTree.bind (f x)
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
  cbn [o2n_S]. rewrite unfold_iter, bind_bind.
  apply (sb'_clo_bind_lift_eq (R := chain_b R)). { reflexivity. }
  intros. destruct x0.
  2: { rewrite bind_ret_l. reflexivity. }
  destruct (observe (g y)) eqn:?.
  - setoid_rewrite (ctree_eta (g y)). rewrite Heqc.
    rewrite bind_ret_l. destruct r.
    + apply step_sb'_guard. intros.
      setoid_rewrite unfold_iter at 2.
      rewrite (ctree_eta (g y)), Heqc, bind_ret_l.
      apply CH.
    + apply step_sb'_guard_r.
      rewrite unfold_iter, bind_bind.
      rewrite (ctree_eta (g y)), Heqc, !bind_ret_l. reflexivity.

  - setoid_rewrite (ctree_eta (g y)). rewrite Heqc, bind_stuck.
    rewrite unfold_iter, bind_bind, (ctree_eta (g y)), Heqc, bind_stuck.
    apply step_sb'_guard_r'. auto.

  - setoid_rewrite (ctree_eta (g y)). rewrite Heqc, bind_step.
    rewrite unfold_iter, bind_bind, (ctree_eta (g y)), Heqc, bind_step.
    apply step_sb'_guard_r'.
    apply step_sb'_step; [constructor |].
    intros.
    apply (sb'_clo_bind_lift_eq (R := R)); auto.
    intros. destruct x0.
    + apply step_sb'_guard_l'. intros; apply CH.
    + rewrite bind_ret_l. reflexivity.

  - setoid_rewrite (ctree_eta (g y)). rewrite Heqc, bind_guard.
    rewrite unfold_iter, bind_bind, (ctree_eta (g y)), Heqc, bind_guard.
    apply step_sb'_guard.
    apply step_sb'_guard_r'.
    intros.
    apply (sb'_clo_bind_lift_eq (R := R)); auto.
    intros. destruct x0.
    + apply step_sb'_guard_l'. intros; apply CH.
    + rewrite bind_ret_l. reflexivity.

  - setoid_rewrite (ctree_eta (g y)). rewrite Heqc, bind_vis.
    apply step_sb'_guard_r.
    rewrite unfold_iter, bind_bind, (ctree_eta (g y)), Heqc, bind_vis.
    apply step_sb'_vis_id; [| constructor; constructor].
    intros. apply (b_chain R). apply step_sb'_passive_id; [| constructor; constructor].
    intros. apply (sb'_clo_bind_lift_eq (R := R)). { reflexivity. }
    intros. destruct x1.
    + apply step_sb'_guard_l'. apply CH.
    + rewrite bind_ret_l. reflexivity.

  - setoid_rewrite (ctree_eta (g y)). rewrite Heqc, bind_br.
    apply step_sb'_guard_r'. intros.
    rewrite unfold_iter, bind_bind, (ctree_eta (g y)), Heqc, bind_br.
    apply step_sb'_br_id; auto. intros.
    apply (sb'_clo_bind_lift_eq (R := R)). { reflexivity. }
    intros. destruct x1.
    + apply step_sb'_guard_l'. intros. apply CH.
    + rewrite bind_ret_l. reflexivity.
Qed.

Lemma iter_dinatural_ctree {E C X Y Z} :
  forall (f : X -> ctree E C (Y + Z)) (g : Y -> ctree E C (X + Z)) (x : X),
  iter
    (fun x : X =>
     CTree.bind (f x)
     (fun yz : Y + Z =>
        match yz with
        | inl y => g y
        | inr z => Ret (inr z)
        end)) x
  ≃ CTree.bind (f x)
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
  rewrite unfold_iter, bind_bind.
  apply sbisim_bind_eq; [reflexivity | intros x0].
  destruct x0.
  2: { rewrite bind_ret_l. reflexivity. }
  rewrite unfold_iter, bind_bind. apply sbisim_bind_eq; [reflexivity | intros x0].
  destruct x0.
  2: { rewrite bind_ret_l. reflexivity. }
  rewrite sbisim_guard. apply iter_dinatural_ctree_inner.
Qed.

Theorem iter_codiagonal_ctree {E C A B} :
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
  - rewrite bind_ret_l, bind_guard. constructor.
    rewrite <- unfold_iter. apply CH.
  - rewrite !bind_ret_l. destruct s; [| reflexivity ].
    constructor. apply CH.
Qed.
