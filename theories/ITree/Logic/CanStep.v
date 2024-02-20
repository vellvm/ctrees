From Coq Require Import
  Basics
  Classes.Morphisms.

From Coinduction Require Import
  coinduction lattice.

From ExtLib Require Import
  Structures.Monad
  Data.Monads.StateMonad.

From CTree Require Import
  Events.Core
  ITree.Core
  ITree.Pred
  ITree.Equ
  ITree.Logic.Trans
  ITree.Events.Writer
  Logic.Ctl
  Logic.Kripke.

Set Implicit Arguments.
Generalizable All Variables.

Import ITreeNotations CtlNotations.
Local Open Scope ctl_scope.
Local Open Scope itree_scope.
  
Lemma can_step_tau `{HE: Encode E} {X: Type}: forall (t: itree E X) w,
    can_step t w ->
    can_step (Tau t) w.
Proof.
  intros.
  destruct H as (t' & w' & TR); cbn in TR.
  dependent induction TR.
  - exists (k v), (Obs e v).
    apply ktrans_tau; cbn.
    rewrite <- x0; apply KtransObs; auto.
  - exists t'0, w'.
    apply ktrans_tau; cbn; auto.
    rewrite <-x0.
    apply ktrans_tau; cbn; auto.
  - exists t0, (Done x0).
    apply ktrans_tau; cbn; auto.
    rewrite <- x1; apply KtransDone; auto.
  - exists t0, (Finish e v x0).
    apply ktrans_tau; cbn; auto.
    rewrite <- x1; apply KtransFinish; auto.
Qed.
Global Hint Resolve can_step_tau: ctl.

Lemma can_step_vis `{HE: Encode E} {X: Type}: forall (e: E) (k: encode e -> itree E X) w (_: encode e),
    not_done w ->
    can_step (Vis e k) w.
Proof.
  intros.
  exists (k X0), (Obs e X0).
  apply ktrans_vis.
  exists X0; auto.
Qed.
Global Hint Resolve can_step_vis: ctl.

Lemma can_step_ret `{HE: Encode E} {X: Type}: forall w (x: X),
    not_done w ->
    can_step (Ret x) w.
Proof.
  intros; inv H.
  Opaque Itree.stuck.
  - exists Itree.stuck, (Done x); now constructor. 
  - exists Itree.stuck, (Finish e v x); now constructor.
Qed.
Global Hint Resolve can_step_ret: ctl.

Lemma can_step_bind_iff `{HE: Encode E} {X Y}: forall (t: itree E Y) (k: Y -> itree E X) w,
    can_step (x <- t ;; k x) w <->        
      (exists t' w', [t, w] ↦ [t', w'] /\ not_done w')
      \/ (exists y w', [t, w] ↦ [Itree.stuck, w']
                 /\ done_eq Y y w'
                 /\ can_step (k y) w).
Proof with (eauto with ctl).
  unfold can_step; split.
  - intros (k' & w' & TR).
    apply ktrans_bind_inv in TR
        as [(t' & TR' & Hd & Eqt) |
             [(y & TRr & -> & TRk) |
               (e & v & x & TRr & -> & TRk)]].
    + left; exists t', w'...
    + right; exists y, (Done y); split; [|split]...
    + right; exists x, (Finish e v x); split; [|split]...
  - intros * [(t' & w' & TR & Hd) | (y & w' & TR & Hd & k_ & w_ & TR_)]; cbn in TR; dependent induction TR.       
    + observe_equ x0; cbn.
      setoid_rewrite Eqt.
      setoid_rewrite bind_vis.
      exists (x <- k0 v ;; k x), (Obs e v); now apply KtransObs.
    + observe_equ x0; cbn in *.
      setoid_rewrite Eqt.
      setoid_rewrite bind_tau.
      destruct (IHTR t0 k t' eq_refl x Hd)
        as (t_ & w_ & TR_).
      exists t_, w_; apply KtransTau; auto.
    + inv Hd.
    + inv Hd.
    + dependent destruction Hd.
    + observe_equ x0; cbn in *.
      setoid_rewrite Eqt.
      setoid_rewrite bind_tau.
      cbn.
      destruct (IHTR t0 k eq_refl x Hd k_ w_ TR_)
        as (k' & wk' & TRk').        
      exists k', wk'; apply KtransTau; auto.
    + observe_equ x1.
      dependent destruction Hd; cbn in *.
      setoid_rewrite Eqt.
      setoid_rewrite bind_ret_l.
      exists k_, w_; auto.
    + observe_equ x1.
      dependent destruction Hd; cbn in *.
      setoid_rewrite Eqt.
      setoid_rewrite bind_ret_l.
      exists k_, w_; auto.
Qed.
Global Hint Resolve can_step_bind_iff: ctl.

Lemma can_step_bind_l `{HE: Encode E} {X Y}: forall (t t': itree E Y) (k: Y -> itree E X) w w',
    [t, w] ↦ [t', w'] ->
    not_done w' ->
    can_step (x <- t ;; k x) w.
Proof.
  intros.
  eapply can_step_bind_iff.
  left; eauto.
Qed.
Global Hint Resolve can_step_bind_l: ctl.

