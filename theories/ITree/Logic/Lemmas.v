From Coq Require Import
  Basics
  Classes.RelationPairs.

From Coinduction Require Import
  coinduction lattice.

From ExtLib Require Import
  Structures.Monad
  Data.Monads.StateMonad.

From CTree Require Import
  Events.Core
  ITree.Core
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

(*| CTL logic lemmas on c/itrees |*)
Section CtlITrees.
  Context {E: Type} {HE: Encode E}.

  Lemma ctl_af_star{X}: forall (t: itree E X * World E) φ,
      <( t |= AF φ )> -> exists t', t ↦* t' /\ <( t' |= φ )>.
  Proof.
    cbn; intros.
    dependent induction H.
    + exists m; split.
      * exists 0%nat; cbn; auto. 
      * assumption.
    + destruct H1 as [(te & we & TRe) ?].
      destruct (H1 _ TRe) as [[t' w'] ((n & TRn) & ?)].
      exists (t', w'); split; auto.
      exists (S n).
      cbn.
      exists (te, we); destruct m as (t, w); split; auto.
  Qed.

  Lemma can_step_bind_iff{X Y}: forall (t: itree E Y) (k: Y -> itree E X) w,
      can_step (x <- t ;; k x, w) <->        
        (exists t' w', (t, w) ↦ (t', w') /\ not_done w')
        \/ (exists y w', (t, w) ↦ (Itree.stuck, w')
                   /\ return_with y w'
                   /\ can_step (k y, w)).
  Proof.
    unfold can_step; split.
    - intros (k' & w' & TR).
      apply ktrans_bind_inv in TR
          as [(t' & TR' & Hd & ?) | (y & w_ & ? & Hd & ?)].
      + left; exists t', w'; auto.
      + right; inv Hd.
        * exists y, (Done y); eauto with ctl.
        * exists y, (Finish e v y); eauto with ctl.
    - intros * [(t' & w' & TR & Hd) | (y & w' & TR & Hd & k_ & w_ & TR_)]; cbn in TR; dependent induction TR.       
      + observe_equ x0; cbn.
        setoid_rewrite Eqt.
        setoid_rewrite bind_vis.
        exists (x <- k0 v ;; k x), (Obs e v); now apply KtransObs.
      + observe_equ x0; cbn in *.
        setoid_rewrite Eqt.
        setoid_rewrite bind_tau.
        destruct (IHTR t0 k w _ _ eq_refl eq_refl Hd)
          as (t_ & w_ & TR_).
        exists t_, w_; apply KtransTau; auto.
      + inv Hd.
      + inv Hd.
      + inv Hd.
      + observe_equ x0; cbn in *.
        setoid_rewrite Eqt.
        setoid_rewrite bind_tau.
        cbn.
        assert (Heq: (observe t', w') = (TauF Itree.stuck, w')) by now rewrite x.
        destruct (IHTR t0 k w _ eq_refl Heq Hd k_ w_ TR_)
          as (k' & wk' & TRk').        
        exists k', wk'; apply KtransTau; auto.
      + observe_equ x1; dependent destruction Hd; cbn in *.
        setoid_rewrite Eqt.
        setoid_rewrite bind_ret_l.
        exists k_, w_; auto.
      + observe_equ x1; dependent destruction Hd; cbn in *.
        setoid_rewrite Eqt.
        setoid_rewrite bind_ret_l.
        exists k_, w_; auto.
  Qed.
  Hint Resolve can_step_bind_iff: ctl.

  Lemma can_step_bind_l{X Y}: forall (t t': itree E Y) (k: Y -> itree E X) w w',
      (t, w) ↦ (t', w') ->
      not_done w' ->
      can_step (x <- t ;; k x, w).
  Proof.
    intros.
    eapply can_step_bind_iff.
    left; eauto.
  Qed.
  Hint Resolve can_step_bind_l: ctl.

  Lemma ctl_stuck_obs_af{X}: forall (x: X) φ w,
      return_with x w ->
      ~ <( {(Itree.stuck: itree E X, w)} |= AF obs φ )>.
  Proof.
    intros * Hret Hcontra.
    inv Hcontra.
    - rewrite ctl_obs in H.
      destruct H as (? & ? & ? & ?); cbn in *; subst.
      inv Hret.
    - destruct H0 as ((? & ? & ?) & ?).
      now apply ktrans_stuck in H0.
  Qed.

  Lemma ctl_obs_af_inv{X}: forall (t: itree E X) φ w,
      <( {(t, w)} |= AF obs φ )> ->
      not_done w.  
  Proof.
    intros * Haf.
    next in Haf; destruct Haf; cbn in H.
    - destruct H as (e & v & -> & ?).
      constructor.
    - destruct H. 
      destruct H as (t' & w' & TR).
      now eapply ktrans_not_done with t t' w'.
  Qed.
  Hint Resolve ctl_obs_af_inv: ctl.

  Opaque entailsF.
  Theorem ctl_bind_af_l{X Y}: forall (t: itree E Y) (k: Y -> itree E X) φ w,
      <( {(t, w)} |= AF obs φ )> ->
      <( {(x <- t ;; k x, w)} |= AF obs φ )>.
  Proof.
    intros * Haf.
    remember (t, w) as m.
    replace t with (fst m) by now subst.
    replace w with (snd m) by now subst.
    clear Heqm t w.
    revert X k.
    induction Haf; intros; destruct m as [t w]; subst; cbn in *.
    - (* MatchA *)
      next; left; cbn.
      destruct H as (e_ & x_ & ? & ?); subst.
      rewrite ctl_obs; eauto.
    - (* StepA *)
      destruct H0, H1; clear H H0.
      destruct H1 as (te & we & TR); cbn in *.
      dependent destruction TR.
      + next; right; next; split. 
        * apply can_step_bind_l with t0 (Obs e v); cbn. 
          -- rewrite <- x0.
             now apply KtransObs.
          -- constructor.
        * intros [k' w'] TR'.
          apply ktrans_bind_inv in TR'
              as [(t' & TR' & Hd & ?) | (y & w_ & TRt' & Hr & TRk)].
          -- rewrite H1.
             specialize (H3 (t', w') TR').
             apply H3.
          -- specialize (H2 (Itree.stuck, w_) TRt').
             Transparent entailsF.
             apply ctl_stuck_obs_af with (x:=y) in H2; intuition.             
      + observe_equ x0.
        rewrite Eqt.
        assert (TRtau: trans_ (observe t, w) (observe t', we)).
        { rewrite x0; now apply KtransTau. }        
        next; right; next; split. 
        * eapply can_step_bind_l; cbn.
          apply KtransTau; eauto.
          specialize (H3 (t', we) TRtau _ k); cbn in H3.        
          now apply ctl_obs_af_inv in H3.
        * intros [k' w'] TR'.
          apply ktrans_bind_inv in TR'
              as [(t_ & TR_ & Hd & ?) | (y & w_ & TRt' & Hd & TRk) ].
          -- rewrite H.
             specialize (H3 (t_, w')); cbn in H2.
             rewrite ktrans_tau in TR_.
             apply H3.
             rewrite x0.
             now apply ktrans_tau.
          -- cbn in TRt'.
             rewrite <- x0 in TRt'.
             specialize (H2 (Itree.stuck, w_) TRt'); cbn in H2.             
             Transparent entailsF.
             eapply ctl_stuck_obs_af with (x:=y) in H2; intuition. 
      + assert (TRt: trans_ (observe t, Pure) (observe Itree.stuck, Done x0)).
        { rewrite <- x1; apply KtransDone; reflexivity. }.
        specialize (H3 (Itree.stuck, Done x0) TRt _ k); cbn in H3.
        apply ctl_obs_af_inv in H3; inv H3.
      + assert (TRt: trans_ (observe t, Obs e v) (observe Itree.stuck, Finish e v x0)).
        { rewrite <- x1; apply KtransFinish; reflexivity. }.
        specialize (H3 (Itree.stuck, Finish e v x0) TRt _ k).
        apply ctl_obs_af_inv in H3; inv H3.
  Qed.

  Lemma can_step_bind_r{X Y} {HP: Productive E}:
    forall (t: itree E Y) (k: Y -> itree E X) w (r: Y),      
      <( {(t, w)} |= AF return r )> ->
      can_step (k r, w) ->
      can_step (x <- t ;; k x, w).
  Proof.    
    intros.
    apply ctl_return_af_inv in H as [H|H].
    - inv H. (* (kr, w) can step, so w != done *)
      + inv H0; destruct H; inv H; inv H5.
      + inv H0; destruct H; inv H; inv H5.
    - revert w k H0.
      remember (observe t) as T.
      generalize dependent t.
      generalize dependent X.            
      induction H; intros; observe_equ HeqT; rewrite Eqt, ?bind_ret_l.
      + exact H0.
      + rewrite bind_br.
        apply can_step_br; destruct b.
        * destruct H1 as (? & ? & ?).
          eapply ktrans_not_done; eauto.
        * exists (Fin.F1).
          eapply H0; try reflexivity; auto.
      + rewrite bind_vis.
        apply can_step_vis.
        * (* Indeed, [x <- Vis (e: void) ;; k x]
             does not step, ughhh *)
          apply HP.
        * destruct H1 as (? & ? & ?).
          eapply ktrans_not_done; eauto.
  Qed.
  Hint Resolve can_step_bind_r: ctl.
  
  Lemma iter_ctl_af: forall (t: X -> itreeW X) (σ: W) (i : X) (φ: W -> Prop),
      <( {(t i, σ)} |= AF done φ )> ->
      <( {(forever t i, σ)} |= AG AF now φ )>.
  Proof.
    intros.
    coinduction R CIH.
    remember (t i, σ).
    generalize dependent i.
    induction H; intros; subst; apply RStepA.
    - apply MatchA.
      now destruct H.
  Admitted.

End CtlITrees.
