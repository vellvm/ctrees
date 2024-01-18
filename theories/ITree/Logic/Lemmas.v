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

  Lemma can_step_tau{X}: forall (t: itree E X) w,
      can_step (t, w) ->
      can_step (Tau t, w).
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

  Lemma can_step_vis{X}: forall (e: E) (k: encode e -> itree E X) w (_: encode e),
      not_done w ->
      can_step (Vis e k, w).
  Proof.
    intros.
    exists (k X0), (Obs e X0).
    apply ktrans_vis.
    exists X0; auto.
  Qed.

  Lemma ctl_af_tau{X}: forall (t: itree E X) w φ,
      <( {(t, w)} |= AF now φ )> -> 
      <( {(Tau t, w)} |= AF (now φ) )>.
  Proof.
    intros.
    unfold entailsF in H.
    remember (t, w) as m.
    replace t with (fst m) by now subst.
    replace w with (snd m) by now subst.
    clear t w Heqm.
    induction H; destruct m as [t w]; simpl fst; simpl snd.
    - now next; left.
    - Opaque entailsF.
      destruct H0, H1; clear H H1.
      destruct H0 as (t' & w' & TR).
      specialize (H3 _ TR); cbn in H3.
      next; right.
      split.
      * apply can_step_tau; auto with ctl.
      * intros [t_ w_] TR_.
        rewrite ktrans_tau in TR_.
        now apply H2.
  Qed.

  Lemma ctl_af_vis{X}: forall (e: E) (k: encode e -> itree E X) (_: encode e) w φ,
      (φ w \/ (not_done w /\ forall (x: encode e), <( {(k x, Obs e x)} |= AF now φ )>)) ->
      <( {(Vis e k, w)} |= AF now φ )>.        
  Proof.
    intros.
    destruct H as [H | [Hd H]].
    - now next; left.
    - next; right; next; split.
      + now apply can_step_vis.
      + intros [t' w'] TR'.
        apply ktrans_vis in TR' as (? & -> & -> & ?).
        apply H.
  Qed.
      
  Lemma can_step_bind_iff{X Y}: forall (t: itree E Y) (k: Y -> itree E X) w,
      can_step (x <- t ;; k x, w) <->        
        (exists t' w', (t, w) ↦ (t', w') /\ not_done w')
        \/ (exists y w', (t, w) ↦ (Itree.stuck, w')
                   /\ return_with Y y w'
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
      return_with X x w ->
      ~ <( {(Itree.stuck: itree E X, w)} |= AF obs φ )>.
  Proof.
    intros * Hret Hcontra.
    inv Hcontra.
    - destruct H as (? & ? & ? & ?); cbn in *; subst.
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

  Lemma ctl_return_af_inv{X}: forall (t: itree E X) w (r: X),
      <( {(t, w)} |= AF return r )> ->
      return_with X r w \/ t ⇓ r.
  Proof.
    intros.
    remember (t, w) as T.
    replace t with (fst T) by now subst.
    replace w with (snd T) by now subst.
    clear HeqT t w.
    induction H; destruct m as (t, w).
    - left; auto.
    - destruct H0, H1; clear H H1.
      destruct H0 as (t' & w' & TR'); cbn.
      generalize dependent r.      
      ktrans_ind TR'; intros.
      + right; eapply ALeafVis.
        * now rewrite x0.
        * intro x'.          
          assert (TR_: (t, w) ↦ (k x', Obs e x')).
          { cbn.
            rewrite <- x0.
            eapply KtransObs; auto.
          }.
          destruct (H3 _ TR_); cbn in H1.
          -- inv H1.
          -- auto.
      + edestruct IHTR' with (t':=t'); eauto.
          -- rewrite x; reflexivity.
          -- intros [t_ w_] TR_.
             apply H2; cbn.
             rewrite <- x0; now apply KtransTau.
          -- intros [t_ w_] TR_.
             apply H3; cbn.
             rewrite <- x0; now apply KtransTau.
          -- right.
             eapply ALeafTau.
             ++ now rewrite x0.
             ++ auto.
      + right; eapply ALeafRet.
        assert (TR_: (t, Pure) ↦ (Itree.stuck, Done x0)).
        { cbn.
          rewrite <- x1.
          replace (TauF Itree.stuck) with (observe Itree.stuck (X:=X)) by reflexivity.
          apply KtransDone; auto.
        }
        destruct (H3 _ TR_); cbn in H0.        
        * dependent destruction H0.
          now rewrite x1.
        * now apply ALeaf_stuck in H0.
      + right; eapply ALeafRet.
        assert (TR_: (t, Obs e v) ↦ (Itree.stuck, Finish e v x0)).
        { cbn.
          rewrite <- x1.
          replace (TauF Itree.stuck) with (observe Itree.stuck (X:=X)) by reflexivity.
          apply KtransFinish; auto.
        }
        destruct (H3 _ TR_); cbn in H0.        
        * dependent destruction H0.
          now rewrite x1.
        * now apply ALeaf_stuck in H0.
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
      + apply can_step_not_done in H0; inv H0.
      + apply can_step_not_done in H0; inv H0. 
    - revert w k H0.
      dependent induction H; intros;
        observe_equ H; rewrite Eqt, ?bind_ret_l.
      + exact H0.
      + rewrite bind_tau.
        apply can_step_tau.
        now apply IHALeaf.
      + rewrite bind_vis.
        apply can_step_vis.
        * (* Indeed, [x <- Vis (e: void) ;; k x]
             does not step, need [Productive E] *)
          apply HP.
        * now apply can_step_not_done in H2. 
  Qed.
  Hint Resolve can_step_bind_r: ctl.

  
  Theorem ctl_bind_af_r{X Y} {HP: Productive E}:
    forall (t: itree E Y) (k: Y -> itree E X) w (r: Y) φ,
      <( {(t, w)} |= AF return r )> ->
      <( {(k r, w)} |= AF now φ )> ->
      <( {(x <- t ;; k x, w)} |= AF now φ )>.
  Proof.
    intros.
    apply ctl_return_af_inv in H as [H|H].
    - inv H; inv H0.
      + now next; left.
      + destruct H1.
        apply can_step_not_done in H0; inv H0. 
      + now next; left.
      + destruct H1.
        apply can_step_not_done in H0; inv H0.
    - dependent induction H; observe_equ H.
      + now rewrite Eqt, bind_ret_l.
      + rewrite Eqt, bind_tau.
        apply ctl_af_tau.
        now apply IHALeaf.
      + rewrite Eqt, bind_vis.
        apply ctl_af_vis.
        * apply HP.
        * destruct (not_done_dec w).
          -- right; split; auto.
             intro x'.
             (* Here, AF [return r] says nothing about the return value
                of [w], need a more specific predicate like [finish ψ] (see slack) *)
             apply H1.
  Admitted.

End CtlITrees.
