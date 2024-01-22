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
  ITree.Logic.CanStep
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
  Context {E: Type} {HE: Encode E} {X: Type}
    (φ: itree E X -> World E -> Prop) {HP: Proper (equ X ==> eq ==> iff) φ}.
  
  (*| [t |= AF φ] is semantic and requires double induction, on [AF] and inside it, in
  [ktrans]. Attempt to simplify to one induction with [AFInd] |*)
  Inductive AFInd: itree E X -> World E -> Prop :=
  | AFIndBase: forall (t: itree E X) (w: World E),
      φ t w ->
      AFInd t w
  | AFIndDoneBase: forall t (x: X),
      observe t = RetF x ->
      φ Itree.stuck (Done x) ->
      AFInd t Pure
  | AFIndFinishBase: forall t (e: E) (v: encode e) (x: X),
      observe t = RetF x ->
      φ Itree.stuck (Finish e v x) ->
      AFInd t (Obs e v)
  | AFIndTau: forall t u w,
      observe t = TauF u ->
      AFInd u w ->
      AFInd t w
  |AFIndVis: forall (t: itree E X) w e k (_: encode e),
      observe t = VisF e k ->
      not_done w ->
      (forall (v: encode e), AFInd (k v) (Obs e v)) ->
      AFInd t w.

  Lemma af_ind_stuck_done: forall (x: X),
    AFInd Itree.stuck (Done x) <->
    φ Itree.stuck (Done x).
  Proof.
    split; intros.
    - dependent induction H; auto.
    - now apply AFIndBase.
  Qed.

  Lemma af_ind_stuck_finish: forall (e: E) (v: encode e) (x: X),
    AFInd Itree.stuck (Finish e v x) <->
    φ Itree.stuck (Finish e v x).
  Proof.
    split; intros.
    - dependent induction H; auto.
    - now apply AFIndBase.
  Qed.

  Lemma af_afind {Hpr: @Productive E HE}
                 {TauInv: forall (t: itree E X) w, φ t w  -> φ (Tau t) w}
    : forall (t: itree E X) (w: World E),
      AFInd t w <-> cau true (fun _ _ => True) φ t w.
  Proof.
    split; intros; induction H.
    (* -> *)
    - now apply MatchA.
    - apply StepA; auto; split.
      + exists Itree.stuck, (Done x).
        Opaque Itree.stuck.
        cbn. rewrite H.
        apply KtransDone; auto.
      + intros t' w' TR.
        ktrans_ind TR.
        * rewrite H in x1; inv x1.
        * rewrite H in x1; inv x1.
        * rewrite H in x2; inv x2.          
          observe_equ x.
          rewrite <- Eqt, H1.          
          now apply MatchA.
    - apply StepA; auto; split.
      + exists Itree.stuck, (Finish e v x).
        Opaque Itree.stuck.
        cbn. rewrite H.
        apply KtransFinish; auto.
      + intros t' w' TR.
        ktrans_ind TR.
        * rewrite H in x1; inv x1.
        * rewrite H in x1; inv x1.
        * rewrite H in x2; inv x2.          
          observe_equ x.
          rewrite <- Eqt, H1.          
          now apply MatchA.
    - observe_equ H.
      rewrite Eqt; clear Eqt.
      destruct IHAFInd.
      + apply MatchA.
        (* TauInv here *)
        now apply TauInv.
      + destruct H2.
        apply StepA; auto.
        split; auto with ctl.
        intros t' w' TR.
        apply H3.
        now rewrite ktrans_tau in TR.
    - observe_equ H.
      rewrite Eqt; clear Eqt.
      apply StepA; auto; split; auto with ctl.
      intros t' w' TR.
      + apply ktrans_vis in TR as (v & ? & -> & ?).
        rewrite H3.
        eapply H2.
    - (* <- *)
      now apply AFIndBase.
    - destruct H0, H1; clear H H1.
      destruct H0 as (t' & w' & TR).
      cbn in TR.
      dependent induction TR.
      + observe_equ x.
        eapply AFIndVis with (e:=e) (k:=k); auto.
        intros v'.
        apply H3; cbn.
        rewrite <- x0.
        apply KtransObs; auto.
      + eapply AFIndTau with (u:=t0); auto.
        eapply (IHTR HP) with (t':=t'); auto.
        -- intros t_ w_ TR_.
           apply H2; cbn.
           rewrite <- x0.
           now apply ktrans_tau.
        -- intros t_ w_ TR_.
           apply H3; cbn.
           rewrite <- x0.
           now apply ktrans_tau.
      + apply AFIndDoneBase with (x:=x0); auto.
        assert (TR_: [t, Pure] ↦ [Itree.stuck, Done x0]).
        { cbn; rewrite <- x1; apply KtransDone; auto. }
        specialize (H3 _ _ TR_).
        now apply af_ind_stuck_done.
      + apply AFIndFinishBase with (x:=x0); auto.
        assert (TR_: [t, Obs e v] ↦ [Itree.stuck, Finish e v x0]).
        { cbn; rewrite <- x1; apply KtransFinish; auto. }
        specialize (H3 _ _ TR_).
        now apply af_ind_stuck_finish.
  Qed.
  
  Lemma ctl_af_tau: forall (t: itree E X) w φ,
      <( t, w |= AF now φ )> -> 
      <( {Tau t}, w |= AF (now φ) )>.
  Proof.
    intros.
    unfold entailsF in H.
    induction H.
    - now next; left.
    - Opaque entailsF.
      destruct H0, H1; clear H H1.
      destruct H0 as (t' & w' & TR).
      specialize (H3 _ _ TR); cbn in H3.
      next; right.
      split.
      * apply can_step_tau.
        exists t', w'; auto.
      * intros t_ w_ TR_.
        rewrite ktrans_tau in TR_.
        now apply H2.
  Qed.

  Lemma ctl_af_vis: forall (e: E) (k: encode e -> itree E X) (_: encode e) w φ,
      (φ w \/ (not_done w /\ forall (x: encode e), <( {k x}, {Obs e x} |= AF now φ )>)) ->
      <( {Vis e k}, w |= AF now φ )>.        
  Proof.
    intros.
    destruct H as [H | [Hd H]].
    - now next; left.
    - next; right; next; split.
      + now apply can_step_vis.
      + intros t' w' TR'.
        apply ktrans_vis in TR' as (? & -> & -> & ?).
        apply H.
  Qed.

End CtlITrees.

Section CtlAfBind.
  Context {E: Type} {HE: Encode E}.

  Lemma ctl_stuck_obs_af{X}: forall (x: X) φ w,
      return_eq X x w ->
      ~ <( {Itree.stuck: itree E X}, w |= AF obs φ )>.
  Proof.
    intros * Hret Hcontra.
    inv Hcontra.
    - inv H; cbn in *; subst. 
      destruct Hret; inv H.
    - destruct H0 as ((? & ? & ?) & ?).
      now apply ktrans_stuck in H0.
  Qed.

  Lemma ctl_obs_af_inv{X}: forall (t: itree E X) φ w,
      <( t, w |= AF obs φ )> ->
      not_done w.  
  Proof.
    intros * Haf.
    next in Haf; destruct Haf; cbn in H.
    - inv H. 
      constructor.
    - destruct H. 
      destruct H as (t' & w' & TR).
      now eapply ktrans_not_done with t t' w'.
  Qed.
  Hint Resolve ctl_obs_af_inv: ctl.

  Theorem ctl_bind_af_l{X Y}: forall (t: itree E Y) (k: Y -> itree E X) φ w,
      <( t, w |= AF obs φ )> ->
      <( {x <- t ;; k x}, w |= AF obs φ )>.
  Proof.
    intros * Haf.
    revert X k.
    induction Haf; intros; subst. 
    - (* MatchA *)
      next; left; cbn.
      apply H.
    - (* StepA *)
      destruct H0, H1; clear H H0.
      destruct H1 as (te & we & TR); cbn in TR.
      dependent destruction TR.
      + next; right; next; split. 
        * apply can_step_bind_l with t0 (Obs e v); cbn. 
          -- rewrite <- x0.
             now apply KtransObs.
          -- constructor.
        * intros k' w' TR'.
          apply ktrans_bind_inv in TR'
              as [(t' & TR' & Hd & ?) |
               [(y & TRr & -> & TRk) |
                 (e' & v' & x' & TRr & -> & TRk)]].
          -- rewrite H1.
             apply (H3 t' w' TR').
          -- specialize (H2 Itree.stuck (Done y) TRr).
             Transparent entailsF.
             apply ctl_stuck_obs_af with (x:=y) in H2; intuition.
          -- specialize (H2 Itree.stuck (Finish e' v' x') TRr).
             apply ctl_stuck_obs_af with (x:=x') in H2; intuition.
      + observe_equ x0.
        rewrite Eqt.
        assert (TRtau: ktrans_ (observe t) w (observe t') we).
        { rewrite x0; now apply KtransTau. }        
        next; right; next; split. 
        * eapply can_step_bind_l; cbn.
          apply KtransTau; eauto.
          specialize (H3 t' we TRtau _ k); cbn in H3.        
          now apply ctl_obs_af_inv in H3.
        * intros k' w' TR'.
          apply ktrans_bind_inv in TR'
              as [(t_ & TR_ & Hd & ?) |
                   [(y & TRt' & -> & TRk) |
                     (e' & v' & x' & TRr & -> & TRk)]].
          -- rewrite H.
             specialize (H3 t_ w'); cbn in H2.
             rewrite ktrans_tau in TR_.
             apply H3; cbn.
             rewrite x0.
             now apply ktrans_tau.
          -- cbn in TRt'.
             rewrite <- x0 in TRt'.
             specialize (H2 Itree.stuck (Done y) TRt'); cbn in H2.             
             Transparent entailsF.
             eapply ctl_stuck_obs_af with (x:=y) in H2; intuition.
          -- cbn in TRr.
             rewrite <- x0 in TRr.
             specialize (H2 Itree.stuck (Finish e' v' x') TRr); cbn in H2.             
             Transparent entailsF.
             eapply ctl_stuck_obs_af with (x:=x') in H2; intuition.
      + assert (TRt: ktrans_ (observe t) Pure (observe Itree.stuck) (Done x0)).
        { rewrite <- x1; apply KtransDone; reflexivity. }.
        specialize (H3 Itree.stuck (Done x0) TRt _ k); cbn in H3.
        apply ctl_obs_af_inv in H3; inv H3.
      + assert (TRt: ktrans_ (observe t) (Obs e v) (observe Itree.stuck) (Finish e v x0)).
        { rewrite <- x1; apply KtransFinish; reflexivity. }.
        specialize (H3 Itree.stuck (Finish e v x0) TRt _ k).
        apply ctl_obs_af_inv in H3; inv H3.
  Qed.

  Lemma ctl_return_af_inv{X}: forall (t: itree E X) w (r: X),
      <( t, w |= AF return r )> ->
      return_eq X r w \/ ALeaf (eq r) t.
  Proof.
    intros.
    induction H.
    - left; auto.
    - destruct H0, H1; clear H H1.
      destruct H0 as (t' & w' & TR'); cbn.
      generalize dependent r.      
      ktrans_ind TR'; intros.
      + right; eapply ALeafVis.
        * now rewrite x0.
        * intro x'.          
          assert (TR_: [t, w] ↦ [k x', Obs e x']).
          { cbn.
            rewrite <- x0.
            eapply KtransObs; auto.
          }.
          destruct (H3 _ _ TR_); cbn in H1.
          -- destruct H1; inv H1.
          -- auto.
      + edestruct IHTR' with (t':=t'); eauto.
          -- intros t_ w_ TR_.
             apply H2; cbn.
             rewrite <- x0; now apply KtransTau.
          -- intros t_ w_ TR_.
             apply H3; cbn.
             rewrite <- x0; now apply KtransTau.
          -- right.
             eapply ALeafTau.
             ++ now rewrite x0.
             ++ auto.
      + right; eapply ALeafRet.
        assert (TR_: [t, Pure] ↦ [Itree.stuck, Done x0]).
        { cbn.
          rewrite <- x1.
          replace (TauF Itree.stuck) with (observe Itree.stuck (X:=X)) by reflexivity.
          apply KtransDone; auto.
        }
        destruct (H3 _ _ TR_); cbn in H0.
        * destruct H0; dependent destruction H0.
          now rewrite x1.
        * now apply ALeaf_stuck in H0.
        * reflexivity.
      + right; eapply ALeafRet.
        assert (TR_: [t, Obs e v] ↦ [Itree.stuck, Finish e v x0]).
        { cbn.
          rewrite <- x1.
          replace (TauF Itree.stuck) with (observe Itree.stuck (X:=X)) by reflexivity.
          apply KtransFinish; auto.
        }
        destruct (H3 _ _ TR_); cbn in H0.        
        * destruct H0; dependent destruction H0.
          now rewrite x1.
        * now apply ALeaf_stuck in H0.
        * reflexivity.
  Qed.

  Lemma can_step_bind_r{X Y} {HP: Productive E}:
    forall (t: itree E Y) (k: Y -> itree E X) w (r: Y),      
      <( t, w |= AF return r )> ->
      can_step (k r) w ->
      can_step (x <- t ;; k x) w.
  Proof.    
    intros.
    apply ctl_return_af_inv in H as [H|H].
    - destruct H; inv H. (* (kr, w) can step, so w != done *)
      + apply can_step_not_done in H0; inv H0.
      + apply can_step_not_done in H0; inv H0. 
    - revert w k H0.
      dependent induction H; intros;
        observe_equ H; rewrite Eqt, ?bind_ret_l; subst.
      + exact H1.
      + rewrite bind_tau.
        eapply can_step_tau.
        now apply IHALeaf.
      + rewrite bind_vis.
        apply can_step_vis.
        * (* Indeed, [x <- Vis (e: void) ;; k x]
             does not step, need [Productive E] *)
          apply HP.
        * now apply can_step_not_done in H2. 
  Qed.
  Hint Resolve can_step_bind_r: ctl.

   Theorem ctl_bind_af_finish{X Y} {HP: Productive E}:
    forall (t: itree E Y) (k: Y -> itree E X) w φ R,
      <( t, w |= AF finish R )> ->
      (forall (e: E) (v: encode e) (y: Y), R e v y -> <( {k y}, {Obs e v} |= AF now φ )>) ->
      <( {x <- t ;; k x}, w |= AF now φ )>.
  Proof.
    intros.
    revert H0.
    generalize dependent φ.
    generalize dependent k.
    induction H; intros; cbn in H.
    - inv H.
     
    - destruct H0, H1; clear H H1.
      destruct H0 as (t' & w' & TR'); cbn.
      generalize dependent r.      
      ktrans_ind TR'; intros.
      
    apply ctl_return_af_inv in H as [H|H].
    - specialize (H0 w).
      destruct H; inv H; inv H0.
      + now next; left.
      + destruct H1.
        apply can_step_not_done in H0; inv H0. 
      + now next; left.
      + destruct H1.
        apply can_step_not_done in H0; inv H0.
    - generalize dependent w.
      revert H0.
      dependent induction H; intros; observe_equ H.
      + now rewrite Eqt, bind_ret_l.
      + rewrite Eqt, bind_tau.
        apply ctl_af_tau.
        now apply IHALeaf.
      + rewrite Eqt, bind_vis.
        apply ctl_af_vis.
        * apply HP.
        * destruct (not_done_dec w).
          -- right; split; auto.
          -- left.
             specialize (H2 w).
             auto.
             apply H1.
             (* Here, AF [return r] says nothing about the return value
                of [w], need a more specific predicate like [finish ψ] (see slack) *)
             apply H1.
  Admitted.
  
  Theorem ctl_bind_af_r{X Y} {HP: Productive E}:
    forall (t: itree E Y) (k: Y -> itree E X) w φ
      (ψ: forall (e: E), encode e -> Y -> Prop),
      <( {(t, w)} |= AF finish ψ )> ->
      (forall (e: E) (v: encode e) (r: Y),
          ψ e v r -> <( {(k r, Obs e v)} |= AF now φ )>) ->
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
    - generalize dependent w.
      dependent induction H; intros; observe_equ H.
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
             apply H1.
             (* Here, AF [return r] says nothing about the return value
                of [w], need a more specific predicate like [finish ψ] (see slack) *)
             apply H1.
  Admitted.

End CtlITrees.
