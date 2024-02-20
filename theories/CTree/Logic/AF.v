From Coq Require Import
  Basics
  Arith.Wf_nat
  Classes.Morphisms.

From Coinduction Require Import
  coinduction lattice.

From CTree Require Import
  Events.Core
  Events.WriterE
  CTree.Core
  CTree.Equ
  CTree.Interp.Core
  CTree.Interp.State
  CTree.Logic.Trans
  CTree.Logic.CanStep
  Logic.Ctl
  Logic.Kripke
  Logic.Setoid.

Set Implicit Arguments.
Generalizable All Variables.

Import CTreeNotations CtlNotations.
Local Open Scope ctl_scope.
Local Open Scope ctree_scope.
  
(*| CTL logic lemmas on c/itrees |*)
Section BasicLemmas.
  Context {E: Type} {HE: Encode E} {X: Type}.

  Lemma done_af: forall (t: ctree E X) φ w,
      is_done w ->
      <( t, w |= AF now φ )> ->
      φ w.
  Proof.
    intros * Hret Hcontra.
    inv Hcontra.
    - now rewrite ctl_now in H.
    - destruct H0 as ((? & ? & ?) & ?).
      exfalso.
      eapply done_not_ktrans with (t:=t); eauto.
  Qed.

  Lemma af_ret: forall r w (Rr: rel X (World E)),      
      Rr r w ->
      not_done w ->
      <( {Ret r}, w |= AF done Rr )>.
  Proof.
    intros * Hr Hd.
    next; right; next; split.
    - now apply can_step_ret.
    - intros t_ w_ TR_.
      inv Hd.
      + cbn in TR_. dependent destruction TR_. 
        next; left.
        rewrite ctl_done.
        now constructor.
      + apply ktrans_finish in TR_ as (-> & ->).
        next; left.
        rewrite ctl_done.
        now constructor.       
  Qed.
  Hint Resolve af_ret: ctl.
  
  Lemma af_tau: forall (t: ctree E X) w φ,
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

  Lemma afax_tau: forall (t: ctree E X) w φ,
      <( t, w |= AF AX now φ )> -> 
      <( {Tau t}, w |= AF AX (now φ) )>.
  Proof.
    intros.
    Transparent entailsF.
    unfold entailsF in H.
    induction H.
    - destruct H.
      next; left. 
      split.
      + now apply can_step_tau.
      + intros *  TR.
        rewrite ktrans_tau in TR.
        now apply H0 with t'.
    - destruct H0, H1; clear H H1.
      next; right.
      split.
      + now apply can_step_tau.
      + intros * TR.
        rewrite ktrans_tau in TR.
        now apply H2.
  Qed.
  
  Lemma af_br: forall n (k: fin' n -> ctree E X) w φ,
      <( {Br n k}, w |= AF now φ )> <->
        (forall (i: fin' n), <( {k i}, w |= AF now φ )>).
  Proof.
    split; intros.
    - next in H; destruct H.
      + next; left.
        now rewrite ctl_now in *.
      + destruct H.
        apply H0.
        apply ktrans_br.
        apply can_step_not_done in H.
        exists i; eauto.
    - destruct (not_done_dec w).
      + next; right.
        next; split; auto.
        * now apply can_step_br.
        * intros t' w' TR'.
          apply ktrans_br in TR' as (? & -> & -> & ?).
          apply H.
      + apply done_af with (φ:=φ) (t:= k Fin.F1) in i; auto.
        next; left.
        now apply ctl_now.
  Qed.

  Lemma af_vis: forall (e: E) (k: encode e -> ctree E X) (_: encode e) w φ,
      (φ w \/ (not_done w /\ forall (x: encode e),
                 <( {k x}, {Obs e x} |= AF now φ )>)) ->
      <( {Vis e k}, w |= AF now φ )>.        
  Proof.
    intros.
    destruct H as [H | [Hd H]].
    - now next; left.
    - next; right; next; split.
      + now apply can_step_vis.
      + intros t' w' TR'.
        apply ktrans_vis in TR' as (? & -> & ? & ?).
        now rewrite <- H0.
  Qed.

End BasicLemmas.

Section AfIndLemma.
  Context {E: Type} {HE: Encode E} {X: Type}.
  
  (*| [t |= AF φ] is semantic and requires double induction, on [AF] and inside it, in
    [ktrans]. Attempt to simplify to one induction with [AFInd] |*)
  Inductive AFInd(φ: ctree E X -> World E -> Prop): ctree E X -> World E -> Prop :=
  | AFIndBase: forall (t: ctree E X) (w: World E),
      φ t w ->
      AFInd φ t w
  | AFIndDoneBase: forall t (x: X),
      observe t = RetF x ->
      φ Ctree.stuck (Done x) ->
      AFInd φ t Pure
  | AFIndFinishBase: forall t (e: E) (v: encode e) (x: X),
      observe t = RetF x ->
      φ Ctree.stuck (Finish e v x) ->
      AFInd φ t (Obs e v)
  | AFIndTau: forall t u w,
      observe t = TauF u ->
      AFInd φ u w ->
      AFInd φ t w
  |AFIndVis: forall (t: ctree E X) w e k (_: encode e),
      observe t = VisF e k ->
      not_done w ->
      (forall (v: encode e), AFInd φ (k v) (Obs e v)) ->
      AFInd φ t w
  |AFIndBr: forall n (t: ctree E X) w k,
      observe t = BrF n k ->
      not_done w ->
      (forall (i: fin' n), AFInd φ (k i) w) ->
      AFInd φ t w.

  Global Instance proper_equ_afind φ {HP: Proper (equ eq ==> eq ==> iff) φ}:
    Proper (equ eq ==> eq ==> iff) (AFInd φ).
  Proof.
    unfold Proper, respectful.
    intros; subst; split; intros Hind.
    - generalize dependent y.
      induction Hind; intros.
      + apply AFIndBase; auto.
        now rewrite <- H0.
      + apply AFIndDoneBase with x; auto.
        unfold equ in H1; step in H1; cbn in H1; dependent destruction H1; congruence.
      + apply AFIndFinishBase with x; auto.
        unfold equ in H1; step in H1; cbn in H1; dependent destruction H1; congruence.
      + unfold equ; step in H0; cbn in H0; rewrite H in H0.
        dependent destruction H0.
        apply IHHind in H0.
        apply AFIndTau with t2; congruence.
      + unfold equ; step in H3; cbn in H3; rewrite H in H3.
        dependent destruction H3.
        eapply AFIndVis with e k2; auto.
        intros.
        apply H2, H3.
      + unfold equ; step in H3; cbn in H3; rewrite H in H3.
        dependent destruction H3.
        eapply AFIndBr; eauto. 
        intros.
        eapply H2 with i, H3.
    - generalize dependent x.
      induction Hind; intros.
      + apply AFIndBase; auto.
        now rewrite H0.
      + apply AFIndDoneBase with x; auto.
        unfold equ in H1; step in H1; cbn in H1; dependent destruction H1; congruence.
      + apply AFIndFinishBase with x; auto.
        unfold equ in H1; step in H1; cbn in H1; dependent destruction H1; congruence.
      + unfold equ; step in H0; cbn in H0; rewrite H in H0.
        dependent destruction H0.
        apply IHHind in H0.
        apply AFIndTau with t1; congruence.
      + unfold equ; step in H3; cbn in H3; rewrite H in H3.
        dependent destruction H3.
        eapply AFIndVis with e k1; auto.
        intros.
        apply H2, H3.
      + unfold equ; step in H3; cbn in H3; rewrite H in H3.
        dependent destruction H3.
        eapply AFIndBr; eauto. 
        intros.
        eapply H2 with i, H3.
  Qed.  

  Lemma af_ind_stuck_done: forall (x: X) φ,
    AFInd φ Ctree.stuck (Done x) <->
    φ Ctree.stuck (Done x).
  Proof.
    split; intros.
    - dependent induction H; auto.
    - now apply AFIndBase.
  Qed.

  Lemma af_ind_stuck_finish: forall (e: E) (v: encode e) (x: X) φ,
    AFInd φ Ctree.stuck (Finish e v x) <->
    φ Ctree.stuck (Finish e v x).
  Proof.
    split; intros.
    - dependent induction H; auto.
    - now apply AFIndBase.
  Qed.

  (* This is a super useful lemma, it allows us to do induction on [AFInd]
     instead of two inductions on [cau] and [trans] *)
  Opaque Ctree.stuck.
  Lemma af_afind : forall (t: ctree E X) (w: World E) φ,
       cau true (fun _ _ => True) φ t w -> AFInd φ t w.
  Proof.
    intros; induction H.
    - now apply AFIndBase.
    - destruct H0, H1; clear H H1.
      destruct H0 as (t' & w' & TR).
      cbn in TR.
      dependent induction TR.
       + eapply AFIndTau with (u:=t0); auto.
        eapply IHTR with (t':=t'); auto.
        -- intros t_ w_ TR_.
           apply H2; cbn.
           rewrite <- x0.
           now apply ktrans_tau.
        -- intros t_ w_ TR_.
           apply H3; cbn.
           rewrite <- x0.
           now apply ktrans_tau.
       + observe_equ x.
         eapply AFIndBr with (n:=n) (k:=k); auto.
         intros j.
         apply H3; cbn.
         rewrite <- x0.
         apply KtransBr with j; auto.
       + observe_equ x.
         eapply AFIndVis with (e:=e) (k:=k); auto.
         intros v'.
         apply H3; cbn.
         rewrite <- x0.
         apply KtransObs; auto.     
       + apply AFIndDoneBase with (x:=x0); auto.
         assert (TR_: [t, Pure] ↦ [Ctree.stuck, Done x0]).
         { cbn; rewrite <- x1; apply KtransDone; auto. }
         specialize (H3 _ _ TR_).
         now apply af_ind_stuck_done.
       + apply AFIndFinishBase with (x:=x0); auto.
         assert (TR_: [t, Obs e v] ↦ [Ctree.stuck, Finish e v x0]).
         { cbn; rewrite <- x1; apply KtransFinish; auto. }
         specialize (H3 _ _ TR_).
         now apply af_ind_stuck_finish.
  Qed.

  (* -> *)
  Lemma afind_af {Hpr: @Productive E HE} φ
    {HP: Proper (equ eq ==> eq ==> iff) φ}
    {TauInv: forall (t: ctree E X) w, φ t w  -> φ (Tau t) w}
    : forall (t: ctree E X) (w: World E),
      AFInd φ t w -> cau true (fun _ _ => True) φ t w.
  Proof.
    intros; induction H.
    - now apply MatchA.
    - apply StepA; auto; split.
      + exists Ctree.stuck, (Done x).
        Opaque Ctree.stuck.
        cbn. rewrite H.
        apply KtransDone; auto.
      + intros t' w' TR.
        cbn in TR.        
        dependent induction TR.
        * rewrite H in x1; inv x1.
        * rewrite H in x1; inv x1.
        * rewrite H in x1; inv x1.
        * observe_equ x.
          rewrite <- Eqt, H1.
          rewrite <- x2 in H.
          inv H.
          now apply MatchA.
    - apply StepA; auto; split.
      + exists Ctree.stuck, (Finish e v x).
        Opaque Ctree.stuck.
        cbn. rewrite H.
        apply KtransFinish; auto.
      + intros t' w' TR.
        cbn in TR.
        dependent induction TR.
        * rewrite H in x1; inv x1.
        * rewrite H in x1; inv x1.
        * rewrite H in x1; inv x1.
        * observe_equ x.
          rewrite <- Eqt, H1.
          rewrite <- x2 in H.
          inv H.
          now apply MatchA.
    - observe_equ H.
      rewrite Eqt; clear Eqt.
      destruct IHAFInd.
      + apply MatchA.
        (* TauInv here *)
        now apply TauInv.
      + destruct H2.
        apply StepA; auto.
        split.
        * now apply can_step_tau.
        * intros t' w' TR.
          apply H3.
          now rewrite ktrans_tau in TR.
    - observe_equ H.
      rewrite Eqt; clear Eqt.
      apply StepA; auto; split.
      + now apply can_step_vis.
      + intros t' w' TR.
        apply ktrans_vis in TR as (v & -> & <- & ?).
        eapply H2.
    - observe_equ H.
      rewrite Eqt; clear Eqt.
      apply StepA; auto; split.
      + now apply can_step_br.
      + intros t' w' TR.
        apply ktrans_br in TR as (v & -> & <- & ?).
        eapply H2.
  Qed.
End AfIndLemma.

Section AfDoneIndLemma.
  Context {E: Type} {HE: Encode E} {X: Type}
    (φ: X -> World E -> Prop).

  (* t |= AF AX done R *)
  Inductive AFDoneInd: ctree E X -> World E -> Prop :=
  | AFDoneDoneBase: forall t (x: X),
      observe t = RetF x ->
      φ x Pure ->
      AFDoneInd t Pure
  | AFDoneFinishBase: forall t (e: E) (v: encode e) (x: X),
      observe t = RetF x ->
      φ x (Obs e v) ->
      AFDoneInd t (Obs e v)
  | AFDoneIndTau: forall t u w,
      observe t = TauF u ->
      AFDoneInd u w ->
      AFDoneInd t w
  |AFDoneIndVis: forall (t: ctree E X) w e k (_: encode e),
      observe t = VisF e k ->
      not_done w ->
      (forall (v: encode e), AFDoneInd (k v) (Obs e v)) ->
      AFDoneInd t w
  |AFDoneIndBr: forall (t: ctree E X) w n (k: fin' n -> _),
      observe t = BrF n k ->
      not_done w ->
      (forall (i: fin' n), AFDoneInd (k i) w) ->
      AFDoneInd t w.

  Global Instance proper_equ_afdoneind:
    Proper (equ eq ==> eq ==> iff) AFDoneInd.
  Proof.
    unfold Proper, respectful.
    intros; subst; split; intros Hind.
    - generalize dependent y.
      induction Hind; intros.
      + apply AFDoneDoneBase with x; auto.
        rewrite <- H.
        unfold equ in H.
        step in H1; cbn in H1; dependent destruction H1;
          congruence.
      + apply AFDoneFinishBase with x; auto.
        rewrite <- H.
        step in H1; cbn in H1; dependent destruction H1;
          congruence.
      + unfold equ; step in H0; cbn in H0; rewrite H in H0.
        dependent destruction H0.
        apply IHHind in H0.
        apply AFDoneIndTau with t2; congruence.
      + unfold equ; step in H3; cbn in H3; rewrite H in H3.
        dependent destruction H3.
        eapply AFDoneIndVis with e k2; auto; intros.
        apply H2, H3.
      + unfold equ; step in H3; cbn in H3; rewrite H in H3.
        dependent destruction H3.
        eapply AFDoneIndBr with _ k2; auto; intros.
        apply H2 with i, H3.
    - generalize dependent x.
      induction Hind; intros.
      + apply AFDoneDoneBase with x; auto.
        rewrite <- H.
        unfold equ in H.
        step in H1; cbn in H1; dependent destruction H1;
          congruence.
      + apply AFDoneFinishBase with x; auto.
        rewrite <- H.
        step in H1; cbn in H1; dependent destruction H1;
          congruence.
      + unfold equ; step in H0; cbn in H0; rewrite H in H0.
        dependent destruction H0.
        apply IHHind in H0.
        apply AFDoneIndTau with t1; congruence.
      + unfold equ; step in H3; cbn in H3; rewrite H in H3.
        dependent destruction H3.
        eapply AFDoneIndVis with e k1; auto; intros.
        apply H2, H3.
      + unfold equ; step in H3; cbn in H3; rewrite H in H3.
        dependent destruction H3.
        eapply AFDoneIndBr with _ k1; auto; intros.
        apply H2 with i, H3.
  Qed.

  Lemma afdoneind_stuck: forall w,
      ~ (AFDoneInd Ctree.stuck w).
  Proof.
    intros * Hcontra.
    dependent induction Hcontra; eauto.
  Qed.

  Lemma afdone_ind: forall (t: ctree E X) w,
      <( t, w |= AF AX done φ )> ->
      AFDoneInd t w.
  Proof.
    intros; induction H.
    - next in H.
      destruct H as [(t' & w' & TR) H].
      cbn in TR.
      dependent induction TR.
      + eapply AFDoneIndTau with (u:=t0); auto.
        eapply IHTR; auto.
        intros t_ w_ TR_.
        apply H; cbn.
        rewrite <- x0.
        now apply ktrans_tau.
      + eapply AFDoneIndBr; eauto.
        intros v'.
        assert (TR: ktrans_ (observe t) w (observe (k v')) w).
        { rewrite <- x0; apply ktrans_br; exists v'; eauto. }
        specialize (H1 _ _ TR).
        rewrite ctl_done in H1.
        inv H1; inv H.
      + eapply AFDoneIndVis; eauto.
        intros v'.
        assert (TR: ktrans_ (observe t) w (observe (k v')) (Obs e v')).
        { rewrite <- x0; apply ktrans_vis; exists v'; eauto. }
        specialize (H1 _ _ TR).
        rewrite ctl_done in H1.
        inv H1.
      + eapply AFDoneDoneBase with (x:=x0); auto.
        assert (TR: ktrans_ (observe t) Pure (observe Ctree.stuck) (Done x0)).
        { rewrite <- x1; econstructor; auto. }
        specialize (H0 _ _ TR).
        rewrite ctl_done in H0.
        now dependent destruction H0.
      + eapply AFDoneFinishBase with (x:=x0); auto.
        assert (TR: ktrans_ (observe t) (Obs e v) (observe Ctree.stuck) (Finish e v x0)).
        { rewrite <- x1; econstructor; auto. }
        specialize (H0 _ _ TR).
        rewrite ctl_done in H0.
        now dependent destruction H0.
    -  destruct H0, H1; clear H H1.
       destruct H0 as (t' & w' & TR).
       cbn in TR.
       dependent induction TR.
       + eapply AFDoneIndTau with (u:=t0); auto.
        eapply (IHTR) with (t':=t'); auto.
        -- intros t_ w_ TR_.
           apply H2; cbn.
           rewrite <- x0.
           now apply ktrans_tau.
        -- intros t_ w_ TR_.
           apply H3; cbn.
           rewrite <- x0.
           now apply ktrans_tau.
       + observe_equ x.
         eapply AFDoneIndBr with n k; auto.
         intros i'.
         apply H3; cbn.
         rewrite <- x0.
         apply KtransBr with i'; auto.
       + observe_equ x.
         eapply AFDoneIndVis with (e:=e) (k:=k); auto.
         intros v'.
         apply H3; cbn.
         rewrite <- x0.
         apply KtransObs; auto.
      + apply AFDoneDoneBase with (x:=x0); auto.
        assert (TR_: ktrans_ (observe t) Pure (observe Ctree.stuck) (Done x0)).
        { rewrite <- x1; apply KtransDone; auto. }
        specialize (H3 _ _ TR_).
        now apply afdoneind_stuck in H3.
      + apply AFDoneFinishBase with (x:=x0); auto.
        assert (TR_: ktrans_ (observe t) (Obs e v) (observe Ctree.stuck) (Finish e v x0)).
        { rewrite <- x1; apply KtransFinish; auto. }
        specialize (H3 _ _ TR_).
        now apply afdoneind_stuck in H3.
  Qed.

  Lemma af_ret_inv: forall (x: X) w R,
      <( {Ret x}, w |= AF (AX done R) )> ->
      R x w.
  Proof.
    intros.
    apply af_afind in H.
    dependent induction H.
    - destruct H.
      destruct H as (t' & w' & TR).
      specialize (H0 _ _ TR).
      inv H0; destruct w; cbn in TR; dependent destruction TR; auto.
    - destruct H0.
      apply can_step_not_done in H.
      inv H.
    - destruct H0.
      apply can_step_not_done in H.
      inv H.
  Qed.

End AfDoneIndLemma.

Section CtlAfBind.
  Context {E: Type} {HE: Encode E}.

  Lemma af_stuck{X}: forall φ w,
      φ w <->
      <( {Ctree.stuck: ctree E X}, w |= AF now φ )>.
  Proof.
    split; intros.
    - next; left; auto.
    - remember Ctree.stuck as S. 
      apply af_afind in H.
      Transparent Ctree.stuck.
      induction H; subst; auto; cbn in *;
        dependent destruction H; auto.      
  Qed.

  Typeclasses Transparent equ.
  Theorem af_bind_vis{X Y}: forall (t: ctree E Y) (k: Y -> ctree E X) φ w,
      <( t, w |= AF vis φ )> ->
      <( {x <- t ;; k x}, w |= AF vis φ )>.
  Proof.
    intros * Haf.
    apply af_afind in Haf.
    revert X k.    
    induction Haf; intros; subst. 
    - (* Base *)
      next; left; cbn; apply H.
    - (* Done *)
      inv H0.
    - (* Finish *)
      inv H0.
    - (* Tau *)
      observe_equ H.
      rewrite Eqt, bind_tau.
      apply af_tau; eauto.
    - (* Vis *)
      observe_equ H.
      rewrite Eqt, bind_vis.
      apply af_vis; eauto.
    - (* Br *)
      observe_equ H.
      rewrite Eqt, bind_br.
      apply af_br; eauto.      
  Qed.

  Theorem af_bind_pure{X Y}: forall (t: ctree E Y) (k: Y -> ctree E X) w,
      <( t, w |= AF pure )> ->
      <( {x <- t ;; k x}, w |= AF pure )>.
  Proof.
    intros * Haf.
    apply af_afind in Haf.
    revert X k.    
    induction Haf; intros; subst. 
    - (* Base *)
      next; left; now cbn. 
    - (* Done *)
      inv H0.
    - (* Finish *)
      inv H0.
    - (* Tau *)
      observe_equ H.
      rewrite Eqt, bind_tau.
      apply af_tau; eauto.
    - (* Vis *)
      observe_equ H.
      rewrite Eqt, bind_vis.
      apply af_vis; eauto.
    - (* Br *)
      observe_equ H.
      rewrite Eqt, bind_br.
      apply af_br; eauto.   
  Qed.

  Lemma can_step_bind_r{X Y}: forall (t: ctree E Y) (k: Y -> ctree E X) w R,      
      <( t, w |= AF AX done R )> ->
      (forall y w, R y w -> can_step (k y) w) ->
      can_step (x <- t ;; k x) w.
  Proof.    
    intros.
    apply afdone_ind in H.
    generalize dependent k.
    induction H; intros; observe_equ H; rewrite Eqt.
    - (* Done x *)
      rewrite bind_ret_l.
      now apply H1.
    - (* Finish *)
      rewrite bind_ret_l.
      now apply H1.
    - (* Tau *)
      rewrite bind_tau.
      apply can_step_tau; eauto.
    - (* Vis *)
      rewrite bind_vis.
      apply can_step_vis; auto.
    - (* Br *)
      rewrite bind_br.
      apply can_step_br; auto.
  Qed.
  Hint Resolve can_step_bind_r: ctl.

  Theorem af_bind_r{X Y}: forall (t: ctree E Y) (k: Y -> ctree E X) w φ R,
      <( t, w |= AF AX done R )> ->
      (forall (y: Y) w, R y w -> not_done w ->
                   <( {k y}, w |= AF now φ )>) ->
      <( {x <- t ;; k x}, w |= AF now φ )>.
  Proof.
    intros.
    apply afdone_ind in H.
    revert H0.
    generalize dependent φ.
    generalize dependent k.
    induction H; intros; observe_equ H; rewrite Eqt.
    - (* Done *)
      rewrite bind_ret_l; eauto with ctl.
    - (* Finish *)
      rewrite bind_ret_l; eauto with ctl.
    - (* Tau *)
      rewrite bind_tau.
      apply af_tau; eauto with ctl.
    - (* Vis *)
      rewrite bind_vis.
      apply af_vis; eauto with ctl.
    - (* Br *)
      rewrite bind_br.
      apply af_br; eauto with ctl.
  Qed.

  Lemma af_bind_r_eq{X Y}: forall (t: ctree E Y) (k: Y -> ctree E X) w φ r w',
      <( t, w |= AF AX done= r w' )> ->
      <( {k r}, w' |= AF now φ )> ->
      <( {x <- t ;; k x}, w |= AF now φ )>.
  Proof.
    intros.
    eapply af_bind_r.
    + apply H.
    + intros.
      now destruct H1 as (-> & ->). 
  Qed.
  
End CtlAfBind.

Section CtlAfIter.
  Context {E: Type} {HE: Encode E}.

  (* Total correctness lemma for [iter] *)
  (* [Ri: I -> World E -> Prop] loop invariant (left).
     [Rr: X -> World E -> Prop] loop postcondition (right).
     [Rv: (I * World E) -> (I * World E) -> Prop)] loop variant (left). *)
  Lemma af_iter{X I} Ri Rr (Rv: relation (I * World E)) (i: I) w (k: I -> ctree E (I + X)):
    (forall (i: I) w,
        Ri i w ->
        <( {k i}, w |= AF AX done
                    {fun (x: I + X) w' =>
                       match x with
                       | inl i' => Ri i' w' /\
                                    Rv (i', w') (i, w)
                       | inr r' => Rr r' w'
                       end})>) ->
    well_founded Rv ->
    Ri i w ->
    <( {iter k i}, w |= AF done Rr )>.
  Proof.      
    intros H WfR Hi.
    generalize dependent k.
    revert Hi.
    remember (i, w) as P.
    replace i with (fst P) by now subst.
    replace w with (snd P) by now subst.
    clear HeqP i w.
    Opaque entailsF.
    induction P using (well_founded_induction WfR);
      destruct P as (i, w); cbn in *. 
    rename H into HindWf.
    intros.
    unfold iter, MonadIter_ctree.
    rewrite unfold_iter.
    eapply af_bind_r with (R:=fun (x : I + X) (w' : World E) =>
                                match x with
                                | inl i' => Ri i' w' /\ Rv (i', w') (i, w)
                                | inr r' => Rr r' w'
                                end); auto.
    intros [i' | r] w'.
    - intros (Hi' & Hv) Hd.
      apply af_tau.
      remember (i', w') as y.
      replace i' with (fst y) by now subst.
      replace w' with (snd y) by now subst.      
      apply HindWf; inv Heqy; auto.
    - apply af_ret. 
  Qed.

  (*| Instead of a WF relation [Rv] provide a "ranking" function [f] |*)
  Lemma af_iter_nat{X I} Ri Rr (f: I -> World E -> nat) (i: I) w (k: I -> ctree E (I + X)):
    (forall (i: I) w,
        Ri i w ->
        <( {k i}, w |= AF AX done
                    {fun (x: I + X) w' =>
                       match x with
                       | inl i' => Ri i' w' /\ f i' w' < f i w
                       | inr r' => Rr r' w'
                       end})>) ->
    Ri i w ->
    <( {iter k i}, w |= AF done Rr )>.
  Proof.
    intros.
    eapply af_iter with Ri (ltof _ (fun '(i, w) => f i w));
      auto.
    apply well_founded_ltof.
  Qed.

  Lemma af_iter_nat'{X I} Rr (f: I -> World E -> nat) (i: I) w (k: I -> ctree E (I + X)):
    (forall (i: I) w,
        not_done w ->
        <( {k i}, w |= AF AX done
                    {fun (x: I + X) w' =>
                       match x with
                       | inl i' => not_done w' /\ f i' w' < f i w
                       | inr r' => Rr r' w'
                       end})>) ->
    not_done w ->
    <( {iter k i}, w |= AF done Rr )>.
  Proof.
    intros.
    eapply af_iter_nat with (Ri:=fun _ => not_done) (f:=f); intros; auto.
  Qed.

  (* Well-founded induction on length of lists *)
  Lemma af_iter_list{A X I} Ri Rr (f: I -> World E -> list A) (i: I) w (k: I -> ctree E (I + X)):
    (forall (i: I) w,
        Ri i w ->
        <( {k i}, w |= AF AX done
                    {fun (x: I + X) w' =>
                       match x with
                       | inl i' => Ri i' w' /\ length (f i' w') < length (f i w)
                       | inr r' => Rr r' w'
                       end})>) ->
    Ri i w ->
    <( {iter k i}, w |= AF done Rr )>.
  Proof.
    intros.
    eapply af_iter_nat with Ri (fun i w => length (f i w)); auto.
  Qed.

  Lemma af_iter_list'{A X I} Rr (f: I -> World E -> list A) (i: I) w (k: I -> ctree E (I + X)):
    (forall (i: I) w,
        not_done w ->
        <( {k i}, w |= AF AX done
                    {fun (x: I + X) w' =>
                       match x with
                       | inl i' => not_done w' /\
                                    length (f i' w') < length (f i w)
                       | inr r' => Rr r' w'
                       end})>) ->
    not_done w ->
    <( {iter k i}, w |= AF done Rr )>.
  Proof.
    intros.
    eapply af_iter_list with (Ri:=fun _ => not_done) (f:=f); intros; auto.
  Qed.
  
End CtlAfIter.

(*| Combinators for [interp_state] |*)
Section CtlAfState.
  Context {E F S: Type} {HE: Encode E} {HF: Encode F}
    (h: E ~> stateT S (ctree F)).

  Theorem af_bind_state_vis{X Y}: forall s w (t: ctree E Y) (k: Y -> ctree E X) φ,
      <( {interp_state h t s}, w |= AF vis φ )> ->
      <( {interp_state h (x <- t ;; k x) s}, w |= AF vis φ )>.
  Proof.
    intros.
    rewrite interp_state_bind.
    now apply af_bind_vis.
  Qed.
  
  Theorem af_bind_state_pure{X Y}: forall s w (t: ctree E Y) (k: Y -> ctree E X),
      <( {interp_state h t s}, w |= AF pure )> ->
      <( {interp_state h (x <- t ;; k x) s}, w |= AF pure )>.
  Proof.
    intros.
    rewrite interp_state_bind.
    now apply af_bind_pure.
  Qed.

  Theorem af_bind_state_r{X Y}: forall s (t: ctree E Y) (k: Y -> ctree E X) w φ R,
      <( {interp_state h t s}, w |= AF AX doneS R )> ->
      (forall (y: Y) w s, R y w s ->
                     not_done w ->
                     <( {interp_state h (k y) s}, w |= AF now φ )>) ->
      <( {interp_state h (x <- t ;; k x) s}, w |= AF now φ )>.
  Proof.
    intros.
    rewrite interp_state_bind.
    apply af_bind_r with (R:=fun '(r, s) w => R r w s); auto.
    intros [y s'] w' Hr Hd; auto.
  Qed.
     
  Theorem af_iter_state{X I} s Ri Rr Rv (i: I) (k: I -> ctree E (I + X)) w:
    (forall (i: I) w s,
        Ri i w s ->
        <( {interp_state h (k i) s}, w |= AF AX doneS
                    {fun (x: (I + X)) w' (s': S) =>
                       match x with
                       | inl i' => Ri i' w' s' /\ Rv (i', w', s') (i, w, s)
                       | inr r' => Rr r' w' s'
                       end})>) ->
    well_founded Rv ->
    Ri i w s ->
    <( {interp_state h (iter k i) s}, w |= AF doneS Rr )>.
  Proof.
    intros H WfR Hi.
    generalize dependent k.
    revert Hi.
    remember (i, w, s) as P.
    replace i with (fst (fst P)) by now subst.
    replace w with (snd (fst P)) by now subst.
    replace s with (snd P) by now subst.
    clear HeqP i w s.
    Opaque entailsF.
    induction P using (well_founded_induction WfR);
      destruct P as ((i, w), s); cbn in *. 
    rename H into HindWf.
    intros.
    rewrite interp_state_unfold_iter.
    eapply af_bind_r with (R:=fun '(r, s0) (w0 : World F) =>
                      match r with
                      | inl i' => Ri i' w0 s0 /\ Rv (i', w0, s0) (i, w, s)
                      | inr r' => Rr r' w0 s0
                      end); auto.
    intros ([i' | r] & s') w'; cbn.
    - intros (Hi' & Hv) Hd.
      apply af_tau.
      remember (i', w',s') as y.
      replace i' with (fst (fst y)) by now subst.
      replace w' with (snd (fst y)) by now subst.
      replace s' with (snd y) by now subst.      
      apply HindWf; inv Heqy; auto.
    - intros; apply af_ret; auto.
  Qed.
    
  (*| Instead of a WF relation [Rv] provide a "ranking" function [f] |*)
  Lemma af_iter_state_nat{X I} (s: S) Ri Rr (f: I -> World F -> S -> nat) (i: I) w
    (k: I -> ctree E (I + X)):
    (forall (i: I) w s,
        Ri i w s ->
        <( {interp_state h (k i) s}, w |= AF AX doneS
                    {fun (x: (I + X)) w' (s': S) =>
                       match x with
                       | inl i' => Ri i' w' s' /\ f i' w' s' < f i w s
                       | inr r' => Rr r' w' s'
                       end})>) ->
    Ri i w s ->
    <( {interp_state h (iter k i) s}, w |= AF doneS Rr )>.
  Proof.
    intros.
    eapply af_iter_state with Ri (ltof _ (fun '(i, w, s) => f i w s)); auto.
    apply well_founded_ltof.
  Qed.

  Lemma af_iter_state_nat'{X I} Rr (f: I -> S -> nat) (s: S)
    (i: I) w (k: I -> ctree E (I + X)):
    (forall (i: I) w s,
        not_done w ->
        <( {interp_state h (k i) s}, w |= AF AX doneS
                    {fun (x: (I + X)) w' (s': S) =>
                       match x with
                       | inl i' => not_done w' /\ f i' s' < f i s
                       | inr r' => Rr r' w' s'
                       end})>) ->
    not_done w ->
    <( {interp_state h (iter k i) s}, w |= AF doneS Rr )>.
  Proof.
    intros.
    eapply af_iter_state_nat with (Ri:=fun _ w _ => not_done w) (f:=fun i _ => f i); auto.
  Qed.
End CtlAfState.

(*| Combinators for [interp_state] with [writerE] |*)
Section CtlAfStateList.
  Context {E F A: Type} {HE: Encode E} {HF: Encode F} (h: E ~> stateT (list A) (ctree F)).

  Lemma af_iter_state_list{X I} Ri Rr (l: list A) w (i: I) (k: I -> ctree E (I + X)):
    (forall (i: I) w (l: list A),
        Ri i w l ->
        <( {interp_state h (k i) l}, w |= AF AX doneS
                 {fun (x: (I + X)) w' (l': list A) =>
                    match x with
                    | inl i' => Ri i' w' l' /\ length l' < length l
                    | inr r' => Rr r' w' l'
                    end})>) ->
    Ri i w l ->
    <( {interp_state h (iter k i) l}, w |= AF doneS Rr )>.
  Proof.
    intros.
    apply af_iter_state_nat with (Ri:=Ri) (f:=fun _ _ l => length l); auto.
  Qed.

  Lemma af_iter_state_list'{X I} Rr (l: list A) (i: I) w (k: I -> ctree E (I + X)):
    (forall (i: I) w (l: list A),
        not_done w ->
        <( {interp_state h (k i) l}, w |= AF AX doneS
                 {fun (x: (I + X)) w' (l': list A) =>
                    match x with
                    | inl i' => not_done w' /\ length l' < length l
                    | inr r' => Rr r' w' l'
                    end})>) ->
    not_done w ->
    <( {interp_state h (iter k i) l}, w |= AF doneS Rr )>.
  Proof.
    intros.
    eapply af_iter_state_list with (Ri:=fun _ w _ => not_done w); auto.
  Qed.

End CtlAfStateList.  
