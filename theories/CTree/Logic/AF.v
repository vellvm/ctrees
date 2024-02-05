From Coq Require Import
  Basics
  Classes.Morphisms.

From Coinduction Require Import
  coinduction lattice.

From CTree Require Import
  Events.Core
  CTree.Core
  CTree.SBisim
  CTree.Equ
  CTree.Trans
  CTree.Logic.Trans
  CTree.Logic.CanStep
  Logic.Ctl
  Logic.Kripke.

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

  (* This lemma is crucial but forces us to have enumerable branches *)
  Lemma af_brD_aux: forall n (k: fin' n -> ctree E X) w φ,
      (forall (i: fin' n), <( {k i}, w |= AF now φ )>) -> 
      φ w \/ (forall i, can_step (k i) w /\
                    (forall (t': ctree E X) w', [k i, w] ↦ [t', w'] ->
                                           <( t', w' |= AF now φ )>)).
  Proof.
    induction n; intros.
    - specialize (H Fin.F1).
      next in H.
      destruct H.
      + now left.
      + right.
        intro i.
        dependent destruction i.
        * next in H.
          destruct H; intuition.
        * dependent destruction i.
    - (* Need to construct [k, i] *)
      pose proof (H Fin.F1).
      edestruct IHn with (k:=fun (i: fin (S n)) =>
                               k (Fin.FS i)) (φ:=φ) (w:=w).
      + intro i.
        apply H.
      + now left.
      + next in H0; destruct H0.
        * now left.
        * right.
          intros.
          dependent destruction i.
          -- now next in H0; destruct H0.
          -- now apply H1.
  Qed.
  
  Lemma af_brD: forall n (k: fin' n -> ctree E X) w φ,
      (forall (i: fin' n), <( {k i}, w |= AF now φ )>) ->
      <( {BrD n k}, w |= AF now φ )>.
  Proof.
    intros.
    apply af_brD_aux in H.
    destruct H.
    + next; now left.
    + next; right.
      next; split. 
      * apply can_step_brD.
        exists (Fin.F1).
        now destruct (H Fin.F1).
      * intros.
        apply ktrans_brD in H0 as (i & TR).
        destruct (H i); eauto.
  Qed.
  
  Lemma af_brS: forall n (k: fin' n -> ctree E X) w φ,
      <( {BrS n k}, w |= AF now φ )> <->
        (forall (i: fin' n), <( {k i}, w |= AF now φ )>).
  Proof.
    split; intros.
    - next in H; destruct H.
      + next; left.
        now rewrite ctl_now in *.
      + destruct H.
        apply H0.
        apply ktrans_brS.
        apply can_step_not_done in H.
        exists i; eauto.
    - destruct (not_done_dec w).
      + next; right.
        next; split; auto.
        * now apply can_step_brS.
        * intros t' w' TR'.
          apply ktrans_brS in TR' as (? & -> & -> & ?).
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
  Context {E: Type} {HE: Encode E} {X: Type}
    (φ: ctree E X -> World E -> Prop).
  
  (*| [t |= AF φ] is semantic and requires double induction, on [AF] and inside it, in
  [ktrans]. Attempt to simplify to one induction with [AFInd] |*)
  Inductive AFInd: ctree E X -> World E -> Prop :=
  | AFIndBase: forall (t: ctree E X) (w: World E),
      φ t w ->
      AFInd t w
  | AFIndDoneBase: forall t (x: X),
      observe t = RetF x ->
      φ Ctree.stuck (Done x) ->
      AFInd t Pure
  | AFIndFinishBase: forall t (e: E) (v: encode e) (x: X),
      observe t = RetF x ->
      φ Ctree.stuck (Finish e v x) ->
      AFInd t (Obs e v)
  | AFIndBr: forall t w b n (k: fin' n -> ctree E X),
      observe t = BrF b n k ->
      (forall (i: fin' n), AFInd (k i) w) ->
      AFInd t w
  |AFIndVis: forall (t: ctree E X) w e k (_: encode e),
      observe t = VisF e k ->
      not_done w ->
      (forall (v: encode e), AFInd (k v) (Obs e v)) ->
      AFInd t w.

  Global Instance proper_equ_afind {HP: Proper (equ eq ==> eq ==> iff) φ}:
    Proper (equ eq ==> eq ==> iff) AFInd.
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
      + step in H2; cbn in H2; rewrite H in H2.
        dependent destruction H2.
        eapply AFIndBr with b n k2; auto.
        intro i.
        eapply H1, H2.
      + step in H3; cbn in H3; rewrite H in H3.
        dependent destruction H3.
        eapply AFIndVis with e k2; auto.
        intros.
        apply H2, H3.
    - generalize dependent x.
      induction Hind; intros.
      + apply AFIndBase; auto.
        now rewrite H0.
      + apply AFIndDoneBase with x; auto.
        unfold equ in H1; step in H1; cbn in H1; dependent destruction H1; congruence.
      + apply AFIndFinishBase with x; auto.
        unfold equ in H1; step in H1; cbn in H1; dependent destruction H1; congruence.
      + step in H2; cbn in H2; rewrite H in H2.
        dependent destruction H2.
        eapply AFIndBr with b n k1; auto.
        intro i.
        eapply H1, H2.
      + step in H3; cbn in H3; rewrite H in H3.
        dependent destruction H3.
        eapply AFIndVis with e k1; auto.
        intros.
        apply H2, H3.
  Qed.      

  Lemma af_ind_stuck_done: forall (x: X),
    AFInd Ctree.stuck (Done x) <->
    φ Ctree.stuck (Done x).
  Proof.
    split; intros.
    - Transparent Ctree.stuck. dependent induction H; auto.
      cbn in x0; dependent destruction x0.
      apply H1; eauto.
      exact Fin.F1.
    - now apply AFIndBase.
  Qed.

  Lemma af_ind_stuck_finish: forall (e: E) (v: encode e) (x: X),
    AFInd Ctree.stuck (Finish e v x) <->
    φ Ctree.stuck (Finish e v x).
  Proof.
    split; intros.
    - dependent induction H; auto.
      cbn in x0; dependent destruction x0.
      apply H1; eauto.
      exact Fin.F1.
    - now apply AFIndBase.
  Qed.

  (* This is a super useful lemma, it allows us to do
     induction on [AFInd] instead of two inductions on
     [cau] and [trans] *)
  Opaque Ctree.stuck.
  Lemma af_afind : forall (t: ctree E X) (w: World E),
       cau true (fun _ _ => True) φ t w -> AFInd t w.
  Proof.
    intros; induction H.
    - now apply AFIndBase.
    - destruct H0, H1; clear H H1.
      destruct H0 as (t' & w' & TR).
      cbn in TR.
      
      (* induction on ktrans_ for ctrees *)      
      dependent induction TR.
      + (* BrD *)
        eapply AFIndBr; eauto.
        intro i'.        
        eapply H3; cbn.
        rewrite <- x0.
        apply KtransBrD with i'.

        
        eapply IHTR. with t'; auto.
      + eapply AFIndVis with (e:=e); auto.
        observe_equ x.
        
        intros v'.
        apply H3; cbn.
        rewrite <- x0.
        apply KtransObs; auto.
      + eapply AFIndTau with (u:=t0); auto.
        eapply (IHTR) with (t':=t'); auto.
        -- intros t_ w_ TR_.
           apply H2; cbn.
           rewrite <- x0.
           now apply ktrans_tau.
        -- intros t_ w_ TR_.
           apply H3; cbn.
           rewrite <- x0.
           now apply ktrans_tau.
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
  Lemma afind_af {Hpr: @Productive E HE}
    {HP: Proper (equ X ==> eq ==> iff) φ}
    {TauInv: forall (t: ctree E X) w, φ t w  -> φ (Tau t) w}
    : forall (t: ctree E X) (w: World E),
      AFInd t w -> cau true (fun _ _ => True) φ t w.
  Proof.
    intros; induction H.
    - now apply MatchA.
    - apply StepA; auto; split.
      + exists Ctree.stuck, (Done x).
        Opaque Ctree.stuck.
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
      + exists Ctree.stuck, (Finish e v x).
        Opaque Ctree.stuck.
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
  Qed.
End AfIndLemma.
