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

  (* This lemma forces us to have finite branches.
     Alternatively, a classical φ would also allow
     us to work without induction on branch arity. *)
  Lemma af_brD_aux: forall n (k: fin' n -> ctree E X) w φ,
      (forall (i: fin' n), <( {k i}, w |= AF now φ )>) -> 
      φ w \/ (forall i, can_step (k i) w /\
                    (forall (t': ctree E X) w', [k i, w] ↦ [t', w'] ->
                                           <( t', w' |= AF now φ )>)).
  Proof.
    induction n; intros.
    - specialize (H Fin.F1).
      next in H; destruct H.
      + now left.
      + right.
        intro i.
        dependent destruction i; try solve [inv i].
        next in H.
        destruct H; intuition.
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

  Lemma af_br: forall n (k: fin' n -> ctree E X) w φ b,
    (forall (i: fin' n), <( {k i}, w |= AF now φ )>) ->
      <( {Br b n k}, w |= AF now φ )>.
  Proof.
    destruct b; intros.
    - now apply af_brS.
    - now apply af_brD.
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

  (* t, w |= WF now φ *)
  Inductive AFNowInd(φ: World E -> Prop): ctree E X -> World E -> Prop :=
  | AFNowIndBase: forall (t: ctree E X) (w: World E),
      φ w ->
      AFNowInd φ t w
  | AFNowIndDone: forall t (x: X),
      observe t = RetF x ->
      φ (Done x) ->
      AFNowInd φ t Pure
  | AFNowIndFinish: forall t (e: E) (v: encode e) (x: X),
      observe t = RetF x ->
      φ (Finish e v x) ->
      AFNowInd φ t (Obs e v)
  | AFNowIndBr: forall t w b n (k: fin' n -> ctree E X),
      observe t = BrF b n k ->
      not_done w ->
      (forall (i: fin' n), (* can_step (k i) w ->*) AFNowInd φ (k i) w) ->
      AFNowInd φ t w
  | AFNowIndVis: forall (t: ctree E X) w e k (_: encode e),
      observe t = VisF e k ->
      not_done w ->
      (forall (v: encode e), AFNowInd φ (k v) (Obs e v)) ->
      AFNowInd φ t w.

  Global Instance proper_equ_afind φ:
    Proper (equ eq ==> eq ==> iff) (AFNowInd φ).
  Proof.
    unfold Proper, respectful.
    intros; subst; split; intros Hind.
    - generalize dependent y.
      induction Hind; intros.
      + apply AFNowIndBase; auto.
      + apply AFNowIndDone with x; auto.
        unfold equ in H1; step in H1; cbn in H1;
          dependent destruction H1; congruence.
      + apply AFNowIndFinish with x; auto.
        unfold equ in H1; step in H1; cbn in H1;
          dependent destruction H1; congruence.
      + step in H3; cbn in H3; rewrite H in H3.
        dependent destruction H3.
        eapply AFNowIndBr with b n k2; auto.
        intros i.
        apply H2 with i, H3.
      + step in H3; cbn in H3; rewrite H in H3.
        dependent destruction H3.
        eapply AFNowIndVis with e k2; auto.
        intros.
        apply H2, H3.
    - generalize dependent x.
      induction Hind; intros.
      + apply AFNowIndBase; auto.        
      + apply AFNowIndDone with x; auto.
        unfold equ in H1; step in H1; cbn in H1;
          dependent destruction H1; congruence.
      + apply AFNowIndFinish with x; auto.
        unfold equ in H1; step in H1; cbn in H1;
          dependent destruction H1; congruence.
      + step in H3; cbn in H3; rewrite H in H3.
        dependent destruction H3.
        eapply AFNowIndBr with b n k1; auto.
        intros i.
        eapply H2 with i, H3. 
      + step in H3; cbn in H3; rewrite H in H3.
        dependent destruction H3.
        eapply AFNowIndVis with e k1; auto.
        intros.
        apply H2, H3.
  Qed.

  Lemma afind_brD_aux: forall n (k: fin' n -> ctree E X) w φ,
      (forall i, AFNowInd φ (k i) w) ->
      φ w \/ (forall i, can_step (k i) w /\
                    (forall t' w', [k i, w] ↦ [t', w'] ->
                              AFNowInd φ t' w')).
  Proof.
    induction n; intros.
    - specialize (H Fin.F1).
      dependent induction H.
      + (* AFIndNow *) now left.
      + (* AFIndDone *)
        right; intros.
        dependent destruction i; try solve [inv i].
        split; unfold can_step; cbn; rewrite H.
        * exists Ctree.stuck, (Done x).
          now econstructor.
        * intros * TR.
          dependent destruction TR.
          now apply AFNowIndBase.
      + (* AFIndFinish *)
        right; intros.
        dependent destruction i; try solve [inv i].
        split; unfold can_step; cbn; rewrite H.
        * exists Ctree.stuck, (Finish e v x).
          now econstructor.
        * intros * TR.
          dependent destruction TR.
          now apply AFNowIndBase.
      + (* AFIndBr *) destruct b.
        * (* BrS *) right.
          intro i.
          dependent destruction i; try solve [inv i].
          unfold can_step; cbn; setoid_rewrite H.
          split; intros.
          -- exists (k0 Fin.F1), w; try econstructor; auto.
          -- admit. 
        * (* BrD *)
          induction n.
          -- edestruct H2.
  Admitted.

  Lemma pull1_iff: forall {A B} (P : A -> Prop) (R : A -> B -> Prop),
      (forall a, (exists b, R a b)-> P a) <-> (forall a b, R a b -> P a).
    split; intros; eauto.
    destruct H0.
    now apply H with x.
  Qed.

  Lemma pull2_iff: forall {A B C} (P : A -> B -> Prop) (R : A -> B -> C -> Prop),
      (forall a b, (exists c, R a b c)-> P a b) <-> (forall a b c, R a b c -> P a b).
    split; intros; eauto.
    destruct H0.
    now apply H with x.
  Qed.

  Lemma af_afind_aux: forall (t: ctree E X) w φ,
    (can_step t w /\
             (forall t' w',
                 [t, w] ↦ [t', w'] ->
                 AFNowInd φ t' w')) ->
    AFNowInd φ t w.
  Proof.
    intros.
    destruct H as ((t' & w' & TR) & ?).
    pose proof (H _ _ TR).
    generalize dependent t.
    revert w.
    induction H0; intros.
    + admit.
  Admitted.
  
  (* This is a super useful lemma, it allows us to do
     induction on [AFInd] instead of two inductions on
     [cau] and [trans] *)
  Opaque Ctree.stuck.
  Lemma af_afind : forall (t: ctree E X) (w: World E) φ,
       <( t, w |= AF now φ )> -> AFNowInd φ t w.
  Proof.    
    intros; cbn in H.
    induction H.
    - now apply AFNowIndBase.
    - destruct H0, H1; clear H H1.
      destruct H0 as (t' & w' & TR).
      apply af_afind_aux.
      split.
      + now (exists t', w').
      + intros.
        now apply H3.
  Qed.
  
End AfIndLemma.

Section CtlAfBind.
  Context {E: Type} {HE: Encode E}.

  (* LEF: This lemma is not provable with [can_step]
     in AFNowBr *)
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
        dependent destruction H. 
      apply H2; auto.
      exact Fin.F1.
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
      destruct H0 as (? & ? & ? & ?).
      inv H0.
    - (* Finish *)
      destruct H0 as (? & ? & ? & ?).
      inv H0.
    - (* Tau *)
      observe_equ H.
      rewrite Eqt, bind_br.
      apply af_br; eauto.
    - (* Vis *)
      observe_equ H.
      rewrite Eqt, bind_vis.
      apply af_vis; eauto.
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
      rewrite Eqt, bind_br.
      apply af_br; eauto.
    - (* Vis *)
      observe_equ H.
      rewrite Eqt, bind_vis.
      apply af_vis; eauto.
  Qed.
  
  Lemma can_step_bind_r{X Y}: forall (t: ctree E Y) (k: Y -> ctree E X) w R,      
      <( t, w |= AF AX done R )> ->
      (forall y w, R y w -> can_step (k y) w) ->
      can_step (x <- t ;; k x) w.
  Proof.    
    intros.
    apply af_afind in H.
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
  Qed.
  Hint Resolve can_step_bind_r: ctl.

  Theorem af_bind_r{X Y}: forall (t: itree E Y)
                            (k: Y -> itree E X) w φ R,
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
  Qed.

End CtlAfBind.

Section CtlAfIter.
  Context {E: Type} {HE: Encode E}.

  (* Total correctness lemma for [iter] *)
  (* [Ri: I -> World E -> Prop] loop invariant (left).
     [Rr: X -> World E -> Prop] loop postcondition (right).
     [Rv: (I * World E) -> (I * World E) -> Prop)] loop variant (left). *)
  Lemma af_iter{X I} Ri Rr (Rv: relation (I * World E)) (i: I) w (k: I -> itree E (I + X)):
      (forall (i: I) w, Ri i w ->
                   <( {k i}, w |= AF AX done {fun (x: I + X) w' =>
                                             match x with
                                             | inl i' => Ri i' w' /\ Rv (i', w') (i, w)
                                             | inr r' => Rr r' w'
                                             end})>) ->
      well_founded Rv ->
      Ri i w ->
      <( {Itree.iter k i}, w |= AF done Rr )>.
  Proof.      
    intros H WfR Hi.
    generalize dependent k.
    revert Hi.
    remember (i, w) as P.
    replace i with (fst P) by now subst.
    replace w with (snd P) by now subst.
    clear HeqP i w.
    Opaque entailsF.
    induction P using (well_founded_induction WfR); (* wf_ind *)
      destruct P as (i, w); cbn in *. 
    rename H into HindWf.
    intros.
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
    - intros Hr Hd.
      next; right; next; split.
      + now apply can_step_ret.
      + intros t_ w_ TR_.
        inv Hd.
        * apply ktrans_pure in TR_ as (-> & ->).
          next; left.
          rewrite ctl_done.
          now constructor.
        * apply ktrans_finish in TR_ as (-> & ->).
          next; left.
          rewrite ctl_done.
          now constructor.          
  Qed.
End CtlAfIter.
