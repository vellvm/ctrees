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

  Lemma af_brD_inv: forall n (k: fin' n -> ctree E X) w φ,
      <( {BrD n k}, w |= AF now φ )> ->
      (forall (i: fin' n), <( {k i}, w |= AF now φ )>).
  Proof.
    intros.
    next in H; destruct H.
    - now next; left.
    - apply af_brD_aux in H.
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
  
  Lemma af_stuck: forall w φ,
      <( {Ctree.stuck: ctree E X}, w |= AF now φ )> <->
      φ w.
  Proof.
    split; intros.
    - cbn in H; dependent induction H; auto.
      destruct H0, H1.
      apply can_step_stuck in H1.
      contradiction.
    - now next; left.
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

Section AfDoneIndLemma.
  Context {E: Type} {HE: Encode E} {X: Type}.
  
  (* t |= AF AX done R *)
  Inductive AFDoneInd(φ: X -> World E -> Prop): ctree E X -> World E -> Prop :=
  | AFDoneDone: forall t (x: X),
      observe t = RetF x ->
      φ x Pure ->
      AFDoneInd φ t Pure
  | AFDoneFinish: forall t (e: E) (v: encode e) (x: X),
      observe t = RetF x ->
      φ x (Obs e v) ->
      AFDoneInd φ t (Obs e v)
  | AFDoneBrD: forall n t (k: fin' n -> ctree E X) w,
      observe t = BrF false n k ->
      not_done w ->
      (exists i, can_step (k i) w) -> 
      (forall (i: fin' n), can_step (k i) w -> AFDoneInd φ (k i) w) ->
      AFDoneInd φ t w
  | AFDoneBrS: forall n t (k: fin' n -> ctree E X) w,
      observe t = BrF true n k ->
      not_done w ->
      (forall (i: fin' n), AFDoneInd φ (k i) w) ->
      AFDoneInd φ t w
  |AFDoneVis: forall (t: ctree E X) w e k,
      observe t = VisF e k ->
      not_done w ->
      (forall (v: encode e), AFDoneInd φ (k v) (Obs e v)) ->
      AFDoneInd φ t w.
  
  Global Instance proper_equ_afdoneind φ:
    Proper (equ eq ==> eq ==> iff) (AFDoneInd φ).
  Proof.
  Admitted.

  Lemma afdoneind_stuck: forall w φ,
      ~ (AFDoneInd φ Ctree.stuck w).
  Proof.
    intros * Hcontra.
    dependent induction Hcontra; eauto.
    cbn in x.
    dependent destruction x.
    inv H1.
    now apply can_step_stuck in H.
  Qed.

  Arguments ctl_au_ind {M}%function_scope {W}%type_scope {HE KMS} [X]%type_scope 
    (p q) (P _ _)%function_scope [t w] _.
  Lemma afdone_ind: forall φ (t: ctree E X) w,
      <( t, w |= AF AX done φ )> ->
      AFDoneInd φ t w.
  Proof.
    intros.
    refine (ctl_au_ind (<( ⊤ )>) (<( AX done φ)>) _ _ _ H); clear t w H; intros.
    - (* now *)
      admit.
    - destruct H0, H1.

      cbn in H2, H3.
      + 
        
        admit.
      + (* Br *)
        destruct b.
        * admit.
        * (* BrD *)
          setoid_rewrite ktrans_brD in H3.
          rewrite pull2_iff in H3.
          apply AFDoneBrD with n k; auto.
          destruct H1 as (? & ? & ?).
          apply ktrans_not_done with t x x0; auto.
          apply can_step_brD in H0.
          exact H0.
          (* Universal quant *)
          intros i Hs.
          destruct Hs as (k_ & w_ & TR_).
          clear -H3 TR_ H2.
          setoid_rewrite ktrans_brD in H2.
          rewrite pull2_iff in H2.
          rewrite ctree_eta.
          specialize (H _ _ TR_).
          dependent destruction TR_; dependent destruction H; auto.
      + (* Br *)
        destruct b.
        * apply AFDoneBrS with n k; auto.
          now apply ktrans_not_done with (Br true n k) t_ w_.
           intros v'.
           specialize (H _ _ TR_).
           dependent destruction TR_; dependent destruction H1; inv H.
        * (* BrD *)
          setoid_rewrite ktrans_brD in H.
          rewrite pull2_iff in H.

          apply AFDoneBrD with n k; auto.
        apply AFDoneBr with b n k; auto.
        * now apply ktrans_not_done with (Br b n k) t_ w_.
        * destruct b.
          -- (* BrS *)
            intros v'.
            specialize (H _ _ TR_).
            dependent destruction TR_; dependent destruction H1; inv H.
          -- (* BrD *)
            setoid_rewrite ktrans_brD in H.
            apply ktrans_brD in TR_ as (i & TR_).
            rewrite pull2_iff in H.
            clear Heqt t.
            (* things are looking reasonable at this point! *)
            generalize dependent k.
            revert i.
            revert t_ w_ w φ.
            induction n; intros.
            ++ dependent destruction i0; try solve [inv i0].
               dependent destruction i; try solve [inv i].
               specialize (H _ _ Fin.F1 TR_).
               dependent destruction H.
               ** apply afdone_step_done with
                    (t:=k Fin.F1) (w:=w) (t':=t_) (x:=x) (φ:=φ) in TR_;
                    intuition.
               ** apply afdone_step_finish with
                    (t:=k Fin.F1) (w:=w) (t':=t_) (x:=x) (φ:=φ) in TR_;
                    intuition.
            ++ admit.
      + (* Vis *)
        apply AFDoneVis with e k; eauto.
        * now apply ktrans_not_done with (Vis e k) t_ w_.
        * intros v'.
          specialize (H _ _ TR_).
          dependent destruction TR_; dependent destruction H1; inv H.
    - (* AX AF *)
      destruct H0, H1.
      clear H H1.
      destruct H0 as (t_ & w_ & TR_).
      cbn in TR_, H2, H3.
      desobs t.
      + (* Ret *)
        pose proof (ktrans_not_done (Ret x) t_ w w_ TR_).
        inv H.
        * (* Ret, Pure *)
          apply AFDoneDone with x; auto.
          specialize (H3 _ _ TR_).
          dependent destruction TR_; dependent destruction H3; inv H0.
        * (* Ret, Obs *)
          apply AFDoneFinish with x; auto.
          specialize (H3 _ _ TR_).
          dependent destruction TR_; dependent destruction H3; inv H0.
      + (* Br *)
        apply AFDoneBr with b n k; auto.
        * now apply ktrans_not_done with (Br b n k) t_ w_.
        * destruct b.
          -- (* BrS *)
            intros v'.
            specialize (H2 _ _ TR_).
            apply H3; econstructor; auto.
            now apply ktrans_not_done with (Br true n k) t_ w_.
          -- (* BrD *)
            setoid_rewrite ktrans_brD in H2.
            setoid_rewrite ktrans_brD in H3.
            apply ktrans_brD in TR_ as (i & TR_).
            rewrite pull2_iff in H2, H3.
            (* things are looking reasonable at this point! *)
            admit.
      + (* Vis *)
        apply AFDoneVis with e k; eauto.
        * now apply ktrans_not_done with (Vis e k) t_ w_.
        * intros v'.
          specialize (H2 _ _ TR_).
          dependent destruction TR_; dependent destruction H2; apply H3; econstructor; auto.
  Admitted.

  Lemma af_ret_inv: forall (x: X) w R,
      <( {Ret x}, w |= AF (AX done R) )> ->
      R x w.
  Proof.
    intros.
    apply afdone_ind in H.
    dependent induction H; auto.
  Qed.

End AfDoneIndLemma.

Section CtlAfBind.
  Context {E: Type} {HE: Encode E}.

  Typeclasses Transparent equ.
  Theorem af_bind_vis{X Y}: forall (t: ctree E Y) (k: Y -> ctree E X) φ w,
      <( t, w |= AF vis φ )> ->
      <( {x <- t ;; k x}, w |= AF vis φ )>.
  Proof.
    intros * Haf.
    revert X k.
    induction Haf; intros; subst.
    - (* MatchA *)
      next; left; cbn; destruct H as (e_ & x_ & ? & ?); subst.
      now (exists e_, x_).
    - (* StepA *)
      destruct H0, H1; clear H H0.
      destruct H1 as (t_ & w_ & TR_).
      next; right; next; split.
      * eapply can_step_bind_l; eauto.
  Admitted.

  Theorem af_bind_pure{X Y}: forall (t: itree E Y) (k: Y -> itree E X) w,
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
  Qed.
  
  Lemma can_step_bind_r{X Y}: forall (t: itree E Y) (k: Y -> itree E X) w R,      
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
