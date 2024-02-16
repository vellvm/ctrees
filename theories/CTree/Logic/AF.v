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
  | AFDoneBr: forall b n t (k: fin' n -> ctree E X) w,
      observe t = BrF b n k ->
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
    unfold Proper, respectful.
    intros; subst; split; intros Hind.
    - generalize dependent y.
      induction Hind; intros.
      + apply AFDoneDone with x; auto.
        rewrite <- H.
        unfold equ in H.
        step in H1; cbn in H1; dependent destruction H1;
          congruence.
      + apply AFDoneFinish with x; auto.
        rewrite <- H.
        step in H1; cbn in H1; dependent destruction H1;
          congruence.
      + unfold equ; step in H3; cbn in H3; rewrite H in H3.
        dependent destruction H3.
        apply AFDoneBr with b n k2; auto; intros.
        apply H2 with i, H3.
      + unfold equ; step in H3; cbn in H3; rewrite H in H3.
        dependent destruction H3.
        eapply AFDoneVis with e k2; auto; intros.
        apply H2, H3.
    - generalize dependent x.
      induction Hind; intros.
      + apply AFDoneDone with x; auto.
        rewrite <- H.
        unfold equ in H.
        step in H1; cbn in H1; dependent destruction H1;
          congruence.
      + apply AFDoneFinish with x; auto.
        rewrite <- H.
        step in H1; cbn in H1; dependent destruction H1;
          congruence.
      + unfold equ; step in H3; cbn in H3; rewrite H in H3.
        dependent destruction H3.
        apply AFDoneBr with b n k1; auto; intros.
        apply H2 with i, H3.
      + unfold equ; step in H3; cbn in H3; rewrite H in H3.
        dependent destruction H3.
        eapply AFDoneVis with e k1; auto; intros.
        apply H2, H3.
  Qed.

  Lemma afdoneind_stuck: forall w φ,
      ~ (AFDoneInd φ Ctree.stuck w).
  Proof.
    intros * Hcontra.
    dependent induction Hcontra; eauto.
    cbn in x.
    dependent destruction x.
    apply H2; auto.
    exact (Fin.F1).
  Qed.

  Lemma afdone_step_done (t t': ctree E X) (w w': World E) φ : forall x,
      [t, w] ↦ [t', Done x] ->      
      φ x Pure ->
      w = Pure /\ AFDoneInd φ t w.
  Proof.
    intros x TR; cbn in TR.
    dependent induction TR; intros; split.
    - now destruct (IHTR _ _ x0 eq_refl eq_refl eq_refl H).
    - apply AFDoneBr with false n k; auto.
      + now apply ktrans_not_done with (k i) t'0 (Done x0).
      + admit.
  Admitted.

  Lemma afdone_step_finish (t t': ctree E X) (w w': World E) φ : forall (e: E) (v: encode e) x,
      [t, w] ↦ [t', Finish e v x] ->      
      φ x (Obs e v) ->
      w = Obs e v /\ AFDoneInd φ t w.
  Proof.
  Admitted.

  Lemma afdone_ind: forall φ (t: ctree E X) w,
      <( t, w |= AF AX done φ )> ->
      AFDoneInd φ t w.
  Proof.
    intros; induction H.
    - (* now *)
      next in H.
      destruct H as [(t_ & w_ & TR_) H].
      cbn in TR_, H.
      desobs t.
      + (* Ret *)
        pose proof (ktrans_not_done (Ret x) t_ w w_ TR_).
        inv H0.
        * (* Ret, Pure *)
          apply AFDoneDone with x; auto.
          specialize (H _ _ TR_).
          dependent destruction TR_; dependent destruction H; auto.
        * (* Ret, Obs *)
          apply AFDoneFinish with x; auto.
          specialize (H _ _ TR_).
          dependent destruction TR_; dependent destruction H; auto.
      + (* Br *)
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

Section AfIndLemma.
  Context {E: Type} {HE: Encode E} {X: Type}.

  (* t |= AX AF done R *)
  Inductive AXAFInd(φ: World E -> Prop): ctree E X -> World E -> Prop :=
  | AXAFDoneBase: forall t (x: X),
      observe t = RetF x ->
      φ Ctree.stuck (Done x) ->
      AXAFDoneInd t Pure
  | AXAFFinishBase: forall t (e: E) (v: encode e) (x: X),
      observe t = RetF x ->
      φ Ctree.stuck (Finish e v x) ->
      AXAFDoneInd t (Obs e v)
  | AXAFBrD: forall t u w,
      observe t = BrF b n k ->
      (forall (i: fin' n), AFDoneInd (k i) w) ->
      AFDoneInd t w
  |AFDoneIndVis: forall (t: itree E X) w e k (_: encode e),
      observe t = VisF e k ->
      not_done w ->
      (forall (v: encode e), AFDoneInd (k v) (Obs e v)) ->
      AFDoneInd t w.

  (* t, w |= AX AF now φ *)
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
  | AFNowIndBrS: forall t w n (k: fin' n -> ctree E X),
      observe t = BrF true n k ->
      not_done w ->
      (forall (i: fin' n), AFNowInd φ (k i) w) ->
      AFNowInd φ t w
  | AFNowIndBrD: forall t t' w w' n (k: fin' n -> ctree E X),
      observe t = BrF false n k ->
      not_done w ->
      (exists i, can_step (k i) w) ->
      (forall (i: fin' n), [k i, w] ↦ [t', w'] -> AFNowInd φ t' w') ->
      AFNowInd φ t w
  | AFNowIndVis: forall (t: ctree E X) w e k,
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
  Admitted.

  Lemma afind_stuck: forall w φ,
      AFNowInd φ (Ctree.stuck: ctree E X) w -> φ w.
  Proof.
    intros.
    Transparent Ctree.stuck.
    dependent induction H; auto.
    - cbn in x.
      dependent destruction x.
      destruct H1.
      now apply can_step_stuck in H.
  Qed.

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
      rewrite ctree_eta in H0; rewrite ctree_eta; cbn in H2, H3.
      destruct H0 as (t_ & w_ & TR_); cbn in TR_.
      desobs t; [|destruct b | ].
      + (* RetF *)
        destruct w.
        * (* RetF, Pure *)
          destruct (H2 _ _ TR_); dependent destruction TR_.
          -- apply AFNowIndDone with x0; auto.
          -- destruct H1.
             apply can_step_not_done in H1.
             inv H1.
        * (* RetF, Obs e v *)
          destruct (H2 _ _ TR_); dependent destruction TR_.
          -- apply AFNowIndFinish with x0; auto.
          -- destruct H1.
             apply can_step_not_done in H1.
             inv H1.
        * (* RetF, Done *) dependent destruction TR_.
        * (* RetF, Finish *) dependent destruction TR_.
      + (* BrS n k *)
        apply AFNowIndBrS with n k; auto.
        * apply ktrans_not_done with (BrS n k) t_ w_; auto.
        * intros i.
          apply H3.
          apply KtransBrS with i; auto.
          apply ktrans_not_done with (BrS n k) t_ w_; auto.
      + (* BrD n k *)
        
            exists x.
            exists t', w'.
            admit.
          -- (* BrD *)
            apply ktrans_brD in TR.
            ++ destruct TR.
               exists x.
               exists t', w'; auto.
        * (* AF *)
          intros i Hd.
          destruct b.
          ++ admit.
          ++ (* BrD *)           
            apply ktrans_brD in TR as (j & TR).
            apply H3.
            cbn.
            rewrite Heqt.
            apply ktrans_brD.
            
            
              intros i (t_ & w_ & TR_).
            assert(TR': [t, w] ↦ [t_, w_]).
            { cbn; rewrite Heqt; apply ktrans_brD; exists i; auto. }
            cbn in TR_, TR', H2, H3.
            rewrite Heqt in *.
            clear TR TR_ t' w'.
            specialize (H2 t_ w_ TR').
            specialize (H3 t_ w_ TR').            
            clear t Heqt.
            rewrite ctree_eta.
            rewrite ctree_eta in H2, H3.
            remember (BrF false n k) as T.
            remember (observe t_) as T_.            
            clear HeqT_ t_.
            revert i.
            generalize dependent n.
            generalize dependent φ.
            dependent induction TR'; intros; dependent destruction HeqT.
            apply AFNowIndBr with false n0 k0;  eauto.            
            (* BrD *)            
            ++ cbn. admit.
            ++ now apply ktrans_not_done with (k0 i) t' w'.
            ++ intros j Hs.
               rewrite ctree_eta.
               apply IHTR'; auto.
               admit.
      + (* Vis e k *)
        apply AFNowIndVis with e k; auto.
        * apply ktrans_not_done with (Vis e k) t' w'; auto.
        * intros v. 
          apply ktrans_vis in TR as (? & -> & ? & ?).
          apply H3; cbn.
          rewrite Heqt.
          apply ktrans_vis.
          exists v; auto.
  Admitted.
  
End AfIndLemma.
