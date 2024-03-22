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
  CTree.SBisim
  CTree.Interp.Core
  CTree.Interp.State
  CTree.Logic.Trans
  CTree.Logic.CanStep
  Logic.Ctl
  Logic.AX
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

  Lemma af_done: forall (t: ctree E X) φ w,
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

  Lemma af_stuck: forall w φ,
      <( {Ctree.stuck: ctree E X}, w |= AF φ )> <->
      <( {Ctree.stuck: ctree E X}, w |= φ )>.
  Proof.
    split; intros.
    - cbn in H; dependent induction H; auto.
      destruct H0, H1.
      apply can_step_stuck in H1.
      contradiction.
    - now next; left.
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

  Lemma not_done_vis_af: forall (t: ctree E X) φ w,
      <( t, w |= AF vis φ )> ->
      not_done w.
  Proof with eauto with ctl.
    intros * Hf.
    next in Hf ; destruct Hf.
    - rewrite ctl_vis in H; inv H...
    - destruct H.
      now apply can_step_not_done with t.
  Qed.

  Lemma not_done_pure_af: forall (t: ctree E X) w,
      <( t, w |= AF pure )> ->
      not_done w.
  Proof with eauto with ctl.
    intros * Hf.
    next in Hf ; destruct Hf.
    - rewrite ctl_pure in H; subst...
    - destruct H.
      now apply can_step_not_done with t.
  Qed.

  Lemma af_guard: forall (t: ctree E X) w φ,
      <( {Guard t}, w |= AF φ )> <->
      <( t, w |= AF φ )>.
  Proof.
    intros.
    now rewrite sb_guard.
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
      + apply af_done with (φ:=φ) (t:= k Fin.F1) in i; auto.
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

  Lemma af_ret_inv: forall (x: X) w R,
      <( {Ret x}, w |= AF (AX done R) )> ->
      R x w.
  Proof.
    intros.
    next in H; destruct H.
    - destruct H.
      destruct H as (tstuck & w' & TR).
      specialize (H0 _ _ TR).
      inv TR; cbn in H0; now dependent destruction H0.
    - next in H; destruct H.
      destruct H as (tstuck & w' & TR).
      specialize (H0 _ _ TR).
      inv TR; observe_equ H1; rewrite <- Eqt, H3 in H0.
      + rewrite af_stuck in H0.
        apply ax_stuck in H0.
        rewrite ctl_done in H0.
        now dependent destruction H0.
      + rewrite af_stuck in H0.
        apply ax_stuck in H0.
        cbn in H0.
        now dependent destruction H0.
  Qed.

End BasicLemmas.

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
  | AFDoneIndGuard: forall t u w,
      observe t = GuardF u ->
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
        apply AFDoneIndGuard with t2; congruence.
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
        apply AFDoneIndGuard with t1; congruence.
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
  Proof with eauto with ctl.
    intros; induction H.
    - next in H.
      destruct H as [(t' & w' & TR) H].
      cbn in TR.
      dependent induction TR.
      + eapply AFDoneIndGuard with (u:=t0); auto.
        eapply IHTR...
        intros t_ w_ TR_.
        apply H; cbn.
        rewrite <- x0... 
      + eapply AFDoneIndBr...
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
       + eapply AFDoneIndGuard with (u:=t0); auto.
        eapply (IHTR) with (t':=t'); auto.
        -- intros t_ w_ TR_.
           apply H2; cbn.
           rewrite <- x0.
           now apply ktrans_guard.
        -- intros t_ w_ TR_.
           apply H3; cbn.
           rewrite <- x0.
           now apply ktrans_guard.
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
      next; left; cbn.
      apply ctl_vis in H; inv H; now constructor.
    - (* StepA *)
      destruct H0, H1; clear H H0.      
      next; right; next; split.
      + (* can_step *)
        destruct H1 as (t' & w' & TR').
        eapply can_step_bind_l with t' w'; auto.
        eapply not_done_vis_af with (t:=t').
        now apply H2.
      + (* AX AF *)
        intros t_ w_ TR_.
        apply ktrans_bind_inv in TR_ as
            [(t' & TR' & Hd & ->) |
              (x & w' & TR' & Hr & TRk)].
        * now apply H3.
        * specialize (H2 _ _ TR').
          inv H2.
          apply ctl_vis in H; inv H. 
          -- inv Hr.
          -- destruct H0.
             now apply can_step_stuck in H0.
  Qed.

  Theorem af_bind_pure{X Y}: forall (t: ctree E Y) (k: Y -> ctree E X) w,
      <( t, w |= AF pure )> ->
      <( {x <- t ;; k x}, w |= AF pure )>.
  Proof.
    intros * Haf.
    revert X k.
    induction Haf; intros; subst.
    - (* MatchA *)
      next; left; cbn.
      now apply ctl_pure in H. 
    - (* StepA *)
      destruct H0, H1; clear H H0.      
      next; right; next; split.
      + (* can_step *)
        destruct H1 as (t' & w' & TR').
        eapply can_step_bind_l with t' w'; auto.
        eapply not_done_pure_af with (t:=t').
        now apply H2.
      + (* AX AF *)
        intros t_ w_ TR_.
        apply ktrans_bind_inv in TR_.
        destruct TR_ as [(t' & TR' & Hd & ->) | (x & w' & TR' & Hr & TRk)].
        * now apply H3.
        * specialize (H2 _ _ TR').
          inv H2.
          apply ctl_pure in H; subst.
          -- inv Hr.
          -- destruct H0.
             now apply can_step_stuck in H0.
  Qed.

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
      rewrite bind_guard.
      apply af_guard; eauto with ctl.
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
    eapply af_bind_r with
      (R:=fun (x : I + X) (w' : World E) =>
            match x with
            | inl i' => Ri i' w' /\ Rv (i', w') (i, w)
            | inr r' => Rr r' w'
            end); auto.
    intros [i' | r] w'.
    - intros (Hi' & Hv) Hd.
      apply af_guard.
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
    eapply af_iter_nat with
      (Ri:=fun _ => not_done) (f:=f); intros; auto.
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
    eapply af_iter_nat with
      Ri (fun i w => length (f i w)); auto.
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
    eapply af_iter_list with
      (Ri:=fun _ => not_done) (f:=f); intros; auto.
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

  Theorem af_bind_state_r{X Y}: forall s (t: ctree E Y) (k: Y -> ctree E X) w φ (R: Y * S -> World F -> Prop),
      <( {interp_state h t s}, w |= AF AX done R )> ->
      (forall (y: Y) (s: S) w, R (y,s) w ->
                    not_done w ->
                    <( {interp_state h (k y) s}, w |= AF now φ )>) ->
      <( {interp_state h (x <- t ;; k x) s}, w |= AF now φ )>.
  Proof.
    intros.
    rewrite interp_state_bind.
    apply af_bind_r with (R:=R); auto.
    intros [y s'] w' Hr Hd; auto.
  Qed.
     
  Theorem af_iter_state{X I} s Ri (Rr: rel (X * S) (World F))  Rv (i: I) (k: I -> ctree E (I + X)) w:
    (forall (i: I) w s,
        Ri i w s ->
        <( {interp_state h (k i) s}, w |= AF AX done
          {fun '(x, s') w' =>
             match x with
             | inl i' => Ri i' w' s'
                        /\ Rv (i', w', s') (i, w, s)
             | inr r' => Rr (r',s') w'
             end})>) ->
    well_founded Rv ->
    Ri i w s ->
    <( {interp_state h (Ctree.iter k i) s}, w |= AF done Rr )>.
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
                      | inr r' => Rr (r',s0) w0
                      end); auto.
    intros ([i' | r] & s') w'; cbn.
    - intros (Hi' & Hv) Hd.
      apply af_guard.
      remember (i', w',s') as y.
      replace i' with (fst (fst y)) by now subst.
      replace w' with (snd (fst y)) by now subst.
      replace s' with (snd y) by now subst.      
      apply HindWf; inv Heqy; auto.
    - intros; apply af_ret; auto.
  Qed.
    
  (*| Instead of a WF relation [Rv] provide a "ranking" function [f] |*)
  Lemma af_iter_state_nat{X I} (s: S) Ri (Rr: rel (X * S) (World F)) (f: I -> World F -> S -> nat) (i: I) w
    (k: I -> ctree E (I + X)):
    (forall (i: I) w s,
        Ri i w s ->
        <( {interp_state h (k i) s}, w |= AF AX done
                    {fun '(x, s') w' =>
                       match x with
                       | inl i' => Ri i' w' s' /\ f i' w' s' < f i w s
                       | inr r' => Rr (r',s') w'
                       end})>) ->
    Ri i w s ->
    <( {interp_state h (Ctree.iter k i) s}, w |= AF done Rr )>.
  Proof.
    intros.
    eapply af_iter_state with Ri (ltof _ (fun '(i, w, s) => f i w s)); auto.
    apply well_founded_ltof.
  Qed.

  Lemma af_iter_state_nat'{X I} (Rr: rel (X * S) (World F)) (f: I -> S -> nat) (s: S)
    (i: I) w (k: I -> ctree E (I + X)):
    (forall (i: I) w s,
        not_done w ->
        <( {interp_state h (k i) s}, w |= AF AX done
                    {fun '(x, s') w' =>
                       match x with
                       | inl i' => not_done w' /\ f i' s' < f i s
                       | inr r' => Rr (r',s') w'
                       end})>) ->
    not_done w ->
    <( {interp_state h (Ctree.iter k i) s}, w |= AF done Rr )>.
  Proof.
    intros.
    eapply af_iter_state_nat with (Ri:=fun _ w _ => not_done w) (f:=fun i _ => f i); auto.
  Qed.
End CtlAfState.

(*| Combinators for [interp_state] with [writerE] |*)
Section CtlAfStateList.
  Context {E F A: Type} {HE: Encode E} {HF: Encode F} (h: E ~> stateT (list A) (ctree F)).

  Lemma af_iter_state_list{X I} Ri (Rr: rel (X * list A) (World F)) (l: list A) w (i: I) (k: I -> ctree E (I + X)):
    (forall (i: I) w (l: list A),
        Ri i w l ->
        <( {interp_state h (k i) l}, w |= AF AX done
                 {fun '(x, l') w' =>
                    match x with
                    | inl i' => Ri i' w' l' /\ length l' < length l
                    | inr r' => Rr (r', l') w'
                    end})>) ->
    Ri i w l ->
    <( {interp_state h (Ctree.iter k i) l}, w |= AF done Rr )>.
  Proof.
    intros.
    apply af_iter_state_nat with (Ri:=Ri) (f:=fun _ _ l => length l); auto.
  Qed.

  Lemma af_iter_state_list'{X I} (Rr: rel (X * list A) (World F)) (l: list A) (i: I) w (k: I -> ctree E (I + X)):
    (forall (i: I) w (l: list A),
        not_done w ->
        <( {interp_state h (k i) l}, w |= AF AX done
             {fun '(x, l') w' =>
                match (x: I + X) with
                | inl _ => not_done w' /\ length l' < length l
                | inr r' => Rr (r',l') w'
                end})>) ->
    not_done w ->
    <( {interp_state h (Ctree.iter k i) l}, w |= AF done Rr )>.
  Proof.
    intros.
    eapply af_iter_state_list with (Ri:=fun _ w _ => not_done w); auto.
  Qed.

End CtlAfStateList.  
