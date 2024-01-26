From Coq Require Import
  Basics
  Init.Wf.

From CTree Require Import
  Events.Core
  CTree.Core
  CTree.Pred
  CTree.Trans
  CTree.Logic.Trans
  CTree.SBisim
  CTree.Equ
  Logic.Ctl
  Logic.Kripke.

Set Implicit Arguments.
Generalizable All Variables.

Import CTreeNotations CtlNotations.
Local Open Scope ctl_scope.
Local Open Scope ctree_scope.


(*| CTL logic lemmas on c/itrees |*)
Section CtlCTrees.
  Context {E: Type} {HE: Encode E}.
  Notation encode := (@encode E HE).
  Notation equiv_ctl X := (equiv_ctl (X:=X) (M:= ctree E)).
  (* I shouldn't have to reprove this, because
     [equ eq] is a subrelation of [sbisim eq]
     and I already proved this for [sbisim] *)
  
  Lemma ctl_stuck_obs_af{X}: forall (x: X) φ w,
      return_with X x w ->
      ~ <( {(Ctree.stuck: ctree E X, w)} |= AF obs φ )>.
  Proof.
    intros * Hret Hcontra.
    inv Hcontra.
    - rewrite ctl_obs in H.
      destruct H as (? & ? & ? & ?); cbn in *; subst.
      inv Hret.
    - destruct H0 as ((? & ? & ?) & ?).
      now apply ktrans_stuck in H0.
  Qed.

  Opaque entailsF.
  Theorem ctl_bind_af_l{X Y}: forall (t: ctree E Y) (k: Y -> ctree E X) φ w,
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
      ktrans_inv TR.
      + next; right; next; split. 
        * eapply can_step_bind_l; eauto; apply KtransTau; eauto.
        * intros [k' w'] TR'.
          apply ktrans_bind_inv in TR'
              as [(t' & TR' & Hd & ?) | (y & w_ & TRt' & Hd & TRk) ].
          -- rewrite H.
             specialize (H3 (t', w') TR').
             apply H3.
          -- specialize (H2 (Ctree.stuck, w_) TRt').
             Transparent entailsF.
             eapply ctl_stuck_obs_af with (x:=y) in H2; intuition. 
      + next; right; next; split. 
        * apply can_step_bind_l with te (Obs e x); [apply KtransObs|constructor]; auto. 
        * intros [k' w'] TR'.
          apply ktrans_bind_inv in TR'
              as [(t' & TR' & Hd & ?) | (y & w_ & TRt' & Hr & TRk)].
          -- rewrite H.
             specialize (H3 (t', w') TR').
             apply H3.
          -- specialize (H2 (Ctree.stuck, w_) TRt').
             Transparent entailsF.
             apply ctl_stuck_obs_af with (x:=y) in H2; intuition.
      + assert (TRt: (t, Pure) ↦ (Ctree.stuck, Done x)).
        { apply ktrans_trans; exists (val x); split; auto.
          now rewrite Heqt in TR.
          right; right; left; exists x; auto. }        
        specialize (H2 (Ctree.stuck, Done x) TRt).
        apply ctl_stuck_obs_af with (x:=x) in H2; intuition.
      + assert (TRt: (t, Obs e v) ↦ (Ctree.stuck, Finish e v x)).
        { apply ktrans_trans; exists (val x); split; auto.
          now rewrite Heqt in TR.
          right; right; right; exists e, v, x; auto. }        
        specialize (H2 (Ctree.stuck, Finish e v x) TRt).
        apply ctl_stuck_obs_af with (x:=x) in H2; intuition.
  Qed.

  Lemma aleaf_trans_back{X}: forall (t t': ctree E X) l r,
      t ⇓ r ->
      trans l t t' ->
      ~ is_val l ->
      t' ⇓ r.
  Proof.
    intros.
    unfold trans in *.
    remember (observe t') as T'.
    remember (observe t) as T.
    clear HeqT HeqT' t t'.
    generalize dependent l.
    induction H; intros.
    - inv H0.
      exfalso; apply H1; constructor.
    - dependent destruction H1.
      + now specialize (H0 _ _ H1 H2).
      + now rewrite <- H1.
    - remember (go T') as t'.
      replace T' with (observe t') in * by now subst.
      clear Heqt' T'.
      destruct (trans_vis_inv H1) as (? & ? & ->).
      now rewrite H3.
  Qed.

  Lemma ktrans_aleaf{X}: forall (t t': ctree E X) w w' (r: X),
      (t, w) ↦ (t', w') ->
      t ⇓ r ->
      return_with X r w' \/ t' ⇓ r.
  Proof.
    intros.
    rewrite (ctree_eta t), (ctree_eta t') in H.    
    apply ktrans_trans in H as (? & ? & ?).
    remember (observe t) as T.
    remember (observe t') as T'.
    clear t t' HeqT HeqT'.
    cbn in *.
    generalize dependent r.
    induction H; intros; dependent destruction H0.
    - 
  Admitted.

  Lemma ctl_return_af_inv{X}: forall (t: ctree E X) w (r: X),
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
      destruct H0 as (t' & w' & TR'); cbn in *.
  Admitted.      
  
  Typeclasses Transparent equ.
  Lemma can_step_bind_r{X Y} {HP: Productive E}:
    forall (t: ctree E Y) (k: Y -> ctree E X) w (r: Y),      
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
        apply can_step_br_iff; destruct b.
        * destruct H1 as (? & ? & ?).
          eapply ktrans_not_done; eauto.
        * exists (Fin.F1).
          eapply H0; try reflexivity; auto.
      + rewrite bind_vis.
        apply can_step_vis_iff.
        * (* Indeed, [x <- Vis (e: void) ;; k x]
             does not step and need [Productive E] here *)
          apply HP.
        * destruct H1 as (? & ? & ?).
          eapply ktrans_not_done; eauto.
  Qed.
  Hint Resolve can_step_bind_r: ctl.

  Lemma can_step_not_done{X}: forall (t: ctree E X) w,
      is_done w ->
      ~ can_step (t, w).
  Proof.
    intros * Hinv; inv Hinv; intros (t' & w' & TR');    
      inv TR'; inv H4.
  Qed.
  Hint Resolve can_step_not_done: ctl.

  Theorem ctl_bind_af_r{X Y} {HP: Productive E}:
    forall (t: ctree E Y) (k: Y -> ctree E X) w (r: Y) φ,
      <( {(t, w)} |= AF return r )> ->
      <( {(k r, w)} |= AF now φ )> ->
      <( {(x <- t ;; k x, w)} |= AF now φ )>.
  Proof.
    intros.
    apply ctl_return_af_inv in H as [H|H].
    - inv H; inv H0.
      + now next; left.
      + destruct H1.
        apply can_step_not_done in H0; [try contradiction | auto with ctl].
      + now next; left.
      + destruct H1.
        apply can_step_not_done in H0; [try contradiction | auto with ctl].
    - rewrite (ctree_eta t).
      remember (observe t) as T.
      clear HeqT t.
      generalize dependent w.
      revert k.
      induction H; intros.
      + now rewrite bind_ret_l.
      + rewrite bind_br.
        destruct b.
        * rewrite ctl_af_brS_iff.
          intro i.
          now apply H0.
        * Check ktrans_semiproper.
          assert (Hsim: BrD n (fun x : fin (S n) => x0 <- k x;; k0 x0) ~ x0 <- k Fin.F1;; k0 x0).
          { admit. }
          rewrite Hsim.
          now apply H0.
          Check sb_brD.
          rewrite ctl_af_brD_iff.
      + rewrite bind_vis.
        rewrite ctl_af_vis_iff.
        right.
        intro x.
        apply H0.
  Admitted.
    
  Theorem ctl_guard_af{X}: forall (w: World E) (t: ctree E X) φ,
      <( {(t, w)} |= AF φ )> <->
      <( {(guard t, w)} |= AF φ )>.
  Proof.
    intros.
    rewrite sb_guard.
    reflexivity.
  Qed.

  Lemma ctl_done_af_now{X}: forall (t: ctree E X) (w: World E) φ,
      <( {(t, w)} |= AF (done {fun _ _ => φ}) )> -> <( {(t, w)} |= AF (now φ) )>.
  Proof.
    intros.
    unfold entailsF in H.
    induction H.
    - destruct H as (x & Heq & w' & Heq' & Hφ).
      apply ctl_af_ax; left.
      destruct m; cbn in *.
      exists w'; intuition.
    - destruct H1, H0.
      clear H1.
      next; right.
      next; split; auto.
  Qed.

  (* Need a lemma that mimics the loop invariant rule of hoare logic with iter.
     Perhaps a good place to start is well-founded proof spaces of Kincaid et al [2016].
     Or ranking functions from termination literature...
   *)
  (*
  Lemma ctl_iter_af_l{I R}: forall (f: I -> ctree E (I + R)) (σ: World E) (i : I)
                              (ψ: I + R -> Prop) (φ: World E -> Prop),
      ψ (inl i) /\ φ σ ->
      (forall (i': I + R), (f i, σ_) i' -> ψ i') ->
      ( <( {(f i, σ)} |= AF done φ )>) -> 

      <( {(iter f i, σ)} |= AF now φ )>.
   *)


  Lemma ctl_iter_body_af{I R}: forall (k: I -> ctree E (I + R)) w (i : I) φ,
      <( {(k i, w)} |= AF done φ )> ->
      <( {(iter k i, w)} |= AF done {fun X x w => φ (inr x) w} )>.
  Proof.    
    intros.
    unfold entailsF in H.
    remember (k i, w) as M.
    generalize dependent k.
    revert i w.
    induction H; intros; subst.
    - unfold is_stuck in H; cbn in H.
      destruct H as (y & Heq & w' & -> & Hφ).
      apply ctl_af_ax; left.
      apply ctl_done.
      exists w', 
    - destruct H1, H0.
      clear H1.
      rewrite sb_unfold_forever.
      apply ctl_bind_af_l.
      next; right.
      next; split; auto.
      intros [t' w'] TR'.
      specialize (H3 _ TR').
      assert(H3': <( {(t', w')} |= AF done {fun _ _ => φ} )>) by apply H3; clear H3.
      now apply ctl_done_af_now.
  Qed.
  
  Lemma ctl_iter_wf {I R} `{r: relation (I * World E) } `{Wfr:well_founded r}:
    forall (k: I -> ctree E (I + R)) (i: I) (w: World E) ψ,
      (forall i' w', r (i',w') (i,w) -> <( {(k i',w')} |= AF done ψ )>) ->
                <( {(iter k i, w)} |= AF done ψ )>.
  Proof.
    intros.
    unfold well_founded in Wfr.
    induction (Wfr (i, w)).
    
  Lemma ctl_forever_af{X}: forall (t: X -> ctree E X) w (x : X) (φ: Bar E -> Prop),
      <( {(t x, w)} |= AF done {fun _ _ => φ} )> ->
      <( {(forever t x, w)} |= AF now φ )>.
  Proof.    
    intros.
    unfold entailsF in H.
    remember (t x, w) as M.
    generalize dependent t.
    revert x w.
    induction H; intros; subst.
    - unfold is_stuck in H; cbn in H.
      destruct H as (y & Heq & Hφ).
      now apply ctl_af_ax; left.
    - destruct H1, H0.
      clear H1.
      rewrite sb_unfold_forever.
      apply ctl_bind_af_l.
      next; right.
      next; split; auto.
      intros [t' w'] TR'.
      specialize (H3 _ TR').
      assert(H3': <( {(t', w')} |= AF done {fun _ _ => φ} )>) by apply H3; clear H3.
      now apply ctl_done_af_now.
  Qed.

  Lemma ctl_forever_ag{X}: forall (t: X -> ctree E X) w (x : X) (φ: Bar E -> Prop),
      <( {(t x, w)} |= AF done {fun _ _ => φ} )> ->
      <( {(forever t x, w)} |= WG AF now φ )>.
  Proof.
    intros.
    coinduction R CIH.
    eapply RStepA.
    - now apply ctl_forever_af.
    - remember (t x, w) as m.
      generalize dependent t.
      generalize dependent x.
      generalize dependent w.
      revert R. 
      unfold entailsF in H.
      induction H; intros; subst; split; trivial;
        intros [t' w'] TR; cbn in H.
      + destruct H as (x' & HeqRet & ? & ? & ?); subst.
  Admitted.

  Lemma can_step_forever_l{X}: forall (k: X -> ctree E X) w x,
    can_step (k x, w) ->
    can_step (forever k x, w).
  Proof.
    unfold can_step in *.
    intros k w x (t & w' & TR).
    setoid_rewrite unfold_forever.
    exists (r <- t;; guard (forever k r)), w'.
    now apply ktrans_bind_l.
  Qed.
  Hint Resolve can_step_forever_l: ctree.

  Lemma can_step_forever_r{X}: forall (k: X -> ctree E X) w x r,
      only_ret (k x) r ->
      can_step (forever k r, w) ->
      can_step (forever k x, w).
  Proof.
    unfold can_step in *.
    intros k w x r H (t & w' & TR).
    unfold only_ret in H.
    dependent induction H.
    - (* Only BrD *)
      setoid_rewrite unfold_forever.
      observe_equ x.
      setoid_rewrite Eqt.
      setoid_rewrite bind_br.
      setoid_rewrite ktrans_brD.
      exists t, w', Fin.F1.
      apply ktrans_bind_r_strong with x0.
      + now apply ktrans_guard.      
      + apply H.
    - (* Only Ret *)
      exists t, w'.
      rewrite unfold_forever.
      observe_equ x.
      rewrite Eqt.
      rewrite bind_ret_l.
      now rewrite ktrans_guard.
  Qed.
  Hint Resolve can_step_forever_r: ctree.

  
  Lemma ctl_iter_ag_af{X}: forall (t: X -> ctree E X) w (i : X) (φ: Bar E -> Prop),
      <( {(t i, w)} |= AF done {fun _ _ => φ} )> ->
      <( {(forever t i, w)} |= AG AF now φ )>.
  Proof.
    coinduction R CIH; intros.
    - apply RStepA.
      + admit. (* now apply ctl_iter_af. *)
  Abort.

  Lemma ctl_forever_agR{X}: forall (k: X -> ctree E X) w x φ,
      (forall y, <( {(k y, w)} |= WG now φ )>) ->
      <( {(forever k x, w)} |= WG now φ )>.
  Proof.
    intros.
    coinduction R CIH.
    eapply RStepA; cbn; specialize (H x).
    - next in H.
      destruct H.
      apply H.
    - split; trivial.
      intros (t' & w') TR.
      rewrite unfold_forever in TR.
      next in H.
      destruct H.
      next in H0. 
      apply ktrans_bind_inv_l_strong in TR; eauto.
      destruct TR as (? & ? & ?).
      assert (Hsim: t' ~ x <- x0;; (forever k x)). 
      * rewrite H2.
        __upto_bind_sbisim; auto.
        intros.
        apply sb_guard_l.
        reflexivity.
      * 
        (* Up-to-bind lemma for [cart] *)
        admit.
  Admitted.

  Lemma can_step_brS{X}:forall n (k: fin' n -> ctree E X) w,
      can_step (BrS n k, w).
  Proof.
    intros.
    do 2 eexists. apply ktrans_brS.
    exists Fin.F1; eauto.
  Qed.


End CtlCTrees.
