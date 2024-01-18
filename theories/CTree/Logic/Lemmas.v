From Coq Require Import
  Basics
  Eqdep
  Classes.RelationPairs
  Init.Wf.

From Coinduction Require Import
  coinduction lattice.

From ExtLib Require Import
  Structures.Monad
  Data.Monads.StateMonad.

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

Section BindCtxUnary.
  Context {E: Type} {HE: Encode E} {X Y: Type}.
  Notation MP X := (ctree E X * World E -> Prop).
  
  Definition bind_ctx_unary
    (R: ctree E X -> Prop) (S: (X -> ctree E Y) -> Prop):
    ctree E Y -> Prop :=
    fun t => sup R
      (fun x => sup S
               (fun k => t = bind x k)).
  
  Lemma leq_bind_ctx_unary:
    forall R S S', bind_ctx_unary R S <= S' <->
                (forall x, R x -> forall k, S k -> S' (bind x k)).
  Proof.
    intros.
    unfold bind_ctx_unary.
    split; intros; repeat red in H; repeat red.
    - apply H.
      exists x; auto.
      exists k; auto.
    - intro t.
      intros [x Hs].
      destruct H0; subst.
      apply H; auto.
  Qed.

  Lemma in_bind_ctx_unary (R S : _ -> Prop) x y:
    R x -> S y -> bind_ctx_unary R S (bind x y).
  Proof. intros. apply ->leq_bind_ctx_unary; eauto. Qed.
  #[global] Opaque bind_ctx_unary.

  (* 
  Program Definition bind_clos_ar: mon (MP X -> MP X -> MP X) :=
    {| body R '(t, w) :=
        bind_ctx_unary (fun t => R (t, w)) 
          (fun k => _) (bind t |}.
   *)
End BindCtxUnary.


(*| CTL logic lemmas on c/itrees |*)
Section CtlCTrees.
  Context {E: Type} {HE: Encode E}.
  Notation encode := (@encode E HE).
  Notation equiv_ctl X := (equiv_ctl (X:=X) (M:= ctree E)).
  (* I shouldn't have to reprove this, because
     [equ eq] is a subrelation of [sbisim eq]
     and I already proved this for [sbisim] *)
  Global Add Parametric Morphism{X}: (entailsF (X:=X))
         with signature (equiv_ctl X ==> equ eq * eq ==> iff)
           as proper_ctree_entailsF.
  Proof.
    intros x y Hy t u EQt.
    destruct t as (t & w).
    destruct u as (u & s).
    unfold RelProd, fst, snd in EQt.
    destruct EQt as (EQ & ->).
    red in EQ.
    unfold equiv_ctl in Hy.
    apply proper_entailsF; eauto.
    split; cbn.
    - rewrite EQ. (* equ ≤ sbisim *)
      reflexivity.
    - reflexivity.
  Qed.
  
  Global Add Parametric Morphism{X}: (can_step (M:=ctree E) (X:=X))
         with signature (equ eq * eq ==> iff)
           as proper_ctree_can_step.
  Proof.
    intros [t w] [t' w'] Hy.
    destruct2 Hy; subst.
    unfold can_step.
    setoid_rewrite Heqt.
    reflexivity.
  Qed.

  Lemma ktrans_star_ef{X}: forall (t: ctree E X * World E) φ t',
      t ↦* t' -> <( t' |= φ )> -> <( t |= EF φ )>.
  Proof.
    intros t φ t' ? Hφ.
    revert Hφ.
    revert φ.    
    destruct H as (n & TR).
    revert TR.
    generalize dependent t.
    generalize dependent t'.
    induction n; intros.
    - apply ctl_ef_ex; left.
      cbn in TR; destruct t, t'.
      destruct2 TR; subst.
      now rewrite Heqt.
    - destruct TR as (t'' & TR & TRi).
      next; right.
      exists t''; split; auto.
      eapply IHn; eauto.
  Qed.

  (* This is weak, maybe I can prove I think
      [<( t |= AF φ )> -> forall t', t ↦* t' /\ <( t' |= AF φ )>]
  *)
  Lemma ktrans_star_af{X}: forall (t: ctree E X * World E) φ,
      <( t |= AF φ )> -> exists t', t ↦* t' /\ <( t' |= φ )>.
  Proof.
    intros t φ Hφ.
    induction Hφ; intros.
    - (* refl *)
      exists m; split.
      * exists 0; auto.
      * auto.
    - (* step *)
      destruct H0, H1; clear H1.
      destruct H0 as (m' & w' & ?), m as (m, w).
      destruct (H3 _ H0) as ([m_ w_] & TR_ & Hφ_).      
      exists (m_, w_); split; auto.
      apply ktrans_ktrans_trc with (m', w'); auto.
  Qed.

  (*| Br |*)  
  Lemma can_step_br_iff{n X}: forall (k: fin' n -> ctree E X) w b,
      can_step (Br b n k, w) <->
        (if b then not_done w else exists (i: fin' n), can_step (k i, w)).
  Proof.
    destruct b.
    - split; intros.
      + destruct H as (t' & w' & TR).
        eapply ktrans_not_done; eauto.
      + exists (k Fin.F1), w.
        apply ktrans_brS; exists Fin.F1; auto.
    - split.
      + intros (t & w' & TR).
        apply ktrans_brD in TR as (i & ?).
        exists i, t, w'; auto.
      + intros (i & t & w' & TR).
        exists t, w'. 
        apply ktrans_brD.
        exists i; eauto.
  Qed.
  
  Lemma can_step_brD_iff{n X}: forall (k: fin' n -> ctree E X) w,
      can_step (BrD n k, w) <->
        (exists (i: fin' n), can_step (k i, w)).
  Proof.
    intros; now rewrite can_step_br_iff.
  Qed.

  Lemma can_step_brS_iff{n X}: forall (k: fin' n -> ctree E X) w,
      can_step (BrS n k, w) <-> (not_done w).
  Proof.
    intros; now rewrite can_step_br_iff.
  Qed.

  Lemma ctl_done_ktrans{X}: forall (t: ctree E X) w,
      is_done w ->
      ~ (exists m', ktrans (t, w) m').
  Proof.
    intros * Hret Htr.
    destruct Htr as ([? ?] & ?).
    inv Hret;
      apply ktrans_not_done in H; inv H.
  Qed.
  
  Lemma ctl_done_now_af{X}: forall (t: ctree E X) φ w,
      is_done w ->
      <( {(t, w)} |= AF now φ )> ->
      φ w.
  Proof.
    intros * Hret Hcontra.
    inv Hcontra.
    - now rewrite ctl_now in H.
    - destruct H0 as ((? & ? & ?) & ?).
      exfalso.
      eapply ctl_done_ktrans with (t:=t); eauto.
  Qed.

  Lemma ctl_af_brD_inv{X}: forall n (k: fin' n -> ctree E X) w φ,
      <( {(BrD n k, w)} |= AF now φ )> ->
      exists (i: fin' n), <( {(k i, w)} |= AF now φ )>.
  Proof.
    intros.
    next in H; destruct H.
    - exists Fin.F1; next; now left.
    - destruct H as [Hd Hφ].
      + destruct Hd as (t' & w' & TR').
        apply ktrans_brD in TR' as (i & TR').
        exists i.
        next; right; split.
        * exists t', w'; auto.
        * intros [t_ w_] TR_.
          assert (TrBrD: (BrD n k, w) ↦ (t_, w_)).
          { apply ktrans_brD; now exists i. }          
          apply (Hφ (t_, w_) TrBrD).
  Qed.

  Lemma ctl_af_brD_goal{X}: forall n (k: fin' n -> ctree E X) w φ i,
      <( {(k i, w)} |= AF now φ )> ->
      <( {(BrD n k, w)} |= AF now φ )>.
  Proof.
    intros.
    setoid_rewrite ctl_af_ax in H.
    destruct H.
    - now next; left.      
    - destruct H as [Hd Hφ].
      + next; right; split.
        * apply can_step_brD_iff.
          eexists.
          apply Hd.
        * intros [t' w'] TR'.
          apply ktrans_semiproper with (t:= k i) in TR' as (t_ & TR_ & Hsm).
          -- rewrite Hsm.
             now apply Hφ.
          -- unfold Trans.sbisim.
             (** Arggg this is not true unless [BrD n k] is [guard] or deterministic *)
             admit.
  Admitted.             
  
  Lemma ctl_af_brS_iff{X}: forall n (k: fin' n -> ctree E X) w φ,
      <( {(BrS n k, w)} |= AF now φ )> <->
        (forall (i: fin' n), <( {(k i, w)} |= AF now φ )>).
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
        next; split.
        * now apply can_step_brS_iff.
        * intros [t' w'] TR'.
          apply ktrans_brS in TR' as (? & -> & -> & ?).
          apply H.
      + apply ctl_done_now_af with (φ:=φ) (t:= k Fin.F1) in i.
        * next; left.
          now apply ctl_now.
        * apply H.
  Qed.
  
  Lemma can_step_vis_iff{X}: forall (e:E) (k: encode e -> ctree E X) (_: encode e) w,
      can_step (Vis e k, w) <-> not_done w.
  Proof.
    split; intros.
    - destruct H as (t' & w' & TR).
      eapply ktrans_not_done; eauto.
    - exists (k X0), (Obs e X0).
      apply ktrans_vis; exists X0; auto.
  Qed.
  
  Lemma ctl_af_vis_iff{X}: forall (e: E) (k: encode e -> ctree E X) (_: encode e) w φ,
      <( {(Vis e k, w)} |= AF now φ )> <->
        (φ w \/ (not_done w /\ forall (x: encode e), <( {(k x, Obs e x)} |= AF now φ )>)).
  Proof.
    split; intros.
    - next in H; destruct H.
      + now left.
      + destruct H.
        right; split; intros.
        * now apply can_step_not_done in H.
        * apply H0.
          apply ktrans_vis.
          apply can_step_not_done in H.
          exists x; eauto. 
    - destruct H as [H | [Hd H]].
      + now next; left.
      + next; right; next; split.
        * now apply can_step_vis_iff.
        * intros [t' w'] TR'.
          apply ktrans_vis in TR' as (? & -> & <- & ?).
          apply H.
  Qed.
  
  Lemma can_step_bind_iff{X Y}: forall (t: ctree E Y) (k: Y -> ctree E X) w,
      can_step (x <- t ;; k x, w) <->        
        (exists t' w', (t, w) ↦ (t', w') /\ not_done w')
        \/ (exists y w', (t, w) ↦ (Ctree.stuck, w')
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
    - intros * [(t' & w' & TR & Hd) | (y & w' & TR & Hd & k_ & w_ & TR_)];
        ktrans_inv TR.
      + exists (x <- t' ;; k x), w; apply ktrans_bind_l; auto with ctl.
      + exists (x <- t' ;; k x), (Obs e x); apply ktrans_bind_l; auto with ctl.
      + inv Hd.
      + inv Hd.
      + inv Hd; inv H0.
      + inv Hd. 
      + dependent destruction Hd.
        exists k_, w_; ktrans_inv TR_; try world_inv; eapply ktrans_bind_r; eauto with ctl.
        rewrite Heqt0 in TR_; auto with ctl.
      + dependent destruction Hd.
        exists k_, w_; ktrans_inv TR_; try world_inv;
          try solve [eapply ktrans_bind_r; try world_inv; eauto with ctl].
        rewrite Heqt0.
        rewrite Heqt0 in TR_.
        eapply ktrans_bind_r with (w_:=Finish e0 v0 x) (y:=x); eauto with ctl.
  Qed.
  Hint Resolve can_step_bind_iff: ctl.

  Lemma can_step_bind_l{X Y}: forall (t t': ctree E Y) (k: Y -> ctree E X) w w',
      (t, w) ↦ (t', w') ->
      not_done w' ->
      can_step (x <- t ;; k x, w).
  Proof.
    intros.
    eapply can_step_bind_iff; firstorder.
  Qed.
  Hint Resolve can_step_bind_l: ctl.

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

  Lemma ctl_brS_ag{X}: forall n (k: fin' n -> ctree E X) w φ,
      (forall (i: fin' n), <( {(k i, Some w)} |= AG now φ )>) <->
        <( {(BrS n k, Some w)} |= AG now φ )>.
  Proof.
    split; intros.
    - next; split.
      + specialize (H Fin.F1).
        next in H.
        destruct H.
        now cbn in *.
      + next; split.
        apply can_step_brS.
        intros.
        destruct m'.
        apply ktrans_brS in H0 as (i & ? & <-).        
        now rewrite H0.
    - next in H.
      destruct H.      
      next in H0.
      destruct H0.
      apply H1.
      apply ktrans_brS.
      exists i; auto.
  Qed.
  
End CtlCTrees.
