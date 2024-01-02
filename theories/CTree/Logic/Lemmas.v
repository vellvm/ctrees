From Coq Require Import
  Basics
  Classes.RelationPairs
  Init.Wf.

From Coinduction Require Import
  coinduction lattice.

From ExtLib Require Import
  Structures.Monad
  Data.Monads.StateMonad.

From CTree Require Import
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
  Notation MP X := (ctree E X * option (Bar E) -> Prop).
  
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

  Lemma ctl_star_ef{X}: forall (t: ctree E X * World E) φ t',
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
  Lemma ctl_star_af{X}: forall (t: ctree E X * World E) φ,
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

  Lemma can_step_brD{n X}: forall (k: fin' n -> ctree E X) w,
      can_step (BrD n k, w) <->
        (exists (i: fin' n), can_step (k i, w)).
  Proof.
    split.
    - intros (t & w' & TR).
      apply ktrans_brD in TR as (i & ?).
      exists i, t, w'; auto.
    - intros (i & t & w' & TR).
      exists t, w'. 
      apply ktrans_brD.
      exists i; eauto.
  Qed.
  
  Lemma can_step_bind_iff{X Y}: forall (t: ctree E Y) (k: Y -> ctree E X) w,
      can_step (x <- t ;; k x, w) <->        
        (exists t' w', (t, w) ↦ (t', w') /\ not_done w')
        \/ (exists y, (t, w) ↦ (Ctree.stuck, Done y)
                /\ can_step (k y, w))
        \/ (exists e (v: encode e) (y: Y), (t, w) ↦ (Ctree.stuck, Finish e v y)
                /\ can_step (k y, w)).
  Proof.
    unfold can_step; split.
    - intros (k' & w' & TR).
      apply ktrans_bind_inv in TR
          as [(t' & TR' & Hd & ?) | [(y & TRt & -> & TRk) | (e & v & y & TRt & -> & ?)]].
      + left; exists t', w'; auto.
      + right; left; exists y; split; eauto.
      + right; right; exists e, v, y; split; eauto.
    - intros * [(t' & w' & TR & Hd) | [(y & TR & k' & w' & TR') | (e & b & y & TR & k' & w' & TR')]];
        ktrans_inv TR; try world_inv.
      + exists (x <- t' ;; k x), w; apply ktrans_bind_l; auto with ctl.
      + exists (x <- t' ;; k x), (Obs e x); apply ktrans_bind_l; auto with ctl.
      + inv Hd.
      + inv Hd.
      + inv H0.
      + exists k', w'; ktrans_inv TR'; try world_inv.
        * eapply ktrans_bind_r with x (Done x); auto with ctl.
        * eapply ktrans_bind_r with x (Done x); auto with ctl.
        * eapply ktrans_bind_r with x (Done x); auto with ctl.
          rewrite Heqt0 in TR'; auto with ctl.
      + inv H0.
      + exists k', w'; ktrans_inv TR'; try world_inv.
        * eapply ktrans_bind_r with x (Finish e0 v x); auto with ctl.
        * eapply ktrans_bind_r with x (Finish e0 v x); auto with ctl.
        * eapply ktrans_bind_r with x (Finish e v0 x); auto with ctl.
          rewrite Heqt0 in TR'; auto with ctl.
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

  Lemma can_step_bind_r{X Y}: forall (t t': ctree E Y) (k: Y -> ctree E X) w w' y,
      (t, w) ↦ (Ctree.stuck, w') ->
      is_done_with w' y ->
      can_step (k y, w) ->
      can_step (x <- t ;; k x, w).
  Proof.
    intros.
    apply can_step_bind_iff; right.
    inv H0; ktrans_inv H; try world_inv.
    - inv H2.
    - destruct H1 as (k' & w' & TR); ktrans_inv TR; try world_inv.
      * left; exists x; split.
        apply KtransDone; auto.
        exists k', Pure.
        apply KtransTau; auto with ctl.
      * left; exists x; split.
        apply KtransDone; auto.
        exists k', (Obs e x0).
        apply KtransObs; auto with ctl.
      * left; exists x; rewrite Heqt0 in TR; split.
        apply KtransDone; auto.
        exists k', (Done x0).
        apply KtransDone; auto.
    - destruct H1 as (k' & w' & TR); ktrans_inv TR; try world_inv.
      * inv H1.
      * inv H1.
    - destruct H1 as (k' & w' & TR); ktrans_inv TR; try world_inv.
      * right; exists e0, v0, x; split.
        apply KtransFinish; auto.
        exists k', (Obs e0 v0).
        apply KtransTau; auto with ctl.
      * right; exists e0, v0, x; split. 
        apply KtransFinish; auto.
        exists k', (Obs e x0).
        apply KtransObs; auto with ctl.
      * right; exists e, v, x; rewrite Heqt0 in TR; split.
        apply KtransFinish; auto.
        exists k', (Finish e v x0).
        apply KtransFinish; auto.
  Qed.

  Lemma ctl_stuck_done_af{X}: forall (x: X) φ,
      ~ <( {(Ctree.stuck: ctree E X, Done x)} |= AF obs φ )>.
  Proof.
    intros * Hcontra.
    inv Hcontra.
    - rewrite ctl_obs in H.
      destruct H as (? & ? & ? & ?).
      inv H.
    - destruct H0 as ((? & ? & ?) & ?).
      inv H0; inv H7; inv H8.
  Qed.

  Lemma ctl_stuck_finish_af{X}: forall (x: X) (e: E) (v: encode e) φ,
      ~ <( {(Ctree.stuck: ctree E X, Finish e v x)} |= AF obs φ )>.
  Proof.
    intros * Hcontra.
    inv Hcontra.
    - rewrite ctl_obs in H.
      destruct H as (? & ? & ? & ?).
      inv H.
    - destruct H0 as ((? & ? & ?) & ?).
      inv H0; inv H7; inv H8.
  Qed.
  
  Theorem ctl_bind_af_l{X Y}: forall (t: ctree E Y) (k: Y -> ctree E X) φ w,
      <( {(t, w)} |= AF obs φ )> ->
      <( {(x <- t ;; k x, w)} |= AF obs φ )>.
  Proof.
    intros * Haf.
    remember (t, w) as m.
    Transparent entailsF.
    unfold entailsF in Haf.
    Opaque entailsF.
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
              as [(t' & TR' & Hd & ?) | [(y & TRt' & TRk) | (e & v & x & TRt & -> & TRk)]].
          -- rewrite H.
             specialize (H3 (t', w') TR').
             apply H3.
          -- specialize (H2 (Ctree.stuck, Done y) TRt').
             Transparent entailsF.
             now apply ctl_stuck_done_af in H2.
          -- specialize (H2 (Ctree.stuck, Finish e v x) TRt).
             now apply ctl_stuck_finish_af in H2.
      + next; right; next; split. 
        * apply can_step_bind_l with te (Obs e x); [apply KtransObs|constructor]; auto. 
        * intros [k' w'] TR'.
          apply ktrans_bind_inv in TR'
              as [(t' & TR' & Hd & ?) | [(y & TRt' & -> & TRk) | (e' & v' & x' & TRt & -> & TRk)]].
          -- rewrite H.
             specialize (H3 (t', w') TR').
             apply H3.
          -- specialize (H2 (Ctree.stuck, Done y) TRt').
             Transparent entailsF.
             now apply ctl_stuck_done_af in H2.
          -- specialize (H2 (Ctree.stuck, Finish e' v' x') TRt).
             now apply ctl_stuck_finish_af in H2.
      + assert (TRt: (t, Pure) ↦ (Ctree.stuck, Done x)).
        { apply ktrans_trans; exists (val x); split; auto.
          now rewrite Heqt in TR.
          right; right; left; exists x; auto. }        
        specialize (H2 (Ctree.stuck, Done x) TRt).
        now apply ctl_stuck_done_af in H2.
      + assert (TRt: (t, Obs e v) ↦ (Ctree.stuck, Finish e v x)).
        { apply ktrans_trans; exists (val x); split; auto.
          now rewrite Heqt in TR.
          right; right; right; exists e, v, x; auto. }        
        specialize (H2 (Ctree.stuck, Finish e v x) TRt).
        now apply ctl_stuck_finish_af in H2.
  Qed.

  (*
  Lemma ctl_af_done_trc{X}: forall (t t': ctree E X) w w' (r: X),
    <( {(t, w)} |= AF done {eq r} )> ->
    (t, w) ↦* (t', w') ->
    (t', w') ↦ (Ctree.stuck, Done r).
  Proof.
    intros.
  Admitted. *)

  Theorem ctl_bind_af_r{X Y}:
    forall (w: World E) (t: ctree E Y) (k: Y -> ctree E X) r φ,
      <( {(t, Pure)} |= AF done {eq r} )> ->
      <( {(k r, Pure)} |= AF obs φ )> ->
      <( {(x <- t ;; k x, w)} |= AF obs φ )>.
  Proof.
    intros * Hret Haf.
    Transparent entailsF.
    unfold entailsF in Haf.
    Opaque entailsF.
    remember (k r, Pure) as m.
    revert k Heqm k t w Hret.
    revert Y r.
    induction Haf; intros; destruct m; inv Heqm; subst; cbn in *.
    - (* MatchA *)
      destruct H as (? & ? & Hcontra & ?).
      inv Hcontra.
    - (* StepA *)
      destruct H0, H1; clear H H0.
      destruct H1 as (te & we & TR); cbn in *.
      
      next; right; next; split.      
      + apply can_step_bind_l.
        exists x_, w_; auto.
      + intros [t' w'] TR'.
        clear x_ w_ TR_ Hd.
        apply ktrans_bind_inv in TR' as [(t_ & TR_ & ->)| (y & TRt & TRk) ].
        
        next; right; next; split.



        * destruct (Hs _ TR_) as (x & ? & ?); cbn in H; subst.
          
          apply ktrans_bind_r.
        apply ktrans_bind_inv
      rewrite ctl_now; cbn.
      
      destruct H0.
      
    induction Haf; intros; destruct m; subst; cbn in *.
    - (* MatchA *)
      next; left; cbn.
      destruct H as (e_ & x_ & ? & ?); subst.
      rewrite ctl_now; eauto.
    - (* StepA *)
      destruct H0, H1; clear H H0.
      destruct H1 as (te & we & TR & Hd); cbn in *.
      next; right.
      next; split.
      + apply can_step_bind_l; exists te, we; auto.
      + intros [k' w'] TR'.
        apply ktrans_bind_inv in TR' as [(t' & TR' & ->)| (y & TRt & TRk) ].
        * apply (H3 (t', w') TR').
        * specialize (H2 (Ctree.stuck, Done y) TRt).
          now apply (@ctl_is_done_af _ Ctree.stuck y φ) in H2.
  Qed.
    
    remember ((k r, w)) as T.
    generalize dependent k.
    generalize dependent t.
    revert w r.
    dependent induction Haf; intros; subst; cbn in H.
    - apply ctl_af_ax; left. (* MatchA *)
      next; auto.
    - next; right. (* StepA *)
      destruct H0, H1.
      clear H1.
      next; split.
      + apply can_step_bind_r_strong with r; auto.
      + intros (t' & w') TR.
        eapply ktrans_bind_inv_r_strong with (r:=r) in TR; auto.
        apply H2; eauto.
  Qed.

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
