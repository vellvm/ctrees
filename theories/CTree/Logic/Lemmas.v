From Coq Require Import
  Basics
  Classes.RelationPairs.

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
  Notation opt E := (option (Bar E)).

  (* I shouldn't have to reprove this, because
     [equ eq] is a subrelation of [sbisim eq]
     and I already proved this for [sbisim] *)
  Global Add Parametric Morphism{X}: (entailsF (X:=X)) with signature
         (equiv_ctl (M:=ctree E) ==> equ eq * eq ==> iff)
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

  (* The [af] version of this should also hold? *)
  Lemma ctl_star_ef{X}: forall (t: ctree E X * opt E) φ t',
      t ↦* t' -> <( t' |= φ )> -> <( t |= EF φ )>.
  Proof.
    intros t φ t' ? Hφ.
    revert Hφ.
    revert φ.
    destruct H as (n & TR).
    induction n; intros.
  Admitted.

  (* This is weak, maybe I can prove I think
      [<( t |= AF φ )> -> forall t', t ↦* t' /\ <( t' |= AF φ )>]
  *)
  Lemma ctl_star_af{X}: forall (t: ctree E X * opt E) φ,
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
      destruct H0 as (m' & w' & ?).
      destruct m as (m & w).
      destruct (H3 _ H0) as (m0 & ? & ?).
      exists m0; split.
  Admitted.

  (*| LEF: I believe this lemma requires excluded middle to prove... |*)
  (*| These predicates are contradictory in pairs of two
      ~ is_stuck t -> forall w, can_step (t, w) \/  exists x, only_ret t x
      ~ can_step (t, w) -> is_stuck t \/ exists x, only_ret t x
      ~ ~ (exists x, only_ret t x) -> is_stuck t \/ can_step (t, w)
   |*)
  Lemma t_trinity{X}(t: ctree E X):
    {is_stuck t} + {forall w, can_step (t,w)} + {exists x, only_ret t x}.
  Proof.    
    desobs t.
    - right.
      unfold only_ret; rewrite Heqt.
      exists x; econstructor.
    - admit.
    - assert(He: {exists (x: encode e), true = true} + { ~ exists (x: encode e), True}).
      admit. (* excluded middle for existential? *)
      destruct He.
      + left; right.
        observe_equ Heqt.
        setoid_rewrite Eqt.
        intros; unfold can_step.
        do 2 eexists.
        apply ktrans_vis.
        eexists; split; eauto.
        Unshelve.
        admit.
  Admitted.

  Lemma only_ret_ktrans_r{X}: forall (t t': ctree E X) (w w': opt E) x,
      only_ret t' x ->
      (t, w) ↦ (t', w') ->         
      (t, w) ↦ (Ret x, w').
  Proof.
    intros.
    unfold only_ret in H.
    remember (observe t') as T'.
    generalize dependent t'.
    revert t w w'.
    induction H; intros; subst.  
    - observe_equ HeqT'.
      rewrite Eqt in H1.
      apply ktrans_semiproper with (t:=t) in H1 as (t_ & TR_ & Hsim).
  Admitted.

  Lemma can_step_bind_inv_r:
    forall {E : Type} {HE : Encode E} {X Y : Type}
      (t : ctree E Y) (k : Y -> ctree E X) 
      (w : opt E) x,
      can_step (x <- t;; k x, w) ->
      only_ret t x ->
      can_step (k x, w).
  Proof.
    intros.
  Admitted.

  Lemma can_step_brD{n X}: forall (k: fin' n -> ctree E X) w,
      can_step (BrD n k, w) <-> (exists (i: fin' n), can_step (k i, w)).
  Proof.
    split.
    - intros (t & w' & TR).      
      apply ktrans_brD in TR as (i & ?).
      exists i; eauto.
    - intros (i & t & w' & TR).
      exists t, w'.
      apply ktrans_brD.
      exists i; eauto.
  Qed.

  Lemma can_step_ret_inv{X}: forall (x: X) (w: option (Bar E)),
      can_step (Ret x, w) -> False.
  Proof.
    intros.
    destruct H as (? & ? & ?).
    apply ktrans_trans in H as (l & ? & [(-> & ?) | (e & x' & -> & ?)]);
      inversion H.
  Qed.
  Hint Resolve can_step_ret_inv: core.
  
  Theorem ctl_bind_af_l{X Y}: forall w (t: ctree E Y) (k: Y -> ctree E X) φ,
      <( {(t, w)} |= AF now φ )> ->
      <( {(x <- t ;; k x, w)} |= AF now φ )>.
  Proof.
    intros * Haf.
    unfold entailsF in Haf.
    remember ((t, w)) as T.
    generalize dependent t.
    revert w k.
    dependent induction Haf; intros; subst.
    - apply ctl_af_ax; left. (* MatchA *)
      next; auto.
    - next; right. (* StepA *)
      destruct H0, H1.
      clear H1.
      next; split.
      + now apply can_step_bind_l.
      + intros (t' & w') TR.
        apply ktrans_bind_inv_l_strong in TR as (t_ & TR_ & Eqt_); eauto.
        rewrite Eqt_.
        apply H3 with (t_, w'); auto.
  Qed.

  Theorem ctl_bind_af_r{X Y}: forall (w: opt E) (t: ctree E Y) (k: Y -> ctree E X) r φ,
      only_ret t r ->
      <( {(k r, w)} |= AF now φ )> ->
      <( {(x <- t ;; k x, w)} |= AF now φ )>.
  Proof.
    intros * Hret Haf.
    unfold entailsF in Haf.
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

  Lemma not_can_step{X}: forall (t: ctree E X) (σ: opt E),
      ~ can_step (t, σ) -> ((exists x, only_ret t x) \/ (sbisim (Y:=X) eq t Ctree.stuck)).
  Proof.
    intros t σ.
  Admitted.

  Lemma ctl_done_af{X}: forall (t: ctree E X) (w: opt E) φ,
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
  Lemma ctl_iter_af_l{I R}: forall (f: I -> ctree E (I + R)) (σ: opt E) (i : I)
                              (ψ: I + R -> Prop) (φ: opt E -> Prop),
      ψ (inl i) /\ φ σ ->
      (forall (i': I + R), (f i, σ_) i' -> ψ i') ->
      ( <( {(f i, σ)} |= AF done φ )>) -> 

      <( {(iter f i, σ)} |= AF now φ )>.
   *)

  
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
      now apply ctl_done_af.
  Qed.

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
