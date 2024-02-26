From Coq Require Import
  Basics
  Classes.Morphisms.

From Coinduction Require Import
  coinduction rel tactics.

From CTree Require Import
  Events.Core
  CTree.Core
  CTree.Equ
  CTree.Logic.Trans
  CTree.Logic.CanStep
  Logic.Ctl
  Logic.Kripke.

Generalizable All Variables.

Import Ctree CTreeNotations CtlNotations.
Local Open Scope ctl_scope.
Local Open Scope ctree_scope.

Section BasicLemmas.
  Context {E: Type} {HE: Encode E} {X: Type}.

  Lemma ag_vis: forall e (k: encode e -> ctree E X) (_ : encode e) w φ,
      (vis_with φ w /\
         forall (v: encode e), <( {k v}, {Obs e v} |= AG vis φ )>) <->
        <( {Vis e k}, w |= AG vis φ )>.
  Proof.
    split; intros.
    - destruct H as (Hd & H).
      next; split.
      + inv Hd.
        now apply ctl_now.
      + next; split; inv Hd.
        * apply can_step_vis; auto with ctl.
        * intros.
          apply ktrans_vis in H0 as (i & -> & <- & ?).
          apply H.
    - next in H.
      destruct H.      
      next in H0.
      destruct H0.
      apply can_step_not_done in H0. 
      split; auto.
      intro v.
      apply H1.
      apply ktrans_vis.
      exists v; auto.
  Qed.
  
  Lemma ag_br: forall n (k: fin' n -> ctree E X) w φ,
      (not_done w /\
         forall (i: fin' n), <( {k i}, w |= AG now φ )>) <->
        <( {Br n k}, w |= AG now φ )>.
  Proof.
    split; intros.
    - destruct H as (Hd & H).
      next; split.
      + specialize (H Fin.F1).
        next in H.
        destruct H.
        now cbn in *.
      + next; split.
        * now apply can_step_br.
        * intros.
          apply ktrans_br in H0 as (i & ? & <- & ?).        
          now rewrite H0.
    - next in H.
      destruct H.      
      next in H0.
      destruct H0.
      apply can_step_not_done in H0.
      split; auto.
      intro i.
      apply H1.
      apply ktrans_br.
      exists i; auto.
  Qed.

  Lemma ag_ret: forall (x: X) w φ,      
      <( {Ret x}, w |= AG φ )> -> False.
  Proof.
    intros. 
    next in H.
    destruct H.
    next in H0; destruct H0.
    destruct H0 as (t' & w' & TR).
    cbn in TR, H1.
    specialize (H1 _ _ TR).
    dependent destruction TR; observe_equ x;
      rewrite <- Eqt, H0 in H1; step in H1; inv H1; try contradiction;
      destruct H3; apply can_step_not_done in H1; inv H1.
  Qed.

  Lemma ag_stuck: forall w φ,
      <( {stuck: ctree E X}, w |= AG now φ )> -> False.
  Proof.
    intros.
    next in H; destruct H.
    next in H0; destruct H0.
    now apply can_step_stuck in H0.
  Qed.

  
  Inductive tau_clos_body `{Encode E} {X} (R: relation (ctree E X)): relation (ctree' E X) :=
  | Tau_closL: forall (t: ctree E X) u,
      tau_clos_body R (observe t) u ->
      tau_clos_body R (TauF t) u
  | Tau_closR: forall t (u : ctree E X),
      tau_clos_body R t (observe u) ->
      tau_clos_body R t (TauF u)
  | Tau_closRec: forall t u,
      R t u ->
      tau_clos_body R (TauF t) (TauF u).

  Program Definition tau_clos `{Encode E} {X}: mon (relation (ctree E X)) :=
    {| body R t u:= @tau_clos_body H X R (observe t) (observe u) |}.
  Next Obligation.
    unfold impl; repeat red; intros.
    induction H1.
    - apply Tau_closL; auto.
    - apply Tau_closR; eauto.
    - apply Tau_closRec; eauto.
  Qed.

  
  Lemma tau_clos_car:
    tau_clos_body <= cart.
  Proof.    
    
    
End BasicLemmas.  

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

Section AGIndLemma.
  Context {E: Type} {HE: Encode E} {X: Type}.
  Notation MP := (rel (ctree E X) (World E)). 
  
  (*| [t,w |= AG φ] is semantic and equivalent to [gfp AGCoindF φ t w] |*)
  Inductive AGCoindF (R: MP -> MP) (φ: MP): ctree' E X -> World E -> Prop :=
  | AGCoindTau: forall u w,
      not_done w ->
      R φ u w ->
      φ (Tau u) w ->
      AGCoindF R φ (TauF u) w
  | AGCoindVis: forall w e k (_: encode e),
      not_done w ->
      (forall (v: encode e), R φ (k v) (Obs e v)) ->
      φ (Vis e k) w ->
      AGCoindF R φ (VisF e k) w
  | AGCoindBr: forall n w k,
      not_done w ->
      (forall (i: fin' n), R φ (k i) w) ->
      φ (Br n k) w ->
      AGCoindF R φ (BrF n k) w.
  Hint Constructors AGCoindF: ctl.

  Program Definition agcoind_: mon (MP -> MP) :=
    {| body R φ t w := AGCoindF R φ (observe t) w |}. 
  Next Obligation.
    unfold pointwise_relation, Basics.impl, Proper, respectful.
    cbn; intros; dependent induction H0; rewrite <- x; auto with ctl.
  Qed.

  Definition agcoind: MP -> MP := gfp (agcoind_).
  
End AGIndLemma.

Ltac fold_agcoind_in H:=
  multimatch type of H with
  | context[gfp (@agcoind_ ?E ?HE ?X ?RR)] =>
      fold (@agcoind E HE X RR) in H
  end.

Ltac fold_agcoind :=
  match goal with
  | |- context[gfp (@agcoind_ ?E ?HE ?X ?RR)] =>
      fold (@agcoind E HE X RR)
  end.

Ltac __coinduction_agcoind R H :=
  unfold agcoind; apply_coinduction; intros R H.

Ltac __step_agcoind := unfold agcoind; step; fold_agcoind.

#[global] Tactic Notation "step" := __step_agcoind || step.

#[global] Tactic Notation "coinduction" simple_intropattern(R) simple_intropattern(H) :=
  __coinduction_agcoind R H.

Ltac __step_agcoind_in H := unfold agcoind in H; step in H; fold_agcoind_in H.

#[global] Tactic Notation "step" "in" ident(H) :=
  __step_agcoind_in H || step in H.

Global Instance proper_equ_agcoind `{Encode E} {X} (φ: ctree E X -> World E -> Prop)
  {HP: Proper (equ eq ==> eq ==> iff) φ}:
  Proper (equ eq ==> eq ==> iff) (agcoind φ).
Proof.
  unfold Proper, respectful.
  split; subst; revert y0; generalize dependent y;  generalize dependent x;
  coinduction R CIH; intros. 
  - (* -> *) desobs y; observe_equ Heqt;
               rewrite Eqt in H0; step in H0; cbn in H0; dependent destruction H0;
               step in H1; cbn in H1; do 3 red; cbn.
    + (* Ret *)
      rewrite <- x in H1.
      inv H1.
    + (* Br *)
      rewrite Heqt.
      rewrite <- x in H1.
      dependent destruction H1.
      assert (HeqBr: Br n k1 ≅ Br n k) by (step; cbn; auto).
      rewrite HeqBr in H3.
      eapply AGCoindBr; auto.
      intro i.
      specialize (H0 i).
      eapply CIH with (k1 i); auto.
    + (* Vis *)
      rewrite Heqt.
      rewrite <- x in H1.
      inv H1.
      apply AGCoindTau; auto.
      eapply CIH with t1; eauto.
      assert (HeqTau: Tau t1 ≅ Tau t) by (step; cbn; auto).
      now rewrite <- HeqTau.
    + rewrite Heqt.
      rewrite <- x in H1.
      dependent destruction H1.
      assert (HeqVis: Vis e k1 ≅ Vis e k) by (step; cbn; auto).
      rewrite HeqVis in H3.
      eapply AGCoindVis; auto.
      intro v.
      specialize (H0 v).
      eapply CIH with (k1 v); auto.
  - (* <- *)  desobs x; observe_equ Heqt;
               rewrite Eqt in H0; step in H0; cbn in H0; dependent destruction H0;
               step in H1; cbn in H1; do 3 red; cbn.
    + rewrite <- x in H1.
      inv H1.
    + rewrite Heqt.
      rewrite <- x in H1.
      dependent destruction H1.
      assert (HeqBr: Br n k ≅ Br n k2) by (step; cbn; auto).
      rewrite <- HeqBr in H3.
      eapply AGCoindBr; auto.
      intro i.
      specialize (H0 i).
      eapply CIH with (k2 i); auto.
    + rewrite Heqt.
      rewrite <- x in H1.
      inv H1.
      apply AGCoindTau; auto.
      eapply CIH with t2; eauto.
      assert (HeqTau: Tau t ≅ Tau t2) by (step; cbn; auto).
      now rewrite HeqTau.
    + rewrite Heqt.
      rewrite <- x in H1.
      dependent destruction H1.
      assert (HeqVis: Vis e k ≅ Vis e k2) by (step; cbn; auto).
      rewrite <- HeqVis in H3.
      eapply AGCoindVis; auto.
      intro v.
      specialize (H0 v).
      eapply CIH with (k2 v); auto.
Qed.

Section AGCoindProof.
  Context {E: Type} {HE: Encode E} {X: Type}.
  Notation MP := (rel (ctree E X) (World E)).

  Lemma ag_agcoind: forall (t: ctree E X) w φ
                      {HP: Proper (equ eq ==> eq ==> iff) φ}
                      {Hφ: forall t w, φ (Tau t) w <-> φ t w},
      car φ (fun _ _ => False) t w -> agcoind φ t w.
  Proof.
    coinduction R CIH.
    intros.
    step in H.
    do 3 red; cbn.
    inv H; try contradiction.
    destruct H1 as ((t' & w' & TR) & H).
    cbn in TR, H.
    rewrite ctree_eta in H0.
    remember (observe t) as T.
    remember (observe t') as T'.
    clear HeqT t HeqT' t'.
    induction TR.
    - (* Tau *)
      apply AGCoindTau; auto.
      + now apply ktrans_not_done with t t' w'.
      + apply CIH; auto.
        step; apply RStepA.
        * now apply Hφ.
        * split. 
          -- now (exists t', w').
          -- intros t_ w_ TR_; auto.
    - (* Br *)
      apply AGCoindBr; auto.
      intro j.
      apply CIH; auto.
      now apply H; econstructor.
    - (* Vis *)
      apply AGCoindVis; auto.
    - (* Done *)
      assert (TR: [Ret x, Pure] ↦ [stuck, Done x]) by now constructor.
      specialize (H stuck (Done x) TR).
      step in H; cbn in H.
      dependent destruction H; try contradiction.
      destruct H2 as ((t' & w' & TR') & H').
      now apply ktrans_stuck in TR'.
    - (* Finish *)
      assert (TR: [Ret x, Obs e v] ↦ [stuck, Finish e v x]) by now constructor.
      specialize (H stuck (Finish e v x) TR).
      step in H; cbn in H.
      dependent destruction H; try contradiction.
      destruct H2 as ((t' & w' & TR') & H').
      now apply ktrans_stuck in TR'.
  Qed.
  
  Lemma ag_bind_l{Y}: forall (t: ctree E X) w (k: X -> ctree E Y) φ,
    <( t, w |= AG now φ )> ->
    <( {x <- t ;; k x} , w |= AG now φ )>.
  Proof.
    cbn.
    coinduction R CIH.
    intros.
    apply ag_agcoind in H; auto with typeclass_instances.
    step in H; cbn in H; dependent destruction H.
    - (* Tau *)
      apply RStepA; auto.
      split.
      + eapply can_step_bind_l with (w':=w); auto.
        admit.
      + intros t' w' TR'.
        apply ktrans_bind_inv in TR' as
            [(t_ & TR & Hd & Hequ) | [(v & TR & ? & ?) | (e' & v' & x' & TR & -> & TR')]].
        * rewrite Hequ.
          apply CIH; auto.
          cbn in TR.
          rewrite <- x in TR.
          apply ktrans_tau in TR.
          step in H0; cbn in H0; inv H0.
