From Coq Require Import
  Basics
  Classes.Morphisms.

From Coinduction Require Import
  coinduction lattice.

From CTree Require Import
  Events.Core
  CTree.Core
  CTree.SBisim
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
  
  Lemma af_brD_inv: forall n (k: fin' n -> ctree E X) w φ,
      <( {BrD n k}, w |= AF now φ )> ->
      exists (i: fin' n), <( {k i}, w |= AF now φ )>.
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
        * intros t_ w_ TR_.
          assert (TrBrD: [BrD n k, w] ↦ [t_, w_]).
          { apply ktrans_brD; now exists i. }          
          apply (Hφ t_ w_ TrBrD).
  Qed.
  
  Lemma af_brD: forall n (k: fin' n -> ctree E X) w φ,
      (forall (i: fin' n), <( {k i}, w |= AF now φ )>) -> 
      <( {BrD n k}, w |= AF (now φ) )>.
  Proof.
    intros.
    pose proof (H Fin.F1).
    unfold entailsF in H.
    remember (k Fin.F1) as K.
    generalize dependent k.
    induction H0; intros; subst.
    - now next; left.
    - destruct H0, H1; clear H H1.
      destruct H0 as (t' & w' & TR').
      remember (k Fin.F1) as K.
      generalize dependent k.
      revert H3 H4.
      apply ktrans_trans in TR' as (l & TR & ?).
      revert H.
      dependent induction TR; intros; subst.
      + next; right; split.
        * apply can_step_brD.
          exists Fin.F1. auto.
  Admitted.

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
      + apply done_af with (φ:=φ0) (t:= k Fin.F1) in i; auto.
        next; left.
        now apply ctl_now.
  Qed.
  
  Lemma af_vis: forall (e: E) (k: encode e -> ctree E X) (_: encode e) w φ,
      (φ w \/ (not_done w /\ forall (x: encode e), <( {k x}, {Obs e x} |= AF now φ )>)) ->
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
