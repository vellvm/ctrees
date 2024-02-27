From Coq Require Import
  Basics
  Arith.Wf_nat
  Classes.Morphisms.

From Coinduction Require Import
  coinduction lattice.

From CTree Require Import
  Events.Core
  CTree.Core
  CTree.Equ
  CTree.Logic.Trans
  CTree.Logic.CanStep
  Logic.Ctl
  Logic.Kripke
  Logic.Setoid.

Set Implicit Arguments.
Generalizable All Variables.

Import CTreeNotations CtlNotations Ctree.
Local Open Scope ctl_scope.
Local Open Scope ctree_scope.
  
(*| CTL logic lemmas on c/itrees |*)
Section BasicLemmas.
  Context {E: Type} {HE: Encode E} {X: Type}.

  Lemma done_ax: forall (t: ctree E X) φ w,
      is_done w ->
      ~ <( t, w |= AX φ )>.
  Proof.
    intros * Hret Hcontra.
    inv Hcontra.
    apply can_step_not_done in H.
    inv Hret; inv H.
  Qed.

  (* This lemma forces us to have finite branches.
     Alternatively, a classical [φ] would also allow
     us to work without induction on branch arity. *)
  Lemma ax_brD_aux: forall n (k: fin' n -> ctree E X) w φ,
      (forall i, <( {k i}, w |= AX φ )>) -> 
      (forall i, can_step (k i) w /\
              (forall (t': ctree E X) w', [k i, w] ↦ [t', w'] ->
                                           <( t', w' |= φ )>)).
  Proof.
    induction n; intros.
    - specialize (H Fin.F1).
      next in H; destruct H.
      now dependent destruction i; try solve [inv i].
    - split.
      + now destruct (H i).
      + intros.
        pose proof (H i).
        next in H1.
        destruct H1.
        edestruct IHn with (k:=fun (i: fin (S n)) => k (Fin.FS i)) (φ:=φ) (w:=w).
        * intros j.
          apply H.
        * now apply H2.
        Unshelve.
        exact Fin.F1.
  Qed.
  
  Lemma ax_brD: forall n (k: fin' n -> ctree E X) w φ,
      (forall (i: fin' n), <( {k i}, w |= AX φ )>) ->
      <( {BrD n k}, w |= AX φ )>.  
  Proof.
    intros.
    next; split.
    + apply can_step_brD.
      exists Fin.F1.      
      now eapply ax_brD_aux with (i:=Fin.F1) in H as (? & ?).
    + intros.
      apply ktrans_brD in H0 as (j & TR).
      destruct (H j).
      eapply H1, TR.
  Qed.

  Lemma ax_brD_example:
    <( {brD2 (stuck) (Ret tt): ctree void unit}, Pure |= AX done {fun '(tt) _ => True} )>.
  Proof.
    unfold Ctree.brD2.
    next; split.
    - apply can_step_brD.
      exists (Fin.FS Fin.F1).
      apply can_step_ret; constructor.
    - intros t' w' TR.
      apply ktrans_brD in TR as (i & TR).
      dependent destruction i.
      + now apply ktrans_stuck in TR.
      + cbn in TR.
        dependent destruction TR.
        apply ctl_done; now constructor.
  Qed.

  Lemma ax_brD_inv: forall n (k: fin' n -> ctree E X) w φ,
      <( {BrD n k}, w |= AX φ )> ->
      (forall (i: fin' n), can_step (k i) w -> <( {k i}, w |= AX φ )>).
  Proof.
    intros.
    next in H; destruct H.
    next; split.
    + apply can_step_brD in H as (j & Hd).
      apply H0. (* LEF: all branches can step here *)
    + intros.
      setoid_rewrite ktrans_brD in H1.
      rewrite pull2_iff in H1.
      now apply H1 with i.
  Qed.

  Lemma ax_stuck: forall w φ,
      <( {Ctree.stuck: ctree E X}, w |= AX φ )> ->
      <( {Ctree.stuck: ctree E X}, w |= φ )>.
  Proof.
    intros.
    cbn in H; dependent induction H; auto.
    apply can_step_stuck in H.
    contradiction.
  Qed.
  
  Lemma ax_brS: forall n (k: fin' n -> ctree E X) w φ,
      <( {BrS n k}, w |= AX φ )> <->
        not_done w /\ (forall (i: fin' n), <( {k i}, w |= φ )>).
  Proof with auto with ctl.
    split; intros.
    - next in H; destruct H.
      assert(Hd: not_done w) by now apply can_step_br in H.
      split...
      intros i.
      apply H0.
      apply ktrans_brS.
      exists i...
    - destruct H; split.
      + apply can_step_br...
      + intros t' w' TR.
        apply ktrans_brS in TR as (i & -> & -> & TR).
        apply H0.
  Qed.

  Lemma ax_vis: forall (e: E) (k: encode e -> ctree E X) (_: encode e) w φ,
      <( {Vis e k}, w |= AX φ )> <->
        not_done w /\ (forall (v: encode e), <( {k v}, {Obs e v} |= φ )>).
  Proof with auto with ctl.
    split; intros.
    - next in H; destruct H.
      assert(Hd: not_done w) by now apply can_step_vis in H.
      split...
      intros v.
      apply H0.
      apply ktrans_vis.
      exists v...
    - destruct H; split.
      + apply can_step_vis...
      + intros t' w' TR.
        apply ktrans_vis in TR as (i & -> & <- & TR); subst.
        apply H0.
  Qed.

  Lemma ax_done: forall (x: X) φ,
      <( {Ret x}, Pure |= AX done φ )> <-> φ x Pure. 
  Proof with auto with ctl.
    split; intros.
    - next in H; destruct H.
      destruct H as (t' & w' & TR).
      specialize (H0 _ _ TR).
      apply ktrans_done in TR as (-> & ?).
      inv H0; now invert. 
    - split.
      + apply can_step_ret...
      + intros t' w' TR.
        apply ktrans_done in TR as (-> & ->).
        now constructor.
  Qed.

  Lemma ax_finish: forall (x: X) (e: E) (v: encode e) φ,
      <( {Ret x}, {Obs e v} |= AX done φ )> <-> φ x (Obs e v). 
  Proof with auto with ctl.
    split; intros.
    - next in H; destruct H.
      destruct H as (t' & w' & TR).
      specialize (H0 _ _ TR).
      apply ktrans_finish in TR as (-> & ?).
      inv H0; now invert. 
    - split.
      + apply can_step_ret...
      + intros t' w' TR.
        apply ktrans_finish in TR as (-> & ->).
        now constructor.
  Qed.
End BasicLemmas.
