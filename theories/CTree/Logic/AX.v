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

Import CTreeNotations CtlNotations.
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

  Lemma ax_tau: forall (t: ctree E X) w φ,
      <( {Tau t}, w |= AX now φ )> <->
      <( t, w |= AX now φ )>.
  Proof with auto with ctl.
    split; intros; destruct H as [(t' & w' & TR) H].   
    - split.
      * rewrite ktrans_tau in TR...
      * intros t_ w_ TR_.
        apply ktrans_tau in TR_...
    - split.
      * apply can_step_tau...
      * intros t_ w_ TR_.
        rewrite ktrans_tau in TR_...
  Qed.
  
  Lemma ax_br: forall n (k: fin' n -> ctree E X) w φ,
      <( {Br n k}, w |= AX φ )> <->
        not_done w /\ (forall (i: fin' n), <( {k i}, w |= φ )>).
  Proof with auto with ctl.
    split; intros.
    - next in H; destruct H.
      assert(Hd: not_done w) by now apply can_step_br in H.
      split...
      intros i.
      apply H0.
      apply ktrans_br.
      exists i...
    - destruct H; split.
      + apply can_step_br...
      + intros t' w' TR.
        apply ktrans_br in TR as (i & -> & -> & TR).
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
