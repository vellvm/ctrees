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
  CTree.SBisim
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

  Lemma ax_stuck: forall w φ,
      <( {Ctree.stuck: ctree E X}, w |= AX φ )> ->
      <( {Ctree.stuck: ctree E X}, w |= φ )>.
  Proof.
    intros.
    cbn in H; dependent induction H; auto.
    apply can_step_stuck in H.
    contradiction.
  Qed.

  Lemma ax_guard: forall (t: ctree E X) w φ,
      <( {Guard t}, w |= AX φ )> <->
      <( t, w |= AX φ )>.
  Proof.
    intros.
    now rewrite sb_guard.
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

  Lemma ax_done: forall (x: X) φ w,
      <( {Ret x}, w |= AX done φ )> <-> not_done w /\ φ x w. 
  Proof.
    split; intros.
    - next in H; destruct H.
      destruct H as (t' & w' & TR).
      specialize (H0 _ _ TR).
      split.
      + now apply ktrans_not_done with (Ret x) t' w'.
      + cbn in TR.
        dependent destruction TR; observe_equ x;
          rewrite <- Eqt in H0;
          now apply ctl_done in H0;
          dependent destruction H0.
    - split; destruct H.
      + now apply can_step_ret.
      + intros t' w' TR.
        inv H.
        * apply ktrans_done in TR as (? & ->).
          apply ctl_done; subst.
          now constructor.
        * apply ktrans_finish in TR as (-> & ->).
          apply ctl_done.
          now constructor.
  Qed.

End BasicLemmas.

Section BindLemmas.
  Context {E: Type} {HE: Encode E}.

  Theorem ax_bind_vis{X Y}: forall (t: ctree E Y) (k: Y -> ctree E X) φ w,
      <( t, w |= AX vis φ )> ->
      <( {x <- t ;; k x}, w |= AX vis φ )>.
  Proof with auto with ctl.
    intros.
    next in H.
    destruct H as [(t' & w' & TR') Hs].
    next; split.
    + specialize (Hs _ _ TR').
      apply ctl_vis in Hs; inv Hs.
      eapply can_step_bind_l with t' (Obs e v)...
    + intros t_ w_ TR_.
      clear t' w' TR' w'.
      apply ktrans_bind_inv in TR_ as
          [(t' & TR' & Hd & Ht_) |
            (x & w' & TR' & Hr & TRk)].
      * now eapply (Hs t').
      * dependent destruction Hr;
        specialize (Hs _ _ TR');
        apply ctl_vis in Hs; inv Hs. 
  Qed.

  Theorem ax_bind_pure{X Y}: forall (t: ctree E Y) (k: Y -> ctree E X) w,
      <( t, w |= AX pure )> ->
      <( {x <- t ;; k x}, w |= AX pure )>.
  Proof with auto with ctl.
    intros.
    next in H.
    destruct H as [(t' & w' & TR') Hs].
    next; split.
    + specialize (Hs _ _ TR').
      apply ctl_pure in Hs as ->.
      eapply can_step_bind_l with t' Pure... 
    + intros t_ w_ TR_.
      clear t' w' TR' w'.
      apply ktrans_bind_inv in TR_ as
          [(t' & TR' & Hd & Ht_) |
            (x & w' & TR' & Hr & TRk)].
      * now eapply (Hs t').
      * dependent destruction Hr;
        specialize (Hs _ _ TR');
        apply ctl_pure in Hs; inv Hs. 
  Qed.

  Opaque Ctree.stuck.
  Theorem ax_bind_r{X Y}: forall (t: ctree E Y) (k: Y -> ctree E X) w φ R,
      <( t, w |= AX done R )> ->
      (forall x w, R x w -> <( {k x}, w |= AX φ )>) ->
      <( {x <- t ;; k x}, w |= AX φ )>.
  Proof.
    intros.
    next; split.
    - apply can_step_bind_r with R.
      + now next; left.
      + intros y w' HR.
        specialize (H0 y w' HR).
        now next in H0; destruct H0.
    - intros t' w' TR'. 
      apply ktrans_bind_inv in TR' as
          [(t_ & TR_ & Hd & ->) |
            (x & w_ & TR_ & Hr & TRk)].
      + next in H; destruct H.
        specialize (H1 _ _ TR_).
        apply ctl_done in H1; inv H1; inv Hd.
      + next in H; destruct H.
        specialize (H1 _ _ TR_).
        apply ctl_done in H1.       
        dependent destruction H1; dependent destruction Hr.
        * specialize (H1 _ _ H0).
          next in H1.
          destruct H1 as (Hs & Ht').
          apply Ht'.
          now apply ktrans_to_done_inv in TR_ as (_ & ->). 
        * specialize (H1 _ _ H0).
          next in H1.
          destruct H1 as (Hs & Ht').
          apply Ht'.
          now apply ktrans_to_finish_inv in TR_ as (_ & ->). 
  Qed.
End BindLemmas.

