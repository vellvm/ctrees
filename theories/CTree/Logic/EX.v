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
  
(*| CTL EX lemmas on ctrees |*)
Section BasicLemmas.
  Context {E: Type} {HE: Encode E} {X: Type}.

  Lemma done_ex: forall (t: ctree E X) φ w,
      is_done w ->
      ~ <( t, w |= EX φ )>.
  Proof.
    intros * Hret Hcontra.
    destruct Hcontra as (t' & w' & TR & H).
    apply ktrans_not_done in TR.
    inv TR; inv Hret.
  Qed.

  Lemma ex_stuck: forall w φ,
      <( {Ctree.stuck: ctree E X}, w |= EX φ )> ->
      <( {Ctree.stuck: ctree E X}, w |= φ )>.
  Proof.
    intros.
    destruct H as (t' & w' & TR' & H).
    now apply ktrans_stuck in TR'.
  Qed.

  Lemma ex_guard: forall (t: ctree E X) w φ,
      <( {Guard t}, w |= EX φ )> <->
      <( t, w |= EX φ )>.
  Proof.
    intros.
    now rewrite sb_guard.
  Qed.
  
  Lemma ex_br: forall n (k: fin' n -> ctree E X) w φ,
      <( {Br n k}, w |= EX φ )> <->
        not_done w /\ (exists (i: fin' n), <( {k i}, w |= φ )>).
  Proof with auto with ctl.
    split; intros.
    - next in H; destruct H as (t' & w' & TR & H).
      apply ktrans_br in TR as (i & H' & -> & Hd').
      split...
      exists i.
      now rewrite H' in H.
    - destruct H as (Hd & i & H).
      + exists (k i), w; split...
        apply ktrans_br.
        exists i...
  Qed.

  Lemma ex_vis: forall (e: E) (k: encode e -> ctree E X) (_: encode e) w φ,
      <( {Vis e k}, w |= EX φ )> <->
        not_done w /\ (exists (v: encode e), <( {k v}, {Obs e v} |= φ )>).
  Proof with auto with ctl.
    split; intros.
    - next in H; destruct H as (t' & w' & TR & H).
      apply ktrans_vis in TR as (v & -> & ? & ?).
      rewrite <- H0 in H.
      split; [|exists v]...
    - destruct H as (Hd & v & ?).
      exists (k v), (Obs e v); split...
      apply ktrans_vis.
      exists v...
  Qed.

  Lemma ex_done: forall (x: X) φ w,
      <( {Ret x}, w |= EX done φ )> <->
        not_done w /\ φ x w. 
  Proof with eauto with ctl.
    split; intros.
    - next in H; destruct H as (t' & w' & TR & H).
      split.
      + now apply ktrans_not_done with (Ret x) t' w'.
      + now inv TR; cbn in H; dependent destruction H.
    - destruct H as ([] & ?); exists (Ctree.stuck).
      + exists (Done x); split.
        * apply ktrans_done...
        * now constructor.
      + exists (Finish e v x); split.
        * apply ktrans_finish...
        * now constructor.
  Qed.
End BasicLemmas.

Section BindLemmas.
  Context {E: Type} {HE: Encode E}.

  Theorem ex_bind_vis{X Y}: forall (t: ctree E Y) (k: Y -> ctree E X) φ w,
      <( t, w |= EX vis φ )> ->
      <( {x <- t ;; k x}, w |= EX vis φ )>.
  Proof with auto with ctl.
    intros.
    destruct H as (t' & w' & TR' & H).
    exists (x <- t';; k x), w'; split...
    apply ktrans_bind_l...
    inv H; constructor.
  Qed.

  Theorem ex_bind_pure{X Y}: forall (t: ctree E Y) (k: Y -> ctree E X) w,
      <( t, w |= EX pure )> ->
      <( {x <- t ;; k x}, w |= EX pure )>.
  Proof with auto with ctl.
    intros.
    destruct H as (t' & w' & TR' & H).
    exists (x <- t';; k x), w'; split...
    apply ktrans_bind_l...
    inv H; constructor.
  Qed.

  Opaque Ctree.stuck.
  Typeclasses Transparent equ.
  Theorem ex_bind_r{X Y}: forall (t: ctree E Y) (k: Y -> ctree E X) w φ R,
      <( t, w |= EX done R )> ->
      (forall x w, R x w -> <( {k x}, w |= EX φ )>) ->
      <( {x <- t ;; k x}, w |= EX φ )>.
  Proof with eauto with ctl.
    intros.
    next in H; destruct H as (t' & w' & TR & H).
    cbn in H, TR.
    rewrite (ctree_eta t).
    remember (observe t) as T; clear t HeqT.
    remember (observe t') as T'; clear t' HeqT'.
    hinduction TR before Y; intros; subst.
    - setoid_rewrite <- ctree_eta in IHTR.
      rewrite bind_guard.
      apply ex_guard...
    - rewrite bind_br.
      inv H; inv H1.
    - inv H1.
    - dependent destruction H0.
      rewrite bind_ret_l...
    - dependent destruction H0.
      rewrite bind_ret_l...
  Qed.
End BindLemmas.

