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
    setoid_rewrite ktrans_brD in H1.
    rewrite pull2_iff in H1.
    apply can_step_brD in H as (j & t' & w' & TR).
    generalize dependent w.
    revert i k.
    induction n; intros.
    + dependent destruction i; try solve [inv i];
        dependent destruction j; try solve [inv j].
      next; split.
      * now (exists t', w').
      * intros.
        now apply H1 with Fin.F1.
    + dependent destruction i; try solve [inv i];
        dependent destruction j; try solve [inv j].
      * next; split.
        -- now (exists t', w').
        -- intros.
           now apply H1 with Fin.F1.
      * edestruct IHn with (k:= fun i => k (Fin.FS i)) (i:=@Fin.F1 n); eauto.
  Admitted.

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
        dependent destruction TR; observe_equ x; rewrite <- Eqt in H0;
          now apply ctl_done in H0; dependent destruction H0.
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
  Proof with (auto with ctl).
    intros.
    next in H.
    destruct H as [(t' & w' & TR') Hs].
    next; split.
    + specialize (Hs _ _ TR').
      apply ctl_vis in Hs as (e & v & -> & ?).
      eapply can_step_bind_l with t' (Obs e v)...
    + intros t_ w_ TR_.
      clear t' w' TR' w'.
      apply ktrans_bind_inv in TR_ as
          [(t' & TR' & Hd & Ht_) |
            (x & w' & TR' & Hr & TRk)].
      * now eapply (Hs t').
      * dependent destruction Hr;
        specialize (Hs _ _ TR');
        apply ctl_vis in Hs as (? & ? & ? & ?); inv H.
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
  Print Assumptions ax_bind_r.
End BindLemmas.

Section SyntacticLemmas.
  Context {E: Type} {HE: Encode E} {X: Type} (R: X -> World E -> Prop).

  Inductive AXDoneInd: ctree' E X -> World E -> Prop :=
  | AXDonePure: forall x,
    R x Pure ->
    AXDoneInd (RetF x) Pure
  | AXDoneFinish: forall e (v: encode e) x,
    R x (Obs e v) ->
    AXDoneInd (RetF x) (Obs e v)
  | AXDoneBrD: forall n k w,
    (forall i, AXDoneInd (observe (k i)) w) ->
    AXDoneInd (BrF false n k) w.

  Check Productive.
  Lemma axdone_ind {HP: Productive E}: forall t w,
      <( t, w |= AX done R )> -> AXDoneInd (observe t) w.
  Proof.
    intros.
    rewrite ctree_eta in H.
    desobs t.
    - apply ax_done in H as (? & ?).
      inv H; now constructor.
    - destruct b.
      + apply ax_brS in H as (? & ?).
        specialize (H0 Fin.F1).
        inv H0; inv H.
      + constructor.
        intros i.
        admit.
    - apply ax_vis in H as (? & ?).
      + specialize (H0 (HP e)).
        inv H0.
      + exact (HP e).
  Admitted.
End SyntacticLemmas.
