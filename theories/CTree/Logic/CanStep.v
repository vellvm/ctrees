From Coq Require Import
  Basics
  Init.Wf.

From CTree Require Import
  Events.Core
  CTree.Core
  CTree.Pred
  CTree.Trans
  CTree.Logic.Trans
  CTree.Equ
  CTree.SBisim
  CTree.Equ
  Logic.Ctl
  Logic.Kripke.

Generalizable All Variables.

Import CTreeNotations CtlNotations.
Local Open Scope ctl_scope.
Local Open Scope ctree_scope.

(*| CTL logic lemmas on c/itrees |*)
Section CanStepCtrees.
  Context {E: Type} {HE: Encode E}.
  Notation encode := (@encode E HE).
  Notation equiv_ctl X := (equiv_ctl (X:=X) (M:= ctree E)).

  Global Add Parametric Morphism{X}: (can_step (M:=ctree E) (X:=X))
         with signature (equ eq ==> eq ==> iff)
           as proper_ctree_can_step.
  Proof.
    intros t w Ht w'. 
    unfold can_step.
    setoid_rewrite Ht.
    reflexivity.
  Qed.

  (*| Br |*)  
  Lemma can_step_br{n X}: forall (k: fin' n -> ctree E X) w b,
      can_step (Br b n k) w <->
        (if b then not_done w else exists (i: fin' n), can_step (k i) w).
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

  Lemma can_step_brD{n X}: forall (k: fin' n -> ctree E X) w,
      can_step (BrD n k) w <->
        (exists (i: fin' n), can_step (k i) w).
  Proof.
    intros; now rewrite can_step_br.
  Qed.

  Lemma can_step_brS{n X}: forall (k: fin' n -> ctree E X) w,
      can_step (BrS n k) w <-> (not_done w).
  Proof.
    intros; now rewrite can_step_br.
  Qed.

  Lemma can_step_stuck{X}: forall w,
      can_step (Ctree.stuck: ctree E X) w -> False.
  Proof.
    intros w (t' & w' & TR).
    cbn in TR.
    dependent induction TR; eauto.
  Qed.

  Lemma can_step_vis{X}: forall (e:E) (k: encode e -> ctree E X) (_: encode e) w,
      can_step (Vis e k) w <-> not_done w.
  Proof.
    split; intros.
    - destruct H as (t' & w' & TR).
      eapply ktrans_not_done; eauto.
    - exists (k X0), (Obs e X0).
      apply ktrans_vis; exists X0; auto.
  Qed.

  Lemma can_step_bind{X Y}: forall (t: ctree E Y) (k: Y -> ctree E X) w,
      can_step (x <- t ;; k x) w <->        
        (exists t' w', [t, w] ↦ [t', w'] /\ not_done w')
        \/ (exists y w', [t, w] ↦ [Ctree.stuck, w']
                   /\ return_val Y y w'
                   /\ can_step (k y) w).
  Proof with eauto with ctl.
    unfold can_step; split.
    - intros (k' & w' & TR).
      apply ktrans_bind_inv in TR
          as [(t' & TR' & Hd & ?) | (y & w_ & ? & Hd & ?)].
      + left; exists t', w'...
      + right; inv Hd.
        * exists y, (Done y)...
        * exists y, (Finish e v y)...
    - intros * [(t' & w' & TR & Hd) | (y & w' & TR & Hd & k_ & w_ & TR_)];
        ktrans_inv TR.
      + exists (x <- t' ;; k x), w; apply ktrans_bind_l...
        apply ktrans_trans; exists (tau)... 
      + exists (x <- t' ;; k x), (Obs e x); apply ktrans_bind_l...
        apply ktrans_trans; exists (obs e x); split; [|right; left]...
      + inv Hd.
      + inv Hd.
      + inv Hd; inv H0.
      + inv Hd. 
      + exists k_, w_; eapply ktrans_bind_r with (w_:=Done x) (y:=x)...
        apply ktrans_trans; exists (val x); split; [|right; right; left]...
        now dependent destruction Hd.        
      + exists k_, w_; eapply ktrans_bind_r with (w_:=Finish e v x) (y:=x)...
        apply ktrans_trans; exists (val x); split; [| right; right; right]...
        exists e, v ,x...
        now dependent destruction Hd.
  Qed.
  Hint Resolve can_step_bind: ctl.

  Lemma can_step_bind_l{X Y}: forall (t t': ctree E Y) (k: Y -> ctree E X) w w',
      [t, w] ↦ [t', w'] ->
      not_done w' ->
      can_step (x <- t ;; k x) w.
  Proof.
    intros.
    eapply can_step_bind.
    left.
    exists t', w'; auto.
  Qed.
  Hint Resolve can_step_bind_l: ctl.
End CanStepCtrees.
