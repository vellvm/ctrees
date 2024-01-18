From ExtLib Require Import
     Structures.Monads
     Structures.MonadState
     Data.Monads.StateMonad.

From Coq Require Import
  Relations.Relation_Definitions
  Basics
  Classes.SetoidClass
  Classes.RelationPairs.

From CTree Require Import
  Events.Core
  Logic.Kripke
  ITree.Events.Writer
  ITree.Equ
  ITree.Interp
  ITree.Core.

Generalizable All Variables.

Import Itree ITreeNotations.
Local Open Scope itree_scope.
Local Open Scope ctl_scope.


(*| Kripke transition system |*)
Section KripkeTrans.
  Context {E: Type} `{HE: Encode E}.

  (*| Kripke transition system |*)
  Inductive trans_{X}: relation (itree' E X * World E) :=
  | KtransObs (w: World E) (e: E) (v: encode e)
      (k: encode e -> itree E X) (t: itree E X):
    t ≅ k v ->
    not_done w ->
    trans_ (VisF e k, w) (observe t, Obs e v)
  | KtransTau (w w': World E) (t t': itree E X):
    trans_ (observe t, w) (observe t', w') ->
    trans_ (TauF t, w) (observe t', w')
  | KtransDone (x: X) (t: itree E X):
    t ≅ Itree.stuck ->
    trans_ (RetF x, Pure) (observe t, Done x)
  | KtransFinish (x: X) (e: E) (v: encode e) (t: itree E X):
    t ≅ Itree.stuck ->
    trans_ (RetF x, Obs e v) (observe t, Finish e v x).
  Hint Constructors trans_ : core.

  Definition trans {X}: relation (itree E X * World E) :=
    fun '(t, w) '(t', w') => trans_ (observe t, w) (observe t', w').
  Arguments trans /.
  
  Global Instance trans_equ_aux1 {X}(t: itree' E X) (w: World E):
    Proper (going (equ eq) * eq ==> flip impl) (trans_ (t,w)).
  Proof.
    unfold Proper, respectful, iff, fst, snd; cbn; unfold fst, snd;
      cbn; unfold RelCompFun; cbn.
    intros (u & su) (u' & su') (equ & <-) TR.
    inv equ; rename H into equ; cbn in *.
    step in equ.
    revert u equ.
    dependent induction TR; intros; subst; eauto;
      rename u into U;
      remember ({| _observe := U |}) as u;
      replace U with (observe u) in * by now subst.
    - eapply KtransObs; auto.
      transitivity t0; auto.
      now step.
    - eapply KtransTau; auto.
      eapply IHTR; auto.
    - eapply KtransDone.
      transitivity t0; auto.
      now step.
    - eapply KtransFinish.
      transitivity t0; auto.
      now step.
  Qed.

  Global Instance trans_equ_aux2 {X}:
    Proper (going (equ eq) * eq ==> going (equ eq) * eq ==> impl) (trans_ (X:=X)).
  Proof.
    intros (t & s) (t' & s') (eqt & eqs) (u & su)
      (u' & su') (equ & eqsu) TR; cbn in *;
      unfold RelCompFun in *; cbn in *; subst.
    rewrite <- equ; clear u' equ.
    inv eqt; rename H into eqt.
    revert t' eqt.
    dependent induction TR; intros; auto.
    + step in eqt; cbn in eqt; dependent destruction eqt.
      rewrite H.
      apply KtransObs; auto.
    + step in eqt; cbn in eqt; dependent destruction eqt.
      apply KtransTau; auto.
      eapply IHTR; auto.
      now rewrite <- !itree_eta.
    + step in eqt; cbn in eqt; dependent destruction eqt.
      apply KtransDone; auto.
    + step in eqt; cbn in eqt; dependent destruction eqt.
      apply KtransFinish; auto.
  Qed.

  Global Instance trans_equ_proper{X}:
    Proper (equ eq * eq ==> equ eq * eq ==> iff) (trans (X:=X)).
  Proof.
    unfold Proper, respectful, RelCompFun, fst, snd; cbn; intros.
    destruct2 H0; destruct2 H; destruct x, y, x0, y0; subst.
    split; intros TR; unfold trans.
    - now rewrite <- Heqt0, <- Heqt.
    - now rewrite Heqt0, Heqt.
  Qed.

  Definition equ X := @equ E HE X X eq.
  Arguments equ /.
  Global Program Instance itree_kripke: Kripke (itree E) equ E := {
      ktrans X '(t,w) '(t',w') :=
        trans_ (X:=X) (observe t, w) (observe t', w')
    }.
  Next Obligation.
    setoid_rewrite H in H0.
    exists s'; auto.
  Defined.
  Next Obligation.
    remember (observe t, w) as m.
    remember (observe t', w') as m'.
    replace w with (snd m) by now subst.
    clear Heqm Heqm' t t' w w'.
    induction H; cbn; auto with ctl.
  Defined.
  Arguments ktrans /.
  
End KripkeTrans.

Ltac ktrans_ind H :=
  simpl ktrans in H;
  dependent induction H; eauto with ctl.

Section KripkeLemmas.
  Context {E: Type} {HE: Encode E}.

  (* Always step from impore [w] to impure [w']  |*)
  Lemma ktrans_not_pure {X} : forall (t t': itree E X) w w',
      ktrans (t, w) (t', w') ->
      not_pure w ->
      not_pure w'.
  Proof.
    intros.
    ktrans_ind H.
    inv H0.
  Qed.
  
  Lemma ktrans_stuck{X}: forall (t: itree E X) w w',
      ~ ((stuck, w) ↦ (t, w')).
  Proof.
    intros * Hcontra.
    ktrans_ind Hcontra.
  Qed.
  Hint Resolve ktrans_stuck: ctl.

  Lemma ktrans_tau {X}: forall (t t': itree E X) s s',
      (Tau t, s) ↦ (t', s') <-> ktrans (t, s) (t', s').
  Proof.
    intros; split; intro H.
    - ktrans_ind H; cbn; now rewrite x in H.
    - cbn; apply KtransTau; now cbn in H.
  Qed.

  Lemma ktrans_pure {X}: forall (t: itree E X) (w': World E) x,
      ktrans (Ret x, Pure) (t, w') <-> (w' = Done x /\ t ≅ stuck).
  Proof.
    intros; split; intros.
    - ktrans_ind H; split; try reflexivity.
      step; cbn; rewrite <- x; now step in H.
    - cbn; destruct H as (-> & ->); now apply KtransDone.
  Qed.

  Lemma ktrans_finish {X}: forall (t: itree E X) (w': World E) (e: E) (v: encode e) x,
      ktrans (Ret x, Obs e v) (t, w') <-> (w' = Finish e v x /\ t ≅ stuck).
  Proof.
    intros; split; intros.
    - ktrans_ind H; split; try reflexivity.
      step; cbn; rewrite <- x; now step in H.                                              
    - cbn; destruct H as (-> & ->); now apply KtransFinish.
  Qed.
  
  Lemma ktrans_vis {X} {t': itree E X} s s' e (k: encode e -> itree E X):
    (Vis e k, s) ↦ (t', s') <->
      (exists (v: encode e), t' ≅ k v /\ s' = Obs e v /\ not_done s).
  Proof.
    intros; split; intro TR; ktrans_ind TR.
    - exists v; split; auto.
      step; cbn; rewrite <- x; now step in H.
    - cbn; destruct H as (-> & -> & ?); apply KtransObs; auto.
  Qed.

  (* TODO *)
  Lemma ktrans_bind_inv_aux {X Y} (w w': World E)(T U: itree' E Y) :
    trans_ (T, w) (U, w') ->
    forall (t: itree E X) (k: X -> itree E Y) (u: itree E Y),
      go T ≅ t >>= k ->
      go U ≅ u ->
      (exists t', (t, w) ↦ (t', w')
             /\ not_done w'
             /\ u ≅ x <- t' ;; k x) \/
        (exists x w_, (t, w) ↦ (stuck, w_)
                 /\ return_with X x w_
                 /\ (k x, w) ↦ (u, w')).
  Proof.
    intros TR.
    dependent induction TR; intros.
    - rewrite unfold_bind in H1; unfold ktrans, trans; cbn; desobs t0; observe_equ Heqt.
      + right.        
        exists x; inv H0.
        * exists (Done x).
          replace (TauF stuck) with (observe stuck (X:=X)) by reflexivity.
          split; [|split]; auto with ctl.
          -- now apply KtransDone.
          -- rewrite <- H1; cbn; apply KtransObs; auto with ctl.
             rewrite <- itree_eta in H2.
             transitivity t; [symmetry|]; auto.             
        * exists (Finish e0 v0 x).
          replace (TauF stuck) with (observe stuck (X:=X)) by reflexivity.
          split; [|split]; auto with ctl.
          -- now apply KtransFinish.
          -- rewrite <- H1; cbn; apply KtransObs; auto with ctl.
             rewrite <- itree_eta in H2.
             transitivity t; [symmetry|]; auto.             
      + step in H1; inv H1.
      + left.
        pose proof (equ_vis_invT H1) as (_ & <-).
        eapply equ_vis_invE with v in H1.
        exists (k1 v); split; [|split]; auto with ctl.
        * now cbn; apply KtransObs.
        * rewrite <- H1, <- H.
          symmetry.
          now rewrite <- itree_eta in H2.
    - rewrite unfold_bind in H; unfold ktrans, trans; cbn; desobs t0; observe_equ Heqt.
      + right.
        exists x.
        pose proof (ktrans_not_done (X:=Y) t t' w w' TR) as Hw.
        inv Hw.
        * exists (Done x).
          replace (TauF stuck) with (observe stuck (X:=X)) by reflexivity.
          split; [|split]; auto with ctl.
          -- now apply KtransDone.
          -- rewrite <- H, <- H0; cbn; now apply KtransTau.
        * exists (Finish e v x).
          replace (TauF stuck) with (observe stuck (X:=X)) by reflexivity.
          split; [|split]; auto with ctl.
          -- now apply KtransFinish.
          -- rewrite <- H, <- H0; cbn; now apply KtransTau.
      + pose proof (equ_tau_invE H).
        rewrite itree_eta in H1.
        destruct (IHTR _ _ _ _ eq_refl eq_refl t1 k u H1 H0) as [(t2 & TR2 & Hd & Eq2) | (x & w_ & TRr & Hr & TRk)].
        * left.
          exists t2; split; [|split]; auto with ctl.
          now apply KtransTau.
        * right.
          exists x; inv Hr.
          -- exists (Done x); split; auto with ctl.
             replace (TauF stuck) with (observe stuck (X:=X)) by reflexivity.
             now apply KtransTau.
          -- exists (Finish e v x); split; auto with ctl.
             replace (TauF stuck) with (observe stuck (X:=X)) by reflexivity.
             now apply KtransTau.
      + step in H; inv H.
    - rewrite unfold_bind in H0; unfold ktrans, trans; cbn; desobs t0; observe_equ Heqt.
      + right.
        exists x0, (Done x0).
        split; [|split]; auto with ctl.
        * replace (TauF stuck) with (observe stuck (X:=X)) by reflexivity.
          now apply KtransDone.
        * rewrite <- H1, H, <- H0; cbn.
          replace (TauF stuck) with (observe stuck (X:=Y)) by reflexivity.
          now apply KtransDone.
      + step in H0; inv H0.
      + step in H0; inv H0.
    - rewrite unfold_bind in H0; unfold ktrans, trans; cbn; desobs t0; observe_equ Heqt.
      + right.
        exists x0, (Finish e v x0).
        split; [|split]; auto with ctl.
        * replace (TauF stuck) with (observe stuck (X:=X)) by reflexivity.
          now apply KtransFinish.
        * rewrite <- H1, H, <- H0; cbn.
          replace (TauF stuck) with (observe stuck (X:=Y)) by reflexivity.
          now apply KtransFinish.
      + step in H0; inv H0.
      + step in H0; inv H0.
  Qed.

  Lemma ktrans_bind_inv: forall {X Y} (w w': World E)
                           (t: itree E X) (u: itree E Y) (k: X -> itree E Y),
      (x <- t ;; k x, w) ↦ (u, w') ->
      (exists t', (t, w) ↦ (t', w')
             /\ not_done w'
             /\ u ≅ x <- t' ;; k x) \/
        (exists x w_, (t, w) ↦ (stuck, w_)
                 /\ return_with X x w_
                 /\ (k x, w) ↦ (u, w')).
  Proof.
    intros * TR.
    eapply ktrans_bind_inv_aux.
    apply TR.
    rewrite <- itree_eta; reflexivity.
    rewrite <- itree_eta; reflexivity.
  Qed.

  Lemma ktrans_bind_l{X Y}: forall (t t': itree E Y)
                              (k: Y -> itree E X) w w',
      (t, w) ↦ (t', w') ->
      not_done w' ->
      (x <- t ;; k x, w) ↦ (x <- t' ;; k x, w').
  Proof.
    intros; cbn in *.
    ktrans_ind H; rewrite unfold_bind; cbn.
    - desobs t; dependent destruction x0.      
      apply ktrans_vis.
      exists v; split; auto.
      observe_equ x.
      rewrite <- Eqt, H.
      reflexivity.
    - desobs t; dependent destruction x0.
      apply ktrans_tau.
      cbn; apply IHtrans_; auto.
      now rewrite x.
    - inv H0.
    - inv H0.
  Qed.

  Lemma ktrans_bind_r{X Y}:
    forall (t: itree E Y) (u: itree E X) (k: Y -> itree E X)
      (y: Y) w w_ w',
      (t, w) ↦ (stuck, w_) ->
      return_with Y y w_ ->
      (k y, w) ↦ (u, w') ->
      (y <- t ;; k y, w) ↦ (u, w').
  Proof.
    intros; cbn in *.
    replace (TauF stuck) with (observe stuck (X:=Y)) in H
        by reflexivity.
    ktrans_ind H; rewrite unfold_bind; cbn.
    - inv H1.
    - desobs t; dependent destruction x0.
      apply ktrans_tau.
      cbn; eapply IHtrans_; eauto.
      now rewrite x.
    - dependent destruction H0.
      desobs t; dependent destruction x1; auto.
    - dependent destruction H0.
      desobs t; dependent destruction x1; auto.
  Qed.

End KripkeLemmas.
