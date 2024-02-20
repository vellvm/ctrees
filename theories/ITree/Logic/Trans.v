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
  Logic.Setoid
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
  Inductive ktrans_{X}: itree' E X -> World E -> itree' E X -> World E -> Prop :=
  | KtransObs (w: World E) (e: E) (v: encode e)
      (k: encode e -> itree E X) (t: itree E X):
    t ≅ k v ->
    not_done w ->
    ktrans_ (VisF e k) w (observe t) (Obs e v)
  | KtransTau (w w': World E) (t t': itree E X):
    ktrans_ (observe t) w (observe t') w' ->
    ktrans_ (TauF t) w (observe t') w'
  | KtransDone (x: X) (t: itree E X):
    t ≅ Itree.stuck ->
    ktrans_ (RetF x) Pure (observe t) (Done x)
  | KtransFinish (x: X) (e: E) (v: encode e) (t: itree E X):
    t ≅ Itree.stuck ->
    ktrans_ (RetF x) (Obs e v) (observe t) (Finish e v x).
  Hint Constructors ktrans_ : core.
  
  Global Instance ktrans_equ_aux1 {X}(t: itree' E X) (w: World E):
    Proper (going (equ eq) ==> eq ==> flip impl) (ktrans_ t w).
  Proof.
    unfold Proper, respectful, iff, fst, snd; cbn; unfold fst, snd;
      cbn; unfold RelCompFun; cbn.
    intros u u' Hequ s s' <-  TR.
    inv Hequ; rename H into equ; cbn in *.
    step in equ.
    revert u equ.
    dependent induction TR; intros; subst; eauto;
      rename u into U;
      remember ({| _observe := U |}) as u;
      replace U with (observe u) in * by now subst.
    - eapply KtransObs; auto.
      transitivity t; auto.
      now step.
    - eapply KtransTau; auto.
    - eapply KtransDone.
      transitivity t; auto.
      now step.
    - eapply KtransFinish.
      transitivity t; auto.
      now step.
  Qed.

  Global Instance ktrans_equ_aux2 {X}:
    Proper (going (equ eq) ==> eq ==> going (equ eq) ==> eq ==> impl) (ktrans_ (X:=X)).
  Proof.
    intros t t' Heqt x x' <- u u' Hequ y y' <- TR.
    rewrite <- Hequ; clear u' Hequ.
    inv Heqt; rename H into eqt.
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

  Global Program Instance itree_kripke: Kripke (itree E) E := {
      ktrans X t w t' w' :=
        ktrans_ (X:=X) (observe t) w (observe t') w'
    }.
  Next Obligation.
    dependent induction H; cbn; eauto with ctl.
  Defined.
  Next Obligation.
    dependent induction H; cbn; eauto with ctl; inv H0.
  Defined.
  Arguments ktrans /.
  
  Global Instance ktrans_equ_proper{X}:
    Proper (equ eq ==> eq ==> equ eq ==> eq ==> iff) (ktrans (X:=X)).
  Proof.
    unfold Proper, respectful, RelCompFun, fst, snd; cbn; intros; subst.
    split; intros TR; unfold ktrans.
    - now rewrite <- H, <- H1.
    - now rewrite H, H1.
  Qed.
End KripkeTrans.

(*| Allow rewriting with [equ] under CTL entailment |*)
Global Instance equ_kripke `{HE: Encode E} {X}: KripkeSetoid (itree E) E X (equ eq).
Proof.
  repeat red.
  intros.
  exists s'.
  rewrite H in H0.
  rewrite <- H in *; auto.
Qed.

Ltac ktrans_ind H :=
  simpl ktrans in H;
  dependent induction H; eauto with ctl.

Section KripkeLemmas.
  Context {E: Type} {HE: Encode E}.
  
  Lemma ktrans_stuck{X}: forall (t: itree E X) w w',
      ~ [stuck, w] ↦ [t, w'].
  Proof.
    intros * Hcontra.
    ktrans_ind Hcontra.
  Qed.
  Hint Resolve ktrans_stuck: ctl.

  Lemma ktrans_tau {X}: forall (t t': itree E X) s s',
      [Tau t, s] ↦ [t', s'] <-> [t, s] ↦ [t', s'].
  Proof.
    intros; split; intro H.
    - ktrans_ind H; cbn; now rewrite x in H.
    - cbn; apply KtransTau; now cbn in H.
  Qed.

  Lemma ktrans_pure {X}: forall (t: itree E X) (w': World E) x,
      [Ret x, Pure] ↦ [t, w'] <-> (w' = Done x /\ t ≅ stuck).
  Proof.
    intros; split; intros.
    - ktrans_ind H; split; try reflexivity.
      step; cbn; rewrite <- x; now step in H.
    - cbn; destruct H as (-> & ->); now apply KtransDone.
  Qed.

  Lemma ktrans_finish {X}: forall (t: itree E X) (w': World E) (e: E) (v: encode e) x,
      [Ret x, Obs e v] ↦ [t, w'] <-> (w' = Finish e v x /\ t ≅ stuck).
  Proof.
    intros; split; intros.
    - ktrans_ind H; split; try reflexivity.
      step; cbn; rewrite <- x; now step in H.                                              
    - cbn; destruct H as (-> & ->); now apply KtransFinish.
  Qed.
  
  Lemma ktrans_vis {X} {t': itree E X} s s' e (k: encode e -> itree E X):
    [Vis e k, s] ↦ [t', s'] <->
      (exists (v: encode e), t' ≅ k v /\ s' = Obs e v /\ not_done s).
  Proof.
    intros; split; intro TR; ktrans_ind TR.
    - exists v; split; auto.
      step; cbn; rewrite <- x; now step in H.
    - cbn; destruct H as (-> & -> & ?); apply KtransObs; auto.
  Qed.

  Lemma ktrans_bind_inv_aux {X Y} (w w': World E)(T U: itree' E Y) :
    ktrans_ T w U w' ->
    forall (t: itree E X) (k: X -> itree E Y) (u: itree E Y),
      go T ≅ t >>= k ->
      go U ≅ u ->
      (* [t] steps, [t>>=k] steps *)
      (exists t', [t, w] ↦ [t', w']        
             /\ not_done w'
             /\ u ≅ x <- t' ;; k x) \/
        (* [t] pure return [Done x], [t>>=k] steps if [k x] steps *)
      (exists (x: X),                      
          [t, w] ↦ [stuck, Done x]
          /\ w = Pure
          /\ [k x, Pure] ↦ [u, w']) \/
        (* [t] impure return [Finish e v x], [t>>=k] steps if [k x] steps *)
      (exists (e: E) (v: encode e) (x: X), 
          [t, w] ↦ [stuck, Finish e v x]
          /\ w = Obs e v
          /\ [k x, Obs e v] ↦ [u, w']).
  Proof with (auto with ctl).
    intros TR.
    dependent induction TR; intros.
    - rewrite unfold_bind in H1; unfold ktrans; cbn; desobs t0; observe_equ Heqt.
      + right; inv H0;
          replace (TauF stuck) with (observe stuck (X:=X)) by reflexivity.
        * left; exists x.
          split; [|split]... 
          -- now apply KtransDone.
          -- rewrite <- H1; cbn; apply KtransObs... 
             rewrite <- itree_eta in H2.
             transitivity t; [symmetry|]... 
        * right; exists e0, v0, x. 
          split; [|split]... 
          -- now apply KtransFinish.
          -- rewrite <- H1; cbn; apply KtransObs... 
             rewrite <- itree_eta in H2.
             transitivity t; [symmetry|]... 
      + step in H1; inv H1.
      + left.
        pose proof (equ_vis_invT H1) as (_ & <-).
        eapply equ_vis_invE with v in H1.
        exists (k1 v); split; [|split]; auto with ctl.
        * now cbn; apply KtransObs.
        * rewrite <- H1, <- H.
          symmetry.
          now rewrite <- itree_eta in H2.
    - rewrite unfold_bind in H; unfold ktrans; cbn;
        desobs t0; observe_equ Heqt.
      + right.
        pose proof (ktrans_not_done (X:=Y) t t' w w' TR) as Hw.
        replace (TauF stuck) with (observe stuck (X:=X)) by reflexivity.
        inv Hw.
        * left; exists x.
          split; [|split]...
          -- now apply KtransDone.
          -- rewrite <- H, <- H0; cbn; now apply KtransTau.
        * right; exists e, v, x.
          split; [|split]... 
          -- now apply KtransFinish.
          -- rewrite <- H, <- H0; cbn; now apply KtransTau.
      + pose proof (equ_tau_invE H).
        rewrite itree_eta in H1.
        destruct (IHTR _ _ _ H1 H0)
          as [(t2 & TR2 & Hd & Eq2) |
               [(x & TRr & -> & TRk) |
                 (e & v & x & TRr & -> & TRk)]];
          replace (TauF stuck) with (observe stuck (X:=X))
          by reflexivity.
        * left.
          exists t2; split; [|split]... 
          now apply KtransTau.
        * right; left.
          exists x.
          split... 
          now apply KtransTau.
        * right; right.
          exists e, v, x.
          split...
          now apply KtransTau.
      + step in H; inv H.
    - rewrite unfold_bind in H0; unfold ktrans; cbn;
        desobs t0; observe_equ Heqt.
      + right; left.
        exists x0.
        split; [|split]...
        * replace (TauF stuck) with (observe stuck (X:=X))
            by reflexivity.
          now apply KtransDone.
        * rewrite <- H1, H, <- H0; cbn.
          replace (TauF stuck) with (observe stuck (X:=Y))
            by reflexivity.
          now apply KtransDone.
      + step in H0; inv H0.
      + step in H0; inv H0.
    - rewrite unfold_bind in H0; unfold ktrans; cbn; desobs t0; observe_equ Heqt.
      + right; right.
        exists e, v, x0.
        split; [|split]... 
        * replace (TauF stuck) with (observe stuck (X:=X))
            by reflexivity.
          now apply KtransFinish.
        * rewrite <- H1, H, <- H0; cbn.
          replace (TauF stuck) with (observe stuck (X:=Y))
            by reflexivity.
          now apply KtransFinish.
      + step in H0; inv H0.
      + step in H0; inv H0.
  Qed.

  Lemma ktrans_bind_inv: forall {X Y} (w w': World E)
                           (t: itree E X) (u: itree E Y) (k: X -> itree E Y),
      [x <- t ;; k x, w] ↦ [u, w'] ->
      (exists t', [t, w] ↦ [t', w']
             /\ not_done w'
             /\ u ≅ x <- t' ;; k x) \/
      (exists (x: X),              
          [t, w] ↦ [stuck, Done x]
          /\ w = Pure
          /\ [k x, Pure] ↦ [u, w']) \/
      (exists (e: E) (v: encode e) (x: X),
          [t, w] ↦ [stuck, Finish e v x]
          /\ w = Obs e v
          /\ [k x, Obs e v] ↦ [u, w']).
  Proof.
    intros * TR.
    eapply ktrans_bind_inv_aux.
    apply TR.
    rewrite <- itree_eta; reflexivity.
    rewrite <- itree_eta; reflexivity.
  Qed.

  Lemma ktrans_bind_l{X Y}: forall (t t': itree E Y)
                              (k: Y -> itree E X) w w',
      [t, w] ↦ [t', w'] ->
      not_done w' ->
      [x <- t ;; k x, w] ↦ [x <- t' ;; k x, w'].
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
      cbn; apply IHktrans_; auto.
    - inv H0.
    - inv H0.
  Qed.

  Lemma ktrans_bind_r{X Y}:
    forall (t: itree E Y) (u: itree E X) (k: Y -> itree E X)
      (y: Y) w w_ w',
      [t, w] ↦ [stuck, w_] ->
      done_eq Y y w_ ->
      [k y, w] ↦ [u, w'] ->
      [y <- t ;; k y, w] ↦ [u, w'].
  Proof.
    intros; cbn in *.
    replace (TauF stuck) with (observe stuck (X:=Y)) in H
        by reflexivity.
    ktrans_ind H; rewrite unfold_bind; cbn.
    - inv H1; inv H3.
    - desobs t; dependent destruction x0.
      apply ktrans_tau.
      cbn; eapply IHktrans_; eauto.
    - dependent destruction H0. 
      desobs t; dependent destruction x1; auto.
    - dependent destruction H0.
      desobs t; dependent destruction x1; auto.
  Qed.

End KripkeLemmas.
