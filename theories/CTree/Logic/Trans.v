From ExtLib Require Import
  Structures.MonadWriter
  Structures.Monads
  Structures.MonadState
  Data.Monads.StateMonad.

From Coq Require Import
  List
  Basics
  Fin
  Relations.Relation_Definitions
  Classes.SetoidClass
  Classes.RelationPairs.

From CTree Require Import
  CTree.Core
  CTree.Equ
  Utils.Trc
  CTree.Events.Writer
  Events.Core
  Logic.Kripke
  Logic.Setoid.

Generalizable All Variables.

Import Ctree CTreeNotations.
Local Open Scope ctree_scope.

Notation ctreeW W := (ctree (writerE W)).

Section CTreeTrans.
  Context {E: Type} `{HE: Encode E} {X: Type}.
  Notation encode := (@encode E HE).

  (*| Kripke transition system |*)
  Inductive ktrans_{X}: ctree' E X -> World E -> ctree' E X -> World E -> Prop :=
  | KtransTau w w' (t t': ctree E X): 
    ktrans_ (observe t) w (observe t') w' ->
    ktrans_ (TauF t) w (observe t') w'
  | KtransBr (n: nat) (i: fin' n) k t w:
    not_done w ->
    t ≅ k i ->
    ktrans_ (BrF n k) w (observe t) w
  | KtransObs (e: E) (v: encode e) k t w:
    not_done w ->
    t ≅ k v ->
    ktrans_ (VisF e k) w (observe t) (Obs e v)
  | KtransDone (x: X) t:
    t ≅ Ctree.stuck ->
    ktrans_ (RetF x) Pure (observe t) (Done x)
  | KtransFinish (e: E) (v: encode e) (x: X) t:
    t ≅ Ctree.stuck ->
    ktrans_ (RetF x) (Obs e v) (observe t) (Finish e v x).

  Global Instance ktrans_equ_aux1 (t: ctree' E X) (w: World E):
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
    - eapply KtransTau; auto.
    - eapply KtransBr; auto.
      transitivity t; eauto.
      now step.
    - eapply KtransObs; auto.
      transitivity t; eauto.
      now step.      
    - eapply KtransDone.
      transitivity t; auto.
      now step.
    - eapply KtransFinish.
      transitivity t; auto.
      now step.
  Qed.

  Global Instance ktrans_equ_aux2:
    Proper (going (equ eq) ==> eq ==> going (equ eq) ==> eq ==> impl) (ktrans_ (X:=X)).
  Proof.
    intros t t' Heqt x x' <- u u' Hequ y y' <- TR.
    rewrite <- Hequ; clear u' Hequ.
    inv Heqt; rename H into eqt.
    revert t' eqt.
    dependent induction TR; intros; auto.
    + step in eqt; cbn in eqt; dependent destruction eqt.
      eapply KtransTau; eauto.
      eapply IHTR; auto.
      now rewrite <- !ctree_eta.
    + step in eqt; cbn in eqt; dependent destruction eqt.
      rewrite H0.
      eapply KtransBr; auto.
    + step in eqt; cbn in eqt; dependent destruction eqt.
      rewrite H0.
      apply KtransObs; auto.
    + step in eqt; cbn in eqt; dependent destruction eqt.
      apply KtransDone; auto.
    + step in eqt; cbn in eqt; dependent destruction eqt.
      apply KtransFinish; auto.
  Qed.

  Global Program Instance ctree_kripke: Kripke (ctree E) E := {
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
  
  Global Instance ktrans_equ_proper:
    Proper (equ eq ==> eq ==> equ eq ==> eq ==> iff) (ktrans (X:=X)).
  Proof.
    unfold Proper, respectful, RelCompFun, fst, snd; cbn; intros; subst.
    split; intros TR; unfold ktrans.
    - now rewrite <- H, <- H1.
    - now rewrite H, H1.
  Qed.

End CTreeTrans.

Global Hint Constructors ktrans_: core.

(*| Lemmas that depend on structure of [ctrees] |*)
Section CTreeTransLemmas.
  Context {E: Type} `{HE: Encode E}.
  Local Open Scope ctl_scope.  

  Lemma ktrans_tau {X}: forall (t t': ctree E X) w w',
      [Tau t, w] ↦ [t', w'] <-> [t, w] ↦ [t', w'].
  Proof.
    split; intro H.
    - cbn in H; dependent induction H; cbn in *.
      now rewrite <- x.
    - cbn in *.
      now econstructor.
  Qed.

  Lemma ktrans_br {X}: forall n (t: ctree E X) (k: fin' n -> ctree E X) w w',
      [Br n k, w] ↦ [t, w'] <->
        (exists (i: fin' n), t ≅ k i /\ w = w' /\ not_done w).
  Proof.
    split; intro H.
    - cbn in H; dependent induction H. 
      exists i; intuition.
      step in H0; step; cbn in *.
      now rewrite <- x.
    - destruct H as (i & Heq & -> & Hd).
      econstructor; eauto.
  Qed.
  
  Lemma ktrans_done {X}: forall (t: ctree E X) (w': World E) x,
      [Ret x, Pure] ↦ [t, w'] <-> (w' = Done x /\ t ≅ stuck).
  Proof.
    intros; split; intros.
    - cbn in H; dependent destruction H; split; auto.
      step; cbn; rewrite <- x; step in H; cbn in H; auto.
    - destruct H as (-> & ->); constructor.
      reflexivity. 
  Qed.

  Lemma ktrans_finish {X}: forall (t: ctree E X) (w': World E) (e: E) (v: encode e) x,
      [Ret x, Obs e v] ↦ [t, w'] <->
        (w' = Finish e v x /\ t ≅ stuck).
  Proof.
    intros; split; intros.
     - cbn in H; dependent destruction H; split; auto.
      step; cbn; rewrite <- x; step in H; cbn in H; auto.
    - destruct H as (-> & ->); constructor.
      reflexivity. 
  Qed.

  Lemma ktrans_vis{X}: forall (t: ctree E X) (s s': World E) (e: E) (k: encode e -> ctree E X),
      [Vis e k, s] ↦ [t, s'] <->
        (exists (x: encode e), s' = Obs e x /\ k x ≅ t /\ not_done s).
  Proof.
    intros; split; intro TR.
    - cbn in TR.
      dependent induction TR. 
      exists v; split; [reflexivity|split]; auto.
      transitivity t0; [now symmetry|].
      step; cbn; rewrite x; reflexivity.
    - destruct TR as (? & -> & <- & ?).
      econstructor; auto.
  Qed.

  Lemma ktrans_pure_pred{X}: forall (t t': ctree E X) w,
      [t, w] ↦ [t', Pure] -> w = Pure.
  Proof.
    intros * H; cbn in H; dependent induction H; eauto. 
  Qed.
  Hint Resolve ktrans_pure_pred: ctl.
  
  Lemma ktrans_stuck{X}: forall (t: ctree E X) w w',
      ~ [stuck, w] ↦ [t, w'].
  Proof.
    intros * Hcontra.
    cbn in Hcontra; dependent induction Hcontra; eauto.
  Qed.
  Hint Resolve ktrans_stuck: ctl.
  
  Lemma done_not_ktrans{X}: forall (t: ctree E X) w,
      is_done w ->
      ~ (exists t' w', [t, w] ↦ [t', w']).
  Proof.
    intros * Hret Htr.
    destruct Htr as (? & ? & ?).
    inv Hret;
      apply ktrans_not_done in H; inv H.
  Qed.

  Lemma ktrans_done_inv{X}: forall (t t': ctree E X) (x: X) w,
      ~ [t, Done x] ↦ [t', w].
  Proof.
    intros * Hcontra; cbn in Hcontra; dependent induction Hcontra; eauto; inv H.
  Qed.
  
  Lemma ktrans_finish_inv{X}: forall (t t': ctree E X) (e: E) (v: encode e) (x: X) w,
      ~ [t, Finish e v x] ↦ [t', w].
  Proof.
    intros * Hcontra; cbn in Hcontra; dependent induction Hcontra; eauto; inv H.
  Qed.

  Lemma ktrans_bind_l{X Y}: forall (t t': ctree E Y) (k: Y -> ctree E X) w w',
      [t, w] ↦ [t', w'] ->
      not_done w' ->
      [x <- t ;; k x, w] ↦ [x <- t' ;; k x, w'].
  Proof.
    intros; cbn in *.
    revert k. 
    dependent induction H; intros; rewrite unfold_bind.
    - rewrite <- x0.
      econstructor; eauto.
    - rewrite <- x0.
      econstructor; eauto.
      eapply equ_clo_bind with (S:=eq).
      + step; cbn; rewrite <- x.
        step in H0; apply H0.
      + now intros * ->.
    - rewrite <- x0.
      econstructor; auto.
      eapply equ_clo_bind with (S:=eq).
      + rewrite <- H0.
        step; cbn; rewrite x.
        reflexivity.
      + now intros * ->.
    - inv H0.
    - inv H0.
  Qed.

  Typeclasses Transparent equ.
  Lemma ktrans_bind_r{X Y}: forall (t: ctree E Y) (u: ctree E X) (k: Y -> ctree E X) (y: Y) w w_ w',
      [t, w] ↦ [stuck, w_] ->
      return_val Y y w_ ->
      [k y, w] ↦ [u, w'] ->
      [y <- t ;; k y, w] ↦ [u, w'].
  Proof.
    intros.
    generalize dependent y.
    cbn in H; dependent induction H; intros.
    - assert(Hx: t ≅ Tau t0) by (step; cbn; rewrite <- x0; reflexivity).
      setoid_rewrite Hx.
      rewrite bind_tau.
      econstructor.
      eapply IHktrans_; eauto.
    - inv H1; inv H.
    - inv H1.
    - dependent destruction H0.
      assert(Hx: t ≅ Ret x0) by (step; cbn; rewrite <- x1; reflexivity).
      setoid_rewrite Hx.
      now rewrite bind_ret_l.
    - dependent destruction H0.
      assert(Hx: t ≅ Ret x0) by (step; cbn; rewrite <- x1; reflexivity).
      setoid_rewrite Hx.
      now rewrite bind_ret_l.
  Qed.      

  Lemma ktrans_bind_inv{X Y}: forall (t: ctree E Y) (u: ctree E X) (k: Y -> ctree E X)
                                (w w': World E) ,
      [x <- t ;; k x, w] ↦ [u, w'] ->
      (exists t', [t, w] ↦ [t', w']
             /\ not_done w'
             /\ u ≅ x <- t' ;; k x) \/
      (exists y w_, [t, w] ↦ [stuck, w_]
               /\ return_val Y y w_
               /\ [k y, w] ↦ [u, w']).
  Proof with (auto with ctl).
    intros * TR.
    ktrans_inv TR; destruct (trans_bind_inv _ _ TR) as
      [(Hv & t' & TR' & Heq) | (y & TRv & TR')].
    - left; exists t'; split...
      apply ktrans_trans.        
      exists tau; intuition.
    - inv H0.
      + right; exists y, (Done y); split;
          [apply ktrans_trans|split]... 
        * exists (val y); split...
          right; right; left; exists y; constructor...
        * apply ktrans_trans.
          exists tau; split...
      + right; exists y, (Finish e v y); split...
        * apply ktrans_trans.
          exists (val y); split...
          right; right; right.
          exists e, v, y...
        * split...
          apply ktrans_trans.
          exists tau; split...
    - left; exists t'; split...
      apply ktrans_trans.
      exists (obs e x); split...
      right; left.
      exists e, x...
    - inv H0; right.
      + exists y, (Done y); split; [apply ktrans_trans|split]... 
        * exists (val y); split... 
          right; right; left; exists y... 
        * apply ktrans_trans.
          exists (obs e x); split...
          right; left.
          exists e, x...
      + exists y, (Finish e0 v y); split...
        * apply ktrans_trans.
          exists (val y); split...
          right; right; right.
          exists e0, v, y...
        * split...
          apply ktrans_trans.
          exists (obs e x); split...
          right; left.
          exists e, x...
    - exfalso; apply Hv; constructor.
    - right; exists y, (Done y); split;
        [apply ktrans_trans|split]...
      + exists (val y); split... 
        right; right; left; exists y...
      + apply ktrans_trans.
        exists (val x); split...
        right; right; left.
        exists x; auto.
    - exfalso; apply Hv; constructor.
    - right; exists y, (Finish e v y); split;
        [apply ktrans_trans|split]...
      * exists (val y); split... 
        right; right; right; exists e, v, y...
      * apply ktrans_trans.
        exists (val x); split...
        right; right; right.
        exists e, v, x...
  Qed.

End CTreeTransLemmas.

Local Typeclasses Transparent equ.
Local Open Scope ctl_scope.
Lemma ktrans_trigger_inv `{ReSumRet E1 E2}{X}:forall (e: E2) w w' (k: encode (resum e) -> ctree E2 X) (u': ctree E2 X),
      [z <- trigger e ;; k z, w] ↦ [u', w'] ->
      (not_done w /\ exists z, w' = Obs e z /\ u' ≅ k z).
Proof.    
  intros.
  unfold trigger in H3.
  apply ktrans_bind_inv in H3 as
      [(t' & TR & Hd & Hequ) | (x & w_ & TR & ? & ?) ].
  - apply ktrans_vis in TR as (y & ? & ? & ?).
    unfold resum, ReSum_refl, resum_ret, ReSumRet_refl in *; world_inv.
    split; [auto | exists y]; split; [reflexivity|].
    now rewrite <- H4, bind_ret_l in Hequ.
  - apply ktrans_vis in TR as (y & ? & ? & ?); subst.
    step in H6; cbn in H6; inv H6.
Qed.


