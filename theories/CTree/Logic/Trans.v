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
  CTree.Pred
  CTree.Equ
  Utils.Trc
  CTree.Trans
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
  | KtransBrD (n: nat) (i: fin' n) k w w' (t': ctree E X): 
    ktrans_ (observe (k i)) w (observe t') w' ->
    ktrans_ (BrF false n k) w (observe t') w'
  | KtransBrS (n: nat) (i: fin' n) k t w:
    not_done w ->
    t ≅ k i ->
    ktrans_ (BrF true n k) w (observe t) w
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
    - eapply KtransBrD; auto.
    - eapply KtransBrS; auto.
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
      eapply KtransBrD; eauto.
      eapply IHTR; auto.
      now rewrite <- !ctree_eta.
    + step in eqt; cbn in eqt; dependent destruction eqt.
      rewrite H0.
      eapply KtransBrS; auto.
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

  (*| Prove [trans], [ktrans] are in lockstep and worlds/labels are 1-1 |*)
  Lemma ktrans_trans: forall (t t': ctree E X) w w',
      ktrans_ (observe t) w (observe t') w' <->
        (exists l, trans_ l (observe t) (observe t') /\
                ((l = tau /\ not_done w /\ w' = w)
                 \/ (exists e (x: encode e), l = obs e x /\ not_done w /\ w' = Obs e x)
                 \/ (exists (x: X), l = val x /\ w = Pure /\ t' ≅ stuck /\ w' = Done x)
                 \/ (exists e (v: encode e) (x: X), l = val x /\ w = Obs e v /\ t' ≅ stuck /\ w' = Finish e v x))).
  Proof.
    intros; split; intro H.
    - remember (observe t) as T; remember (observe t') as T';
      generalize dependent t; generalize dependent t'.
      induction H; intros; subst.
      + destruct (IHktrans_ _ HeqT' (k i) eq_refl) as (l & TR & Hl). 
        exists l; split; auto.
        apply trans_brD with (t:=k i) (x:=i); auto.
      + exists tau; split; auto.
        apply trans_brS with (x:=i).
        now symmetry. 
      + exists (obs e v); split.
        * econstructor; now symmetry.
        * right; left.
          exists e, v; auto.
      + exists (val x); rewrite H; split.
        * now econstructor.
        * right; right; left.
          exists x; intuition.
          transitivity t; auto.
          step; cbn; rewrite HeqT'; reflexivity.
      + exists (val x); rewrite H; split; auto.
        * now econstructor.
        * right; right; right.
          exists e, v, x; intuition.
          transitivity t; auto.
          step; cbn; rewrite HeqT'; reflexivity.
    - destruct H as (l & ? & Hl);
      remember (observe t) as T; remember (observe t') as T';
        generalize dependent t; generalize dependent t'; revert w w'.
      induction H; intros; subst.
      + apply KtransBrD with x; eauto.
      + destruct Hl as [ (? & ? & ?) |
             [(e & x' & ? & ? & ?) |
               [(x' & ? & ? & Ht & ?) |
                 (e & v & x' & ? & ? & Ht & ?)]]]; subst; inv H0.
        apply KtransBrS with x; auto.
        now symmetry.
      + destruct Hl as [ (? & ? & ?) |
             [(e' & x' & ? & ? & ?) |
               [(x' & ? & ? & Ht & ?) |
                 (e' & v & x' & ? & ? & Ht & ?)]]]; subst; dependent destruction H0.
        apply KtransObs; auto.
        now symmetry.
      + destruct Hl as [ (? & ? & ?) |
             [(e' & x' & ? & ? & ?) |
               [(x' & ? & ? & Ht & ?) |
                 (e' & v & x' & ? & ? & Ht & ?)]]]; subst; dependent destruction H0.
        * apply KtransDone.
          transitivity t'; auto.
          step; cbn; rewrite HeqT'; reflexivity.
        * apply KtransFinish.
          transitivity t'; auto.
          step; cbn; rewrite HeqT'; reflexivity.
  Qed.

End CTreeTrans.

Ltac ktrans_inv H :=
  let e := fresh "e" in
  let x := fresh "x" in
  let v := fresh "v" in
  let l := fresh "l" in
  let Ht := fresh "Heqt" in
  apply ktrans_trans in H as
        (l & H &
           [ (? & ? & ?) |
             [(e & x & ? & ? & ?) |
               [(x & ? & ? & Ht & ?) |
                 (e & v & x & ? & ? & Ht & ?)]]]); subst.

Global Hint Constructors ktrans_: core.

From CTree Require Import CTree.SBisim.
Section SbisimSetoid.
  Context {E: Type} `{HE: Encode E} {X: Type}.
  Notation encode := (@encode E HE).
  Local Open Scope ctl_scope.

  (*| CTree is a kripke setoid with [strong bisimulation] equivalence |*)
  Global Instance sbisim_kripke : KripkeSetoid (ctree E) E X (sbisim eq).
  Proof.
    repeat red; intros.
    ktrans_inv H0;
      destruct (SBisim.sbisim_trans (X:=X) _ _ _ _ eq H H0)
      as (l' & c1' & ? & <- & ?); exists c1'.
    + split; [apply ktrans_trans|auto].
      exists tau; split; auto. 
    + split; [apply ktrans_trans|auto].
      exists (obs e x); split; auto.
      right; left.
      exists e, x; intuition.
    + split; [apply ktrans_trans|auto].
      exists (val x); split; auto.
      right; right; left.
      pose proof trans_val_inv H1.
      exists x; intuition.
    + split; [apply ktrans_trans|auto].
      exists (val x); split; auto.
      right; right; right.
      pose proof trans_val_inv H1.
      exists e, v, x; intuition.
  Qed.
End SbisimSetoid.

(*| Lemmas that depend on structure of [ctrees] |*)
Section CTreeTransLemmas.
  Context {E: Type} `{HE: Encode E}.
  Local Open Scope ctl_scope.  

  Lemma ktrans_brD {X}: forall n (t': ctree E X) (k: fin' n -> ctree E X) w w',
      [BrD n k, w] ↦ [t', w'] <->
        (exists (i: fin' n), [k i, w] ↦ [t', w']).
  Proof.
    split; intro H.
    - ktrans_inv H; apply trans_brD_inv in H as (n' & ?);
        exists n'; apply ktrans_trans; eexists.
      + split; [eassumption|]; left; auto.
      + split; [eassumption|]; right; left; eauto.
      + split; [eassumption|]; right; right; left; eauto.
      + split; [eassumption|]; right; right; right; exists e, v, x; auto.
    - destruct H as (n' & H); ktrans_inv H; apply ktrans_trans; eexists.
      + split; [econstructor|left]; eauto.
      + split; [econstructor|right; left]; eauto.
      + split; [econstructor|right; right; left]; eauto.
      + split; [econstructor; apply H|right; right; right]; exists e, v, x; eauto.
  Qed.

  Lemma ktrans_brS {X}: forall n (t: ctree E X) (k: fin' n -> ctree E X) w w',
      [BrS n k, w] ↦ [t, w'] <->
        (exists (i: fin' n), t ≅ k i /\ w = w' /\ not_done w).
  Proof.
    split; intro H.
    - ktrans_inv H; apply trans_brS_inv in H as (n' & ? & ?);
        exists n'; subst; inv H0; auto.
    - destruct H as (n' & -> & -> & ?).
      apply ktrans_trans; exists tau.
      split; econstructor.
      * reflexivity.
      * auto.
  Qed.
  
  Lemma ktrans_guard {X}: forall (t t': ctree E X) s s',
      [guard t, s] ↦ [t', s'] <-> [t, s] ↦ [t', s'].
  Proof.
    intros; split; intros.
    - now apply ktrans_brD in H as (i & ?). 
    - apply ktrans_brD; now (exists (F1)).
  Qed.

  Lemma ktrans_done {X}: forall (t: ctree E X) (w': World E) x,
      [Ret x, Pure] ↦ [t, w'] <-> (w' = Done x /\ t ≅ stuck).
  Proof.
    intros; split; intros.
    - ktrans_inv H; dependent destruction H; split; auto with ctl.
    - destruct H as (-> & ->); constructor; etrans. 
  Qed.

  Lemma ktrans_finish {X}: forall (t: ctree E X) (w': World E) (e: E) (v: encode e) x,
      [Ret x, Obs e v] ↦ [t, w'] <->
        (w' = Finish e v x /\ t ≅ stuck).
  Proof.
    intros; split; intros.
    - ktrans_inv H; dependent destruction H; split; auto with ctl.
    - destruct H as (-> & ->); constructor; etrans. 
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
      apply ktrans_trans; exists (obs e x).
      split; [econstructor|]; auto.      
      right; left; eauto.
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
    apply ktrans_trans in Hcontra as (l & TR & ?).
    now apply trans_stuck in TR.
  Qed.
  Hint Resolve ktrans_stuck: ctl.
  
  Lemma ktrans_pure_inv{X}: forall (t t': ctree E X) w,
    [t, Pure] ↦ [t', w] ->
    (w = Pure /\ trans tau t t') \/
    (exists (e: E) (v: encode e), w = Obs e v /\ trans (obs e v) t t') \/
    (exists (x: X), w = Done x /\ t' ≅ stuck /\ trans (val x) t Ctree.stuck).
  Proof.
    intros.
    ktrans_inv H.
    - left; auto.
    - right; left.
      exists e, x; auto.
    - right; right.
      exists x.
      rewrite Heqt in H; auto.
    - inv H1.
  Qed.
  
  Lemma ktrans_obs_inv{X}: forall (t t': ctree E X) (e: E) (v: encode e) w,
    [t, Obs e v] ↦ [t', w] ->
    (w = Obs e v /\ trans tau t t') \/
    (exists (e': E) (v': encode e'), w = Obs e' v' /\ trans (obs e' v') t t') \/
    (exists (e': E) (v': encode e') (x: X), w = Finish e' v' x /\ t' ≅ stuck /\ trans (val x) t Ctree.stuck).
  Proof.
    intros.
    ktrans_inv H.
    - left; auto.
    - right; left.
      exists e0, x; auto.
    - inv H1.
    - right; right; world_inv.
      exists e0, v0, x.
      rewrite Heqt in H; auto.
  Qed.

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

  Lemma ktrans_to_done_inv{X}: forall (t t': ctree E X) w (x: X),
      [t, w] ↦ [t', Done x] ->
      t' ≅ Ctree.stuck /\ w = Pure.
  Proof.
    intros.
    cbn in H.
    dependent induction H; intros; eauto.
    - inv H.
    - observe_equ x.
      rewrite Eqt in H.
      intuition.
  Qed.
  
  Lemma ktrans_to_finish_inv{X}: forall (t t': ctree E X) w (e: E) (v: encode e) (x: X),
      [t, w] ↦ [t', Finish e v x] ->
      t' ≅ Ctree.stuck /\ w = Obs e v.
  Proof.
    intros.
    cbn in H.
    dependent induction H; intros; eauto.
    - inv H.
    - observe_equ x.
      rewrite Eqt in H.
      intuition.
  Qed.

  Lemma ktrans_bind_l{X Y}: forall (t t': ctree E Y) (k: Y -> ctree E X) w w',
      [t, w] ↦ [t', w'] ->
      not_done w' ->
      [x <- t ;; k x, w] ↦ [x <- t' ;; k x, w'].
  Proof.
    intros.
    ktrans_inv H; apply ktrans_trans.    
    - exists tau; split. (* BrS *)
      + apply trans_bind_l; auto.
        intro Hcontra; inv Hcontra.
      + left; auto with ctl.
    - exists (obs e x); split. (* Vis *)
      + apply trans_bind_l; auto.
        intro Hcontra; inv Hcontra; world_inv.
      + (* Ret *)
        right; left; eauto.      
    - inv H0.
    - inv H0.
  Qed.

  Lemma ktrans_bind_r{X Y}: forall (t: ctree E Y) (u: ctree E X) (k: Y -> ctree E X) (y: Y) w w_ w',
      [t, w] ↦ [stuck, w_] ->
      return_val Y y w_ ->
      [k y, w] ↦ [u, w'] ->
      [y <- t ;; k y, w] ↦ [u, w'].
  Proof.
    intros.
    ktrans_inv H; apply ktrans_trans;
      repeat dependent destruction H0. 
    - inv H3.
    - inv H3.
    - ktrans_inv H1. 
      + exists tau; split.
        * apply trans_bind_r with x; auto.          
        * left; auto. 
      + exists (obs e x0); split.
        * apply trans_bind_r with x; etrans.
        * right; left; eauto. 
      + exists (val x0); split.
        * apply trans_bind_r with x; etrans.
        * right; right; left; eauto.
      + inv H2.
    - ktrans_inv H1; try world_inv.
      + exists tau; split.
        * apply trans_bind_r with x; auto.          
        * left; auto. 
      + exists (obs e0 x0); split.
        * apply trans_bind_r with x; etrans.
        * right; left; eauto. 
      + exists (val x0); split.
        * apply trans_bind_r with x; etrans.
        * right; right; right; exists e0, v0, x0; etrans.
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
