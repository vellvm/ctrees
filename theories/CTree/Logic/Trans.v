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
  CTree.SBisim
  Utils.Trc
  CTree.Trans
  CTree.Events.Writer
  Events.Core
  Logic.Kripke.

Generalizable All Variables.

Import Ctree CTreeNotations.
Local Open Scope ctree_scope.

Notation ctreeW W := (ctree (writerE W)).

Section CTreeTrans.
  Context {E: Type} `{HE: Encode E} {X: Type}.
  Notation encode := (@encode E HE).
  
  (* The Kripke transition system *)
  Variant ktrans_: relation (ctree E X * World E) :=    
    | KtransObs (w: World E) (e: E) (x: encode e)
        (t t': ctree E X):
      trans (obs e x) t t' ->
      not_done w ->
      ktrans_ (t, w) (t', Obs e x)
    | KtransTau (w: World E) (t t': ctree E X):
      trans tau t t' ->
      not_done w ->
      ktrans_ (t, w) (t', w)
    | KtransDone (x: X) (t t': ctree E X):
      trans (val x) t stuck ->
      t' ≅ stuck ->
      ktrans_ (t, Pure) (t', Done x)
    | KtransFinish (e: E) (v: encode e) (x: X) (t t': ctree E X):
      trans (val x) t stuck ->
      t' ≅ stuck ->
      ktrans_ (t, Obs e v) (t', Finish e v x).      
  
  Global Instance trans_equ_proper:
    Proper (equ eq * eq ==> equ eq * eq ==> iff) ktrans_.
  Proof.
    unfold Proper, respectful, RelCompFun, fst, snd;
      cbn; intros.
    destruct2 H; destruct2 H0; destruct x, y, x0, y0; subst.
    split; intros TR; inv TR.
    - apply KtransObs; auto. now rewrite <- Heqt0, <- Heqt. 
    - apply KtransTau; auto. now rewrite <- Heqt0, <- Heqt.
    - apply KtransDone; auto.
      + now rewrite <- Heqt.
      + now rewrite <- Heqt0.
    - apply KtransFinish; auto.
      + now rewrite <- Heqt.
      + now rewrite <- Heqt0.
    - apply KtransObs; auto. now rewrite Heqt0, Heqt.
    - apply KtransTau; auto. now rewrite Heqt0, Heqt.
    - apply KtransDone; auto.
      + now rewrite Heqt.
      + now rewrite Heqt0.
    - apply KtransFinish; auto.
      + now rewrite Heqt.
      + now rewrite Heqt0.
  Qed.
 
  (*| This version is more amenable to induction on [trans] |*)
  Lemma ktrans_trans: forall t t' w w',
      ktrans_ (t, w) (t', w') <->
        (exists l, trans_ l (observe t) (observe t') /\
                ((l = tau /\ not_done w /\ w' = w)
                 \/ (exists e (x: encode e), l = obs e x /\ not_done w /\ w' = Obs e x)
                 \/ (exists (x: X), l = val x /\ w = Pure /\ t' ≅ stuck /\ w' = Done x)
                 \/ (exists e (v: encode e) (x: X), l = val x /\ w = Obs e v /\ t' ≅ stuck /\ w' = Finish e v x))).
  Proof.
    intros; split; intro H.    
    - inv H. 
      + exists (obs e x); split; auto. 
        right; left.
        exists e, x; auto.
      + exists tau; split; auto.
      + exists (val x); rewrite H5; split; auto.
        right; right; left.
        exists x; auto.
      + exists (val x); rewrite H5; split; auto.
        right; right; right.
        exists e, v, x; auto.
    - destruct H as (l & ? & []).
      + destruct H0 as (-> & ? & ->).
        now apply KtransTau.
      + destruct H0 as [(e & x & -> & ? & ->) | [(x & -> & -> & ? & ->) | (e & v & x & -> & -> & ? & ->)]].
        * now apply KtransObs.
        * rewrite H0 in *.
          apply KtransDone; auto with trans.
        * rewrite H0 in *.
          apply KtransFinish; auto with trans.
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

Section CTreeTrans.
  Context {E: Type} `{HE: Encode E}.
  Notation encode := (@encode E HE).
  Local Open Scope ctl_scope.
  Definition sbisim (X: Type) := @sbisim E E HE HE X X eq.
  Arguments sbisim /.
  Hint Unfold sbisim: core.

  (*| CTree is a kripke automaton with [Sb] equivalence |*)
  Global Program Instance ctree_kripke : Kripke (ctree E) sbisim E :=
    {| ktrans X m m' := @ktrans_ E HE X m m' |}.
  Next Obligation.
    ktrans_inv H0;
      destruct (SBisim.sbisim_trans (X:=X) _ _ _ _ eq H H0)
      as (l' & c1' & ? & <- & ?); exists c1'.
    + split; [apply KtransTau|]; auto.      
    + split; [apply KtransObs|]; auto.
    + split; auto.
      pose proof trans_val_inv H1.
      rewrite <- H3 in *.
      now apply KtransDone.
    + split; auto.
      pose proof trans_val_inv H1.
      rewrite <- H3 in *.
      now apply KtransFinish.
  Defined.
  Next Obligation.
    inv H; auto with ctl.
  Defined.

  (* Always step from impore [w] to impure [w']  |*)
  Lemma ktrans_not_pure {X} : forall (t t': ctree E X) w w',
      ktrans_ (t, w) (t', w') ->
      not_pure w ->
      not_pure w'.
  Proof.
    intros.
    ktrans_inv H; auto with ctl; inv H0.
  Qed.
  Hint Resolve ktrans_not_pure: ctl.
  
  (*| Lemmas that depend on structure of [ctrees] |*)
  Lemma ktrans_brD {X}: forall n (t': ctree E X) (k: fin' n -> ctree E X) w w',
      ktrans_ (BrD n k, w) (t', w') <->
        (exists (i: fin' n), ktrans_ (k i, w) (t', w')).
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
      + split; [econstructor; apply H|right; right; right];exists e, v, x; eauto.
  Qed.

  Lemma ktrans_brS {X}: forall n (t: ctree E X) (k: fin' n -> ctree E X) w w',
      ktrans_ (BrS n k, w) (t, w') <->
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
      ktrans_ (guard t, s) (t', s') <-> ktrans_ (t, s) (t', s').
  Proof.
    intros; split; intros.
    - now apply ktrans_brD in H as (i & ?). 
    - apply ktrans_brD; now (exists (F1)).
  Qed.

  Lemma ktrans_done {X}: forall (t: ctree E X) (w': World E) x,
      ktrans_ (Ret x, Pure) (t, w') <-> (w' = Done x /\ t ≅ stuck).
  Proof.
    intros; split; intros.
    - ktrans_inv H; dependent destruction H; split; auto with ctl.
    - destruct H as (-> & ->); etrans. 
  Qed.

  Lemma ktrans_finish {X}: forall (t: ctree E X) (w': World E) (e: E) (v: encode e) x,
      ktrans_ (Ret x, Obs e v) (t, w') <-> (w' = Finish e v x /\ t ≅ stuck).
  Proof.
    intros; split; intros.
    - ktrans_inv H; dependent destruction H; split; auto with ctl.
    - destruct H as (-> & ->); etrans. 
  Qed.

  Lemma ktrans_vis{X}: forall (t: ctree E X) (s s': World E) (e: E) (k: encode e -> ctree E X),
      ktrans_ (Vis e k, s) (t, s') <->
      (exists (x: encode e), s' = Obs e x /\ k x ≅ t /\ not_done s).
  Proof.
    intros; split; intro TR.
    - ktrans_inv TR.
      + inv TR.
      + cbn in TR.
        dependent induction TR.        
        exists x0; split; [reflexivity|split].
        * step; step in H; cbn in *; rewrite <- x; auto.
        * assumption.
      + inv TR.
      + inv TR.
    - destruct TR as (? & -> & <- & ?).
      apply ktrans_trans; exists (obs e x).
      split; [econstructor|]; auto.      
      right; left; eauto.
  Qed.

  Lemma ktrans_pure_pred{X}: forall (t t': ctree E X) w,
      ktrans_ (t, w) (t', Pure) -> w = Pure.
  Proof.
    intros * H.
    inv H; reflexivity.
  Qed.
  Hint Resolve ktrans_pure_pred: ctl.
  
  Lemma ktrans_stuck{X}: forall (t: ctree E X) w w',
      ~ ktrans_ (stuck, w) (t, w').
  Proof.
    intros * Hcontra.
    apply ktrans_trans in Hcontra as (l & TR & ?).
    now apply trans_stuck in TR.
  Qed.
  Hint Resolve ktrans_stuck: ctl.
  
  Lemma ktrans_pure_inv{X}: forall (t t': ctree E X) w,
    ktrans_ (t, Pure) (t', w) ->
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
    ktrans_ (t, Obs e v) (t', w) ->
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

  Lemma ktrans_done_inv{X}: forall (t t': ctree E X) (x: X) w,
      ~ ktrans_ (t, Done x) (t', w).
  Proof.
    intros * Hcontra.
    inv Hcontra; inv H4.
  Qed.

  Lemma ktrans_finish_inv{X}: forall (t t': ctree E X) (e: E) (v: encode e) (x: X) w,
      ~ ktrans_ (t, Finish e v x) (t', w).
  Proof.
    intros * Hcontra.
    inv Hcontra; inv H4.
  Qed.

  Lemma ktrans_bind_l{X Y}: forall (t t': ctree E Y) (k: Y -> ctree E X) w w',
      ktrans_ (t, w) (t', w') ->
      not_done w' ->
      ktrans_ (x <- t ;; k x, w) (x <- t' ;; k x, w').
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
      ktrans_ (t, w) (stuck, w_) ->
      return_with Y y w_ ->
      ktrans_ (k y, w) (u, w') ->
      ktrans_ (y <- t ;; k y, w) (u, w').
  Proof.
    intros.
    ktrans_inv H; apply ktrans_trans; try world_inv; dependent destruction H0.
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

  Lemma ktrans_bind_inv{X Y}: forall (t: ctree E Y) (u: ctree E X) (k: Y -> ctree E X) (w w': World E) ,
      ktrans_ (x <- t ;; k x, w) (u, w') ->
      (exists t', ktrans_ (t, w) (t', w')
             /\ not_done w'
             /\ u ≅ x <- t' ;; k x) \/
      (exists y w_, ktrans_ (t, w) (stuck, w_)
               /\ return_with Y y w_
               /\ ktrans_ (k y, w) (u, w')).
  Proof.
    intros * TR.
    ktrans_inv TR; destruct (trans_bind_inv _ _ TR) as
      [(Hv & t' & TR' & Heq) | (y & TRv & TR')].
    - left; exists t'; split; auto.
    - inv H0.
      + right; exists y, (Done y); split; [apply ktrans_trans|split]; auto with ctl.
        exists (val y); split; auto.
        right; right; left; exists y; auto.
      + right; exists y, (Finish e v y); split; auto with ctl.       
    - left; exists t'; split; auto with ctl.
    - inv H0.
      + right; exists y, (Done y); split; [apply ktrans_trans|split]; auto with ctl.
        exists (val y); split; auto.
        right; right; left; exists y; auto.
      + right; exists y, (Finish e0 v y); split; auto with ctl.
    - exfalso; apply Hv; constructor.
    - right; exists y, (Done y); split; [apply ktrans_trans|split]; auto with ctl.
      exists (val y); split; auto with ctl.
      right; right; left; exists y; auto with ctl.
      rewrite (ctree_eta (k y)) in *; cbn.
      desobs (k y).
      rewrite Heqt in TR', TR.
      + eauto with trans ctl.
      + destruct b.
        inv TR'.
        rewrite Heqt in *.
        econstructor; eauto with ctl.
      + inv TR'.
    - exfalso; apply Hv; constructor.
    - right; exists y, (Finish e v y); split; [apply ktrans_trans|split]; auto.      
      exists (val y); split; auto with ctl.
      right; right; right; exists e, v, y; auto.
      rewrite (ctree_eta (k y)) in *; cbn.
      desobs (k y).
      rewrite Heqt in TR', TR.
      + eauto with trans ctl.
      + destruct b.
        inv TR'.
        rewrite Heqt in *.
        right; eauto with ctl.
      + right; eauto with ctl. 
      + rewrite Heqt in TR'.
        apply KtransFinish; auto.
  Qed.

End CTreeTrans.

Local Typeclasses Transparent equ.
Lemma ktrans_trigger_inv `{ReSumRet E1 E2}{X}:forall (e: E2) w w' (k: encode (resum e) -> ctree E2 X) (u': ctree E2 X),
      ktrans_ (z <- trigger e ;; k z, w) (u', w') ->
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
  - apply ktrans_vis in TR as (y & ? & ? & ?).
    subst; inv H3.
Qed.

