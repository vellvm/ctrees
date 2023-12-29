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
Notation ctreeEW E := (ctree (writerE (Bar E))).

Section CTreeTrans.
  Context {E: Type} `{HE: Encode E} {X: Type}.
  Notation encode := (@encode E HE).
  
  (* Note: This Kripke transition rel observes labels, this is important
     for the [ktrans_bind_inv] lemma *)
  Variant ktrans_: relation (ctree E X * World E) :=    
    | KtransObs (ts: World E) (e: E) (x: encode e)
        (t t': ctree E X):
      trans (obs e x) t t' ->
      ~ is_done ts ->
      ktrans_ (t, ts) (t', Obs e x)
    | KtransTau (ts: World E) (t t': ctree E X):
      trans tau t t' ->
      ~ is_done ts ->
      ktrans_ (t, ts) (t', ts)
    | KtransRet (ts: World E) (t t': ctree E X) (x: X):
      trans (val x) t stuck ->
      ~ is_done ts ->
      t' ≅ stuck ->
      ktrans_ (t, ts) (t', Done x).

  Global Instance trans_equ_proper:
    Proper (equ eq * eq ==> equ eq * eq ==> iff) ktrans_.
  Proof.
    unfold Proper, respectful, RelCompFun, fst, snd;
      cbn; intros.
    destruct2 H; destruct2 H0; destruct x, y, x0, y0; subst.
    split; intros TR; inv TR.
    - apply KtransObs; auto. now rewrite <- Heqt0, <- Heqt. 
    - apply KtransTau; auto. now rewrite <- Heqt0, <- Heqt.
    - apply KtransRet; auto.
      + now rewrite <- Heqt.
      + now rewrite <- Heqt0.                         
    - apply KtransObs; auto. now rewrite Heqt0, Heqt.
    - apply KtransTau; auto. now rewrite Heqt0, Heqt.
    - apply KtransRet; auto.
      + now rewrite Heqt.
      + now rewrite Heqt0. 
  Qed.
  
  (*| This version is more amenable to induction |*)
  Lemma ktrans_trans: forall t t' w w',
      ktrans_ (t, w) (t', w') <->
        (exists l, trans_ l (observe t) (observe t') /\
                ~ is_done w /\
                ((l = tau /\ w' = w)
                 \/ (exists e (x: encode e), l = obs e x /\ w' = Obs e x)
                 \/ (exists (x: X), l = val x /\ t' ≅ stuck /\ w' = Done x))).
  Proof.
    intros; split; intro H.
    inv H. 
    - exists (obs e x); split; auto; split; auto.
      right; left.
      exists e, x; auto.
    - exists tau; split; auto. 
    - exists (val x); rewrite H6; split; auto; split; auto.
      right; right.
      exists x; auto.
    - destruct H as (l & ? & ? & ?).
      + destruct H1.
        * destruct H1 as (-> & ->).
          now apply KtransTau.
        * destruct H1.
          -- destruct H1 as (e & x & -> & ->).
             now apply KtransObs.
          -- destruct H1 as (x & -> & ? & ->).
             rewrite H1 in *.
             apply KtransRet; auto.
  Qed.  

End CTreeTrans.

Ltac ktrans_inv H :=
  let Hw := fresh "Heqw" in
  let e := fresh "e" in
  let x := fresh "x" in
  let l := fresh "l" in
  let TR := fresh "TR" in
  let Ht := fresh "Heqt" in
  apply ktrans_trans in H as
      (l & H & ? & [(Hl & Hw) | [(e & x & Hl & Hw) | (x & Hl & Ht & Hw)]]); subst.

Ltac ktrans_goal :=
  simpl ktrans; eexists; apply ktrans_trans.

Global Hint Constructors ktrans_: core.

Section CTreeTrans.
  Context {E: Type} `{HE: Encode E}.
  Notation encode := (@encode E HE).
  Local Open Scope ctl_scope.
  Notation sbisim := (fun (X: Type) => @sbisim E E HE HE X X eq).

  (*| CTree is a kripke automaton with [Sb] equivalence |*)
  Global Program Instance ctree_kripke : Kripke (ctree E) sbisim E :=
    {| ktrans X m m' := ktrans_ (X:=X) m m' |}.
  Next Obligation.
    ktrans_inv H0;
      destruct (SBisim.sbisim_trans (X:=X) _ _ _ _ eq H H0)
      as (l & c1' & ? & <- & ?).
    + exists c1'; split; [apply KtransTau|]; auto.      
    + exists c1'; split; [apply KtransObs|]; auto.
    + exists c1'; split; auto.
      pose proof trans_val_inv H2.
      rewrite <- H4 in H2.
      now apply KtransRet. 
  Defined.
  Next Obligation.
    ktrans_inv H; auto with ctl.
  Defined.
  Next Obligation.
    intros (t' & w' & TR).
    ktrans_inv TR; apply H; constructor. 
  Defined.

  (*| Lemmas that depend on structure of [ctrees] |*)
  Lemma ktrans_brD {X}: forall n (t': ctree E X) (k: fin' n -> ctree E X) w w',
      (BrD n k, w) ↦ (t', w') <->
        (exists (i: fin' n), (k i, w) ↦ (t', w')).
  Proof.
    split; intro H.
    - ktrans_inv H; apply trans_brD_inv in H as (n' & ?);
        exists n'; apply ktrans_trans; eexists.
      + split; [eassumption|split]; auto. 
      + split; [eassumption|split]; auto.
        right; left; eauto.
      + split; [eassumption|split]; auto.
        right; right; eauto.
    - destruct H as (n' & H); ktrans_inv H; apply ktrans_trans; eexists.
      + split; [|split].
        * econstructor; eassumption.
        * assumption.
        * left; split; reflexivity. 
      + split; [|split].
        * econstructor; eassumption.
        * assumption.
        * right; left; exists e, x; split; reflexivity.
      + split; [|split].
        * econstructor; eassumption.
        * assumption.
        * right; right; exists x; split; auto. 
  Qed.

  Lemma ktrans_brS {X}: forall n (t: ctree E X) (k: fin' n -> ctree E X) w w',
      (BrS n k, w) ↦ (t, w') <->
        (exists (i: fin' n), t ≅ k i /\ w = w' /\ ~ is_done w).
  Proof.
    split; intro H.
    - ktrans_inv H; apply trans_brS_inv in H as (n' & ? & ?);
        exists n'; subst; inv H1; auto.
    - destruct H as (n' & -> & -> & ?).
      apply ktrans_trans; exists tau.
      split; econstructor.
      * reflexivity.
      * auto.
      * now left.
  Qed.
  
  Lemma ktrans_guard {X}: forall (t t': ctree E X) s s',
      ktrans_ (guard t, s) (t', s') <-> ktrans_ (t, s) (t', s').
  Proof.
    intros; split; intros.
    - now apply ktrans_brD in H as (i & ?). 
    - apply ktrans_brD; now (exists (F1)).
  Qed.

  Lemma ktrans_ret {X}: forall (t: ctree E X) s s' x,
      ktrans_ (Ret x, s) (t, s') <-> (s' = Done x /\ t ≅ stuck /\ ~ is_done s).
  Proof.
    intros; split; intros.
    - ktrans_inv H; dependent destruction H; auto.
    - destruct H as (-> & -> & ?). 
      apply KtransRet; etrans.
  Qed.

  Lemma ktrans_vis{X}: forall (t: ctree E X) (s s': World E) (e: E) (k: encode e -> ctree E X),
      ktrans_ (Vis e k, s) (t, s') <->
      (exists (x: encode e), s' = Obs e x /\ k x ≅ t /\ ~ is_done s).
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
    - destruct TR as (? & -> & <- & ?).
      apply ktrans_trans; exists (obs e x).
      split; [econstructor|split]; auto.
      right; left; eauto.
  Qed.

  Lemma ktrans_not_started{X}: forall (t t': ctree E X) w,
      ktrans_ (t, w) (t', NotStarted) ->
        w = NotStarted.
  Proof.
    intros * H.
    inv H; reflexivity.
  Qed.

  Lemma ktrans_not_done{X}: forall (t t': ctree E X) w w',
    (t, w) ↦ (t', w') ->
    ~ is_done w.
  Proof.
    intros; inv H; auto.
  Qed.
  Hint Resolve ktrans_not_done: ctl.
            
  Lemma ktrans_bind_l{X Y}: forall (t t': ctree E Y) (k: Y -> ctree E X) w w',
      ktrans_ (t, w) (t', w') ->
      ~ is_done w' ->
      ktrans_ (x <- t ;; k x, w) (x <- t' ;; k x, w').
  Proof.
    intros.
    ktrans_inv H; apply ktrans_trans.    
    - exists tau; split. (* BrS *)
      + apply trans_bind_l; auto.
        intro Hcontra; inv Hcontra.
      + split; auto with ctl.
    - exists (obs e x); split. (* Vis *)
      + apply trans_bind_l; auto.
        intro Hcontra; inv Hcontra; world_inv.
      + split; auto with ctl. (* Ret *)
        right; eauto.
    - exfalso; apply H0; constructor. 
  Qed.

  Lemma ktrans_bind_r{X Y}: forall (t: ctree E Y) (u: ctree E X) (k: Y -> ctree E X) (y: Y) w w',
      ktrans_ (t, w) (stuck, Done y) ->
      ktrans_ (k y, w) (u, w') ->
      ktrans_ (y <- t ;; k y, w) (u, w').
  Proof.
    intros.
    ktrans_inv H; apply ktrans_trans.
    - exfalso; apply H1; constructor.
    - world_inv.
    - ktrans_inv H0; world_inv.
      + exists tau; split.
        * apply trans_bind_r with x; etrans. 
        * split; auto.
      + exists (obs e x0); split.
        * apply trans_bind_r with x; etrans.
        * split; auto.
          right; left; eauto.
      + exists (val x0); split.
        * apply trans_bind_r with x; etrans.
        * split; auto.
          right; right; eauto.
  Qed.

  Lemma ktrans_bind_inv{X Y}: forall (t: ctree E Y) (u: ctree E X) (k: Y -> ctree E X) w w',
      ktrans_ (x <- t ;; k x, w) (u, w') ->
      (exists t', ktrans_ (t, w) (t', w')
             /\ u ≅ x <- t' ;; k x) \/
      (exists y, ktrans_ (t, w) (stuck, Done y)
            /\ ktrans_ (k y, w) (u, w')).
  Proof.
    intros * TR.
    ktrans_inv TR; destruct (trans_bind_inv _ _ TR) as
      [(Hv & t' & TR' & Heq) | (y & TRv & TR')]. 
    + left; exists t'; split; auto.
    + right; exists y; split; apply ktrans_trans.
      * exists (val y); split; auto; split; auto with ctl.
        right; right; exists y; auto.
      * exists (tau); split; auto.
    + left; exists t'; split; auto with ctl.
    + right; exists y; cbn; auto with ctl.
    + exfalso; apply Hv; constructor.
    + right; exists y; cbn; split; auto.
      apply ktrans_trans.
      exists (val x); split; [|split]; auto.
      right; right; exists x; auto.
  Qed.

End CTreeTrans.

Local Typeclasses Transparent equ.
Lemma ktrans_trigger_inv `{ReSumRet E1 E2} {X}: forall (e: E2) w w' (k: encode (resum e) -> ctree E2 X) (u': ctree E2 X),
      ktrans_ (z <- trigger e ;; k z, w) (u', w') ->
      (exists z, w' = Obs e z /\ u' ≅ k z).
Proof.    
  intros.
  unfold trigger in H3.
  destruct w'.
  - rewrite bind_vis in H3.
    apply ktrans_vis in H3 as (? & ? & ?); world_inv.
  - apply ktrans_bind_inv in H3 as [(? & ? & ?) | (x0 & Hret & Hcont)].
    + apply ktrans_vis in H3 as (y & ? & ? & ?).
      unfold resum, ReSum_refl, resum_ret, ReSumRet_refl in *; world_inv.
      exists y; setoid_rewrite <- H5 in H4; rewrite bind_ret_l in H4; auto.
    + apply ktrans_vis in Hret as (? & ? & ?); world_inv. 
  - rewrite bind_vis in H3.
    apply ktrans_vis in H3 as (? & ? & ?); world_inv. 
Qed.
