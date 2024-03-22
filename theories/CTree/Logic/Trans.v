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
  CTree.Trans
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
  Context {E: Type} `{HE: Encode E}.
  Notation encode := (@encode E HE).

  (*| Kripke transition system |*)
  Inductive ktrans_{X}: ctree' E X -> World E -> ctree' E X -> World E -> Prop :=
  | KtransGuard w w' (t t': ctree E X): 
    ktrans_ (observe t) w (observe t') w' ->
    ktrans_ (GuardF t) w (observe t') w'
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
  Hint Constructors ktrans_: ctl.
  
  Local Instance ktrans_equ_aux1 {X}(t: ctree' E X) (w: World E):
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
    - eapply KtransGuard; auto.
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

  Global Instance ktrans_equ_aux2{X}:
    Proper (going (equ eq) ==> eq ==> going (equ eq) ==> eq ==> impl) (ktrans_ (X:=X)).
  Proof.
    intros t t' Heqt x x' <- u u' Hequ y y' <- TR.
    rewrite <- Hequ; clear u' Hequ.
    inv Heqt; rename H into eqt.
    revert t' eqt.
    dependent induction TR; intros; auto.
    + step in eqt; cbn in eqt; dependent destruction eqt.
      eapply KtransGuard; eauto.
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
  Hint Unfold ktrans: ctl.
  Arguments ktrans /.
  
  Global Instance ktrans_equ_proper{X}:
    Proper (equ eq ==> eq ==> equ eq ==> eq ==> iff) (ktrans (X:=X)).
  Proof.
    unfold Proper, respectful, RelCompFun, fst, snd; cbn; intros; subst.
    split; intros TR; unfold ktrans.
    - now rewrite <- H, <- H1.
    - now rewrite H, H1.
  Qed.

  (*| Prove [trans], [ktrans] are in lockstep and worlds/labels are 1-1 |*)
  Lemma ktrans_trans{X}: forall (t t': ctree E X) w w',
      ktrans_ (observe t) w (observe t') w' <->
        (exists l, trans_ l (observe t) (observe t') /\
                ((l = tau /\ not_done w /\ w' = w)
                 \/ (exists e (x: encode e), l = obs e x /\ not_done w /\ w' = Obs e x)
                 \/ (exists (x: X), l = val x /\ w = Pure /\ t' ≅ stuck /\ w' = Done x)
                 \/ (exists e (v: encode e) (x: X), l = val x /\ w = Obs e v /\ t' ≅ stuck /\ w' = Finish e v x))).
  Proof with eauto with ctree.
    intros; split; intro H.
    - remember (observe t) as T; remember (observe t') as T';
      generalize dependent t; generalize dependent t'.
      induction H; intros; subst.
      + destruct (IHktrans_ _ HeqT' _ eq_refl) as (l & TR & Hl). 
        exists l; split...
        apply trans_guard...
      + exists tau; split... 
        apply trans_br with (x:=i).
        now symmetry. 
      + exists (obs e v); split.
        * econstructor; now symmetry.
        * right; left.
          exists e, v...
      + exists (val x); rewrite H; split.
        * now econstructor.
        * right; right; left.
          exists x; intuition.
          transitivity t...
          step; cbn; rewrite HeqT'; reflexivity.
      + exists (val x); rewrite H; split; auto.
        * now econstructor.
        * right; right; right.
          exists e, v, x; intuition.
          transitivity t...
          step; cbn; rewrite HeqT'; reflexivity.
    - destruct H as (l & ? & Hl);
      remember (observe t) as T; remember (observe t') as T';
        generalize dependent t; generalize dependent t'; revert w w'.
      induction H; intros; subst.
      + apply KtransGuard...
      + destruct Hl as [ (? & ? & ?) |
             [(e & x' & ? & ? & ?) |
               [(x' & ? & ? & Ht & ?) |
                 (e & v & x' & ? & ? & Ht & ?)]]];
          subst; inv H0.
        apply KtransBr with x... 
        now symmetry.
      + destruct Hl as [ (? & ? & ?) |
             [(e' & x' & ? & ? & ?) |
               [(x' & ? & ? & Ht & ?) |
                 (e' & v & x' & ? & ? & Ht & ?)]]]; subst;
          dependent destruction H0.
        apply KtransObs; auto.
        now symmetry.
      + destruct Hl as [ (? & ? & ?) |
             [(e' & x' & ? & ? & ?) |
               [(x' & ? & ? & Ht & ?) |
                 (e' & v & x' & ? & ? & Ht & ?)]]]; subst;
          dependent destruction H0.
        * apply KtransDone.
          transitivity t'; auto.
          step; cbn; rewrite HeqT'; reflexivity.
        * apply KtransFinish.
          transitivity t'; auto.
          step; cbn; rewrite HeqT'; reflexivity.
  Qed.

  (* Here I define two setoid instaces, one for [equ eq]
     and one for [sbisim eq]. Even though [equ eq] is a subrelation
     of [sbisim eq], I had to delete the subrelation instance and
     duplicate here because instance resolution became extremely slow. *)
  Global Instance KripkeSetoidEqu {X}:
    @KripkeSetoid (ctree E) E HE ctree_kripke X (equ eq) _.
  Proof.    
    repeat red; intros.
    rewrite H in H0.
    exists s'; intuition.
  Qed.

  Local Open Scope ctl_scope.
  Lemma ktrans_guard{X}: forall (t t': ctree E X) w w',
      [Guard t, w] ↦ [t', w'] <-> [t, w] ↦ [t', w'].
  Proof.
    split; intro H.
    - cbn in H; dependent induction H; cbn in *.
      now rewrite <- x.
    - cbn in *.
      now econstructor.
  Qed.
  Hint Resolve ktrans_guard: ctl.
  
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
  Hint Resolve ktrans_br: ctl.
  
  Lemma ktrans_done {X}: forall (t: ctree E X) (w': World E) x,
      [Ret x, Pure] ↦ [t, w'] <-> (w' = Done x /\ t ≅ stuck).
  Proof.
    intros; split; intros.
    - cbn in H; dependent destruction H; split; auto.
      step; cbn; rewrite <- x; step in H; cbn in H; auto.
    - destruct H as (-> & ->); constructor.
      reflexivity. 
  Qed.
  Hint Resolve ktrans_done: ctl.
  
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
  Hint Resolve ktrans_finish: ctl.
  
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
  Hint Resolve ktrans_vis: ctl.
  
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
  Hint Resolve done_not_ktrans: ctl.
  
  Lemma ktrans_done_inv{X}: forall (t t': ctree E X) (x: X) w,
      ~ [t, Done x] ↦ [t', w].
  Proof.
    intros * Hcontra; cbn in Hcontra; dependent induction Hcontra; eauto; inv H.
  Qed.
  Hint Resolve ktrans_done_inv: ctl.
  
  Lemma ktrans_finish_inv{X}: forall (t t': ctree E X) (e: E) (v: encode e) (x: X) w,
      ~ [t, Finish e v x] ↦ [t', w].
  Proof.
    intros * Hcontra; cbn in Hcontra; dependent induction Hcontra; eauto; inv H.
  Qed.
  Hint Resolve ktrans_finish_inv: ctl.
  
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
  Hint Resolve ktrans_to_done_inv: ctl.
  
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
  Hint Resolve ktrans_to_finish_inv: ctl.
  
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
      done_eq Y y w_ ->
      [k y, w] ↦ [u, w'] ->
      [y <- t ;; k y, w] ↦ [u, w'].
  Proof.
    intros.
    generalize dependent y.
    cbn in H; dependent induction H; intros.
    - assert(Hx: t ≅ Guard t0) by (step; cbn; rewrite <- x0; reflexivity).
      rewrite Hx.
      rewrite bind_guard.
      econstructor.
      eapply IHktrans_; eauto.
    - inv H1; inv H.
    - inv H1.
    - dependent destruction H0.
      observe_equ x1.
      rewrite Eqt.
      now rewrite bind_ret_l.
    - dependent destruction H0.
      observe_equ x1.
      setoid_rewrite Eqt.
      now rewrite bind_ret_l.
  Qed.      
  Typeclasses Opaque equ.
  
  Opaque Ctree.stuck.  
  Lemma ktrans_bind_inv_aux {X Y} (w w': World E)(T U: ctree' E Y) :
    ktrans_ T w U w' ->
    forall (t: ctree E X) (k: X -> ctree E Y) (u: ctree E Y),
      go T ≅ t >>= k ->
      go U ≅ u ->
      (* [t] steps, [t>>=k] steps *)
      (exists t', [t, w] ↦ [t', w']        
             /\ not_done w'
             /\ u ≅ x <- t' ;; k x) \/
        (* [t] returns [x], [t>>=k] steps if [k x] steps *)
        (exists y w_, [t, w] ↦ [stuck, w_]
                 /\ done_eq X y w_
                 /\ [k y, w] ↦ [u, w']).
  Proof with (auto with ctl).
    intros TR.
    dependent induction TR; intros.
    - rewrite unfold_bind in H; unfold ktrans; cbn;
        desobs t0; observe_equ Heqt.
      + right.
        pose proof (ktrans_not_done (X:=Y) t t' w w' TR) as Hw.
        inv Hw; exists x.        
        * exists (Done x). 
          split; [|split]...
          rewrite <- H, <- H0; cbn; now apply KtransGuard.
        * exists (Finish e v x). 
          split; [|split]... 
          rewrite <- H, <- H0; cbn; now apply KtransGuard.
      + step in H; inv H.
      + pose proof (equ_guard_invE H).
        rewrite ctree_eta in H1.
        destruct (IHTR _ _ _ H1 H0)
          as [(t2 & TR2 & Hd & Eq2) |
               (x & w_ & TRr & ? & TRk)].
        * left.
          exists t2; split; [|split]... 
        * right.
          inv H2.
          -- exists x0, (Done x0); split...
          -- exists x0, (Finish e v x0); split...
      + step in H; inv H.
    - rewrite unfold_bind in H1; unfold ktrans; cbn; desobs t0; observe_equ Heqt.
      + right; inv H.
        * exists x, (Done x).
          split; [|split]... 
          rewrite <- H1; cbn; apply KtransBr with i... 
          rewrite <- ctree_eta in H2.
          transitivity t; [symmetry|]... 
        * exists x, (Finish e v x). 
          split; [|split]... 
          rewrite <- H1; cbn; apply KtransBr with i... 
          rewrite <- ctree_eta in H2.
          transitivity t; [symmetry|]... 
      + left.
        pose proof (equ_br_invT H1); subst. 
        eapply equ_br_invE with i in H1.
        exists (k1 i); split; [|split]... 
        * apply KtransBr with i...
        * rewrite <- H2, <- H1.
          now rewrite <- ctree_eta.
      + step in H1; inv H1.
      + step in H1; inv H1.
    - rewrite unfold_bind in H1; unfold ktrans; cbn; desobs t0; observe_equ Heqt.
      + right; inv H.
        * exists x, (Done x).
          split; [|split]... 
          rewrite <- H1; cbn; apply KtransObs... 
          rewrite <- ctree_eta in H2.
          transitivity t; [symmetry|]... 
        * exists x, (Finish e0 v0 x). 
          split; [|split]... 
          rewrite <- H1; cbn; apply KtransObs... 
          rewrite <- ctree_eta in H2.
          transitivity t; [symmetry|]... 
      + step in H1; inv H1.
      + step in H1; inv H1.
      + left.
        pose proof (equ_vis_invT H1) as (_ & <-).
        eapply equ_vis_invE with v in H1.
        exists (k1 v); split; [|split]; auto with ctl.
        rewrite <- H1, <- H2.        
        now rewrite <- ctree_eta.       
    - rewrite unfold_bind in H0; unfold ktrans; cbn;
        desobs t0; observe_equ Heqt.
      + right. 
        exists x0, (Done x0).
        split; [|split]...
        rewrite <- H1, H, <- H0; cbn.
        now apply KtransDone.
      + step in H0; inv H0.
      + step in H0; inv H0.
      + step in H0; inv H0.
    - rewrite unfold_bind in H0; unfold ktrans; cbn;
        desobs t0; observe_equ Heqt.
      + right. 
        exists x0, (Finish e v x0).
        split; [|split]...
        rewrite <- H1, H, <- H0; cbn.
        now apply KtransFinish.
      + step in H0; inv H0.
      + step in H0; inv H0.
      + step in H0; inv H0.
  Qed.

  Lemma ktrans_bind_inv: forall {X Y} (w w': World E)
                           (t: ctree E X) (u: ctree E Y) (k: X -> ctree E Y),
      [x <- t ;; k x, w] ↦ [u, w'] ->
      (exists t', [t, w] ↦ [t', w']
             /\ not_done w'
             /\ u ≅ x <- t' ;; k x) \/
        (* [t] returns [x], [t>>=k] steps if [k x] steps *)
        (exists y w_, [t, w] ↦ [stuck, w_]
                 /\ done_eq X y w_
                 /\ [k y, w] ↦ [u, w']).
  Proof.
    intros * TR.
    eapply ktrans_bind_inv_aux.
    apply TR.
    rewrite <- ctree_eta; reflexivity.
    rewrite <- ctree_eta; reflexivity.
  Qed.
  Hint Resolve ktrans_bind_inv: ctl.
  
End CTreeTrans.

Local Typeclasses Transparent equ.
Local Open Scope ctl_scope.
Lemma ktrans_trigger_inv `{ReSumRet E1 E2}{X}:forall (e: E2) w w' (k: encode (resum e) -> ctree E2 X) (u': ctree E2 X),
      [z <- trigger e ;; k z, w] ↦ [u', w'] ->
      (not_done w /\ exists z, w' = Obs e z /\ u' ≅ k z).
Proof.    
  intros.
  unfold trigger in H3.
  apply ktrans_bind_inv in H3 as
      [(t' & TR & Hd & Hequ) |
        (x & w_ & TRr & ? & TRk)].
  - apply ktrans_vis in TR as (y & ? & ? & ?).
    unfold resum, ReSum_refl, resum_ret, ReSumRet_refl in *; world_inv.
    split; [auto | exists y]; split; [reflexivity|].
    now rewrite <- H4, bind_ret_l in Hequ.
  - apply ktrans_vis in TRr as (y & ? & ? & ?); subst.
    inv H3.
Qed.

Global Hint Constructors
  ktrans_ not_done done_with vis_with: ctl.

Global Hint Resolve
  ktrans_stuck ktrans_br ktrans_vis ktrans_done
  ktrans_done_inv ktrans_finish can_step_not_done
  ktrans_not_done ktrans_finish_inv ktrans_bind_inv
  ktrans_to_done_inv ktrans_to_finish_inv
  ktrans_guard ktrans_pure_pred: ctl.

From CTree Require Import CTree.SBisim.
Local Typeclasses Opaque equ.      
Global Instance KripkeSetoidSBisim{E} {HE: Encode E} {X}:
    @KripkeSetoid (ctree E) E HE ctree_kripke X (sbisim eq) _.
Proof.    
  repeat red; intros.
  apply ktrans_trans in H0 as
      (l & TR &
         [ (? & ? & ?) |
           [(e & x & ? & ? & ?) |
             [(x & ? & ? & Ht & ?) |
               (e & v & x & ? & ? & Ht & ?)]]]); subst;
    destruct (SBisim.sbisim_trans (X:=X) _ _ _ _ eq H TR)
    as (l' & c1' & ? & <- & ?); exists c1'.
  - split; [apply ktrans_trans|auto].
    exists tau; split; auto. 
  - split; [apply ktrans_trans|auto].
    exists (obs e x); split; auto.
    right; left.
    exists e, x; intuition.
  - split; [apply ktrans_trans|auto].
    exists (val x); split; auto.
    right; right; left.
    pose proof trans_val_inv H0.
    exists x; intuition. 
  - split; [apply ktrans_trans|auto].
    exists (val x); split; auto.
    right; right; right.
    pose proof trans_val_inv H0.
    exists e, v, x; intuition.
Defined.
