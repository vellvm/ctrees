(*|
=========================================
Modal logics over ctrees
=========================================
|*)

From ITree Require Import
     Events.State
     CategoryOps.

From CTree Require Import
     Eq
     CTree
     Interp.Par
     FoldStateT.

From Coq Require Import
     Classes.SetoidClass
     Classes.RelationPairs.

Import CTreeNotations.

Set Implicit Arguments.

(* From ctree labels to kripke states *)
Class Handler (E: Type -> Type) (S: Type) := {
    hfold: forall X, E X -> X -> S -> S;
  }.

#[global] Instance Handler_state S: Handler (stateE S) S :=
  {|
    hfold _ e _ s :=
    match e with
    | Put s => s
    | Get _ => s
    end
  |}.

#[global] Instance Handler_par: Handler parE nat := 
  {| hfold _ e _ s := match e with Switch i => i end |}.

(* WHY this loops during instance resolution *)
#[global] Instance Handler_plus{E F: Type -> Type}{S T}
 (h: Handler E S) (g: Handler F T) : Handler (E+'F) (S*T) :=
  {|
    hfold _ ef x '(s,t) := 
    match ef with
    | inl1 e => (h.(hfold) e x s, t)
    | inr1 f => (s, g.(hfold) f x t)
    end
  |}.

Section Kripke.
  Context {E C: Type -> Type} {X S: Type}
          {h: Handler E S} {HasStuck: B0 -< C}.

  (* Kripke state predicates *)
  Notation SP := (ctree E C X -> S -> Prop).
    
  (* Kripke transition given a handler *)
  Variant ktrans: (ctree E C X * S) -> (ctree E C X * S) -> Prop :=
    | kTau (t u: ctree E C X) (s: S):
      trans tau t u ->
      ktrans (t, s) (u, s)
    | kVis (t u: ctree E C X) {Y} (x: Y) (e: E Y) (s: S):
      trans (obs e x) t u ->
      ktrans (t, s) (u, h.(hfold) e x s)
             
    | kRet (t u: ctree E C X) (x: X) (s: S):
      trans (val x) t stuckD ->
      u ≅ Ret x ->
      ktrans (t, s) (u, s).

  Hint Constructors ktrans: core.

  #[global] Instance proper_ktrans_equ:
    Proper (equ eq * eq ==> equ eq * eq ==> iff) ktrans.
  Proof.
    unfold Proper, respectful, impl; cbn.
    intros [t s] [u x] [EQt ?] [t' s'] [u' x'] [EQt' H3]; simpl in *.
    unfold RelCompFun in *; cbn in *; subst.    
    split; intro H; inv H.
    - rewrite EQt, EQt' in H1.
      now apply kTau.
    - rewrite EQt, EQt' in H1.
      now apply kVis.
    - apply kRet with x0; [now rewrite <- EQt | now rewrite <- EQt'].
    - rewrite <- EQt, <- EQt' in H1.
      now apply kTau.
    - rewrite <- EQt, <- EQt' in H1.
      now apply kVis.
    - apply kRet with x0; [now rewrite EQt | now rewrite EQt'].
  Qed.

  Lemma trans_val_sbisim: forall (t u: ctree E C X) (x: X),
      trans (val x) t stuckD ->
      t ~ u ->
      trans (val x) u stuckD.
  Proof.
    intros.    
    unfold trans, transR in H; cbn in H.
    remember (val x).
    induction H; intros; eauto; try solve [inv Heql].
    (* Ah lost [observe t] *)
  Admitted.

  Lemma ktrans_sbisim_l: forall (t1 t2 t1': ctree E C X) s s',
      ktrans (t1,s) (t1',s') ->
      t1 ~ t2 ->
      exists t2', ktrans (t2,s) (t2',s') /\ t1' ~ t2'.
  Proof.
    intros * TR  Hsb.
    inv TR; intros.
    1,2: step in Hsb; apply Hsb in H0 as (l2 & t2' & TR2 & ? & <-); exists t2'; split; eauto.
    exists (Ret x); rewrite H4; split; eauto.
    apply kRet with x; [| reflexivity]. 
    now apply trans_val_sbisim with (u:=t2) in H2.
  Qed.

  (*| Invert [ktrans] |*)
  Ltac shallow_inv_ktrans H := dependent destruction H; try solve [inv H];
                               intuition; unfold trans,transR in H; cbn in H;
                               dependent destruction H;
                               repeat change (CTree.subst ?k ?t) with (CTree.bind t k) in H;
                               repeat lazymatch goal with
                                      | H: ?t |- ?t => exact H
                                      | H: observe ?t = observe ?u |- _ => apply observe_equ_eq in H
                                      end.

  Lemma ktrans_ret: forall x (t t': ctree E C X) s s',
      ktrans (Ret x, s) (t', s') <->
      t' ≅ Ret x /\ s = s'.
  Proof.
    split; intros.
    - shallow_inv_ktrans H.
    - destruct H as (-> & ->); eapply kRet; eauto; econstructor.
  Qed.

  Lemma ktrans_tau_inv: forall c (t': ctree E C X) (k: X -> ctree E C X) s s',
      ktrans (BrS c k, s) (t', s') ->
      exists x, t' ≅ k x /\ s = s'.
  Proof.
    intros.
    shallow_inv_ktrans H.
    exists x0; rewrite <- x; intuition.
  Qed.
  
  Lemma ktrans_tau_goal: forall c x (t': ctree E C X) (k: X -> ctree E C X) s s',
      t' ≅ k x /\ s = s' ->
      ktrans (BrS c k, s) (t', s').
  Proof.
    intros.
    destruct H as (-> & ->).
    apply kTau; econstructor; eauto.
  Qed.

  Lemma ktrans_vis_inv: forall e (t': ctree E C X) (k: X -> ctree E C X) s s',
      ktrans (Vis e k, s) (t', s') ->
      exists x, t' ≅ k x /\ s' = h.(hfold) e x s.
  Proof.
    intros.
    shallow_inv_ktrans H.
    exists x0; rewrite <- x; intuition.
  Qed.
  
  Lemma ktrans_vis_goal: forall e x (t': ctree E C X) (k: X -> ctree E C X) s s',
      t' ≅ k x /\ s' = h.(hfold) e x s ->
      ktrans (Vis e k, s) (t', s').
  Proof.
    intros.
    destruct H as (-> & ->).
    apply kVis; econstructor; eauto.
  Qed.

  Lemma ktrans_trigger_inv: forall {Y: Type} (e: E Y) u (k: Y -> ctree E C X) s s',
      ktrans (trigger e >>= k, s) (u, s') ->
      exists x, u ≅ k x /\ s' = h.(hfold) e x s.
  Proof.
    intros.
    shallow_inv_ktrans H.
    rewrite bind_ret_l in H.
    exists x0.
    rewrite x in H.
    intuition.
  Qed.


End Kripke.

Definition is_ret{E C X}(t: ctree E C X): Prop :=
  exists x, t ≅ Ret x.
  
Lemma ktrans_bind_inv: forall {E C X Y S} `{Handler E S} `{B0 -< C} (s s': S)
                         (t: ctree E C Y) (u: ctree E C X) (k: Y -> ctree E C X),
    ktrans (x <- t ;; k x, s) (u, s') ->
    ~ is_ret t /\ (exists t', ktrans (t, s) (t', s') /\ u ≅ x <- t' ;; k x) \/
      (exists x, ktrans (t, s) (Ret x, s) /\ ktrans (k x, s) (u, s')).
Proof.
  intros.
  inv H1.
  - apply trans_bind_inv in H3 as [(HV & t' & TR & EQu) | (x & TRv & TRu)].
    + left; split.
      * intro CONTRA; destruct CONTRA as (tc & ?);
          rewrite H1 in TR; inversion TR.
      * exists t'; split; auto.
        now apply kTau.
    + right; exists x; split.
      * now apply kRet with x.
      * now apply kTau.
  - apply trans_bind_inv in H3 as [(HV & t' & TR & EQu) | (x' & TRv & TRu)].
    + left; split.
      * intro CONTRA; destruct CONTRA as (tc & ?);
          rewrite H1 in TR; inversion TR.
      * exists t'; split; auto.
        now apply kVis.
    + right; exists x'; split.
      * now apply kRet with x'.
      * now apply kVis.
  - apply trans_bind_inv in H5 as [(HV & t' & TR & EQu) | (x' & TRv & TRu)].
    + now contradiction HV.
    + right; exists x'; split.
      * now apply kRet with x'.
      * rewrite H7.
        now apply kRet with x.
Qed.



