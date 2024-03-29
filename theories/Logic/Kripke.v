(*|
=========================================
Modal logics over ctrees
=========================================
|*)

From ITree Require Import
     Basics
     Indexed.Sum
     Indexed.Function.

From ExtLib Require Import
     Structures.Monads
     Structures.MonadState
     Data.Monads.StateMonad.

From CTree Require Import
     CTree
     Eq.

From Coq Require Import
     Classes.SetoidClass
     Classes.RelationPairs.

Set Implicit Arguments.

Import MonadNotation.
Local Open Scope monad_scope.

(** A typeclass definition of a handler, used purely to make inference easy *)
Class Handler(E S: Type -> Type): Type :=
  handler: E ~> S.

Notation "E ~~> S" := (Handler E S) (at level 99, right associativity) : type_scope.

(*| Sums of effects give products in [state] |*)
#[global] Instance handler_plus{A B X Y} `{HA: A ~~> state X} `{HB: B ~~> state Y}:
  A +' B ~~> state (X * Y) :=
  fun _ e =>
    '(x,y) <- get ;;
    match e with
    | inl1 e =>
        let (r, x') := runState (handler _ e) x in
        put (x', y) ;;
        ret r
    | inr1 e =>
        let (r, y') := runState (handler _ e) y in
        put (x, y') ;;
        ret r
    end.

(*| Auto-associate products left |*)
#[global] Instance handler_prod_assoc {E A B C }{h: E ~~> state (A * (B * C))}:
  E ~~> state (A * B * C) :=
  fun _ e =>
    '(x, y, z) <- get ;;
    let '(r, (a, (b, c))) := runState (handler _ e) (x, (y, z)) in
    put (a, b ,c) ;;
    ret r.

(*| Invert [ktrans] |*)
Ltac shallow_inv_ktrans H := cbn in H; dependent destruction H; try solve [inv H];
                             intuition; unfold trans,transR in H; cbn in H;
                             dependent destruction H;
                             repeat change (CTree.subst ?k ?t) with (CTree.bind t k) in H;
                             repeat lazymatch goal with
                                    | H: ?t |- ?t => exact H
                                    | H: observe ?t = observe ?u |- _ => apply observe_equ_eq in H
                                    end.

Section Kripke.
  Context {E C: Type -> Type} {X S: Type}
          `{h: E ~~> state S} `{HasStuck: B0 -< C}.
  (* Kripke state predicates *)
  Definition TS : EqType := 
    {| type_of := (ctree E C X * S)%type ; Eq := (equ eq * eq)%signature |}.

  (* Kripke transition given a handler *)
  Variant ktransR: hrel TS TS :=
    | kTau (t u: ctree E C X) (s: S):
      trans tau t u ->
      ktransR (t, s) (u, s)
    | kVis (t u: ctree E C X) {Y} (x: Y) (e: E Y) (s: S):
      trans (obs e x) t u ->
      ktransR (t, s) (u, execState (h e) s)
    | kRet (t u: ctree E C X) (x: X) (s: S):
      trans (val x) t stuckD ->
      u ≅ Ret x ->
      ktransR (t, s) (u, s).

  Hint Constructors ktransR: core.
  
  #[global] Instance proper_ktransR_equ:
    Proper (equ eq * eq ==> equ eq * eq ==> iff) ktransR.
  Proof.
    unfold Proper, respectful, impl; cbn.
    intros [t s] [u x] [EQt ?] [t' s'] [u' x'] [EQt' H3]; simpl in *.
    unfold RelCompFun in *; cbn in *; subst.    
    split; intro H; inv H.
    - rewrite EQt, EQt' in H1.
      now apply kTau.
    - rewrite EQt, EQt' in H1.
      eapply kVis; eauto.
    - apply kRet with x0; [now rewrite <- EQt | now rewrite <- EQt'].
    - rewrite <- EQt, <- EQt' in H1.
      now apply kTau.
    - rewrite <- EQt, <- EQt' in H1.
      eapply kVis; eauto.
    - apply kRet with x0; [now rewrite EQt | now rewrite EQt'].
  Qed.

  Program Definition ktrans: srel TS TS :=
    {| hrel_of '(t, s) '(t',s') := ktransR (t,s) (t',s') |}. 
  Next Obligation.
    destruct H as (HA & HB);
      unfold RelCompFun in HA, HB; cbn in HA, HB.
    destruct H0 as (HA' & HB');
      unfold RelCompFun in HA', HB'; cbn in HA', HB'.
    subst; rewrite HA; rewrite HA'; intuition.
  Qed.

  #[global] Instance proper_ktrans_equ:
    Proper (equ eq * eq ==> equ eq * eq ==> iff) ktrans.
  Proof.
    unfold Proper, respectful, impl; cbn.    
    intros [t s] [u x] [EQt ?] [t' s'] [u' x'] [EQt' H3]; simpl in *.
    apply proper_ktransR_equ; auto.
  Qed.

  (* LEF: Is this true?
  Lemma trans_obs_sbisim {Y}: forall (t t' u: ctree E C X) (e: E Y) (x: Y) (k: Y -> ctree E C X),
      trans (obs e x) t (k x) ->
      t ~ u ->
      exists s, s ~ k x /\ trans (obs e x) u s.
  Proof. Qed.    
   *)

  Lemma ktrans_sbisim_l: forall (t1 t2 t1': ctree E C X) s s',
      ktrans (t1,s) (t1',s') ->
      t1 ~ t2 ->
      exists t2', ktrans (t2,s) (t2',s') /\ t1' ~ t2'.
  Proof.
    intros * TR  Hsb.
    inv TR; intros.
    1,2: step in Hsb; apply Hsb in H0 as (l2 & t2' & TR2 & ? & <-); exists t2'; cbn; split; eauto.
    exists (Ret x); rewrite H4; split; eauto; cbn.
    apply kRet with x; [| reflexivity]. 
    apply trans_val_sbisim with (u:=t2) in H2 as (? & ? & ?); eauto.
    now rewrite H in H0.
  Qed.


  Lemma ktrans_ret: forall x (t t': ctree E C X) s s',
      ktrans (Ret x, s) (t', s') <->
      t' ≅ Ret x /\ s = s'.
  Proof.
    split; intros.
    - shallow_inv_ktrans H.
    - destruct H as (-> & ->); cbn; eapply kRet; eauto; econstructor.
  Qed.

  Lemma ktrans_ret_refl: forall {x s},
      ktrans (Ret x, s) (Ret x, s).
  Proof.
    intros.
    apply ktrans_ret.
    - exact (Ret x).
    - intuition.
  Qed.
    
  Lemma ktrans_tau_inv: forall {Y : Type} (c : C Y) (t': ctree E C X) (k: Y -> ctree E C X) s s',
      ktrans (BrS c k, s) (t', s') ->
      exists x, t' ≅ k x /\ s = s'.
  Proof.
    intros.
    shallow_inv_ktrans H.
    exists x0; rewrite <- x; intuition.
  Qed.

  Lemma ktrans_tau_goal: forall {Y : Type} (c : C Y) x (t': ctree E C X) (k: Y -> ctree E C X) s s',
      t' ≅ k x /\ s = s' ->
      ktrans (BrS c k, s) (t', s').
  Proof.
    intros.
    destruct H as (-> & ->).
    cbn; apply kTau; econstructor; eauto.
  Qed.

  Lemma ktrans_vis_inv: forall {Y: Type} (e: E Y) (t': ctree E C X) (k: Y -> ctree E C X) s s',
      ktrans (Vis e k, s) (t', s') ->
      exists x, t' ≅ k x /\ s' = execState (h e) s.
  Proof.
    intros.
    shallow_inv_ktrans H.
    exists x0; rewrite <- x; intuition.
  Qed.

  Lemma ktrans_vis_goal: forall {Y: Type} (e: E Y) x (t': ctree E C X) (k: Y -> ctree E C X) s s',
      t' ≅ k x /\ s' = execState (h e) s ->
      ktrans (Vis e k, s) (t', s').
  Proof.
    intros.
    destruct H as (-> & ->).
    cbn; eapply kVis; econstructor; eauto.
  Qed.

  Lemma ktrans_trigger_inv: forall {Y: Type} (e: E Y) u (k: Y -> ctree E C X) s s',
      ktrans (trigger e >>= k, s) (u, s') ->
      exists x, u ≅ k x /\ s' = execState (h e) s.
  Proof.
    intros.
    shallow_inv_ktrans H.
    rewrite bind_ret_l in H.
    exists x0.
    rewrite x in H.
    intuition.
  Qed.

  Lemma ktrans_stuck_inv: forall (t: ctree E C X) s s',
      ktrans (stuckD, s) (t, s') -> False.
  Proof.
    intros * CONTRA.
    inv CONTRA.
    - unfold trans,transR in H0; cbn in H0; dependent destruction H0; contradiction.
    - unfold trans,transR in H0; cbn in H0; dependent destruction H0; contradiction.
    - unfold trans,transR in H2; cbn in H2; dependent destruction H2; contradiction.
  Qed.

  Lemma ktrans_steps: forall (t: ctree E C X) s, 
    exists t' s', ktrans (t, s) (t', s').
  Proof.
    intros.
    pose proof (ctree_eta t).
    desobs t.
    -  exists t, s; rewrite H.
       apply ktrans_ret.
       exact t.
       intuition.
    - eexists. 
      exists (execState (h e) s).
      rewrite H.
      eapply ktrans_vis_goal.
      intuition.
    - admit.
      (* TODO: should be straightforward *)
  Admitted.

End Kripke.

Lemma ktrans_bind_inv: forall {E C X Y S} `{h: E ~~> state S} `{B0 -< C} (s s': S)
                         (t: ctree E C Y) (u: ctree E C X) (k: Y -> ctree E C X),
    ktrans (h:=h) (x <- t ;; k x, s) (u, s') ->
    ~ (exists x, t ≅ Ret x) /\ (exists t', ktrans (h:=h) (t, s) (t', s') /\ u ≅ x <- t' ;; k x) \/
      (exists x, ktrans (h:=h) (t, s) (Ret x, s) /\ ktrans (h:=h) (k x, s) (u, s')).
Proof with eauto.
  intros.
  inv H0.
  - apply trans_bind_inv in H2 as [(HV & t' & TR & EQu) | (x & TRv & TRu)].
    + left; split; cbn.
      * intro CONTRA; destruct CONTRA as (tc & ?);
          rewrite H0 in TR; inversion TR.
      * exists t'; split...
        now apply kTau.
    + right; exists x; split; cbn.
      * now apply kRet with x.
      * now apply kTau.
  - apply trans_bind_inv in H2 as [(HV & t' & TR & EQu) | (x' & TRv & TRu)].
    + left; split; cbn.
      * intro CONTRA; destruct CONTRA as (tc & ?);
          rewrite H0 in TR; inversion TR.
      * exists t'; split...
        eapply kVis...
    + right; exists x'; split; cbn.
      * now apply kRet with x'.
      * eapply kVis...
  - apply trans_bind_inv in H4 as [(HV & t' & TR & EQu) | (x' & TRv & TRu)].
    + now contradiction HV.
    + right; exists x'; split; cbn.
      * now apply kRet with x'.
      * rewrite H6.
        now apply kRet with x.
Qed.

(*
Lemma ktrans_forever_goal: forall {E C X Y S} `{h: E ~~> state S} `{B1 -< C} `{B0 -< C}
                             (s s': S) (t t': ctree E C X),
    ktrans (t, s) (t', s') ->
    ktrans (CTree.forever t: ctree E C Y, s) (CTree.forever t', s').
Proof.
Admitted.

Lemma ktrans_forever_inv: forall {E C X Y S} `{h: E ~~> state S} `{B1 -< C} `{B0 -< C}
                            (s s': S) (t: ctree E C X) (t': ctree E C Y),
    ktrans (CTree.forever t: ctree E C Y, s) (t', s') ->
    exists u, ktrans (t, s) (u, s') /\ t' ≅ CTree.forever u.
Proof.
Admitted.
*)
