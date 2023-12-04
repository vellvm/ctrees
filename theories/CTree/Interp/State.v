From ExtLib Require Export
  Structures.MonadState
  Data.Monads.StateMonad
  Structures.Monad.

From CTree Require Import
  Classes
  CTree.Core
  CTree.Interp.Core
  Events.Core
  Events.Writer
  CTree.Logic.Trans
  CTree.Events.State
  CTree.Equ.

From Coinduction Require Import
  coinduction.
From Coq Require Import Morphisms.

Import CTreeNotations.
Local Open Scope ctree_scope.

Set Implicit Arguments.
Generalizable All Variables.

(*| Observe 1-to-1 interpretation event-to-state -- [state S] to [stateT S (ctree void)] |*)
Global Instance h_state_stateT {E Σ} (h:E ~> state Σ): E ~> stateT Σ (ctree void) := {
    handler e :=
      mkStateT (fun s => Ret (runState (h.(handler) e) s))
  }.

(*| Intrument any [W] by an observation function [obs] and evaluation [E ~> stateT Σ ctree] |*)
Global Instance h_stateT_writerA {E W Σ}(h:E ~> stateT Σ (ctree void))(obs: Bar E * Σ -> W):
  E ~> stateT Σ (ctree (writerE W)) := {
    handler e :=
      mkStateT (fun s =>
                  '(x, σ) <- resumCtree (runStateT (h.(handler) e) s) ;;
                  Ctree.trigger (Log (obs (Obs e x, σ))) ;;
                  Ret (x, σ))
  }.

(*| Observe states. The [stateT S (ctree void)] to [stateT S (ctree (writerE S))] |*)
Global Instance h_stateT_writerΣ {E Σ} (h:E ~> stateT Σ (ctree void)):
  E ~> stateT Σ (ctree (writerE Σ)) := {
    handler := @handler _ _ (h_stateT_writerA h snd)
  }.

(*| Observe events. The [stateT S (ctree void)] to [stateT S (ctree (Bar E))] |*)
Global Instance h_stateT_writerE {E Σ} (h:E ~> stateT Σ (ctree void)):
  E ~> stateT Σ (ctree (writerE (Bar E))) := {
    handler := @handler _ _ (h_stateT_writerA h fst)
  }.

(*| Lemmas about state |*)
Definition interp_state {E W} `{EF: Encode F} (h : E ~> stateT W (ctree F))
  {X} (t: ctree E X) (w: W) : ctree F (X*W) := runStateT (interp h t) w.

(*| Unfolding of [interp_state] given state [s] *)
Notation interp_state_ h t s :=
  (match observe t with
   | RetF r => Ret (r, s)
   | VisF e k => (runStateT (h.(handler) e) s) >>=
                  (fun '(x, s') => guard (interp_state h (k x) s'))
   | BrF b n k => Br b n (fun xs => guard (interp_state h (k xs) s))
   end)%function.

Lemma unfold_interp_state `{Encode F} `(h: E ~> stateT W (ctree F))
  {X} (t: ctree E X) (w : W) :
  interp_state h t w ≅ interp_state_ h t w.
Proof.
  unfold interp_state.  
  unfold interp, iter, MonadIter_stateT, MonadIter_ctree.
  setoid_rewrite unfold_iter at 1.
  cbn.
  rewrite bind_bind.
  desobs t; cbn.
  - now repeat (cbn; rewrite ?bind_ret_l).
  - unfold mbr, MonadBr_ctree.
    rewrite ?bind_bind, ?bind_branch.
    apply br_equ; intros.
    now cbn; rewrite ?bind_ret_l.
  - rewrite ?bind_bind.
    upto_bind_equ.
    destruct x1 eqn:Hx1.
    rewrite ?bind_ret_l; cbn.
    reflexivity.
Qed.

#[global] Instance equ_interp_state `{Encode F} `(h: E ~> stateT W (ctree F)) {X}:
  Proper (@equ E _ X X eq ==> eq ==> equ eq) (interp_state h).
Proof.
  unfold Proper, respectful.
  coinduction ? IH; intros * EQ1 * <-.
  rewrite !unfold_interp_state.
  step in EQ1; inv EQ1; auto.
  - cbn. upto_bind_equ.
    destruct x1.
    constructor; intros.
    apply IH; auto.
    apply H2.
  - cbn.
    constructor; intros.
    step.
    econstructor; intros FF.
    dependent destruction FF; try inversion FF.
    apply IH; auto.
    apply H2.
Qed.

Lemma interp_state_ret `{Encode F} `(h: E ~> stateT W (ctree F)) {X} (w : W) (r : X) :
  (interp_state h (Ret r) w) ≅ (Ret (r, w)).
Proof.
  rewrite ctree_eta. reflexivity.
Qed.

Lemma interp_state_vis `{Encode F} `(h: E ~> stateT W (ctree F)) {X}  
  (e : E) (k : encode e -> ctree E X) (w : W) :
  interp_state h (Vis e k) w ≅ runStateT (h.(handler) e) w >>=
    (fun '(x, w') => guard (interp_state h (k x) w')).
Proof.
  rewrite unfold_interp_state; reflexivity.
Qed.

Lemma interp_state_br `{Encode F} `(h: E ~> stateT W (ctree F)) {X}
  (n : nat) (k : fin' n -> ctree E X) (w : W) b :
  interp_state h (Br b n k) w ≅ Br b n (fun x => guard (interp_state h (k x) w)).
Proof.
  rewrite !unfold_interp_state; reflexivity.
Qed.
