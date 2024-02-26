From ExtLib Require Export
  Structures.MonadState
  Data.Monads.StateMonad
  Structures.Monad.

From CTree Require Import
  Classes
  CTree.Core
  CTree.Interp.Core
  Events.Core
  CTree.Events.Writer
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
Definition h_state `{Encode E} {Σ} (h:E ~> state Σ):
  E ~> stateT Σ (ctree void) :=
  fun e => mkStateT (fun s => Ret (runState (h e) s)).

(*| Intrument by an evaluation [E ~> stateT Σ ctree] and observation function [obs] |*)
Definition h_writerA `{Encode E} {W Σ} (h:E ~> stateT Σ (ctree void))
  (obs: forall (e: E), encode e -> Σ -> option W): E ~> stateT Σ (ctree (writerE W)) :=
  fun e => mkStateT (fun s =>
                    '(x, σ) <- resumCtree (runStateT (h e) s) ;;
                    match obs e x σ with
                    | Some v => Ctree.trigger (Log v);; Ret (x, σ)
                    | None => Ret (x, σ)
                    end).

(*| Observe all states. The [stateT S (ctree void)] to [stateT S (ctree (writerE S))] |*)
Definition h_writerΣ `{Encode E} {Σ} (h:E ~> stateT Σ (ctree void)):
  E ~> stateT Σ (ctree (writerE Σ)) :=
  h_writerA h (fun _ _ s => Some s).

(*| Lemmas about state |*)
Definition interp_state `{Encode E} `{Encode F} {W}
  (h : E ~> stateT W (ctree F)) {X} (t: ctree E X) (w: W) :
  ctree F (X*W) := runStateT (interp h t) w.

(*| Unfolding of [interp_state] given state [s] *)
Notation interp_state_ h t s :=
  (match observe t with
   | RetF r => Ret (r, s)
   | VisF e k => (runStateT (h e) s) >>=
                  (fun '(x, s') => Tau (interp_state h (k x) s'))
   | TauF t => Tau (interp_state h t s)
   | BrF n k => Br n (fun xs => Tau (interp_state h (k xs) s))
   end)%function.

Lemma unfold_interp_state `{Encode E} `{Encode F} `(h: E ~> stateT W (ctree F))
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
  - rewrite ?bind_bind, ?bind_ret_l; cbn.
    reflexivity.
  - rewrite ?bind_bind.
    upto_bind_equ.
    destruct x1 eqn:Hx1.
    rewrite ?bind_ret_l; cbn.
    reflexivity.
Qed.

#[global] Instance equ_interp_state `{Encode E} `{Encode F} W (h: E ~> stateT W (ctree F)) {X}:
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
    apply H3.
  - cbn.
    constructor; intros.
    apply IH; auto.
  - cbn.
    constructor.
    intros i.
    step.
    econstructor.
    apply IH; auto.
    apply H3.
Qed.

Lemma interp_state_ret `{Encode E} `{Encode F} W (h: E ~> stateT W (ctree F)) {X} (w : W) (r : X) :
  (interp_state h (Ret r) w) ≅ (Ret (r, w)).
Proof.
  rewrite ctree_eta. reflexivity.
Qed.

Lemma interp_state_vis `{Encode E} `{Encode F} `(h: E ~> stateT W (ctree F)) {X}  
  (e : E) (k : encode e -> ctree E X) (w : W) :
  interp_state h (Vis e k) w ≅ runStateT (h e) w >>=
    (fun '(x, w') => Tau (interp_state h (k x) w')).
Proof.
  rewrite unfold_interp_state; reflexivity.
Qed.

Lemma interp_state_trigger `{Encode E} `{Encode F} `(h: E ~> stateT W (ctree F)) (e : E) (w : W) :
  interp_state h (Ctree.trigger e) w ≅ runStateT (h (resum e)) w >>= fun x => Tau (Ret x).
Proof.
  unfold Ctree.trigger.
  rewrite interp_state_vis.
  upto_bind_equ.
  destruct x1.
  step; constructor.
  rewrite interp_state_ret.
  reflexivity.
Qed.  

Lemma interp_state_br `{Encode E} `{Encode F} `(h: E ~> stateT W (ctree F)) {X}
  (n : nat) (k : fin' n -> ctree E X) (w : W) :
  interp_state h (Br n k) w ≅ Br n (fun x => Tau (interp_state h (k x) w)).
Proof. rewrite !unfold_interp_state; reflexivity. Qed.

Lemma interp_state_tau `{Encode E} `{Encode F} `(h: E ~> stateT W (ctree F)) {X}
  (t : ctree E X) (w : W) :
  interp_state h (Tau t) w ≅ Tau ((interp_state h t w)).
Proof. rewrite !unfold_interp_state; reflexivity. Qed.

Lemma interp_state_ret_inv `{Encode E} `{Encode F}
  `(h: E ~> stateT W (ctree F)) {X}: forall s (t : ctree E X) r,
    interp_state h t s ≅ Ret r -> t ≅ Ret (fst r) /\ s = snd r.
Proof.
  intros.
  setoid_rewrite (ctree_eta t) in H1.
  setoid_rewrite (ctree_eta t).
  destruct (observe t) eqn:?.
  - rewrite interp_state_ret in H1. step in H1. inv H1. split; reflexivity.
  - rewrite interp_state_br in H1. step in H1. inv H1.
  - rewrite interp_state_tau in H1. step in H1. inv H1.
  - rewrite interp_state_vis in H1. apply ret_equ_bind in H1 as (? & ? & ?).
    destruct x.
    step in H2.
    inv H2.
Qed.

Arguments interp_state: simpl never.
Local Typeclasses Transparent equ.
Lemma interp_state_bind `{Encode E} `{Encode F} `(h : E ~> stateT W (ctree F))
  {A B} (t : ctree E A) (k : A -> ctree E B) (s : W) :
  interp_state h (t >>= k) s ≅ interp_state h t s >>= fun '(x, s) => interp_state h (k x) s.
Proof.
  revert s t.
  coinduction ? IH; intros.
  rewrite (ctree_eta t).
  rewrite unfold_bind, unfold_interp_state.
  destruct (observe t) eqn:Hobs; cbn.
  - rewrite interp_state_ret, bind_ret_l.
    cbn.
    rewrite unfold_interp_state.
    reflexivity.
  - rewrite interp_state_br.
    rewrite bind_br.
    setoid_rewrite bind_guard.
    constructor; intro i.
    step; econstructor; intros.
    apply IH.
  - rewrite interp_state_tau.
    rewrite bind_tau.
    constructor.
    apply IH.
  - rewrite interp_state_vis, bind_bind.
    upto_bind_equ; destruct x.
    rewrite bind_tau.
    constructor.
    apply IH.
Qed.

Lemma interp_state_unfold_iter `{Encode E} `{Encode F}
  `(h : E ~> stateT W (ctree F)) {I R}
  (k : I -> ctree E (I + R)) (i: I) (s: W) :
  interp_state h (Ctree.iter k i) s ≅ interp_state h (k i) s >>= fun '(x, s) =>
      match x with
      | inl l => Tau (interp_state h (iter k l) s)
      | inr r => Ret (r, s)
      end.
Proof.
  Opaque interp_state.
  setoid_rewrite unfold_iter.
  rewrite interp_state_bind.
  upto_bind_equ.
  unfold iter, MonadIter_ctree. 
  destruct x1 as [[l | r] s'].
  - rewrite interp_state_tau.
    reflexivity.
  - rewrite interp_state_ret.
    reflexivity.
Qed.

