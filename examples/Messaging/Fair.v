From ITree Require Import
     Basics
     Subevent
     Events.State
     Indexed.Sum.

From ExtLib Require Import
     Data.Monads.StateMonad
     Structures.MonadState.

From Coq Require Import
     Nat
     Vector.

From Equations Require Import Equations.

From Coinduction Require Import
     coinduction rel tactics.

From CTree Require Import
     CTree
     Eq
     Interp.Preempt
     Interp.Network
     Misc.Vectors
     Logic.Kripke
     Logic.Ctl.

Import CTreeNotations VectorNotations CtlNotations.
Local Open Scope ctree_scope.
Local Open Scope ctl_scope.
Local Open Scope vector_scope.

Set Implicit Arguments.

From Coq Require Import Arith.Compare micromega.Lia.
Check rr'.

Lemma eventually_rr{C : Type -> Type} {X Σ: Type} (n: nat) {s: Σ}
      `{HasStuck: B0 -< C} `{HasTau: B1 -< C}:
  forall (l: vec n (ctree parE C X)) (id: nat),
    id < n ->
    <( {rr' l}, 0 |= AF (now {fun i => i = id}))>.
Proof.
  intros.
  induction n.
  - inv H.
  - dependent destruction l.
    assert(forall m n, m < S n -> m = n \/ m < n) by lia.
    destruct (H0 id n H); clear H0.
    + (* id = n *)
      simp rr'.
      subst.
      unfold preempt.
      rewrite bind_trigger.
      rewrite bind_vis.
      next; right; next.
      intros t' s' TR.
      apply ktrans_vis_inv in TR as ([] & -> & ->).
      Opaque entailsF.
      Opaque take.
      cbn.
      next.
      left.
      auto.
    + simp rr'.
      unfold preempt.
      rewrite bind_trigger, bind_vis.
      next;right; next.
      intros t' s' TR.
      apply ktrans_vis_inv in TR as ([] & -> & ->).
      clear t'.
      
      apply ktrans_trigger_inv in 
    next.
    cbn.
    
(* Fairness proof for [rr] *)
Lemma fair_rr{E C : Type -> Type} {X S: Type} (n: nat) {s: S}
      `{HasStuck: B0 -< C} `{HasTau: B1 -< C} `{Par: parE -< E}
      `{h: E ~~> state (S * nat)}: forall (l: vec n (ctree E C X)) (id: nat),
    id < n ->
    <( {rr l: ctree E C (vec n (ctree E C X))}, {(s,0)} |= AG (AF (now {fun '(_,i) => i = id})))>.
  Proof.
    intros sys i Hid; unfold rr.
    unfold entailsF; coinduction R CIH.
    induction sys.
    - inv Hid.
    - 
    apply RStepA.
    apply MatchA; auto.
    intros.
