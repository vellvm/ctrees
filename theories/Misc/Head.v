(*|
============================
Scheduling head of [ctree]s
============================
It is sometimes useful to compute the set of transition that a process
can perform.
From the traditional perspective of a LTS, this corresponds
to computing all possible finite trees justifying a transition.
From the perspective of [ctree]s, it corresponds to prefix of the
tree only made of invisible br nodes.
We develop in this file the [head] function to compute this prefix.

.. coq:: none
|*)

From ITree Require Import Core.Subevent.
From CTree Require Import
	CTree Eq.

Import CTree.
Import CTreeNotations.
Open Scope ctree_scope.

Set Implicit Arguments.
Set Contextual Implicit.

(*|
The [haction] computation is itself a tree. The values it computes is
the set of possible transition, i.e. enough data to recover the next label
and process.
The [haction] data structure captures trivially this data.
.. coq::
|*)

Variant haction {E B X} :=
	| ARet    (r : X)
	| AStep   (t : ctree E B X)
	| AVis    (Y : Type) (e : E Y) (k : Y -> ctree E B X).


(*|
The [head] computation simply scrolls the tree until it reaches
a visible node.
The resulting ctree does not contain any Vis node, thus its unconstrained
event signature.
Notice that this computation may loop if the original computation
admits a infinite branch of invisible brs.
|*)
Definition head {E F B C X} `{HasB: B -< C} : ctree E B X -> ctree F C (@haction E B X) :=
  cofix head (t : ctree E B X) :=
    match observe t with
    | RetF x          => Ret (ARet x)
    | StuckF          => Stuck
    | StepF t         => Ret (AStep t)
    | GuardF t        => Guard (head t)
    | VisF e k        => Ret (AVis e k)
    | BrF c k         => br c (fun x => head (k x))
    end.

Notation head_ t :=
  match observe t with
    | RetF x          => Ret (ARet x)
    | StuckF          => Stuck
    | StepF t         => Ret (AStep t)
    | GuardF t        => Guard (head t)
    | VisF e k        => Ret (AVis e k)
    | BrF c k         => br c (fun x => head (k x))
  end.

Lemma unfold_head {E F B C X} `{HasB: B -< C} : forall (t : ctree E B X),
    (head t : ctree F C _) ≅ head_ t.
Proof.
  intros.
  now step.
Qed.

Unset Universe Checking.

Section trans_head.

Context {E F B C : Type -> Type} {X : Type}.
Context `{B -< C}.

(*|
Transitions in a tree can always be reflected in their head-tree.
The exact shape of the lemma depends on the nature of the transition.
We wrap them together in [trans_head].
|*)
Lemma trans_head_obs {Y} : forall (t u : ctree E B X) (e : E Y) v,
    trans (obs e v) t u ->
    exists (k : Y -> ctree E B X),
      trans (val (AVis e k)) (head t : ctree F C _) Stuck /\ u ≅ k v.
Proof.
  intros * TR.
  remember (obs e v) as ob.
  setoid_rewrite (ctree_eta u).
  setoid_rewrite unfold_head.
  induction TR; try now inv Heqob.
  - destruct IHTR as (kf & IHTR & EQ); auto.
    exists kf; split; [| exact EQ].
    rename x into y.
    rewrite <- unfold_head in IHTR.
    eapply trans_br with (x := y).
    apply IHTR.
    reflexivity.
  - destruct IHTR as (kf & IHTR & EQ); auto.
    exists kf; split; [| exact EQ].
    rewrite <- unfold_head in IHTR.
    eapply trans_guard.
    apply IHTR.
  - dependent induction Heqob.
    exists k; split.
    constructor.
    rewrite <- ctree_eta; symmetry; assumption.
Qed.

Lemma trans_head_obs_void : forall (t u : ctree E B X) (e : E void),
    ~ trans (obs_void e) t u.
Proof.
  intros * TR.
  remember (obs_void e) as ob.
  induction TR; try now inv Heqob.
Qed.

Lemma trans_head_tau :
  forall (t u : ctree E B X),
    trans τ t u ->
    exists u',
      trans (val (AStep u')) (head t : ctree F C _) Stuck /\ u' ≅ u.
Proof.
  intros * TR.
  remember τ as ob.
  setoid_rewrite (ctree_eta u).
  setoid_rewrite unfold_head.
  induction TR; try now inv Heqob; subst.
  - destruct IHTR as (u' & IHTR & EQ); auto.
    exists u'. split; auto.
    rename x into y.
    rewrite <- unfold_head in IHTR.
    eapply trans_br with (x := y); auto.
    apply IHTR.
  - destruct IHTR as (u' & IHTR & EQ); auto.
    exists u'. split; auto.
    rewrite <- unfold_head in IHTR.
    eapply trans_guard.
    apply IHTR; auto.
  - exists t0. split. apply trans_ret.
    rewrite <- ctree_eta; symmetry; assumption.
Qed.

Lemma trans_head_ret :
  forall (t u : ctree E B X) (v : X),
    trans (val v) t u ->
    trans (val (@ARet E B X v)) (head t : ctree F C _) Stuck /\ u ≅ Stuck.
Proof.
  intros * TR.
  unfold trans in *.
  remember (val v) as ob.
  setoid_rewrite (ctree_eta u).
  setoid_rewrite unfold_head.
  induction TR; try now inv Heqob; subst.
  - destruct IHTR as (IHTR & EQ); auto.
    split; [| exact EQ].
    rewrite <- unfold_head in IHTR.
    rename x into y.
    eapply trans_br with (x := y).
    apply IHTR.
    reflexivity.
  - destruct IHTR as (IHTR & EQ); auto.
    split; [| exact EQ].
    rewrite <- unfold_head in IHTR.
    eapply trans_guard.
    apply IHTR.
  - dependent induction Heqob.
    split.
    constructor.
    reflexivity.
Qed.

Lemma trans_head : forall (t u : ctree E B X) l,
    trans l t u ->
    match l with
    | τ => exists (u' : ctree E B X),
        trans (val (AStep u')) (head t : ctree F C _) Stuck /\ u' ≅ u
    | obs e v => exists (k : _ -> ctree E B X),
        trans (val (AVis e k)) (head t : ctree F C _) Stuck /\ u ≅ k v
    | obs_void e => False
    | val v => trans (val (@ARet E B _ v)) (head t : ctree F C _) Stuck /\ u ≅ Stuck
    end.
Proof.
  intros *; destruct l.
  apply trans_head_tau.
  apply trans_head_obs.
  apply trans_head_obs_void.
  intros A.
  pose proof (trans_val_invT A) as <-; apply trans_head_ret; assumption.
Qed.

(*|
The only transitions that the head-tree can take are value ones.
|*)
Lemma trans_head_inv : forall (P : ctree E B X) l u,
    trans l (head P : ctree F C _) u ->
    is_val l.
Proof.
  intros * TR.
  remember (head P) as AP.
  eq2equ HeqAP.
  rewrite ctree_eta in EQ.
  revert P EQ.
  induction TR; intros; subst.
  - rewrite unfold_head in EQ.
    desobs P; try now (step in EQ; inv EQ).
    step in EQ. destruct (equb_br_invT _ _ _ _ EQ).
    eapply equb_br_invE in EQ as [].
    setoid_rewrite <- ctree_eta in IHTR.
    eapply IHTR; eauto.
  - rewrite unfold_head in EQ.
    desobs P; try now (step in EQ; inv EQ).
    apply equ_guard_inv in EQ.
    rewrite (ctree_eta t) in EQ.
    now apply IHTR in EQ.
  - exfalso.
    rewrite unfold_head in EQ.
    desobs P; step in EQ; inv EQ.
  - exfalso.
    rewrite unfold_head in EQ.
    desobs P; step in EQ; inv EQ.
  - constructor.
Qed.

Lemma trans_ARet :
  forall r (p: ctree E B X) q,
    trans (val (@ARet E B X r)) (head p : ctree F C _) q ->
    trans (val r) p Stuck.
Proof.
  intros * TR.
  remember (head p) as Ap.
  remember (val (ARet r)) as l.
  eq2equ HeqAp.
  rewrite ctree_eta in EQ.
  revert p EQ r Heql.
  induction TR; intros; subst; try now inv Heql.
  - rewrite unfold_head in EQ.
    unfold trans.
    cbn; red.
    desobs p; try now (step in EQ; inv EQ).
    step in EQ; destruct (equb_br_invT _ _ _ _ EQ).
    setoid_rewrite <- ctree_eta in IHTR.
    econstructor.
    apply IHTR; eauto.
    now apply equb_br_invE in EQ.
  - rewrite unfold_head in EQ.
    unfold trans.
    cbn; red.
    desobs p; try now (step in EQ; inv EQ).
    apply equ_guard_inv in EQ.
    setoid_rewrite <- ctree_eta in IHTR.
    econstructor.
    apply IHTR; eauto.
  - unfold trans.
    apply val_eq_inv in Heql; inv Heql.
    rewrite unfold_head in EQ.
    cbn; red.
    desobs p; try now (step in EQ; inv EQ).
    step in EQ; inv EQ. inv REL; constructor.
Qed.

Lemma trans_ABr :
  forall u (p: ctree E B X) q,
    trans (val (AStep u)) (head p : ctree F C _) q ->
    trans τ p u.
Proof.
  intros * TR.
  remember (head p) as Hp.
  remember (val (AStep u)) as l.
  eq2equ HeqHp.
  rewrite ctree_eta in EQ.
  revert p EQ u Heql.
  induction TR; intros; subst; try now inv Heql.
  - rewrite unfold_head in EQ.
    unfold trans.
    cbn; red.
    desobs p; try now (step in EQ; inv EQ).
    step in EQ; destruct (equb_br_invT _ _ _ _ EQ).
    eapply equb_br_invE in EQ as [].
    setoid_rewrite <- ctree_eta in IHTR.
    econstructor.
    apply IHTR; eauto.
  - rewrite unfold_head in EQ.
    unfold trans.
    cbn; red.
    desobs p; try now (step in EQ; inv EQ).
    apply equ_guard_inv in EQ.
    setoid_rewrite <- ctree_eta in IHTR.
    econstructor.
    apply IHTR; eauto.
  - apply val_eq_inv in Heql; inv Heql.
    rewrite unfold_head in EQ.
    unfold trans.
    cbn; red.
    desobs p; inv_equ.
    inv EQ. apply trans_step.
Qed.

Lemma trans_AVis :
  forall {Y} (e : E Y) (p: ctree E B X) (k : Y -> ctree E B X) q,
    trans (val (AVis e k)) (head p : ctree F C _) q ->
    forall i, trans (obs e i) p (k i).
Proof.
  intros * TR.
  remember (head p) as Ap.
  remember (val (AVis e k)) as l.
  eq2equ HeqAp.
  rewrite ctree_eta in EQ.
  revert p EQ k Heql.
  induction TR; intros; subst; try now inv Heql.
  - rewrite unfold_head in EQ.
    unfold trans.
    cbn; red.
    desobs p; try now (step in EQ; inv EQ).
    step in EQ; destruct (equb_br_invT _ _ _ _ EQ).
    eapply equb_br_invE in EQ as [].
    setoid_rewrite <- ctree_eta in IHTR.
    econstructor.
    apply IHTR; eauto.
  - rewrite unfold_head in EQ.
    unfold trans.
    cbn; red.
    desobs p; try now (step in EQ; inv EQ).
    apply equ_guard_inv in EQ.
    setoid_rewrite <- ctree_eta in IHTR.
    econstructor.
    apply IHTR; eauto.
  - apply val_eq_inv in Heql; inv Heql.
    rewrite unfold_head in EQ.
    unfold trans.
    cbn; red.
    desobs p; try now (step in EQ; inv EQ).
    step in EQ; inv EQ.
    dependent induction REL.
    constructor; reflexivity.
Qed.

End trans_head.

(*|
[head] is a computation computing computations. It's therefore not as
well-behaved w.r.t. to [equ] as usual: rewriting [equ eq] leads to [equ eq_haction]
computations, where [eq_haction] propagates [equ] to the computations contained in the
actions.
|*)
Variant eq_haction {E C R} : @haction E C R -> haction -> Prop :=
| eq_haction_ret : forall r, eq_haction (ARet r) (ARet r)
| eq_haction_br : forall t u,
    t ≅ u ->
    eq_haction (AStep t) (AStep u)
| eq_haction_vis : forall X (e : E X) k1 k2,
    (forall x, k1 x ≅ k2 x) ->
    eq_haction (AVis e k1) (AVis e k2).

#[global] Instance eq_haction_equiv {E C R} : Equivalence (@eq_haction E C R).
Proof.
  split.
  - intros []; constructor; auto.
  - intros x y xy.
    dependent destruction xy; constructor; intros; symmetry; auto.
  - intros x y z xy yz.
    dependent destruction xy;
      dependent destruction yz.
    constructor.
    constructor; intros; rewrite H; auto.
    constructor; intros; rewrite H; auto.
Qed.

#[global] Instance head_equ {E F B C X} `{HasB: B -< C} :
  Proper (equ eq ==> equ (eq_haction)) (@head E F B C X _).
Proof.
  unfold Proper, respectful.
  coinduction S CIH.
  intros.
  rewrite 2 unfold_head.
  step in H.
  inv H; repeat constructor; auto.
Qed.

Definition run_haction {E C X} (hd : @haction E C X) : ctree E C X :=
  match hd with
  | ARet r => Ret r
  | AStep t => Step t
  | AVis e k => Vis e k
  end.

Lemma get_run_haction {E C X} : forall (t : ctree E C X),
    t ≅ head t >>= run_haction.
Proof.
  coinduction r cih.
  intros t.
  rewrite (ctree_eta t) at 1.
  rewrite unfold_head.
  desobs t.
  - rewrite bind_ret_l; reflexivity.
  - rewrite bind_stuck; reflexivity.
  - rewrite bind_ret_l; reflexivity.
  - rewrite bind_guard. constructor. apply cih.
  - rewrite bind_ret_l; reflexivity.
  - rewrite bind_br. constructor.
    intros. apply cih.
Qed.
