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
Lemma trans_head_ask {Y} : forall (t : ctree E B X) (e : E Y) (u : S E B X),
    trans (ask e) t u ->
    exists (k : Y -> ctree E B X),
      trans (val (AVis e k)) (head t : ctree F C _) Stuck /\ u ⩸ (β e k).
Proof.
  intros t e u TR.
  enough (G : forall t0, t0 ≅ t -> exists k, trans (val (AVis e k)) (head t0 : ctree F C _) Stuck /\ u ⩸ (β e k))
    by (apply G; reflexivity).
  remember (α t) as st. remember (ask e) as l.
  revert t Heqst Heql.
  hnf in TR; induction TR; intros ? Hs Hl t0 EQ; inv Hs; try discriminate;
    rewrite H0 in EQ; setoid_rewrite unfold_head; rewrite (ctree_eta t0) in EQ;
    desobs t0; try now (step in EQ; inv EQ).
  - destruct (equ_br_invT _ _ _ _ EQ). apply equ_br_invE in EQ as [-> EQ].
    edestruct (IHTR t' eq_refl eq_refl (k0 x)) as (k' & TR' & EQ'); [now rewrite H1|].
    exists k'; split; auto. eapply trans_br with (y := x). exact TR'.
  - apply equ_guard_inv in EQ.
    edestruct (IHTR t' eq_refl eq_refl t) as (k' & TR' & EQ'); [exact EQ|].
    exists k'; split; auto.
  - dependent destruction Hl. destruct (equ_vis_invT _ _ _ _ EQ). apply equ_vis_invE in EQ as [-> EQ].
    exists k0; split; [apply trans_ret | constructor; intros; now rewrite EQ].
Qed.

Lemma trans_head_tau :
  forall (t u : ctree E B X),
    trans τ t u ->
    exists u',
      trans (val (AStep u')) (head t : ctree F C _) Stuck /\ u' ≅ u.
Proof.
  intros t u TR.
  enough (G : forall t0, t0 ≅ t -> exists u', trans (val (AStep u')) (head t0 : ctree F C _) Stuck /\ u' ≅ u)
    by (apply G; reflexivity).
  remember (α t) as st. remember (α u) as su. remember τ as l.
  revert t u Heqst Heqsu Heql.
  hnf in TR; induction TR; intros ? ? Hs Hu Hl t0 EQ; inv Hs; try discriminate;
    rewrite H0 in EQ; setoid_rewrite unfold_head; rewrite (ctree_eta t0) in EQ;
    desobs t0; try now (step in EQ; inv EQ).
  - destruct (equ_br_invT _ _ _ _ EQ). apply equ_br_invE in EQ as [-> EQ].
    edestruct (IHTR t' u0 eq_refl eq_refl eq_refl (k0 x)) as (u' & TR' & EQ'); [now rewrite H1|].
    exists u'; split; auto. eapply trans_br with (y := x). exact TR'.
  - apply equ_guard_inv in EQ.
    edestruct (IHTR t' u0 eq_refl eq_refl eq_refl t) as (u' & TR' & EQ'); [exact EQ|].
    exists u'; split; auto.
  - apply equ_step_inv in EQ. inv Hu.
    exists t; split; [apply trans_ret | now rewrite EQ].
Qed.

Lemma trans_head_ret :
  forall (t u : ctree E B X) (v : X),
    trans (val v) t u ->
    trans (val (@ARet E B X v)) (head t : ctree F C _) Stuck /\ u ≅ Stuck.
Proof.
  intros t u v TR.
  split; [| now apply trans_val_inv in TR].
  enough (G : forall t0, t0 ≅ t -> trans (val (@ARet E B X v)) (head t0 : ctree F C _) Stuck)
    by (apply G; reflexivity).
  remember (α t) as st. remember (val v) as l.
  revert t Heqst Heql.
  hnf in TR; induction TR; intros ? Hs Hl t0 EQ; inv Hs; try discriminate;
    rewrite H0 in EQ; setoid_rewrite unfold_head; rewrite (ctree_eta t0) in EQ;
    desobs t0; try now (step in EQ; inv EQ).
  - destruct (equ_br_invT _ _ _ _ EQ). apply equ_br_invE in EQ as [-> EQ].
    eapply trans_br with (y := x). eapply IHTR; eauto. now rewrite H1.
  - apply equ_guard_inv in EQ. apply trans_guard. eapply IHTR; eauto.
  - apply val_eq_inv in Hl as ->. apply equ_ret_inv in EQ as ->. apply trans_ret.
Qed.

Lemma trans_head : forall (t : ctree E B X) l (u : S E B X),
    trans l t u ->
    match l with
    | τ       => exists u', trans (val (AStep u')) (head t : ctree F C _) Stuck /\ u ⩸ (α u')
    | ask e   => exists k,  trans (val (AVis e k))  (head t : ctree F C _) Stuck /\ u ⩸ (β e k)
    | rcv _ _ => False
    | val v   => trans (val (ARet v)) (head t : ctree F C _) Stuck /\ u ⩸ (α Stuck)
    end.
Proof.
  intros t [] u TR.
  - refine_trans in TR.
    apply trans_head_tau in TR as (u' & TR & EQ'). exists u'; split; [exact TR | now rewrite EQ'].
  - now apply trans_head_ask.
  - now apply trans_rcv_active_inv in TR.
  - pose proof trans_val_inv' TR as EQ. rewrite EQ in TR |- *.
    split; [now apply trans_head_ret in TR | reflexivity].
Qed.

(*|
The only transitions that the head-tree can take are value ones.
|*)
Lemma trans_head_inv : forall (P : ctree E B X) l u,
    trans l (head P : ctree F C _) u ->
    is_val l.
Proof.
  intros P l u TR.
  enough (G : forall st, trans l st u -> forall (T : ctree F C _) (P : ctree E B X), st = Active T -> T ≅ (head P : ctree F C _) -> is_val l)
    by (eapply G; [exact TR | reflexivity | reflexivity]).
  clear. intros st TR. hnf in TR; induction TR; intros T P Hs EQ; inv Hs; try discriminate;
    rewrite H0, unfold_head in EQ; desobs P; try now (step in EQ; inv EQ).
  - destruct (equ_br_invT _ _ _ _ EQ). apply equ_br_invE in EQ as [_ EQ].
    eapply IHTR; [reflexivity | now rewrite H1].
  - apply equ_guard_inv in EQ. eapply IHTR; [reflexivity | exact EQ].
Qed.

Lemma trans_ARet :
  forall r (p: ctree E B X) q,
    trans (val (@ARet E B X r)) (head p : ctree F C _) q ->
    trans (val r) p Stuck.
Proof.
  intros r p q TR.
  enough (G : forall l st, trans l st q -> forall (T : ctree F C _) p, st = Active T -> T ≅ (head p : ctree F C _) -> l = val (ARet r) -> trans (val r) p Stuck)
    by (eapply G; [exact TR | reflexivity | reflexivity | reflexivity]).
  clear. intros l st TR.
  hnf in TR; induction TR; intros T p Hs EQ Hl; inv Hs; try discriminate;
    rewrite H0, unfold_head in EQ; rewrite (ctree_eta p); desobs p; try now (step in EQ; inv EQ).
  - destruct (equ_br_invT _ _ _ _ EQ). apply equ_br_invE in EQ as [_ EQ].
    eapply trans_br with (y := x). eapply IHTR; [reflexivity | now rewrite H1 | reflexivity].
  - apply equ_guard_inv in EQ. apply trans_guard. eapply IHTR; [reflexivity | exact EQ | reflexivity].
  - apply val_eq_inv in Hl as ->. apply equ_ret_inv in EQ. inv EQ. apply trans_ret.
Qed.

Lemma trans_ABr :
  forall u (p: ctree E B X) q,
    trans (val (AStep u)) (head p : ctree F C _) q ->
    trans τ p u.
Proof.
  intros u p q TR.
  enough (G : forall l st, trans l st q -> forall (T : ctree F C _) p, st = Active T -> T ≅ (head p : ctree F C _) -> l = val (AStep u) -> trans τ p u)
    by (eapply G; [exact TR | reflexivity | reflexivity | reflexivity]).
  clear. intros l st TR.
  hnf in TR; induction TR; intros T p Hs EQ Hl; inv Hs; try discriminate;
    rewrite H0, unfold_head in EQ; rewrite (ctree_eta p); desobs p; try now (step in EQ; inv EQ).
  - destruct (equ_br_invT _ _ _ _ EQ). apply equ_br_invE in EQ as [_ EQ].
    eapply trans_br with (y := x). eapply IHTR; [reflexivity | now rewrite H1 | reflexivity].
  - apply equ_guard_inv in EQ. apply trans_guard. eapply IHTR; [reflexivity | exact EQ | reflexivity].
  - apply val_eq_inv in Hl as ->. apply equ_ret_inv in EQ. inv EQ. apply trans_step.
Qed.

Lemma trans_AVis :
  forall {Y} (e : E Y) (p : ctree E B X) (k : Y -> ctree E B X) q,
    trans (val (AVis e k)) (head p : ctree F C _) q ->
    trans (ask e) p (β e k).
Proof.
  intros Y e p k q TR.
  enough (G : forall l st, trans l st q -> forall (T : ctree F C _) p, st = Active T -> T ≅ (head p : ctree F C _) -> l = val (AVis e k) -> trans (ask e) p (β e k))
    by (eapply G; [exact TR | reflexivity | reflexivity | reflexivity]).
  clear. intros l st TR.
  hnf in TR; induction TR; intros T p Hs EQ Hl; inv Hs; try discriminate;
    rewrite H0, unfold_head in EQ; rewrite (ctree_eta p); desobs p; try now (step in EQ; inv EQ).
  - destruct (equ_br_invT _ _ _ _ EQ). apply equ_br_invE in EQ as [_ EQ].
    eapply trans_br with (y := x). eapply IHTR; [reflexivity | now rewrite H1 | reflexivity].
  - apply equ_guard_inv in EQ. apply trans_guard. eapply IHTR; [reflexivity | exact EQ | reflexivity].
  - apply val_eq_inv in Hl as ->. apply equ_ret_inv in EQ. dependent destruction EQ. apply trans_ask.
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
