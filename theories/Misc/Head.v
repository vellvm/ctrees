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
We develop in this file the [get_head] function to compute this prefix.

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
	| ABr     (Y : Type) (c : B Y) (k : Y -> ctree E B X)
	| AVis    (Y : Type) (e : E Y) (k : Y -> ctree E B X).


(*|
The [head] computation simply scrolls the tree until it reaches
a none invisible br node.
Notice that this computation may loop if the original computation
admits a infinite branch of invisible brs.
|*)
Definition head {E F B C X} `{HasB: B -< C} : ctree E B X -> ctree F C (@haction E B X) :=
  cofix head (t : ctree E B X) :=
    match observe t with
    | RetF x          => Ret (ARet x)
    | VisF e k        => Ret (AVis e k)
    | BrSF c k        => Ret (ABr c k)
    | BrDF c k        => br false c (fun x => head (k x))
    end.

Notation head_ t :=
  match observe t with
  | RetF x            => Ret (ARet x)
  | VisF e k          => Ret (AVis e k)
  | BrSF c k      => Ret (ABr c k)
  | BrDF c k      => br false c (fun x => head (k x))
  end.

Lemma unfold_head {E F B C X} `{HasB: B -< C} : forall (t : ctree E B X),
    (head t : ctree F C _) ≅ head_ t.
Proof.
  intros.
  now step.
Qed.

Section trans_head.

Context {E F B C : Type -> Type} {X : Type}.
Context `{B0 -< B} `{B0 -< C} `{B -< C}.

(*|
Transitions in a tree can always be reflected in their head-tree.
The exact shape of the lemma depends on the nature of the transition.
We wrap them together in [trans_head].
|*)
Lemma trans_head_obs {Y} : forall (t u : ctree E B X) (e : E Y) v,
    trans (obs e v) t u ->
    exists (k : Y -> ctree E B X),
      trans (val (AVis e k)) (head t : ctree F C _) stuckD /\ u ≅ k v.
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
    eapply trans_brD with (x := y).
    apply IHTR.
    reflexivity.
  - dependent induction Heqob.
    exists k; split.
    constructor.
    rewrite <- ctree_eta; symmetry; assumption.
Qed.

Lemma trans_head_tau :
  forall (t u : ctree E B X),
    trans tau t u ->
    exists Y (c : B Y) (k : Y -> ctree E B X) x,
      trans (val (ABr c k)) (head t : ctree F C _) stuckD /\ u ≅ k x.
Proof.
  intros * TR.
  unfold trans in *.
  remember tau as ob.
  setoid_rewrite (ctree_eta u).
  setoid_rewrite unfold_head.
  induction TR; try now inv Heqob; subst.
  - destruct IHTR as (m & kf & z & i & IHTR & EQ); auto.
    exists m, kf, z, i. split; [| exact EQ].
    rename x into y.
    rewrite <- unfold_head in IHTR.
    eapply trans_brD with (x := y).
    apply IHTR.
    reflexivity.
  - exists X0,c,k,x; split.
    constructor.
    rewrite <- ctree_eta; symmetry; assumption.
Qed.

Lemma trans_head_ret :
  forall (t u : ctree E B X) (v : X),
    trans (val v) t u ->
    trans (val (@ARet E B X v)) (head t : ctree F C _) stuckD /\ u ≅ stuckD.
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
    eapply trans_brD with (x := y).
    apply IHTR.
    reflexivity.
  - dependent induction Heqob.
    split.
    constructor.
    symmetry; rewrite brD0_always_stuck; reflexivity.
Qed.

Lemma trans_head : forall (t u : ctree E B X) l,
    trans l t u ->
    match l with
    | tau => exists Y (c: B Y) (k : Y -> ctree E B X) x,
        trans (val (ABr c k)) (head t : ctree F C _) stuckD /\ u ≅ k x
    | obs e v => exists (k : _ -> ctree E B X),
        trans (val (AVis e k)) (head t : ctree F C _) stuckD /\ u ≅ k v
    | val v => trans (val (@ARet E B _ v)) (head t : ctree F C _) stuckD /\ u ≅ stuckD
    end.
Proof.
  intros *; destruct l.
  apply trans_head_tau.
  apply trans_head_obs.
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
    destruct vis.
    + step in EQ; inv EQ.
    + step in EQ; destruct (equb_br_invT _ _ _ _ EQ) as [-> _].
      eapply equb_br_invE in EQ as [].
      setoid_rewrite <- ctree_eta in IHTR.
      eapply IHTR; eauto.
  - exfalso.
    rewrite unfold_head in EQ.
    desobs P; try now (step in EQ; inv EQ).
    destruct vis.
    + step in EQ; inv EQ.
    + step in EQ; apply equb_br_invT in EQ as [_ abs]; inv abs.
  - exfalso.
    rewrite unfold_head in EQ.
    desobs P; try now (step in EQ; inv EQ).
    destruct vis; step in EQ; inv EQ.
  - constructor.
Qed.

Lemma trans_ARet :
  forall r (p: ctree E B X) q,
    trans (val (@ARet E B X r)) (head p : ctree F C _) q ->
    trans (val r) p stuckD.
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
    destruct vis.
    + step in EQ; inv EQ.
    + step in EQ; destruct (equb_br_invT _ _ _ _ EQ) as [-> _].
      setoid_rewrite <- ctree_eta in IHTR.
      econstructor.
      apply IHTR; eauto.
      now apply equb_br_invE in EQ.
  - unfold trans.
    apply val_eq_inv in Heql; inv Heql.
    rewrite unfold_head in EQ.
    cbn; red.
    desobs p; try now (step in EQ; inv EQ).
    step in EQ; inv EQ. inv REL; constructor.
    destruct vis.
    + step in EQ. inv EQ. inv REL.
    + step in EQ; inv EQ.
Qed.

Lemma trans_ABr :
  forall (c : B X) k (p: ctree E B X) q,
    trans (val (ABr c k)) (head p : ctree F C _) q ->
    forall i, trans tau p (k i).
Proof.
  intros * TR.
  remember (head p) as Hp.
  remember (val (ABr c k)) as l.
  eq2equ HeqHp.
  rewrite ctree_eta in EQ.
  revert p EQ k Heql.
  induction TR; intros; subst; try now inv Heql.
  - rewrite unfold_head in EQ.
    unfold trans.
    cbn; red.
    desobs p; try now (step in EQ; inv EQ).
    destruct vis.
    + step in EQ; inv EQ.
    + step in EQ; destruct (equb_br_invT _ _ _ _ EQ) as [-> _].
      eapply equb_br_invE in EQ as [].
      setoid_rewrite <- ctree_eta in IHTR.
      econstructor.
      apply IHTR; eauto.
  - apply val_eq_inv in Heql; inv Heql.
    rewrite unfold_head in EQ.
    unfold trans.
    cbn; red.
    desobs p; try now (step in EQ; inv EQ).
    destruct vis.
    + step in EQ; inv EQ.
      dependent induction REL.
      apply trans_brS.
    + step in EQ; inv EQ.
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
    destruct vis.
    + step in EQ; inv EQ.
    + step in EQ; destruct (equb_br_invT _ _ _ _ EQ) as [-> _].
      eapply equb_br_invE in EQ as [].
      setoid_rewrite <- ctree_eta in IHTR.
      econstructor.
      apply IHTR; eauto.
  - apply val_eq_inv in Heql; inv Heql.
    rewrite unfold_head in EQ.
    unfold trans.
    cbn; red.
    desobs p; try now (step in EQ; inv EQ).
    + step in EQ; inv EQ.
      dependent induction REL.
      constructor; reflexivity.
    + destruct vis; step in EQ; inv EQ.
      inv REL.
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
| eq_haction_br : forall X (c : C X) (k1 k2 : X -> _),
    (forall x, k1 x ≅ k2 x) ->
    eq_haction (ABr c k1) (ABr c k2)
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
  unfold equ; coinduction S CIH.
  intros.
  rewrite 2 unfold_head.
  step in H.
  inv H.
  - do 2 constructor.
  - do 2 constructor; auto.
  - destruct b.
    + do 2 constructor; auto.
    + constructor; intros ?; auto.
Qed.

Definition run_haction {E C X} (hd : @haction E C X) : ctree E C X :=
  match hd with
  | ARet r => Ret r
  | @ABr _ _ _ _ n k => BrS n k
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
  - rewrite bind_ret_l; reflexivity.
  - destruct vis.
    + rewrite bind_ret_l; reflexivity.
    + rewrite bind_br; constructor; intros.
      apply cih.
Qed.



