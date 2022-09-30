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
The [head] computation is itself a tree. The values it computes is
the set of possible transition, i.e. enough data to recover the next label
and process.
The [haction] data structure captures trivially this data.
.. coq::
|*)

<<<<<<< HEAD:theories/Head.v
Variant head {E C R} :=
	| HRet    (r : R)
	| HChoice (X : Type) (c : C X) (k : X -> ctree E C R)
	| HVis    (X : Type) (e : E X) (k : X -> ctree E C R).
=======
Variant haction {E R} :=
	| ARet    (r : R)
	| ABr (n : nat) (k : Fin.t n -> ctree E R)
	| AVis    (X : Type) (e : E X) (k : X -> ctree E R).
>>>>>>> master:theories/Misc/Head.v

(*|
The [head] computation simply scrolls the tree until it reaches
a none invisible br node.
Notice that this computation may loop if the original computation
admits a infinite branch of invisible brs.
|*)
<<<<<<< HEAD:theories/Head.v
Definition get_head {E C X} : ctree E C X -> ctree E C (@head E C X) :=
  cofix get_head (t : ctree E C X) :=
    match observe t with
    | RetF x          => Ret (HRet x)
    | VisF e k        => Ret (HVis e k)
    | ChoiceF true c k => Ret (HChoice c k)
    | ChoiceF false c k => Choice false c (fun x => get_head (k x))
    end.

Notation get_head_ t :=
    match observe t with
    | RetF x          => Ret (HRet x)
    | VisF e k        => Ret (HVis e k)
    | ChoiceF true c k => Ret (HChoice c k)
    | ChoiceF false c k => Choice false c (fun x => get_head (k x))
    end.

Lemma unfold_get_head {E C X} : forall (t : ctree E C X),
    get_head t ≅ get_head_ t.
=======
Definition head {E X} : ctree E X -> ctree E (@haction E X) :=
  cofix head (t : ctree E X) :=
    match observe t with
    | RetF x            => Ret (ARet x)
    | VisF e k          => Ret (AVis e k)
    | BrSF n k      => Ret (ABr k)
    | BrDF n k      => Br false n (fun i => head (k i))
    end.

Notation head_ t :=
  match observe t with
  | RetF x            => Ret (ARet x)
  | VisF e k          => Ret (AVis e k)
  | BrSF n k      => Ret (ABr k)
  | BrDF n k      => Br false n (fun i => head (k i))
  end.

Lemma unfold_head {E X} : forall (t : ctree E X),
    head t ≅ head_ t.
>>>>>>> master:theories/Misc/Head.v
Proof.
  intros.
	now step.
Qed.

(*|
Transitions in a tree can always be reflected in their head-tree.
The exact shape of the lemma depends on the nature of the transition.
We wrap them together in [trans_head].
|*)
<<<<<<< HEAD:theories/Head.v
Lemma trans_get_head_obs {E C X} `{C0 -< C} : forall (t u : ctree E C X) Y (e : E Y) v,
    trans (obs e v) t u ->
    exists (k : Y -> ctree E C X),
      trans (val (HVis e k)) (get_head t) stuckI /\
=======
Lemma trans_head_obs {E X} : forall (t u : ctree E X) Y (e : E Y) v,
    trans (obs e v) t u ->
    exists (k : Y -> ctree E X),
      trans (val (AVis e k)) (head t) stuckD /\
>>>>>>> master:theories/Misc/Head.v
        u ≅ k v.
Proof.
  intros * TR.
  unfold transR in *.
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

<<<<<<< HEAD:theories/Head.v
Lemma trans_get_head_tau {E C R} `{C0 -< C} : forall (t u : ctree E C R),
    trans tau t u ->
    exists X (c : C X) (k : X -> ctree E C R) x,
      trans (val (HChoice c k)) (get_head t) stuckI /\
=======
Lemma trans_head_tau {E X} : forall (t u : ctree E X),
    trans tau t u ->
    exists n (k : Fin.t n -> ctree E X) x,
      trans (val (ABr k)) (head t) stuckD /\
>>>>>>> master:theories/Misc/Head.v
        u ≅ k x.
Proof.
  intros * TR.
  unfold trans in *.
  remember tau as ob.
  setoid_rewrite (ctree_eta u).
  setoid_rewrite unfold_head.
  induction TR; try now inv Heqob; subst.
<<<<<<< HEAD:theories/Head.v
  - specialize (IHTR Heqob). destruct IHTR as (Y & c' & k' & y & IHTR & EQ); auto.
    exists Y, c', k', y. split; [| exact EQ].
    rename x into z.
    rewrite <- unfold_get_head in IHTR.
    eapply trans_choiceI with (x := z).
=======
  - destruct IHTR as (m & kf & z & IHTR & EQ); auto.
    exists m, kf, z; split; [| exact EQ].
    rename x into y.
    rewrite <- unfold_head in IHTR.
    eapply trans_brD with (x := y).
>>>>>>> master:theories/Misc/Head.v
    apply IHTR.
    reflexivity.
  - exists X,c,k,x; split.
    constructor.
    rewrite <- ctree_eta; symmetry; assumption.
Qed.

<<<<<<< HEAD:theories/Head.v
Lemma trans_get_head_ret {E C X} `{C0 -< C} : forall (t u : ctree E C X) (v : X),
    trans (val v) t u ->
    trans (val (@HRet E C X v)) (get_head t) stuckI /\
      u ≅ stuckI.
=======
Lemma trans_head_ret {E X} : forall (t u : ctree E X) (v : X),
    trans (val v) t u ->
    trans (val (@ARet E X v)) (head t) stuckD /\
      u ≅ stuckD.
>>>>>>> master:theories/Misc/Head.v
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
<<<<<<< HEAD:theories/Head.v
    constructor. symmetry. unfold stuckI.
    symmetry; rewrite choice0_always_stuck; reflexivity.
Qed.

Lemma trans_get_head : forall {E C R} `{C0 -< C} (t u : ctree E C R) l,
    trans l t u ->
    match l with
    | tau => exists X (c : C X) (k : X -> ctree E C R) x,
        trans (val (HChoice c k)) (get_head t) stuckI /\ u ≅ k x
    | obs e v => exists (k : _ -> ctree E C R),
        trans (val (HVis e k)) (get_head t) stuckI /\ u ≅ k v
    | val v => trans (val (@HRet E C _ v)) (get_head t) stuckI /\ u ≅ stuckI
    end.
Proof.
  intros *; destruct l.
  apply trans_get_head_tau.
  apply trans_get_head_obs.
  intros H0.
  pose proof (trans_val_invT H0); subst; apply trans_get_head_ret; assumption.
=======
    constructor.
    symmetry; rewrite brD0_always_stuck; reflexivity.
Qed.

Lemma trans_head : forall {E X} (t u : ctree E X) l,
    trans l t u ->
    match l with
    | tau => exists n (k : Fin.t n -> ctree E X) x,
        trans (val (ABr k)) (head t) stuckD /\ u ≅ k x
    | obs e v => exists (k : _ -> ctree E X),
        trans (val (AVis e k)) (head t) stuckD /\ u ≅ k v
    | val v => trans (val (@ARet E _ v)) (head t) stuckD /\ u ≅ stuckD
    end.
Proof.
  intros *; destruct l.
  apply trans_head_tau.
  apply trans_head_obs.
  intros A.
  pose proof (trans_val_invT A); subst; apply trans_head_ret; assumption.
>>>>>>> master:theories/Misc/Head.v
Qed.

(*|
The only transitions that the head-tree can take are value ones.
|*)
<<<<<<< HEAD:theories/Head.v
Ltac eq2equ H :=
  match type of H with
  | ?u = ?t => let eq := fresh "EQ" in assert (eq : u ≅ t) by (subst; reflexivity); clear H
  end.

Lemma trans_get_head_inv {E C X} `{C0 -< C} : forall (P : ctree E C X) l u,
    trans l (get_head P) u ->
=======
Lemma trans_head_inv {E X} : forall (P : ctree E X) l u,
    trans l (head P) u ->
>>>>>>> master:theories/Misc/Head.v
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
<<<<<<< HEAD:theories/Head.v
    + step in EQ; destruct (equb_choice_invT _ _ _ _ EQ) as [-> _].
      eapply equb_choice_invE in EQ as [].
=======
    + step in EQ; destruct (equb_br_invT _ _ EQ) as [-> _].
      eapply equb_br_invE in EQ.
>>>>>>> master:theories/Misc/Head.v
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

<<<<<<< HEAD:theories/Head.v
Lemma trans_HRet :
  forall {E C X} `{C0 -< C} r (p: ctree E C X) q,
    trans (val (@HRet E C X r)) (get_head p) q ->
    trans (val r) p stuckI.
=======
Lemma trans_ARet :
  forall {E X} r (p: ctree E X) q,
    trans (val (@ARet E X r)) (head p) q ->
    trans (val r) p stuckD.
>>>>>>> master:theories/Misc/Head.v
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
<<<<<<< HEAD:theories/Head.v
    + step in EQ; destruct (equb_choice_invT _ _ _ _ EQ) as [-> _].
=======
    + step in EQ; destruct (equb_br_invT _ _ EQ) as [-> _].
      eapply equb_br_invE in EQ.
>>>>>>> master:theories/Misc/Head.v
      setoid_rewrite <- ctree_eta in IHTR.
      econstructor.
      apply IHTR; eauto.
      now apply equb_choice_invE in EQ.
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

<<<<<<< HEAD:theories/Head.v
Lemma trans_HChoice :
  forall {E C R X} `{C0 -< C} (c : C X) k (p: ctree E C R) q,
    trans (val (HChoice c k)) (get_head p) q ->
    forall i, trans tau p (k i).
Proof.
  intros * TR.
  remember (get_head p) as Hp.
  remember (val (HChoice c k)) as l.
  eq2equ HeqHp.
=======
Lemma trans_ABr :
  forall {E X} n k (p: ctree E X) q,
    trans (val (ABr (n := n) k)) (head p) q ->
    forall i, trans tau p (k i).
Proof.
  intros * TR.
  remember (head p) as Ap.
  remember (val (ABr k)) as l.
  eq2equ HeqAp.
>>>>>>> master:theories/Misc/Head.v
  rewrite ctree_eta in EQ.
  revert p EQ k Heql.
  induction TR; intros; subst; try now inv Heql.
  - rewrite unfold_head in EQ.
    unfold trans.
    cbn; red.
    desobs p; try now (step in EQ; inv EQ).
    destruct vis.
    + step in EQ; inv EQ.
<<<<<<< HEAD:theories/Head.v
    + step in EQ; destruct (equb_choice_invT _ _ _ _ EQ) as [-> _].
      eapply equb_choice_invE in EQ as [].
=======
    + step in EQ; destruct (equb_br_invT _ _ EQ) as [-> _].
      eapply equb_br_invE in EQ.
>>>>>>> master:theories/Misc/Head.v
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

<<<<<<< HEAD:theories/Head.v
Lemma trans_HVis :
  forall {E C X Y} `{C0 -< C} (e : E Y) (p: ctree E C X) (k : Y -> ctree E C X) q,
    trans (val (HVis e k)) (get_head p) q ->
=======
Lemma trans_AVis :
  forall {E X Y} (e : E Y) (p: ctree E X) (k : Y -> ctree E X) q,
    trans (val (AVis e k)) (head p) q ->
>>>>>>> master:theories/Misc/Head.v
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
<<<<<<< HEAD:theories/Head.v
    + step in EQ; destruct (equb_choice_invT _ _ _ _ EQ) as [-> _].
      eapply equb_choice_invE in EQ as [].
=======
    + step in EQ; destruct (equb_br_invT _ _ EQ) as [-> _].
      eapply equb_br_invE in EQ.
>>>>>>> master:theories/Misc/Head.v
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

(*|
[head] is a computation computing computations. It's therefore not as
well-behaved w.r.t. to [equ] as usual: rewriting [equ eq] leads to [equ eq_haction]
computations, where [eq_haction] propagates [equ] to the computations contained in the
actions.
|*)
<<<<<<< HEAD:theories/Head.v
Variant eq_head {E C R} : @head E C R -> head -> Prop :=
| eq_head_ret : forall r, eq_head (HRet r) (HRet r)
| eq_head_choice : forall X (c : C X) (k1 k2 : X -> _),
    (forall x, k1 x ≅ k2 x) ->
    eq_head (HChoice c k1) (HChoice c k2)
| eq_head_vis : forall X (e : E X) k1 k2,
=======
Variant eq_haction {E R} : @haction E R -> haction -> Prop :=
| eq_haction_ret : forall r, eq_haction (ARet r) (ARet r)
| eq_haction_br : forall n (k1 k2 : fin n -> _),
    (forall i, k1 i ≅ k2 i) ->
    eq_haction (ABr k1) (ABr k2)
| eq_haction_vis : forall X (e : E X) k1 k2,
>>>>>>> master:theories/Misc/Head.v
    (forall x, k1 x ≅ k2 x) ->
    eq_haction (AVis e k1) (AVis e k2).

<<<<<<< HEAD:theories/Head.v
#[global] Instance eq_head_equiv {E C R} : Equivalence (@eq_head E C R).
=======
#[global] Instance eq_haction_equiv {E R} : Equivalence (@eq_haction E R).
>>>>>>> master:theories/Misc/Head.v
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

<<<<<<< HEAD:theories/Head.v
#[global] Instance get_head_equ {E C X} :
  Proper (equ eq ==> equ (eq_head)) (@get_head E C X).
=======
#[global] Instance head_equ {E X} :
  Proper (equ eq ==> equ (eq_haction)) (@head E X).
>>>>>>> master:theories/Misc/Head.v
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

Definition run_haction {E X} (hd : @haction E X) : ctree E X :=
  match hd with
  | ARet r => Ret r
  | @ABr _ _ n k => BrS n k
  | AVis e k => Vis e k
  end.

Lemma get_run_haction {E X} : forall (t : ctree E X),
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



