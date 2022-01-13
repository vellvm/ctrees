From CTree Require Import
	Utils
	CTrees
  Trans
 	Interp
	Equ
	Bisim
  CTreesTheory.

From RelationAlgebra Require Import
     rel
     srel.

From Coinduction Require Import
	coinduction rel tactics.

Import CTreeNotations.
Open Scope ctree_scope.

Set Implicit Arguments.
Set Contextual Implicit.

(*|
We could define generic [get_hd] functions as follows.
For now, we'll work with specialized versions below
|*)
Variant head_gen {E R} :=
	| HRet    (r : R)
	| HChoice (n : nat) (k : Fin.t n -> ctree E R)
	| HVis    (X : Type) (e : E X) (k : X -> ctree E R).

Definition get_head {E F X} : ctree E X -> ctree F (@head_gen E X) :=
  cofix get_head (t : ctree E X) :=
    match observe t with
    | RetF x            => Ret (HRet x)
    | VisF e k          => Ret (HVis e k)
    | ChoiceF true n k  => Ret (HChoice k)
    | ChoiceF false n k => Choice false n (fun i => get_head (k i))
    end.

Notation get_head_ t :=
  match observe t with
  | RetF x            => Ret (HRet x)
  | VisF e k          => Ret (HVis e k)
  | ChoiceF true n k  => Ret (HChoice k)
  | ChoiceF false n k => Choice false n (fun i => get_head (k i))
  end.

Lemma unfold_get_head {E F X} : forall (t : ctree E X),
    get_head (F := F) t ≅ get_head_ t.
Proof.
  intros.
	now step.
Qed.

Lemma trans_get_head_obs {E X} : forall (t u : ctree E X) Y (e : E Y) v,
    trans (obs e v) t u ->
    exists (k : Y -> ctree E X),
      trans (val (HVis e k)) (get_head (F := E) t) CTree.stuck /\
        u ≅ k v.
Proof.
  intros * TR.
  unfold transR in *.
  remember (obs e v) as ob.
  setoid_rewrite (ctree_eta u).
  setoid_rewrite unfold_get_head.
  induction TR; try now inv Heqob.
  - destruct IHTR as (kf & IHTR & EQ); auto.
    exists kf; split; [| exact EQ].
    rename x into y.
    rewrite <- unfold_get_head in IHTR.
    eapply trans_ChoiceI with (x := y).
    apply IHTR.
    reflexivity.
  - dependent induction Heqob.
    exists k; split.
    constructor.
    rewrite <- ctree_eta; symmetry; assumption.
Qed.

Lemma trans_get_head_tau {E X} : forall (t u : ctree E X),
    trans tau t u ->
    exists n (k : Fin.t n -> ctree E X) x,
      trans (val (HChoice k)) (get_head (F := E) t) CTree.stuck /\
        u ≅ k x.
Proof.
  intros * TR.
  unfold trans in *.
  remember tau as ob.
  setoid_rewrite (ctree_eta u).
  setoid_rewrite unfold_get_head.
  induction TR; try now inv Heqob; subst.
  - destruct IHTR as (m & kf & z & IHTR & EQ); auto.
    exists m, kf, z; split; [| exact EQ].
    rename x into y.
    rewrite <- unfold_get_head in IHTR.
    eapply trans_ChoiceI with (x := y).
    apply IHTR.
    reflexivity.
  - exists n,k,x; split.
    constructor.
    rewrite <- ctree_eta; symmetry; assumption.
Qed.

Lemma trans_get_head_ret {E X} : forall (t u : ctree E X) (v : X),
    trans (val v) t u ->
    trans (val (@HRet E X v)) (get_head (F := E) t) CTree.stuck /\
      u ≅ CTree.stuck.
Proof.
  intros * TR.
  unfold trans in *.
  remember (val v) as ob.
  setoid_rewrite (ctree_eta u).
  setoid_rewrite unfold_get_head.
  induction TR; try now inv Heqob; subst.
  - destruct IHTR as (IHTR & EQ); auto.
    split; [| exact EQ].
    rewrite <- unfold_get_head in IHTR.
    rename x into y.
    eapply trans_ChoiceI with (x := y).
    apply IHTR.
    reflexivity.
  - dependent induction Heqob.
    split.
    constructor.
    symmetry; rewrite choiceI0_always_stuck; reflexivity.
Qed.

Lemma trans_get_head : forall {E X} (t u : ctree E X) l,
    trans l t u ->
    match l with
    | tau => exists n (k : Fin.t n -> ctree E X) x,
        trans (val (HChoice k)) (get_head (F := E) t) CTree.stuck /\ u ≅ k x
    | obs e v => exists (k : _ -> ctree E X),
        trans (val (HVis e k)) (get_head (F := E) t) CTree.stuck /\ u ≅ k v
    | val v => trans (val (@HRet E _ v)) (get_head (F := E) t) CTree.stuck /\ u ≅ CTree.stuck
    end.
Proof.
  intros *; destruct l.
  apply trans_get_head_tau.
  apply trans_get_head_obs.
  intros H.
  pose proof (trans_val_invT H); subst; apply trans_get_head_ret; assumption.
Qed.

Inductive eq_head {E R} : @head_gen E R -> head_gen -> Prop :=
| eq_head_ret : forall r, eq_head (HRet r) (HRet r)
| eq_head_choice : forall n (k1 k2 : fin n -> _),
    (forall i, k1 i ≅ k2 i) ->
    eq_head (HChoice k1) (HChoice k2)
| eq_head_vis : forall X (e : E X) k1 k2,
    (forall x, k1 x ≅ k2 x) ->
    eq_head (HVis e k1) (HVis e k2).

#[global] Instance Equivalence_bt_equ_gen {E X Y R S}:
  Proper ((gfp (@fequ E X _ eq)) ==> (gfp (@fequ E Y _ eq)) ==> iff) (bt_equ R S).
Admitted.

#[global] Instance get_head_equ {E F X} :
  Proper (equ eq ==> equ (eq_head)) (@get_head E F X).
Proof.
  unfold Proper, respectful.
  coinduction S CIH.
  intros.
  rewrite 2 unfold_get_head.
  step in H.
  inv H.
  - do 2 constructor.
  - do 2 constructor; auto.
  - destruct b.
    + do 2 constructor; auto.
    + constructor; intros ?; auto.
Qed.

Ltac eq2equ H :=
  match type of H with
  | ?u = ?t => let eq := fresh "EQ" in assert (eq : u ≅ t) by (subst; reflexivity); clear H
  end.

Lemma trans_get_hhead {E F X} : forall (P : ctree E X) l u,
    trans l (get_head (F := F) P) u ->
    is_val l.
Proof.
  intros * TR.
  red in TR.
  remember (get_head P) as HP.
  eq2equ HeqHP.
  rewrite ctree_eta in EQ.
  revert P EQ.
  induction TR; intros; subst.
  - rewrite unfold_get_head in EQ.
    desobs P; try now (step in EQ; inv EQ).
    destruct vis.
    + step in EQ; inv EQ.
    + step in EQ; destruct (equF_choice_invT _ _ EQ) as [-> _].
      eapply equF_choice_invE in EQ.
      setoid_rewrite <- ctree_eta in IHTR.
      eapply IHTR; eauto.
  - exfalso.
    rewrite unfold_get_head in EQ.
    desobs P; try now (step in EQ; inv EQ).
    destruct vis.
    + step in EQ; inv EQ.
    + step in EQ; apply equF_choice_invT in EQ as [_ abs]; inv abs.
  - exfalso.
    rewrite unfold_get_head in EQ.
    desobs P; try now (step in EQ; inv EQ).
    destruct vis; step in EQ; inv EQ.
  - constructor.
Qed.


