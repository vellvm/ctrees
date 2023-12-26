From Coq Require Import
  List
  Basics
  Relations.Relation_Definitions
  Classes.Morphisms.

Import ListNotations.

Generalizable All Variables.

(*| Compose setoid relation [R] n-times with itself |*)
Fixpoint rel_iter {A}(eqA: relation A)`{Equivalence A eqA}(n: nat) (R: relation A): relation A :=
  match n with
  | 0%nat => eqA
  | (S n)%nat => fun a c => exists b, R a b /\ rel_iter eqA n R b c
  end.

(*| Transitive reflexive closure of [R] |*)
Definition trc {A}(eqA: relation A)`{Equivalence A eqA} (R: relation A) (a b: A) :=
  exists n, rel_iter eqA n R a b.
Arguments trc /.

Global Instance Reflexive_trc {A}(eqA: relation A)`{Equivalence A eqA} R:
  Reflexive (trc eqA R).
Proof.
  red; intros.
  exists 0; cbn.
  reflexivity.
Qed.  

Lemma R_trc {A}(eqA: relation A)`{Equivalence A eqA} (R: relation A): forall (a b c: A),
    R a b ->
    trc eqA R b c ->
    trc eqA R a c.
Proof.
  intros.
  destruct H1.
  exists (S x); cbn.
  exists b; split; auto.
Qed.

(*| Compose setoid relation [R] n-times with itself with labels [X] |*)
Fixpoint rel_iter_label {X A}(eqA: relation A)`{Equivalence A eqA}(n: nat)(R: X -> A -> A -> Prop):
  list X -> A -> A -> Prop :=
  match n with
  | 0%nat => fun l a b => l = []%list /\ eqA a b 
  | (S n)%nat => fun l a c => exists h ts b, (l = h::ts) /\ R h a b /\ rel_iter_label eqA n R ts b c
  end.

Definition trc_label{X A}(eqA: relation A)`{Equivalence A eqA}(R: X -> A -> A -> Prop)(l: list X)(a b: A):=
  exists n, rel_iter_label eqA n R l a b.

Arguments trc_label /.

Lemma rel_iter_label_len{X A: Type}`{Equivalence A eqA}: forall n R (l: list X) a b,
    rel_iter_label eqA n R l a b -> length l = n.
Proof.    
  induction n; cbn;intros.
  - destruct H0 as (-> & ?).
    reflexivity.
  - destruct H0 as (h &  ts & b' & -> & HR & HRi).
    cbn.
    cut (length ts = n).
    + intros ->; reflexivity.
    + eapply IHn; eauto.
Qed.

Global Instance rel_iter_proper {A} {n: nat} (R: relation A) `{Equivalence A eqA}
  {HP: Proper (eqA ==> eqA ==> iff) R}:
  Proper (eqA ==> eqA ==> iff) (rel_iter eqA n R).
Proof.
  induction n; unfold Proper, respectful; cbn;
    intros; split; intros; subst.
  - symmetry in H0.
    transitivity x; auto.
    transitivity x0; auto.
  - transitivity y; auto.
    transitivity y0; auto.
    now symmetry.
  - destruct H2 as (t' & TR & TRi).
    exists t'; split.
    + now rewrite <- H0.
    + now rewrite <- H1.
  - destruct H2 as (t' & TR & TRi).
    exists t'; split.
    + now rewrite H0.
    + now rewrite H1.
Qed.

Global Instance trc_proper {A} (R: relation A) `{Equivalence A eqA}
  {HP: Proper (eqA ==> eqA ==> iff) R}:
  Proper (eqA ==> eqA ==> iff) (trc eqA R).
Proof.
  unfold Proper, respectful; cbn; intros; split; intros (n & HH); exists n.
  - now rewrite <- H0, <- H1.
  - now rewrite H0, H1.
Qed.

Global Instance rel_iter_label_proper {X A} {n: nat} (R: X -> relation A) `{Equivalence A eqA}
  {HP: Proper (eq ==> eqA ==> eqA ==> iff) R}:
  Proper (eq ==> eqA ==> eqA ==> iff) (rel_iter_label eqA n R).
Proof.
  induction n; unfold Proper, respectful; cbn;
    intros; split; intros.
  - destruct H3 as (-> & ?); subst.
    split; auto.
    symmetry in H1.
    transitivity x0; auto.
    transitivity x1; auto.
  - destruct H3 as (-> & ?); subst.
    split; auto.
    transitivity y0; auto.
    transitivity y1; auto.
    now symmetry.
  - destruct H3 as (h & ts & c & Eql & HR & TRi).
    subst.
    exists h, ts, c; split; auto; split.
    + now rewrite <- H1.
    + now rewrite <- H2.
  - destruct H3 as (h & ts & c & Eql & HR & TRi).
    subst.
    exists h, ts, c; split; auto; split.
    + now rewrite H1.
    + now rewrite H2.
Qed.

Global Instance trc_label_proper {X A} (R: X -> relation A) `{Equivalence A eqA}
  {HP: Proper (eq ==> eqA ==> eqA ==> iff) R}:
  Proper (eq ==> eqA ==> eqA ==> iff) (trc_label eqA R).
Proof.
  unfold Proper, respectful; cbn; intros; split; intros (n & HH); exists n;
    subst.
  - now rewrite <- H1, <- H2.
  - now rewrite H1, H2.
Qed.
