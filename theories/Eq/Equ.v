(*|
==============================
Syntactic equality over ctrees
==============================
As always with coinductive structures in Rocq, [eq] is too strong
to be usable. We hence define through this file [equ], a coinductive
syntactic equality over the structure. [equ] enforces the trees to
have the exact same shape, constructor by constructor.

This relation is analogous to what is dubbed as _strong bisimulation_
for [itree], but we are trying to avoid this terminology here since
we reserve the notion of bisimulation for the equivalence relations
that take internal non-determinism into account.

.. coq:: none
|*)
From Stdlib Require Import RelationClasses Program.

From Coinduction Require Import all.

From ITree Require Import Core.Subevent.

From CTree Require Import
     CTree
     Eq.Shallow.

Import CTree.

#[local] Ltac step_ := step; simpl body.
#[local] Ltac step := step_.
#[local] Ltac step_in H := step in H; simpl body in H.
#[local] Tactic Notation "step" "in" ident(H) := step_in H.

(*|
.. coq::
|*)

Section equ.

  Context {E B : Type -> Type} {R1 R2 : Type} (RR : R1 -> R2 -> Prop).

(*|
We also need to do some gymnastics to work around the
two-layered definition of [ctree]. We first define a
relation transformer [equb] as an indexed inductive type
on [ctree'], which is then composed with [observe] to obtain
a relation transformer on [ctree] ([equ_]).

In short, this is necessitated by the fact that dependent
pattern-matching is not allowed on [ctree].
|*)

  Variant equb (eq : ctree E B R1 -> ctree E B R2 -> Prop) :
    ctree' E B R1 -> ctree' E B R2 -> Prop :=
    | Eq_Ret x y (REL : RR x y) : equb eq (RetF x) (RetF y)
    | Eq_Stuck : equb eq StuckF StuckF
    | Eq_Guard t u
        (REL : eq t u) :
      equb eq (GuardF t) (GuardF u)
    | Eq_Step t u
        (REL : eq t u) :
      equb eq (StepF t) (StepF u)
    | Eq_Vis {X} (e : E X) k1 k2
        (REL : forall x, eq (k1 x) (k2 x)) :
      equb eq (VisF e k1) (VisF e k2)
    | Eq_Br {X} {c : B X} k1 k2
        (REL : forall x, eq (k1 x) (k2 x)) :
      equb eq (BrF c k1) (BrF c k2)
  .
  Hint Constructors equb: core.

  Definition equb_ eq : ctree E B R1 -> ctree E B R2 -> Prop :=
	fun t1 t2 => equb eq (observe t1) (observe t2).

  Program Definition fequ: mon (ctree E B R1 -> ctree E B R2 -> Prop) := {|body := equb_|}.
  Next Obligation.
    unfold pointwise_relation, Basics.impl, equb_.
    intros ?? INC ?? EQ. inversion_clear EQ; auto.
  Qed.

End equ.

(*|
The relation itself, defined as the greatest fixed-point of [fequ].
Through this development, we use the [coinduction] package developed
by Damien Pous to define and reason about coinductive relations.
The approach is based on the so-called "companion", described in
the paper "Coinduction All the Way Up" (Pous, LICS'16).

The greastest fixed-point is defined by the construction [gfp].
It gives access to the following tactics:
- [coinduction S CIH] initiates a coinductive proof;
- [step in H] unfold in [H] the [gfp], exposing here for instance
[equF], allowing for an inversion to be performed;
- [step] unfolds in the goal the [gfp], exposing [equF], so that
one can play the game once. Note that formally speaking, this
corresponds to reasoning "up-to fequ".
- additionnaly, the companion provides extensive support for
up-to reasoning: any function [f] proved to be below the companion,
denoted [t], is accessible during a proof by coinduction.

|*)

Definition equ {E B R1 R2} R := (gfp (@fequ E B R1 R2 R)).
#[global] Hint Unfold equ: core.
#[global] Hint Constructors equb: core.
Arguments equb_ _ _ _ _/.

Ltac fold_equ :=
  repeat
    match goal with
    | h: context[@fequ ?E ?B ?R1 ?R2 ?RR] |- _ => fold (@equ E B R1 R2 RR) in h
    | |- context[@fequ ?E ?B ?R1 ?R2 ?RR] => fold (@equ E B R1 R2 RR)
    end.

Tactic Notation "__step_equ" :=
  match goal with
  | |- context [@equ ?E ?B ?R1 ?R2 ?RR] =>
      unfold equ;
      step;
      fold (@equ E B R1 R2 RR)
  end.

#[local] Tactic Notation "step" := __step_equ || step.

Ltac __step_in_equ H :=
  match type of H with
  | context [@equ ?E ?B ?R1 ?R2 ?RR] =>
      unfold equ in H;
      step in H;
      fold (@equ E B R1 R2 RR) in H
  end.

#[local] Tactic Notation "step" "in" ident(H) := __step_in_equ H || step in H.

Tactic Notation "__coinduction_equ" simple_intropattern(r) simple_intropattern(cih) :=
  first [unfold equ at 4 | unfold equ at 3 | unfold equ at 2 | unfold equ at 1]; coinduction r cih.
#[local] Tactic Notation "coinduction" simple_intropattern(r) simple_intropattern(cih) :=
  __coinduction_equ r cih || coinduction r cih.

Module EquNotations.

  Infix "≅" := (equ eq) (at level 70).
  Notation "t (≅ Q ) u" := (equ Q t u) (at level 79).
  Notation "t {{≅ Q }} u" := (equb Q (equ Q) t u) (at level 79).
  Notation "t {{≅}} u" := (equb eq (equ eq) t u) (at level 79).

End EquNotations.

Import EquNotations.

Section equ_theory.

  Context {E B : Type -> Type} {R : Type} (RR : R -> R -> Prop).
  Notation fequ := (fequ (E := E) (B := B)).

(*|
This is just a hack suggested by Damien Pous to avoid a
universe inconsistency when using both the relational algebra
and coinduction libraries (we fix the type at which we'll use [eq]).
|*)
  Definition seq: relation (ctree E B R) := eq.

(*|
[eq] is a post-fixpoint, thus [const eq] is below [t]
These kind of lemmas are proofs of validity of up-to reasoning
principles: [t_equ RR] is the companion of the monotone function
[fequ RR]. By proving that the function (on relations over ctrees)
[const seq] (i.e. [fun R => eq]) is below the companion, it is proved
to be a valid enhancement, and hence can be used at any point during
a coinductive proof.
Here concretely, bisimulation candidates don't ever need
to be closed by reflexivity in effect: the companion is always reflexive.
|*)
  Lemma refl_t {RRR: Reflexive RR} {C: Chain (fequ RR)}: Reflexive (elem C).
  Proof.
    apply Reflexive_chain.
    intros. intro.
    cbn. desobs x; auto.
  Qed.

(*|
[converse] is compatible: up-to symmetry is valid
|*)
  Lemma converse_t {RRS: Symmetric RR} {C: Chain (fequ RR)}: Symmetric (elem C).
  Proof.
    apply Symmetric_chain.
    cbn. red. intros.
    destruct H0; auto.
  Qed.

  Hint Constructors equb: core.
(*|
[squaring] is compatible: up-to transitivity is valid
|*)
  Lemma square_t {RRR: Reflexive RR} {RRT: Transitive RR} {C: Chain (fequ RR)}: Transitive (elem C).
  Proof.
    apply Transitive_chain.
    cbn. red. intros ????? xy yz.
    inversion xy; inversion yz; cbn; try (exfalso; congruence); eauto.
    - constructor. replace y0 with x1 in * by congruence; eauto.
    - constructor. replace t0 with u in * by congruence; eauto.
    - constructor. replace t0 with u in * by congruence; eauto.
    - rewrite <- H3 in H2.
      destruct (Vis_eq1 H2).
      destruct (Vis_eq2 H2) as [-> ->].
      constructor. intro x0. eauto.
    - rewrite <- H3 in H2.
      destruct (Br_eq1 H2); subst.
      destruct (Br_eq2 H2) as [-> ->].
      constructor. intros i. eauto.
  Qed.

(*|
Having [const eq], [converse] and [square] below the companion entails respectively
that the companion, at all point, is reflexive, symmetric, transitive.
The companion library directly provide these results for bisimilarity, [t R], [b (t R)]
and [T f R].
|*)
  #[global] Instance Equivalence_et `{Equivalence _ RR} {C: Chain (fequ RR)}: Equivalence (elem C).
  Proof. constructor. apply refl_t. apply converse_t. apply square_t. Qed.

(*|
This instance is a bit annoyingly adhoc, but useful for unfolding laws notably:
essentially we can conclude by reflexivity without stepping completely through
[equb], but only after exposing it by unfolding and case-analysing on the structure
of the tree.
|*)
  #[global] Instance Reflexive_equb (equ : ctree E B R -> ctree E B R -> Prop) :
    Reflexive RR -> Reflexive equ -> Reflexive (equb RR equ).
  Proof.
    red. destruct x; auto.
  Qed.

End equ_theory.

#[global] Instance Equivalence_equ {E B R}: Equivalence (@equ E B R R eq).
Proof. apply Equivalence_et. typeclasses eauto. Qed.

#[global] Hint Constructors equb : core.
Arguments equb_ {E B R1 R2} RR eq t1 t2/.

#[global] Instance equb_eq_equ' {E B X Y} {R : rel X Y} :
  Proper (equ eq ==> equ eq ==> flip impl) (@equ E B X Y R).
Proof.
  unfold Proper, respectful, flip, impl; cbn.
  coinduction C CH. intros t t' EQt u u' EQu EQ.
  step in EQt.
  step in EQu.
  step in EQ.
  cbn in *; inv EQt; rewrite <- H in EQ.
  - inv EQ.
    rewrite <- H3 in EQu.
    inv EQu; auto.
  - inv EQ.
    rewrite <- H1 in EQu.
    inv EQu; auto.
  - inv EQ.
    rewrite <- H3 in EQu.
    inv EQu; eauto.
  - inv EQ.
    rewrite <- H3 in EQu.
    inv EQu; eauto.
  - dependent destruction EQ.
    cbn.
    rewrite <- x in EQu.
    dependent destruction EQu.
    rewrite <- x. eauto.
  - dependent destruction EQ.
    cbn.
    rewrite <- x in EQu.
    dependent destruction EQu.
    rewrite <- x.
    eauto.
Qed.

#[global] Instance equb_eq_equ {E B X} {Q : rel X X} :
  Proper (equ eq ==> equ eq ==> flip impl) (@equ E B X X Q).
Proof. apply equb_eq_equ'. Qed.

Lemma guard_equ: forall (E B: Type -> Type) R (t u : ctree E B R),
    (t ≅ u) ->
    Guard t ≅ Guard u.
Proof.
  intros.
  now step; constructor.
Qed.

(*|
Dependent inversion of [equ] and [equb] equations
-------------------------------------------------
We assume [JMeq_eq] to invert easily bisimilarity of dependently typed constructors
|*)
Lemma equ_ret_inv {E B X Y R} (r1 : X) (r2 : Y) :
  Ret r1 (≅R) (Ret r2 : ctree E B Y) ->
  R r1 r2.
Proof.
  intros EQ. step in EQ.
  dependent induction EQ; auto.
Qed.

Lemma equ_vis_invT {E B X Y S S'} {Q : rel S S'} (e1 : E X) (e2 : E Y) (k1 : X -> ctree E B S) k2 :
  Vis e1 k1 (≅Q) Vis e2 k2 ->
  X = Y.
Proof.
  intros EQ. step in EQ.
  dependent induction EQ; auto.
Qed.

Lemma equ_vis_invE {E B X S S'} {Q : rel S S'} (e1 e2 : E X) (k1 : X -> ctree E B S) k2 :
  Vis e1 k1 (≅Q) Vis e2 k2 ->
  e1 = e2 /\ forall x, k1 x (≅Q) k2 x.
Proof.
  intros EQ. step in EQ.
  inv EQ.
	dependent destruction H2.
	dependent destruction H4.
	auto.
Qed.

Lemma equ_br_invT {E B X Y S S' } {Q : rel S S'} (c1 : B X) (c2 : B Y) (k1 : X -> ctree E B S) k2 :
  Br c1 k1 (≅Q) Br c2 k2 ->
  X = Y.
Proof.
  intros EQ; step in EQ.
	dependent destruction EQ; auto.
Qed.

Lemma equ_br_invE {E B X S S'} {Q : rel S S'} (c1 c2 : B X) (k1 : _ -> ctree E B S) k2 :
  Br c1 k1 (≅Q) Br c2 k2 ->
   c1 = c2 /\ forall x,k1 x (≅Q) k2 x.
Proof.
  intros EQ; step in EQ.
	inv EQ.
	dependent destruction H.
  now dependent destruction H4.
Qed.

Lemma equb_vis_invT {E B X Y S} (e1 : E X) (e2 : E Y) (k1 : X -> ctree E B S) k2 :
  equb eq (equ eq) (VisF e1 k1) (VisF e2 k2) ->
  X = Y.
Proof.
  intros EQ.
	dependent induction EQ; auto.
Qed.

Lemma equb_vis_invE {E B X S} (e1 e2 : E X) (k1 k2 : X -> ctree E B S) :
  equb eq (equ eq) (VisF e1 k1) (VisF e2 k2) ->
  e1 = e2 /\ forall x, equ eq (k1 x) (k2 x).
Proof.
  intros EQ.
  inv EQ.
  dependent destruction H; dependent destruction H4; auto.
Qed.

Lemma equb_br_invT {E B X Y S} (c1 : B X) (c2 : B Y) (k1 : _ -> ctree E B S) k2 :
  equb eq (equ eq) (BrF c1 k1) (BrF c2 k2) ->
  X = Y.
Proof.
  intros EQ.
	dependent induction EQ; auto.
Qed.

Lemma equb_br_invE {E B X S} (c1 c2 : B X) (k1 : _ -> ctree E B S) k2 :
  equb eq (equ eq) (BrF c1 k1) (BrF c2 k2) ->
  c1 = c2 /\ forall x, equ eq (k1 x) (k2 x).
Proof.
  intros EQ.
  inv EQ.
  dependent destruction H. now dependent destruction H4.
Qed.

Lemma equ_guard_inv {E B S S'} {Q : rel S S'} (t : ctree E B S) u :
  Guard t (≅Q) Guard u ->
  t (≅Q) u.
Proof.
  intros EQ; step in EQ.
	now inv EQ.
Qed.

Lemma equ_step_inv {E B S S'} {Q : rel S S'} (t : ctree E B S) u :
  Step t (≅Q) Step u ->
  t (≅Q) u.
Proof.
  intros EQ; step in EQ.
	now inv EQ.
Qed.

(*|
Proper Instances
----------------
equ eq       ==> going (equ eq)  observe
∀(equ eq)    ==> going (equ eq)  BrF
∀(equ eq)    ==> going (equ eq)  VisF
observing eq --> equ eq
going(equ)   ==> eq ==> fimpl    equb eq (t_equ eq r)
eq ==> going(equ)   ==> fimpl    equb eq (t_equ eq r)
leq ==> leq                      equ
weq ==> weq                      equ
|*)

#[global] Instance equ_observe {E B R} :
  Proper (equ eq ==> going (equ eq)) (@observe E B R).
Proof.
  constructor. step in H.
  now step.
Qed.

#[global] Instance equ_BrF {E B R X} (c : B X) :
  Proper (pointwise_relation _ (equ eq) ==> going (equ eq)) (@BrF E B R _ _ c).
Proof.
  constructor. red in H. step. econstructor; eauto.
Qed.

#[global] Instance equ_GuardF {E B R} :
  Proper (equ eq ==> going (equ eq)) (@GuardF E B R _).
Proof.
  constructor. red in H. step. econstructor; eauto.
Qed.

#[global] Instance equ_StepF {E B R} :
  Proper (equ eq ==> going (equ eq)) (@StepF E B R _).
Proof.
  constructor. red in H. step. econstructor; eauto.
Qed.

(* #[global] Instance equ_Guard: *)
(*   forall {E B : Type -> Type} {R : Type}, *)
(*     Proper (equ eq ==> equ eq) (fun (t : ctree E B R) => Guard t). *)
(* Proof. *)
(*   repeat intro. Unset Printing Notations. *)
(*   setoid_rewrite H. *)
(* Qed. *)

(* #[global] Instance equ_Step: *)
(*   forall {E B : Type -> Type} {R : Type} `{B1 -< B}, *)
(*     Proper (equ eq ==> equ eq) (@Step E B R _). *)
(* Proof. *)
(*   repeat intro. *)
(*   unfold Step; now setoid_rewrite H0. *)
(* Qed. *)

#[global] Instance equ_VisF {E B R X} (e : E X) :
  Proper (pointwise_relation _ (equ eq) ==> going (equ eq)) (@VisF E B R _ _ e).
Proof.
  constructor. red in H. step. econstructor; eauto.
Qed.

#[global] Instance observing_sub_equ E B R :
  subrelation (@observing E B R R eq) (equ eq).
Proof.
  repeat intro.
  step. rewrite (observing_observe H). apply Reflexive_equb; eauto.
Qed.

#[global] Instance equ_eq_equ {E C R}  (r : Chain (fequ eq)) :
  Proper (going (equ eq) ==> eq ==> flip impl)
	     (@equb E C R R eq (elem r)).
Proof.
  repeat intro; subst.
  inv H. step in H0. inv H0; inv H1; auto.
  - constructor; rewrite REL; auto.
  - constructor; rewrite REL; auto.
  - invert.
    constructor; intros; rewrite REL; auto.
  - invert.
    constructor; intros; rewrite REL; auto.
Qed.

#[global] Instance equ_leq {E B X Y} : Proper (leq ==> leq) (@equ E B X Y).
Proof.
  unfold Proper, respectful, flip, impl. cbn. unfold impl.
  intros R R'.
  coinduction RR CH. intros.
  do 3 red. cbn. step in H0.
  destruct (observe a), (observe a0); try now inv H0; eauto.
  - dependent destruction H0. constructor.
    intros. apply CH; auto.
  - dependent destruction H0. constructor.
    intros. apply CH; auto.
Qed.

#[global] Instance equ_weq {E B X Y} : Proper (weq ==> weq) (@equ E B X Y) := op_leq_weq_1.

Lemma observe_equ_eq: forall E C X (t u: ctree E C X),
    observe t = observe u -> t ≅ u.
Proof.
  intros.
  step. rewrite H. reflexivity.
Qed.

(* Transitivity for equ with arbitrary relation *)

Definition hsquare {X Y Z} (R : rel X Y) (R' : rel Y Z) :=
  fun x x'' => exists x', R x x' /\ R' x' x''.

Lemma hsquare_eq_l : forall {X Y} (R : rel X Y) x y,
  R x y <-> hsquare eq R x y.
Proof.
  split; intros.
  - exists x. auto.
  - now destruct H as (? & -> & ?).
Qed.

Lemma hsquare_eq_r : forall {X Y} (R : rel X Y) x y,
  R x y <-> hsquare R eq x y.
Proof.
  split; intros.
  - exists y. auto.
  - now destruct H as (? & ? & ->).
Qed.

Lemma equ_trans {E B X Y Z R R'} :
  forall (t : ctree E B X) (u : ctree E B Y) (v : ctree E B Z),
  equ R t u -> equ R' u v -> equ (hsquare R R') t v.
Proof.
  coinduction RR CH. intros.
  step in H. step in H0.
  do 3 red. cbn.
  destruct (observe t), (observe u); (try now inv H); destruct (observe v); try now inv H0; eauto.
  - dependent destruction H. dependent destruction H0.
    constructor. now exists r0.
  - dependent destruction H. dependent destruction H0. eauto.
  - dependent destruction H. dependent destruction H0. eauto.
  - dependent destruction H. dependent destruction H0.
    constructor. intros. apply CH with (u := k0 x); auto.
  - dependent destruction H. dependent destruction H0.
    constructor. intros. apply CH with (u := k0 x); auto.
Qed.

(*|
Up-to bind principle
~~~~~~~~~~~~~~~~~~~~
Consider two computations explicitely built as sequences
[t >>= k] and [u >>= l]. When trying to prove that they are
bisimilar via a coinductive proof, one is faced with a goal
of the shape:
[t_equ RR r (t >>= k) (u >>= l)]
One can of course case analysis on the structure of [t] and [u]
to make progress in the proof.
But if we know from another source that [t ≅ u], we would like
to be able to simply "match" these prefixes, and continue the
coinductive proof over the continuations.
Such a reasoning is dubbed "up-to bind" reasoning, which we
prove sound in the following.

More formally, this corresponds as always to establishing that
the appropriate function is a valid enhancement. The function
in question here is:
f R = {(bind t k, bind u l) | equ SS t u /\ forall x y, SS x y -> R (k x) (l x)}

|*)
Section bind.

(*|
Heterogeneous [pair], todo move to coinduction library
|*)
  Definition pointwise {X X' Y Y'} (SS : rel X X')
    : rel Y Y' -> rel (X -> Y) (X' -> Y') :=
    fun R k k' => forall x x', SS x x' -> R (k x) (k' x').

  Definition pairH {A B : Type} (x : A) (y : B) : A -> B -> Prop :=
    fun x' y' => x = x' /\ y = y'.

  Lemma leq_pairH : forall {A B : Type} (x : A) (y : B) (R : rel A B),
      R x y <-> pairH x y <= R.
  Proof.
    firstorder congruence.
  Qed.

  Section Bind_ctx.

    (* TODO: Comment *)
    (* TODO: Can we define the underlying generic closure in the style of the old [bind_ctx]? *)
    Lemma equ_bind_chain_gen
      {E B: Type -> Type} {X X' Y Y': Type} (SS : X -> X' -> Prop) (RR : Y -> Y' -> Prop)
      {R : Chain (@fequ E B Y Y' RR)} :
      forall (t : ctree E B X) (t' : ctree E B X') (k : X -> ctree E B Y) (k' : X' -> ctree E B Y'),
        equ SS t t' ->
        (forall x x', SS x x' -> elem R (k x) (k' x')) ->
        elem R (bind t k) (bind t' k').
    Proof.
      apply tower.
      - intros ? INC ? ? ? ? tt' kk' ? ?.
        apply INC. apply H. apply tt'.
        intros x x' xx'. apply leq_infx in H. apply H. now apply kk'.
      - intros ? ? ? ? ? ? tt' kk'.
        step in tt'.
        cbn. unfold observe. cbn.
        destruct tt'.
        + now apply kk'.
        + constructor.
        + constructor. apply H. apply REL.
          intros. apply (b_chain x). now apply kk'.
        + constructor. apply H. apply REL.
          intros. apply (b_chain x). now apply kk'.
        + constructor. intros. apply H. apply REL.
          intros. apply (b_chain x). now apply kk'.
        + constructor. intros. apply H. apply REL.
          intros. apply (b_chain x). now apply kk'.
    Qed.

    #[global] Instance equ_bind_chain
      {E B: Type -> Type} {X Y: Type} (RR : Y -> Y -> Prop)
      {R : Chain (@fequ E B Y Y RR)} :
      Proper (equ eq ==>
                (pointwise_relation _ (elem R)) ==>
                (elem R)) (@bind E B X Y).
    Proof.
      repeat intro; eapply equ_bind_chain_gen; eauto.
      intros ?? <-; auto.
    Qed.

    #[global] Instance equ_bind
      {E B: Type -> Type} {X Y: Type} (RR : Y -> Y -> Prop) :
      Proper (equ eq ==>
                (pointwise_relation _ (equ RR)) ==>
                (equ RR)) (@CTree.bind E B X Y).
    Proof.
      apply equ_bind_chain.
    Qed.

  End Bind_ctx.

(*|
Specialization of [bind_ctx] to the [equ]-based closure we are
looking for, and the proof of validity of the principle. As
always with the companion, we prove that it is valid by proving
that it si below the companion.
|*)
End bind.

(*|
Specializing these congruence lemmas at the [sbisim] level for equational proofs
|*)
Lemma equ_clo_bind (E B: Type -> Type) (X1 X2 Y1 Y2 : Type) :
	forall (t1 : ctree E B X1) (t2 : ctree E B X2) (k1 : X1 -> ctree E B Y1) (k2 : X2 -> ctree E B Y2)
    (S : rel X1 X2) (R : rel Y1 Y2),
		equ S t1 t2 ->
    (forall x1 x2, S x1 x2 -> equ R (k1 x1) (k2 x2)) ->
    equ R (bind t1 k1) (bind t2 k2)
.
Proof.
  intros.
  eapply equ_bind_chain_gen; eauto.
Qed.

Lemma equ_clo_bind_eq (E B: Type -> Type) (X Y1 Y2 : Type) :
	forall (t : ctree E B X) (k1 : X -> ctree E B Y1) (k2 : X -> ctree E B Y2)
    (R : rel Y1 Y2),
    (forall x, equ R (k1 x) (k2 x)) ->
    equ R (bind t k1) (bind t k2)
.
Proof.
  intros * EQ.
  eapply equ_clo_bind.
  reflexivity.
  intros ? ? <-.
  apply EQ.
Qed.


(*|
Up-to [equ eq] bisimulations
----------------------------
The transitivity of the [et R] gives us "equ bisimulation up-to equ". Looking forward,
in order to establish "up-to equ" principles for other bisimulations, we define here the
associated enhancing function.
|*)

(*|
Definition of the enhancing function
|*)
Variant equ_clos_body {E F C D X1 X2} (R : rel (ctree E C X1) (ctree F D X2)) : (rel (ctree E C X1) (ctree F D X2)) :=
  | Equ_clos : forall t t' u' u
                 (Equt : t ≅ t')
                 (HR : R t' u')
                 (Equu : u' ≅ u),
      equ_clos_body R t u.

Program Definition equ_clos {E F C D X1 X2} : mon (rel (ctree E C X1) (ctree F D X2)) :=
  {| body := @equ_clos_body E F C D X1 X2 |}.
Next Obligation.
  intros * ?? LE t u EQ; inv EQ.
  econstructor; eauto.
  apply LE; auto.
Qed.

(*|
Sufficient condition to prove compatibility only over the simulation
|*)
Lemma equ_clos_sym {E C X} : compat converse (@equ_clos E E C C X X).
Proof.
  intros R t u EQ; inv EQ.
  apply Equ_clos with u' t'; intuition.
Qed.

Lemma equ_clos_equ {E C X L} {c: Chain (fequ L)}:
  forall x y, @equ_clos E E C C X X (elem c) x y -> (elem c) x y.
Proof.
  apply tower.
  - intros ? INC x y [x' y' x'' y'' EQ' EQ''] ??. red.
    apply INC; auto.
    econstructor; eauto.
    apply leq_infx in H.
    now apply H.
  - clear; intros c IH ?? [].
    step in Equt; step in Equu; cbn in *.
    inv Equt; rewrite <- H in HR; clear H H0 t t'.
    all:inv HR; rewrite <- H in Equu.
    all:try now inv Equu; eauto.
    inv Equu; constructor; apply IH; econstructor; eauto.
    inv Equu; constructor; apply IH; econstructor; eauto.
    dependent induction H1; dependent induction H2. inv Equu.
    dependent induction H2; dependent induction H3.
    econstructor; intros. apply IH; econstructor; eauto.
    dependent induction H1; dependent induction H2. inv Equu.
    dependent induction H2; dependent induction H3.
    econstructor; intros. apply IH; econstructor; eauto.
Qed.

#[global] Instance equ_eq_equ_goal_gen {E C R L} (r : Chain (@fequ E C R R L)) :
  Proper (equ eq ==> equ eq ==> flip impl)
	  (elem r).
Proof.
  repeat intro.
  apply equ_clos_equ; econstructor; eauto; now symmetry.
Qed.

#[global] Instance equ_eq_equ_hyp_gen {E C R L} (r : Chain (@fequ E C R R L)) :
  Proper (equ eq ==> equ eq ==> impl)
	  (elem r).
Proof.
  repeat intro.
  apply equ_clos_equ; econstructor; [| eassumption |]; eauto; now symmetry.
Qed.

Lemma equ_clo_bind_gen_eq (E B: Type -> Type) (X Y1 Y2 : Type)
  (RR : rel Y1 Y2) (R : Chain (@fequ E B Y1 Y2 RR)) :
	forall (t : ctree E B X) (k1 : X -> ctree E B Y1) (k2 : X -> ctree E B Y2),
    (forall x, elem R (k1 x) (k2 x)) ->
    elem R (bind t k1) (bind t k2).
Proof.
  intros * EQ.
  apply equ_bind_chain_gen with (SS := eq); auto.
  intros ?? <-; auto.
Qed.

Lemma fequ_bind_chain_gen
  {E B: Type -> Type} {X X' Y Y': Type} (SS : X -> X' -> Prop) (RR : Y -> Y' -> Prop)
  {R : Chain (@fequ E B Y Y' RR)} :
  forall (t : ctree E B X) (t' : ctree E B X') (k : X -> ctree E B Y) (k' : X' -> ctree E B Y'),
    equ SS t t' ->
    (forall x x', SS x x' -> fequ RR (elem R) (k x) (k' x')) ->
    fequ RR (elem R) (bind t k) (bind t' k').
Proof.
  intros.
  apply equ_bind_chain_gen with (SS := SS); auto.
Qed.

Lemma fequ_bind_chain_eq
  {E B: Type -> Type} {X Y Y': Type} (RR : Y -> Y' -> Prop)
  {R : Chain (@fequ E B Y Y' RR)} :
  forall (t : ctree E B X) (k : X -> ctree E B Y) (k' : X -> ctree E B Y'),
    (forall x, fequ RR (elem R) (k x) (k' x)) ->
    fequ RR (elem R) (bind t k) (bind t k').
Proof.
  intros.
  apply fequ_bind_chain_gen with (SS := eq); auto.
  intros ?? <-; auto.
Qed.

Ltac __upto_bind_equ' R :=
  first [apply equ_clo_bind_eq with (SS := R) |
          apply equ_bind_chain_gen with (SS := R)].
Tactic Notation "__upto_bind_equ" uconstr(t) := __upto_bind_equ' t.

Ltac __eupto_bind_equ :=
  first [eapply equ_clo_bind | eapply equ_bind_chain_gen].

Ltac __upto_bind_equ_eq :=
  first [apply equ_clo_bind_eq | apply equ_clo_bind_gen_eq].

(*|
Elementary equational theory
----------------------------
At this point, equipped with our coinductive structural equality,
we can already express some very tight equations. Mainly
- unfolding lemmas for our operations ([bind] and [iter] notably);
- the three monadic laws
|*)
Import CTree.
Import CTreeNotations.
Open Scope ctree.

(*|
Even eta-laws for coinductive data-structures are not valid w.r.t. to [eq]
in Rocq. We however do recover them w.r.t. [equ].
|*)
Lemma ctree_eta_ {E B R} (t : ctree E B R) : t ≅ go (_observe t).
Proof. step. reflexivity. Qed.

Lemma ctree_eta {E B R} (t : ctree E B R) : t ≅ go (observe t).
Proof.
  now step.
Qed.

Lemma unfold_spin {E B R} : @spin E B R ≅ Guard spin.
Proof.
  exact (ctree_eta spin).
Qed.

Notation bind_ t k :=
  match observe t with
  | RetF r => k%function r
  | StuckF => Stuck
  | GuardF t => Guard (bind t k)
  | StepF t => Step (bind t k)
  | VisF e ke => Vis e (fun x => bind (ke x) k)
  | BrF c ke => Br c (fun x => bind (ke x) k)
  end.

Lemma unfold_bind {E B R S} (t : ctree E B R) (k : R -> ctree E B S)
  : bind t k ≅ bind_ t k.
Proof.
	now step.
Qed.

Notation iter_ step i :=
  (lr <- step%function i;;
   match lr with
   | inl l => Guard (iter step l)
   | inr r => Ret r
   end)%ctree.

Lemma unfold_iter {E B R I} (step : I -> ctree E B (I + R)) i:
	iter step i ≅ iter_ step i.
Proof.
	now step.
Qed.

(* TODO: Understand this better *)
(* TODO: Create ctrees database *)
Hint Constants Transparent : core.
Ltac desobs' t := cbn; desobs t; cbn; eauto.
Tactic Notation "desobs" "*" ident(t) := desobs' t.

Notation "t '[≡' R ']' u" := (fequ R (elem _) t u) (at level 90, only printing).

(*|
Monadic laws
------------
The three usual monadic laws can be estalished w.r.t. [equ eq].
|*)
Lemma bind_ret_l {E B X Y} : forall (x : X) (k : X -> ctree E B Y),
    Ret x >>= k ≅ k x.
Proof.
  intros.
  now rewrite unfold_bind.
Qed.

Lemma bind_ret_r {E B X} : forall (t : ctree E B X),
    x <- t;; Ret x ≅ t.
Proof.
  coinduction S CIH.
  intros t.
  rewrite unfold_bind.
  cbn; desobs t; eauto.
Qed.

Lemma bind_bind {E B X Y Z} : forall (t : ctree E B X) (k : X -> ctree E B Y) (l : Y -> ctree E B Z),
    (t >>= k) >>= l ≅ t >>= (fun x => k x >>= l).
Proof.
  coinduction S CIH; intros.
  rewrite (ctree_eta t). cbn.
  desobs t; cbn; eauto.
Qed.

(*|
Structural rules
|*)
Lemma bind_vis {E B X Y Z} (e : E X) (k : X -> ctree E B Y) (g : Y -> ctree E B Z):
  Vis e k >>= g ≅ Vis e (fun x => k x >>= g).
Proof.
  now rewrite unfold_bind.
Qed.

Lemma bind_trigger {E B X Y} (e : E X) (k : X -> ctree E B Y) :
  trigger e >>= k ≅ Vis e k.
Proof.
  unfold trigger; rewrite bind_vis; setoid_rewrite bind_ret_l.
  reflexivity.
Qed.

Lemma bind_stuck {E B X Y} (g : X -> ctree E B Y):
  Stuck >>= g ≅ Stuck.
Proof.
  now rewrite unfold_bind.
Qed.

Lemma bind_guard {E B X Y} (t : ctree E B X) (g : X -> ctree E B Y):
  Guard t >>= g ≅ Guard (t >>= g).
Proof.
  now rewrite unfold_bind.
Qed.

Lemma bind_step {E B X Y} (t : ctree E B X) (g : X -> ctree E B Y):
  Step t >>= g ≅ Step (t >>= g).
Proof.
  now rewrite unfold_bind.
Qed.

Lemma bind_br {E B X Y Z} (c : B X) (k : X -> ctree E B Y) (g : Y -> ctree E B Z):
  Br c k >>= g ≅ Br c (fun x => k x >>= g).
Proof.
  now rewrite unfold_bind.
Qed.

Lemma bind_branch : forall {E C X Y} (c : C Y) (k : Y -> ctree E C X),
    branch c >>= k ≅ Br c k.
Proof.
  intros. rewrite unfold_bind. cbn. setoid_rewrite bind_ret_l.
  reflexivity.
Qed.

Tactic Notation "sinv" ident(H) := step in H; inv H.

Lemma stuck_equ_bind {E B X Y} :
  forall (t : ctree E B X) (k' : X -> ctree E B Y),
  x <- t;; k' x ≅ Stuck ->
  (exists r, t ≅ Ret r /\ k' r ≅ Stuck) \/ t ≅ Stuck.
Proof.
  intros.
  destruct (observe t) eqn:?.
  - left. exists r. rewrite ctree_eta, Heqc. split; auto.
    rewrite (ctree_eta t), Heqc, unfold_bind in H. cbn in H; auto.
  - right. rewrite ctree_eta, Heqc. reflexivity.
  - rewrite (ctree_eta t), Heqc, bind_step in H. sinv H.
  - rewrite (ctree_eta t), Heqc, bind_guard in H. sinv H.
  - rewrite (ctree_eta t), Heqc, bind_vis in H. sinv H.
  - rewrite (ctree_eta t), Heqc, bind_br in H. sinv H.
Qed.

Lemma guard_equ_bind {E B X Y} :
  forall (t : ctree E B X) (k' : X -> ctree E B Y) u,
  x <- t;; k' x ≅ Guard u ->
  (exists r, t ≅ Ret r /\ k' r ≅ Guard u) \/ exists t', t ≅ Guard t' /\ t' >>= k' ≅ u.
Proof.
  intros.
  destruct (observe t) eqn:?.
  - left. exists r. rewrite ctree_eta, Heqc. split; auto.
    rewrite (ctree_eta t), Heqc, unfold_bind in H; cbn in H; auto.
  - rewrite (ctree_eta t), Heqc, bind_stuck in H. sinv H.
  - rewrite (ctree_eta t), Heqc, bind_step in H. sinv H.
  - right. rewrite (ctree_eta t), Heqc, bind_guard in H.
    sinv H.
    exists t0; split; auto. now apply observe_equ_eq.
  - rewrite (ctree_eta t), Heqc, bind_vis in H. sinv H.
  - rewrite (ctree_eta t), Heqc, bind_br in H. sinv H.
Qed.

Lemma step_equ_bind {E B X Y} :
  forall (t : ctree E B X) (k' : X -> ctree E B Y) u,
  x <- t;; k' x ≅ Step u ->
  (exists r, t ≅ Ret r /\ k' r ≅ Step u) \/ exists t', t ≅ Step t' /\ t' >>= k' ≅ u.
Proof.
  intros.
  destruct (observe t) eqn:?.
  - left. exists r. rewrite ctree_eta, Heqc; split; auto.
    now rewrite unfold_bind, Heqc in H.
  - rewrite (ctree_eta t), Heqc, bind_stuck in H. sinv H.
  - rewrite (ctree_eta t), Heqc, bind_step in H. sinv H.
    right; exists t0; split; auto. now apply observe_equ_eq.
  - rewrite (ctree_eta t), Heqc, bind_guard in H. sinv H.
  - rewrite (ctree_eta t), Heqc, bind_vis in H. sinv H.
  - rewrite (ctree_eta t), Heqc, bind_br in H. sinv H.
Qed.

Lemma vis_equ_bind {E B X Y Z} :
  forall (t : ctree E B X) (e : E Z) k (k' : X -> ctree E B Y),
  x <- t;; k' x ≅ Vis e k ->
  (exists r, t ≅ Ret r /\ k' r ≅ Vis e k) \/
  exists k0, t ≅ Vis e k0 /\ forall x, k x ≅ x <- k0 x;; k' x.
Proof.
  intros.
  destruct (observe t) eqn:?.
  - left. exists r. rewrite ctree_eta, Heqc; split; auto.
    now rewrite unfold_bind, Heqc in H.
  - rewrite (ctree_eta t), Heqc, bind_stuck in H.
    sinv H.
  - rewrite (ctree_eta t), Heqc, bind_step in H.
    sinv H.
  - rewrite (ctree_eta t), Heqc, bind_guard in H.
    sinv H.
  - rewrite (ctree_eta t), Heqc, bind_vis in H.
    apply equ_vis_invT in H as ?. subst.
    pose proof (equ_vis_invE _ _ _ _ H). destruct H0. subst.
    right. exists k0. split.
    + rewrite (ctree_eta t), Heqc. reflexivity.
    + cbn in H1. symmetry in H1. apply H1.
  - rewrite (ctree_eta t), Heqc, bind_br in H. step in H. inv H.
Qed.

Lemma br_equ_bind {E B X Y} :
  forall (t : ctree E B X) Z (ch : B Z) k (k' : X -> ctree E B Y),
  x <- t;; k' x ≅ Br ch k ->
  (exists r, t ≅ Ret r /\ k' r ≅ Br ch k) \/
  exists k0, t ≅ Br ch k0 /\ forall x, k x ≅ x <- k0 x;; k' x.
Proof.
  intros.
  destruct (observe t) eqn:?.
  - left. exists r. rewrite ctree_eta, Heqc; split; auto.
    rewrite (ctree_eta t), Heqc, unfold_bind in H; cbn in H; auto.
  - rewrite (ctree_eta t), Heqc, bind_stuck in H. sinv H.
  - rewrite (ctree_eta t), Heqc, bind_step in H. sinv H.
  - rewrite (ctree_eta t), Heqc, bind_guard in H. sinv H.
  - rewrite (ctree_eta t), Heqc, bind_vis in H. step in H. inv H.
  - rewrite (ctree_eta t), Heqc, bind_br in H.
    apply equ_br_invT in H as ?. subst.
    pose proof (equ_br_invE _ _ _ _ H) as [<- ?].
    right. exists k0. split.
    + rewrite (ctree_eta t), Heqc. reflexivity.
    + cbn in H0. symmetry in H0. apply H0.
Qed.

Lemma ret_equ_bind {E B X Y} :
  forall (t : ctree E B Y) (k : Y -> ctree E B X) r,
  x <- t;; k x ≅ Ret r ->
  exists r1, t ≅ Ret r1 /\ k r1 ≅ Ret r.
Proof.
  intros. setoid_rewrite (ctree_eta t) in H. setoid_rewrite (ctree_eta t).
  destruct (observe t) eqn:?.
  - rewrite bind_ret_l in H. eauto.
  - rewrite bind_stuck in H. sinv H.
  - rewrite bind_step in H. sinv H.
  - rewrite bind_guard in H. sinv H.
  - rewrite bind_vis in H. sinv H.
  - rewrite bind_br in H. sinv H.
Qed.

Lemma unfold_forever {E C X}: forall (k: X -> ctree E C X) (i: X),
    forever k i ≅ r <- k i ;; Guard (forever k r).
Proof.
  intros k i.
  rewrite (ctree_eta (forever k i)).
  rewrite unfold_forever_.
  rewrite <- ctree_eta.
  reflexivity.
Qed.

(*|
Map
|*)
#[global] Instance map_equ {E B X Y} f :
  Proper (equ eq ==> equ eq) (@CTree.map E B X Y f).
Proof.
  do 2 red. intros.
  unfold CTree.map.
  apply equ_clo_bind with eq.
  apply H. intros. subst. reflexivity.
Qed.

Lemma map_map {E B R S T}: forall (f : R -> S) (g : S -> T) (t : ctree E B R),
    map g (map f t) ≅ map (fun x => g (f x)) t.
Proof.
  unfold map. intros. rewrite bind_bind. setoid_rewrite bind_ret_l. reflexivity.
Qed.

Lemma bind_map {E B R S T}: forall (f : R -> S) (k: S -> ctree E B T) (t : ctree E B R),
    bind (map f t) k ≅ bind t (fun x => k (f x)).
Proof.
  unfold map. intros. rewrite bind_bind. setoid_rewrite bind_ret_l. reflexivity.
Qed.

Lemma map_bind {E B X Y Z} (t: ctree E B X) (k: X -> ctree E B Y) (f: Y -> Z) :
  (map f (bind t k)) ≅ bind t (fun x => map f (k x)).
Proof.
  intros. unfold map. apply bind_bind.
Qed.

Lemma map_ret {E B X Y} (f : X -> Y) (x : X) :
    @map E B _ _ f (Ret x) ≅ Ret (f x).
Proof.
  intros. unfold map.
  rewrite bind_ret_l; reflexivity.
Qed.

Lemma map_guard {E B X Y} (f : X -> Y) :
  forall (t : ctree E B X),
  CTree.map f (Guard t) ≅ Guard (CTree.map f t).
Proof.
  intros. unfold map.
  rewrite bind_guard. reflexivity.
Qed.

Lemma map_step {E B X Y} (f : X -> Y) :
  forall (t : ctree E B X),
  CTree.map f (Step t) ≅ Step (CTree.map f t).
Proof.
  intros. unfold map.
  rewrite bind_step; reflexivity.
Qed.

Notation "▷ e" := (subevent _ e) (at level 0, only printing).

(*|
Convenience: all child-less invisible brs can be proved [equ], no need to work w.r.t. a bisim
|*)

Lemma br_equ': forall (E B: Type -> Type) R Y (c : B Y) (k k': Y -> ctree E B R) Q,
    (forall t, k t (≅ Q) k' t) ->
    Br c k (≅ Q) Br c k'.
Proof.
  intros * EQ.
  step; econstructor; auto.
Qed.

Lemma br_equ: forall (E B: Type -> Type) R Y (c : B Y) (k k': Y -> ctree E B R),
    (forall t, k t ≅ k' t) ->
    Br c k ≅ Br c k'.
Proof.
  intros E B R Y c k k'.
  exact (br_equ' E B R Y c k k' eq).
Qed.

#[global] Instance fequ_proper {E B R} {S : Chain (@fequ E B R R eq)} : Proper (equ eq ==> equ eq ==> flip impl) (fequ eq (elem S)).
Proof.
  intros ?? eq1 ?? eq2 ?.
  now rewrite eq1, eq2.
Qed.

Tactic Notation "ibind" := eapply equ_bind_chain; [try reflexivity | unfold pointwise_relation].

Tactic Notation "iguard" := constructor.

#[global] Instance proper_equ_forever {E C X} :
  Proper (pointwise_relation X (@equ E C X X eq) ==> eq ==> @equ E C X X eq) forever.
Proof.
  unfold Proper, respectful; intros; subst.
  revert y0; coinduction R CIH; intros.
  rewrite (unfold_forever_ x), (unfold_forever_ y).
  rewrite H.
  ibind.
  intros.
  iguard.
  apply CIH.
Qed.

(*|
Inversion of [≅] hypotheses
|*)

Ltac subst_hyp_in EQ h :=
  match type of EQ with
  | ?x = ?x => clear EQ
  | ?x = ?y => subst x || subst y || rewrite EQ in h
  end.

Ltac inv_equ h :=
  match type of h with
  | ?t (≅?Q) ?u =>
      (* ctree_head_in t h; ctree_head_in u h; *)
      try solve [ step in h; inv h; (idtac || invert) | step in h; dependent induction h ]
  end;
  match type of h with
  | Ret _ (≅?Q) Ret _ =>
      apply equ_ret_inv in h;
      subst
  | Vis _ _ (≅?Q) Vis _ _ =>
      let EQt := fresh "EQt" in
      let EQe := fresh "EQe" in
      let EQ := fresh "EQ" in
      apply equ_vis_invT in h as EQt;
      subst_hyp_in EQt h;
      apply equ_vis_invE in h as [EQe EQ];
      subst
  | Br _ _ (≅?Q) Br _ _ =>
      let EQt := fresh "EQt" in
      let EQe := fresh "EQe" in
      let EQ := fresh "EQ" in
      apply equ_br_invT in h as EQt;
      subst_hyp_in EQt h;
      apply equ_br_invE in h as [EQe EQ];
      subst
  | Guard _ (≅?Q) Guard _ =>
      apply equ_guard_inv in h
  | Step _ (≅?Q) Step _ =>
      apply equ_step_inv in h
   end.

Ltac inv_equ_one :=
  multimatch goal with
  | [ h : _ (≅?Q) _ |- _ ] =>
      inv_equ h
  end.

Ltac inv_equ_all := repeat inv_equ_one.

Tactic Notation "inv_equ" hyp(h) := inv_equ h.
Tactic Notation "inv_equ" := inv_equ_all.

(*|
Very crude simulation of [subst] for [≅] equations
|*)

Ltac subs_aux x h :=
  match goal with
  | [ h' : context[x] |- _ ] =>
      rewrite h in h'; subs_aux x h
  | [ |- context[x] ] =>
      rewrite h; subs_aux x h
  | _ => clear x h
  end.

Ltac subs x :=
  match goal with
  | [ h : x ≅ _ |- _ ] =>
      subs_aux x h
  | [ h : _ ≅ x |- _ ] =>
      subs_aux x h
  end.

Ltac subs_one :=
  multimatch goal with
  | [ t : _ |- _ ] =>
      subs t
  end.

Ltac subs_all := repeat subs_one.

Tactic Notation "subs" hyp(h) := subs h.
Tactic Notation "subs" := subs_all.
