(*|
==============================
Syntactic equality over ctrees
==============================
As always with coinductive structures in Coq, [eq] is too strong
to be usable. We hence define through this file [equ], a coinductive
syntactic equality over the structure. [equ] enforces the trees to
have the exact same shape, constructor by constructor.

This relation is analogous to what is dubbed as _strong bisimulation_
for [itree], but we are trying to avoid this terminology here since
we reserve the notion of bisimulation for the equivalence relations
that take internal non-determinism into account.

.. coq:: none
|*)
From Coq Require Import RelationClasses Program.

From Coinduction Require Import
	coinduction rel tactics.

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
  | Eq_Vis {X} (e : E X) k1 k2
      (REL : forall x, eq (k1 x) (k2 x)) :
      equb eq (VisF e k1) (VisF e k2)
  | Eq_Br b {X} {c : B X} k1 k2
              (REL : forall x, eq (k1 x) (k2 x)) :
      equb eq (BrF b c k1) (BrF b c k2)
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

Ltac __coinduction_equ R H :=
  unfold equ; apply_coinduction; fold_equ; intros R H.

Tactic Notation "__step_equ" :=
  match goal with
  | |- context [@equ ?E ?B ?R1 ?R2 ?RR _ _] =>
      unfold equ;
      step;
      fold_equ
  end.

#[local] Tactic Notation "step" := __step_equ || step.

#[local] Tactic Notation "coinduction" simple_intropattern(R) simple_intropattern(H) :=
  __coinduction_equ R H.

Ltac __step_in_equ H :=
  match type of H with
  | context [@equ ?E ?B ?R1 ?R2 ?RR _ _] =>
      unfold equ in H;
      step in H;
      fold (@equ E B R1 R2 RR) in H
  end.

#[local] Tactic Notation "step" "in" ident(H) := __step_in_equ H || step in H.

Module EquNotations.

  Infix "≅" := (equ eq) (at level 70).
  Notation "t (≅ Q ) u" := (equ Q t u) (at level 79).
  
(*|
The associated companions:
|*)
  Notation et Q  := (t (fequ Q)).
  Notation eT Q  := (T (fequ Q)).
  Notation ebt Q := (bt (fequ Q)).
  Notation ebT Q := (bT (fequ Q)).
  Notation "t [≅ Q ] u" := (et Q _ t u) (at level 79).
  Notation "t {≅ Q } u" := (ebt Q _ t u) (at level 79).
  Notation "t {{≅ Q }} u" := (equb Q (equ Q) t u) (at level 79).
  Notation "t [≅] u" := (et eq _ t u) (at level 79).
  Notation "t {≅} u" := (ebt eq _ t u) (at level 79).
  Notation "t {{≅}} u" := (equb eq (equ eq) t u) (at level 79).

End EquNotations.

Import EquNotations.

Section equ_theory.

  Context {E B : Type -> Type} {R : Type} (RR : R -> R -> Prop).
  Notation eT  := (coinduction.T (fequ (E := E) (B := B) RR)).
  Notation et  := (coinduction.t (fequ (E := E) (B := B) RR)).
  Notation ebt := (coinduction.bt (fequ (E := E) (B := B) RR)).
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
  Lemma refl_t {RRR: Reflexive RR}: const seq <= et.
  Proof.
    apply leq_t. intro.
    change (@eq (ctree E B R)  <= equb_ RR eq).
    intros p ? <-. cbn. desobs p; auto.
  Qed.

  (*|
[converse] is compatible: up-to symmetry is valid
|*)
  Lemma converse_t {RRS: Symmetric RR}: converse <= et.
  Proof.
    apply leq_t. intros S x y H; cbn. destruct H; auto.
  Qed.

  (*|
[squaring] is compatible: up-to transitivity is valid
|*)
  Lemma square_t {RRR: Reflexive RR} {RRT: Transitive RR}: square <= et.
  Proof.
    apply leq_t.
    intros S x z [y xy yz]; cbn.
    inversion xy; inversion yz; try (exfalso; congruence).
    - constructor. replace y0 with x1 in * by congruence. eauto.
    - rewrite <-H in H2.
      destruct (Vis_eq1 H2).
      destruct (Vis_eq2 H2) as [-> ->].
      constructor. intro x0. now exists (k2 x0).
		                   - rewrite <- H in H2.
			             destruct (Br_eq1 H2); subst.
			             destruct (Br_eq2 H2) as [-> ->].
			             constructor. intros i. now eexists.
  Qed.

  (*|
Having [const eq], [converse] and [square] below the companion entails respectively
that the companion, at all point, is reflexive, symmetric, transitive.
The companion library directly provide these results for bisimilarity, [t R], [b (t R)]
and [T f R].
|*)
  #[global] Instance Equivalence_et `{Equivalence _ RR} S: Equivalence (et S).
  Proof. apply Equivalence_t. apply refl_t. apply square_t. apply converse_t. Qed.
  #[global] Instance Equivalence_T `{Equivalence _ RR} f S: Equivalence (eT f S).
  Proof. apply Equivalence_T. apply refl_t. apply square_t. apply converse_t. Qed.
  #[global] Instance Equivalence_bt `{Equivalence _ RR} S: Equivalence (ebt S).
  Proof. apply Equivalence_bt. apply refl_t. apply square_t. apply converse_t. Qed.

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

Lemma equ_br_invT {E B X Y S S' b b'} {Q : rel S S'} (c1 : B X) (c2 : B Y) (k1 : X -> ctree E B S) k2 :
  Br b c1 k1 (≅Q) Br b' c2 k2 ->
  X = Y /\ b = b'.
Proof.
  intros EQ; step in EQ.
	dependent destruction EQ; auto.
Qed.

Lemma equ_br_invE {E B X S S' b} {Q : rel S S'} (c1 c2 : B X) (k1 : _ -> ctree E B S) k2 :
  Br b c1 k1 (≅Q) Br b c2 k2 ->
   c1 = c2 /\ forall x,k1 x (≅Q) k2 x.
Proof.
  intros EQ; step in EQ.
	inv EQ.
	dependent destruction H.
  now dependent destruction H5.
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

Lemma equb_br_invT {E B X Y S b b'} (c1 : B X) (c2 : B Y) (k1 : _ -> ctree E B S) k2 :
  equb eq (equ eq) (BrF b c1 k1) (BrF b' c2 k2) ->
  X = Y /\ b = b'.
Proof.
  intros EQ.
	dependent induction EQ; auto.
Qed.

Lemma equb_br_invE {E B X S b} (c1 c2 : B X) (k1 : _ -> ctree E B S) k2 :
  equb eq (equ eq) (BrF b c1 k1) (BrF b c2 k2) ->
  c1 = c2 /\ forall x, equ eq (k1 x) (k2 x).
Proof.
  intros EQ.
  inv EQ.
  dependent destruction H. now dependent destruction H5.
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

#[global] Instance equ_BrF {E B R X} b (c : B X) :
  Proper (pointwise_relation _ (equ eq) ==> going (equ eq)) (@BrF E B R _ b _ c).
Proof.
  constructor. red in H. step. econstructor; eauto.
Qed.

#[global] Instance equ_Guard:
  forall {E B : Type -> Type} {R : Type} `{B1 -< B},
    Proper (equ eq ==> equ eq) (@Guard E B R _).
Proof.
  repeat intro.
  unfold Guard; now setoid_rewrite H0.
Qed.

#[global] Instance equ_Step:
  forall {E B : Type -> Type} {R : Type} `{B1 -< B},
    Proper (equ eq ==> equ eq) (@Step E B R _).
Proof.
  repeat intro.
  unfold Step; now setoid_rewrite H0.
Qed.

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

#[global] Instance equ_eq_equ {E B R r} :
  Proper (going (equ eq) ==> eq ==> flip impl)
	     (@equb E B R R eq (et eq r)).
Proof.
  unfold Proper, respectful, flip, impl. intros. subst.
  inv H. step in H0. inv H0; inv H1; auto.
  - invert.
    subst. constructor. intros. rewrite REL. auto.
  - invert.
    subst. constructor. intros. rewrite REL. auto.
Qed.

#[global] Instance eq_equ_equ {E B R r} :
  Proper (eq ==> going (equ eq) ==> flip impl)
	     (@equb E B R R eq (et eq r)).
Proof.
  unfold Proper, respectful, flip, impl. intros. subst.
  inv H0. step in H. inv H; inv H1; auto.
  - invert.
    subst. constructor. intros. rewrite REL. auto.
  - invert.
    subst. constructor. intros. rewrite REL. auto.
Qed.

#[global] Instance equ_clos_eT_goal {E B R} RR f :
  Proper (@equ E B R R eq ==> equ eq ==> flip impl) (eT eq f RR).
Proof.
  cbn; intros ? ? eq1 ? ? eq2 H.
  rewrite eq1, eq2.
  auto.
Qed.

#[global] Instance equ_clos_eT_ctx {E B R} RR f :
  Proper (@equ E B R R eq ==> equ eq ==> impl) (eT eq f RR).
Proof.
  cbn; intros ? ? eq1 ? ? eq2 H.
  rewrite <- eq1, <- eq2.
  auto.
Qed.

#[global] Instance equ_leq {E B X Y} : Proper (leq ==> leq) (@equ E B X Y).
Proof.
  unfold Proper, respectful, flip, impl. cbn. unfold impl.
  intros R R'. coinduction RR CH. intros.
  do 3 red. cbn. step in H0.
  destruct (observe a), (observe a0); try now inv H0.
  - dependent destruction H0. constructor. now apply H.
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
  destruct (observe t), (observe u); (try now inv H); destruct (observe v); try now inv H0.
  - dependent destruction H. dependent destruction H0.
    constructor. now exists r0.
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

    Context {E F C D: Type -> Type} {X X' Y Y': Type}.

(*|
Most general contextualisation function associated to bind].
Can be read more digestly as, where R is a relation on ctrees
(the prefixes of the binds) and S on the continuations:
bind_ctx R S = {(bind t k, bind t' k') | R t t' /\ S k k'}

Note that at this point, this is more general that what we are
interested in: we will specialize [R] and [S] for our purpose,
first here w.r.t. to [equ], later w.r.t. to other relations over
[ctree]s.

Remark: the Coinduction library provides generic binary contexts
[binary_ctx], but whose both arguments are at the same types.
We could provide an heterogeneous version of [binary_ctx] and have
[bind_ctx] be an instance of it to avoid having to rethink in terms
of [sup_all] locally.
|*)

    Definition bind_ctx
               (R: rel (ctree E C X) (ctree F D X'))
               (S: rel (X -> ctree E C Y) (X' -> ctree F D Y')):
      rel (ctree E C Y) (ctree F D Y') :=
      sup_all (fun x => sup (R x)
                         (fun x' => sup_all
                                   (fun k => sup (S k)
                                              (fun k' => pairH (bind x k) (bind x' k'))))).

    (*|
Two lemmas to interact with [bind_ctx] before making it opaque:
- [leq_bind_ctx] specifies relations above the context
- [in_bind_ctx] specifies how to populate it
|*)
    Lemma leq_bind_ctx:
      forall R S S', bind_ctx R S <= S' <->
                  (forall x x', R x x' -> forall k k', S k k' -> S' (bind x k) (bind x' k')).
    Proof.
      intros.
      unfold bind_ctx.
      setoid_rewrite sup_all_spec.
      setoid_rewrite sup_spec.
      setoid_rewrite sup_all_spec.
      setoid_rewrite sup_spec.
      setoid_rewrite <-leq_pairH.
      firstorder.
    Qed.

    Lemma in_bind_ctx (R S :rel _ _) x x' y y':
      R x x' -> S y y' -> bind_ctx R S (bind x y) (bind x' y').
    Proof. intros. now apply ->leq_bind_ctx. Qed.
    #[global] Opaque bind_ctx.

  End Bind_ctx.

(*|
Specialization of [bind_ctx] to the [equ]-based closure we are
looking for, and the proof of validity of the principle. As
always with the companion, we prove that it is valid by proving
that it si below the companion.
|*)
  Section Equ_Bind_ctx.

    Context {E C: Type -> Type} {X1 X2 Y1 Y2: Type}.

(*|
Specialization of [bind_ctx] to a function acting with [equ] on the bound value,
and with the argument (pointwise) on the continuation.
|*)
    Program Definition bind_ctx_equ (SS: rel X1 X2): mon (rel (ctree E C Y1) (ctree E C Y2)) :=
      {|body := fun R => @bind_ctx E E C C X1 X2 Y1 Y2 (equ SS) (pointwise SS R) |}.
    Next Obligation.
      intros ??? H. apply leq_bind_ctx. intros ?? H' ?? H''.
      apply in_bind_ctx. apply H'. intros t t' HS. apply H0, H'', HS.
    Qed.

(*|
The resulting enhancing function gives a valid up-to technique
|*)
    Lemma bind_ctx_equ_t (SS : rel X1 X2) (RR : rel Y1 Y2): bind_ctx_equ SS <= et RR.
    Proof.
      apply Coinduction. intros R. apply (leq_bind_ctx _).
      intros x x' xx' k k' kk'.
      step in xx'.
      cbn; unfold observe; cbn.
      destruct xx'.
      - cbn in *.
        generalize (kk' _ _ REL).
        apply (fequ RR).
        apply id_T.
      - constructor; intros ?. apply (fTf_Tf (fequ _)).
        apply in_bind_ctx. apply REL.
        red; intros. apply (b_T (fequ _)), kk'; auto.
      - constructor. intro a. apply (fTf_Tf (fequ _)).
        apply in_bind_ctx. apply REL.
        red; intros. apply (b_T (fequ _)), kk'; auto.
    Qed.

  End Equ_Bind_ctx.

End bind.

(*|
Expliciting the reasoning rule provided by the up-to principle.
|*)

Lemma et_clo_bind (E B: Type -> Type) (X1 X2 Y1 Y2 : Type) :
	forall (t1 : ctree E B X1) (t2 : ctree E B X2) (k1 : X1 -> ctree E B Y1) (k2 : X2 -> ctree E B Y2)
    (S : rel X1 X2) (R : rel Y1 Y2) RR,
		equ S t1 t2 ->
    (forall x1 x2, S x1 x2 -> et R RR (k1 x1) (k2 x2)) ->
    et R RR (bind t1 k1) (bind t2 k2)
.
Proof.
  intros.
  apply (ft_t (bind_ctx_equ_t S R)).
  now apply in_bind_ctx.
Qed.

Lemma et_clo_bind_eq (E B: Type -> Type) (X Y1 Y2 : Type) :
	forall (t : ctree E B X) (k1 : X -> ctree E B Y1) (k2 : X -> ctree E B Y2)
    (R : rel Y1 Y2) RR,
    (forall x, et R RR (k1 x) (k2 x)) ->
    et R RR (bind t k1) (bind t k2)
.
Proof.
  intros * EQ.
  apply (ft_t (bind_ctx_equ_t (X2 := X) eq R)).
  apply in_bind_ctx.
  reflexivity.
  intros ? ? <-.
  apply EQ.
Qed.

(*|
And in particular, we get the proper instance justifying rewriting [equ]
to the left of a [bind].
|*)
#[global] Instance bind_equ_cong :
 forall (E B : Type -> Type) (X Y : Type) (R : rel Y Y) RR,
   Proper (equ (@eq X) ==> pointwise_relation X (et R RR) ==> et R RR) (@bind E B X Y).
Proof.
  repeat red. intros.
  eapply et_clo_bind; eauto.
  intros ? ? <-; auto.
Qed.

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
  apply (ft_t (bind_ctx_equ_t S R)).
  now apply in_bind_ctx.
Qed.

Lemma equ_clo_bind_eq (E B: Type -> Type) (X Y1 Y2 : Type) :
	forall (t : ctree E B X) (k1 : X -> ctree E B Y1) (k2 : X -> ctree E B Y2)
    (R : rel Y1 Y2),
    (forall x, equ R (k1 x) (k2 x)) ->
    equ R (bind t k1) (bind t k2)
.
Proof.
  intros * EQ.
  apply (ft_t (bind_ctx_equ_t (X2 := X) eq R)).
  apply in_bind_ctx.
  reflexivity.
  intros ? ? <-.
  apply EQ.
Qed.

#[global] Instance bind_equ_equ_cong :
  forall (E B : Type -> Type) (X Y : Type) (R : rel Y Y) RR,
    Proper (equ (equ (@eq X)) ==> pointwise (equ eq) (et R RR) ==> et R RR)
           (@CTree.bind E B (ctree E B X) Y).
Proof.
  repeat red; intros.
  eapply et_clo_bind; eauto.
Qed. 

Ltac __upto_bind_equ' SS :=
  match goal with
    (* Out of a coinductive proof --- terminology abuse, this is simply using the congruence of the relation, not a upto *)
    |- @equ ?E ?B ?R1 ?R2 ?RR (CTree.bind (T := ?T1) _ _) (CTree.bind (T := ?T2) _ _) =>
      apply (@equ_clo_bind E B T1 T2 R1 R2 _ _ _ _ SS RR)

    (* Upto when unguarded *)
  | |- body (t (@fequ ?E ?B ?R1 ?R2 ?RR)) ?R (CTree.bind (T := ?T1) _ _) (CTree.bind (T := ?T2) _ _) =>
        apply (ft_t (@bind_ctx_equ_t E B T1 T2 R1 R2 SS RR)), in_bind_ctx

    (* Upto when guarded *)
  | |- body (bt (@fequ ?E ?B ?R1 ?R2 ?RR)) ?R (CTree.bind (T := ?T1) _ _) (CTree.bind (T := ?T2) _ _) =>
      apply (fbt_bt (@bind_ctx_equ_t E B T1 T2 R1 R2 SS RR)), in_bind_ctx
  end.
Tactic Notation "__upto_bind_equ" uconstr(eq) := __upto_bind_equ' eq.

Ltac __eupto_bind_equ :=
  match goal with
    (* Out of a coinductive proof --- terminology abuse, this is simply using the congruence of the relation, not a upto *)
    |- @equ ?E ?B ?R1 ?R2 ?RR (CTree.bind (T := ?T1) _ _) (CTree.bind (T := ?T2) _ _) =>
      eapply (@equ_clo_bind E B T1 T2 R1 R2 _ _ _ _ _ RR)

    (* Upto when unguarded *)
  | |- body (t (@fequ ?E ?B ?R1 ?R2 ?RR)) ?R (CTree.bind (T := ?T1) _ _) (CTree.bind (T := ?T2) _ _) =>
        eapply (ft_t (@bind_ctx_equ_t E B T1 T2 R1 R2 _ RR)), in_bind_ctx

    (* Upto when guarded *)
  | |- body (bt (@fequ ?E ?B ?R1 ?R2 ?RR)) ?R (CTree.bind (T := ?T1) _ _) (CTree.bind (T := ?T2) _ _) =>
      eapply (fbt_bt (@bind_ctx_equ_t E B T1 T2 R1 R2 _ RR)), in_bind_ctx
  end.

Ltac __upto_bind_eq_equ :=
  __upto_bind_equ eq; [reflexivity | intros ? ? <-].


(*|
Up-to [equ eq] bisimulations
----------------------------
The transitivity of the [et R] gives us "equ bisimulation up-to equ". Looking forward,
in order to establish "up-to equ" principles for other bisimulations, we define here the
associated enhancing function.
This also serves to prove the validity of "equ R up-to equ eq".
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


(* equ up-to (equ eq) principle *)

Lemma equ_clos_et {E B X Y R} : @equ_clos E E B B X Y <= et R.
Proof.
  apply Coinduction. cbn. red.
  intros RR t u [].
  red.
  red in HR.
  step in Equt. step in Equu.
  destruct (observe t'), (observe u'); try now inv HR.
  - inv Equt. inv Equu.
    constructor. now dependent destruction HR.
  - dependent induction HR.
    dependent induction Equt. rewrite <- x.
    dependent induction Equu. rewrite <- x.
    constructor. intros. apply (fTf_Tf (fequ R)).
    cbn. econstructor; [apply REL0 | | apply REL1].
    apply (id_T (fequ R)). apply REL.
  - dependent induction HR.
    dependent induction Equt. rewrite <- x.
    dependent induction Equu. rewrite <- x.
    constructor. intros. apply (fTf_Tf (fequ R)).
    cbn. econstructor; [apply REL0 | | apply REL1].
    apply (id_T (fequ R)). apply REL.
Qed.

#[global] Instance equ_eq_et_goal {E B X Y Q R} :
  Proper (@equ E B X _ eq ==> @equ E B Y _ eq ==> flip impl) (et Q R).
Proof.
  unfold Proper, respectful, flip, impl.
  intros.
  apply (ft_t equ_clos_et).
  apply Equ_clos with (t' := y) (u' := y0); auto.
  now symmetry.
Qed.

#[global] Instance equ_eq_ebt_goal {E B X Y Q R} :
  Proper (@equ E B X _ eq ==> @equ E B Y _ eq ==> flip impl) (ebt Q R).
Proof.
  unfold Proper, respectful, flip, impl.
  intros.
  apply (fbt_bt equ_clos_et).
  apply Equ_clos with (t' := y) (u' := y0); auto.
  now symmetry.
Qed.

#[global] Instance equ_eq_equ_goal {E B X Y R} :
  Proper (@equ E B X _ eq ==> @equ E B Y _ eq ==> flip impl) (equ R).
Proof.
  typeclasses eauto.
Qed.

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
in Coq. We however do recover them w.r.t. [equ].
|*)
Lemma ctree_eta_ {E B R} (t : ctree E B R) : t ≅ go (_observe t).
Proof. now step. Qed.

Lemma ctree_eta {E B R} (t : ctree E B R) : t ≅ go (observe t).
Proof.
  now step.
Qed.

Lemma unfold_spinD {E B R} `{B1 -< B} : @spinD E B _ R ≅ Guard spinD.
Proof.
  exact (ctree_eta spinD).
Qed.

Notation bind_ t k :=
  match observe t with
  | RetF r => k%function r
  | VisF e ke => Vis e (fun x => bind (ke x) k)
  | BrF b c ke => Br b c (fun x => bind (ke x) k)
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

Lemma unfold_iter {E B R I} `{B1 -< B} (step : I -> ctree E B (I + R)) i:
	iter step i ≅ iter_ step i.
Proof.
	now step.
Qed.

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
  cbn*; desobs t; constructor; auto.
Qed.

Lemma bind_bind {E B X Y Z} : forall (t : ctree E B X) (k : X -> ctree E B Y) (l : Y -> ctree E B Z),
    (t >>= k) >>= l ≅ t >>= (fun x => k x >>= l).
Proof.
  coinduction S CIH; intros.
  rewrite (ctree_eta t). cbn*.
  desobs t; cbn.
  - reflexivity.
  - constructor; intros. apply CIH.
  - constructor; intros. apply CIH.
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

Lemma bind_br {E B X Y Z} b (c : B X) (k : X -> ctree E B Y) (g : Y -> ctree E B Z):
  Br b c k >>= g ≅ Br b c (fun x => k x >>= g).
Proof.
  now rewrite unfold_bind.
Qed.

Lemma bind_branch : forall {E C X Y} (c : C Y) (b : bool) (k : Y -> ctree E C X),
    CTree.branch b c >>= k ≅ Br b c k.
Proof.
  intros. rewrite unfold_bind. cbn. setoid_rewrite bind_ret_l.
  reflexivity.
Qed.

Lemma bind_guard {E B X Y} `{B1 -< B} (t : ctree E B X) (g : X -> ctree E B Y):
  Guard t >>= g ≅ Guard (t >>= g).
Proof.
  now unfold Guard; cbn; rewrite bind_br.
Qed.

Lemma bind_step {E B X Y} `{B1 -< B} (t : ctree E B X) (g : X -> ctree E B Y):
  Step t >>= g ≅ Step (t >>= g).
Proof.
  now unfold Step; cbn; rewrite bind_br.
Qed.

Lemma vis_equ_bind {E B X Y Z} :
  forall (t : ctree E B X) (e : E Z) k (k' : X -> ctree E B Y),
  x <- t;; k' x ≅ Vis e k ->
  (exists r, t ≅ Ret r) \/
  exists k0, t ≅ Vis e k0 /\ forall x, k x ≅ x <- k0 x;; k' x.
Proof.
  intros.
  destruct (observe t) eqn:?.
  - left. exists r. rewrite ctree_eta, Heqc. reflexivity.
  - rewrite (ctree_eta t), Heqc, bind_vis in H.
    apply equ_vis_invT in H as ?. subst.
    pose proof (equ_vis_invE _ _ _ _ H). destruct H0. subst.
    right. exists k0. split.
    + rewrite (ctree_eta t), Heqc. reflexivity.
    + cbn in H1. symmetry in H1. apply H1.
  - rewrite (ctree_eta t), Heqc, bind_br in H. step in H. inv H.
Qed.

Lemma br_equ_bind {E B X Y} :
  forall (t : ctree E B X) b Z (ch : B Z) k (k' : X -> ctree E B Y),
  x <- t;; k' x ≅ Br b ch k ->
  (exists r, t ≅ Ret r) \/
  exists k0, t ≅ Br b ch k0 /\ forall x, k x ≅ x <- k0 x;; k' x.
Proof.
  intros.
  destruct (observe t) eqn:?.
  - left. exists r. rewrite ctree_eta, Heqc. reflexivity.
  - rewrite (ctree_eta t), Heqc, bind_vis in H. step in H. inv H.
  - rewrite (ctree_eta t), Heqc, bind_br in H.
    apply equ_br_invT in H as ?. destruct H0 as [-> ->].
    pose proof (equ_br_invE _ _ _ _ H) as [<- ?].
    right. exists k0. split.
    + rewrite (ctree_eta t), Heqc. reflexivity.
    + cbn in H0. symmetry in H0. apply H0.
Qed.

Lemma br_Bn_equ_bind {E B X Y} `{Bn -< B} :
  forall (t : ctree E B X) b n k (k' : X -> ctree E B Y),
  x <- t;; k' x ≅ br b (branchn (S n)) k ->
  (exists r, t ≅ Ret r) \/
  exists k0, t ≅ br b (branchn (S n)) k0 /\ forall x, k x ≅ x <- k0 x;; k' x.
Proof.
  intros.
  now apply br_equ_bind.
Qed.

Lemma ret_equ_bind {E B X Y} :
  forall (t : ctree E B Y) (k : Y -> ctree E B X) r,
  x <- t;; k x ≅ Ret r ->
  exists r1, t ≅ Ret r1 /\ k r1 ≅ Ret r.
Proof.
  intros. setoid_rewrite (ctree_eta t) in H. setoid_rewrite (ctree_eta t).
  destruct (observe t) eqn:?.
  - rewrite bind_ret_l in H. eauto.
  - rewrite bind_vis in H. step in H. inv H.
  - rewrite bind_br in H. step in H. inv H.
Qed.

Lemma unfold_forever {E C X} {HasTau: B1 -< C}: forall (k: X -> ctree E C X)(i: X),
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
  unfold CTree.map. __upto_bind_equ eq.
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

Lemma map_guard {E B X Y} `{B1 -< B} (f : X -> Y) :
  forall (t : ctree E B X),
  CTree.map f (Guard t) ≅ Guard (CTree.map f t).
Proof.
  intros. unfold map.
  rewrite bind_guard. reflexivity.
Qed.

Notation "▷ e" := (subevent _ e) (at level 0).

(*|
Convenience: all child-less invisible brs can be proved [equ], no need to work w.r.t. a bisim
|*)

Lemma br0_always_stuck : forall {E B R} `{B0 -< B} vis (k : _ -> ctree E B R),
    br vis branch0 k ≅ stuck vis.
Proof.
  intros.
  step.
  constructor; intros abs; inv abs.
Qed.

Lemma brD0_always_stuck : forall {E B R} `{B0 -< B} (k : _ -> ctree E B R),
    brD branch0 k ≅ stuckD.
Proof.
  intros.
  step.
  constructor; intros abs; inv abs.
Qed.

Lemma brS0_always_stuck : forall {E B R} `{B0 -< B} (k : _ -> ctree E B R),
    brS branch0 k ≅ stuckS.
Proof.
  intros.
  step.
  constructor; intros abs; inv abs.
Qed.

Lemma br_equ': forall (E B: Type -> Type) R b Y (c : B Y) (k k': Y -> ctree E B R) Q,
    (forall t, k t (≅ Q) k' t) ->
    Br b c k (≅ Q) Br b c k'.
Proof.
  intros * EQ.
  step; econstructor; auto.
Qed.

Lemma br_equ: forall (E B: Type -> Type) R b Y (c : B Y) (k k': Y -> ctree E B R),
    (forall t, k t ≅ k' t) ->
    Br b c k ≅ Br b c k'.
Proof.
  intros E B R b Y c k k'. 
  exact (br_equ' E B R b Y c k k' eq).
Qed.

#[global] Instance proper_equ_forever{E C X}`{HasStuck:B1 -<C}:
  Proper (pointwise_relation X (@equ E C X X eq) ==> eq ==> @equ E C X X eq) forever.
Proof.
  unfold Proper, respectful; intros; subst.
  revert y0; coinduction R CIH; intros.
  rewrite (unfold_forever_ x), (unfold_forever_ y).
  rewrite H.
  __upto_bind_eq_equ.
  econstructor; intros [].
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

Ltac ctree_head_in t h :=
  match t with
  | Guard ?t =>
      change (Guard t) with (brD branch1 (fun _ => t)) in h
  | Step ?t =>
      change (Step t) with (brS branch1 (fun _ => t)) in h
  | @stuck ?E ?B ?X ?H ?vis =>
      change t with (br vis branch0 (fun x : void => match x with end) : ctree E B X) in h
  | @CTree.trigger ?E ?B ?R ?e =>
      change t with (Vis e (fun x => Ret x) : ctree E B R) in h
  | @CTree.branch ?E ?B ?vis ?X ?b =>
      change t with (Br vis b (fun x => Ret x) : ctree E B X) in h
  | _ => idtac
  end.

Ltac inv_equ h :=
  match type of h with
  | ?t (≅?Q) ?u => ctree_head_in t h; ctree_head_in u h;
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
  | Br _ _ _ (≅?Q) Br _ _ _ =>
      let EQt := fresh "EQt" in
      let EQb := fresh "EQb" in
      let EQe := fresh "EQe" in
      let EQ := fresh "EQ" in
      apply equ_br_invT in h as EQt;
      destruct EQt as [EQt EQb];
      subst_hyp_in EQt h;
      subst_hyp_in EQb h;
      apply equ_br_invE in h as [EQe EQ];
      subst
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
