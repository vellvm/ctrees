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

From CTree Require Import
	   Utils
     CTrees
     Shallow.
(*|
.. coq:
|*)

Section equ.

  Context {E : Type -> Type} {R1 R2 : Type} (RR : R1 -> R2 -> Prop).

(*|
We also need to do some gymnastics to work around the
two-layered definition of [ctree]. We first define a
relation transformer [equF] as an indexed inductive type
on [ctree'], which is then composed with [observe] to obtain
a relation transformer on [ctree] ([equ_]).

In short, this is necessitated by the fact that dependent
pattern-matching is not allowed on [ctree].
|*)

  Variant equF (eq : ctree E R1 -> ctree E R2 -> Prop) :
    ctree' E R1 -> ctree' E R2 -> Prop :=
  | Eq_Ret x y (REL : RR x y) : equF eq (RetF x) (RetF y)
  | Eq_Vis {X} (e : E X) k1 k2
      (REL : forall x, eq (k1 x) (k2 x)) :
      equF eq (VisF e k1) (VisF e k2)
  | Eq_Choice b {n} (k1 : Fin.t n -> _) (k2 : Fin.t n -> _)
              (REL : forall i, eq (k1 i) (k2 i)) :
      equF eq (ChoiceF b n k1) (ChoiceF b n k2)
  .
  Hint Constructors equF: core.

  Definition equ_ eq : ctree E R1 -> ctree E R2 -> Prop :=
	fun t1 t2 => equF eq (observe t1) (observe t2).

  Program Definition fequ: mon (ctree E R1 -> ctree E R2 -> Prop) := {|body := equ_|}.
  Next Obligation.
    unfold pointwise_relation, Basics.impl, equ_.
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
Notation equ R := (gfp (fequ R)).
Infix "≅" := (equ eq) (at level 70).

(*|
The associated companions:
|*)
Notation T_equ RR  := (T (fequ RR)).
Notation t_equ RR  := (t (fequ RR)).
Notation bt_equ RR := (bt (fequ RR)).
Arguments equ_ _ _ _ _/.
#[global] Hint Constructors equF: core.

Section equ_equiv.

	Variable (E : Type -> Type) (R : Type) (RR : R -> R -> Prop).
  Notation T  := (coinduction.T (fequ (E := E) RR)).
  Notation t  := (coinduction.t (fequ (E := E) RR)).
  Notation bt := (coinduction.bt (fequ (E := E) RR)).
(*|
This is just a hack suggested by Damien Pous to avoid a
universe inconsistency when using both the relational algebra
and coinduction libraries (we fix the type at which we'll use [eq]).
|*)
  Definition seq: relation (ctree E R) := eq.

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
	Lemma refl_t {RRR: Reflexive RR}: const seq <= t_equ RR.
	Proof.
		apply leq_t. intro.
		change (@eq (ctree E R)  <= equ_ RR eq).
		intros p ? <-. cbn. desobs p; auto.
	Qed.

(*|
[converse] is compatible: up-to symmetry is valid
|*)
	Lemma converse_t {RRS: Symmetric RR}: converse <= t.
	Proof.
		apply leq_t. intros S x y H; cbn. destruct H; auto.
	Qed.

(*|
[squaring] is compatible: up-to transitivity is valid
|*)
	Lemma square_t {RRR: Reflexive RR} {RRT: Transitive RR}: square <= t.
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
			destruct (Choice_eq1 H2); subst.
			destruct (Choice_eq2 H2).
			constructor. intros i. now (exists (k0 i)).
	Qed.

(*|
Having [const eq], [converse] and [square] below the companion entails respectively
that the companion, at all point, is reflexive, symmetric, transitive.
The companion library directly provide these results for bisimilarity, [t R], [b (t R)]
and [T f R].
|*)
	#[global] Instance Equivalence_et `{Equivalence _ RR} S: Equivalence (t S).
	Proof. apply Equivalence_t. apply refl_t. apply square_t. apply converse_t. Qed.
	#[global] Instance Equivalence_T `{Equivalence _ RR} f S: Equivalence (T f S).
	Proof. apply Equivalence_T. apply refl_t. apply square_t. apply converse_t. Qed.
	#[global] Instance Equivalence_bt `{Equivalence _ RR} S: Equivalence (bt S).
	Proof. apply Equivalence_bt. apply refl_t. apply square_t. apply converse_t. Qed.

(*|
This instance is a bit annoyingly adhoc, but useful for unfolding laws notably:
essentially we can conclude by reflexivity without stepping completely through
[equF], but only after exposing it by unfolding and case-analysing on the structure
of the tree.
|*)
  #[global] Instance Reflexive_equF (equ : ctree E R -> ctree E R -> Prop) :
    Reflexive RR -> Reflexive equ -> Reflexive (equF RR equ).
  Proof.
    red. destruct x; auto.
  Qed.

End equ_equiv.

#[global] Instance Equivalence_equ {E R}: Equivalence (gfp (@fequ E R _ eq)).
Proof. apply Equivalence_et. typeclasses eauto. Qed.

#[global] Hint Constructors equF : core.
Arguments equ_ {E R1 R2} RR eq t1 t2/.

(*|
Dependent inversion of [equ] and [equF] equations
-------------------------------------------------
We assume [JMeq_eq] to invert easily bisimilarity of dependently typed constructors
|*)
Lemma equ_vis_invT {E X Y S} (e1 : E X) (e2 : E Y) (k1 : X -> ctree E S) k2 :
  Vis e1 k1 ≅ Vis e2 k2 ->
  X = Y.
Proof.
  intros EQ.
	step in EQ. dependent induction EQ; auto.
Qed.

Lemma equ_vis_invE {E X S} (e1 e2 : E X) (k1 k2 : X -> ctree E S) :
  Vis e1 k1 ≅ Vis e2 k2 ->
  e1 = e2 /\ forall x, k1 x ≅ k2 x.
Proof.
  intros EQ; step in EQ.
	inv EQ.
	dependent destruction H2.
	dependent destruction H4.
	auto.
Qed.

Lemma equF_vis_invT {E X Y S} (e1 : E X) (e2 : E Y) (k1 : X -> ctree E S) k2 :
  equF eq (equ eq) (VisF e1 k1) (VisF e2 k2) ->
  X = Y.
Proof.
  intros EQ.
	dependent induction EQ; auto.
Qed.

Lemma equF_vis_invE {E X S} (e1 e2 : E X) (k1 k2 : X -> ctree E S) :
  equF eq (equ eq) (VisF e1 k1) (VisF e2 k2) ->
  e1 = e2 /\ forall x, equ eq (k1 x) (k2 x).
Proof.
  intros EQ.
	inv EQ.
	dependent destruction H; dependent destruction H4; auto.
Qed.

Lemma equF_choice_invT {E S b b' n m} (k1 : _ -> ctree E S) k2 :
  equF eq (equ eq) (ChoiceF b n k1) (ChoiceF b' m k2) ->
  n = m /\ b = b'.
Proof.
  intros EQ.
	dependent induction EQ; auto.
Qed.

Lemma equF_choice_invE {E S b n} (k1 : _ -> ctree E S) k2 :
  equF eq (equ eq) (ChoiceF b n k1) (ChoiceF b n k2) ->
  forall x, equ eq (k1 x) (k2 x).
Proof.
  intros EQ.
	inv EQ.
	dependent destruction H; auto.
Qed.

(*|
Proper Instances
----------------
TODO: step back and think a bit better about those

equ eq       ==> going (equ eq)  observe
∀(equ eq)    ==> going (equ eq)  ChoiceF
∀(equ eq)    ==> going (equ eq)  VisF
observing eq --> equ eq
going(equ)   ==> eq ==> fimpl    equF eq (t_equ eq r)
eq ==> going(equ)   ==> fimpl    equF eq (t_equ eq r)
equ ==> equ ==> flip impl)       bt_equ eq r
|*)

#[global] Instance equ_observe {E R} :
  Proper (equ eq ==> going (equ eq)) (@observe E R).
Proof.
  constructor. step in H. now step.
Qed.

#[global] Instance equ_ChoiceF {E R} b n :
  Proper (pointwise_relation _ (equ eq) ==> going (equ eq)) (@ChoiceF E R _ b n).
Proof.
  constructor. red in H. step. econstructor; eauto.
Qed.

#[global] Instance equ_VisF {E R X} (e : E X) :
  Proper (pointwise_relation _ (equ eq) ==> going (equ eq)) (@VisF E R _ _ e).
Proof.
  constructor. red in H. step. econstructor; eauto.
Qed.

#[global] Instance observing_sub_equ E R :
  subrelation (@observing E R R eq) (equ eq).
Proof.
  repeat intro.
  step. rewrite (observing_observe H). apply Reflexive_equF; eauto.
Qed.

#[global] Instance equ_eq_equF {E R r} :
  Proper (going (equ eq) ==> eq ==> flip impl)
	     (@equF E R R eq (t_equ eq r)).
Proof.
  unfold Proper, respectful, flip, impl. intros. subst.
  inv H. step in H0. inv H0; inv H1; auto.
  - invert.
    subst. constructor. intros. rewrite REL. auto.
  - invert.
    subst. constructor. intros. rewrite REL. auto.
Qed.

#[global] Instance eq_equ_equF {E R r} :
  Proper (eq ==> going (equ eq) ==> flip impl)
	     (@equF E R R eq (t_equ eq r)).
Proof.
  unfold Proper, respectful, flip, impl. intros. subst.
  inv H0. step in H. inv H; inv H1; auto.
  - invert.
    subst. constructor. intros. rewrite REL. auto.
  - invert.
    subst. constructor. intros. rewrite REL. auto.
Qed.

#[global] Instance gfp_bt_equ {E R r} :
	 Proper (gfp (@fequ E R R eq) ==> equ eq ==> flip impl)
	  (bt_equ eq r).
Proof.
	unfold Proper, respectful, flip, impl.
	intros.
	pose proof (gfp_bt (fequ eq) r).
	etransitivity; [|etransitivity]; [|apply H1 |].
	apply H2; assumption.
	apply H2; symmetry; assumption.
Qed.

(*|
Elementary equational theory
----------------------------
At this point, equipped with our coinductive structural equality,
we can already express tight equations. Mainly
- unfolding lemmas for our operations ([bind] and [iter] notably);
- up-to bind coinductive principle for [equ];
- the three monadic laws
|*)
Import CTree.
Import CTreeNotations.
Open Scope ctree.

(*|
Even eta-laws for coinductive data-structures are not valid w.r.t. to [eq]
in Coq. We however do recover them w.r.t. [equ].
|*)
Lemma ctree_eta_ {E R} (t : ctree E R) : t ≅ go (_observe t).
Proof. now step. Qed.

Lemma ctree_eta {E R} (t : ctree E R) : t ≅ go (observe t).
Proof.
  now step.
Qed.

Lemma unfold_spin {E R} : @spin E R ≅ TauI spin.
Proof.
  exact (ctree_eta spin).
Qed.

Notation bind_ t k :=
  match observe t with
  | RetF r => k%function r
  | VisF e ke => Vis e (fun x => bind (ke x) k)
  | ChoiceF b n ke => Choice b n (fun x => bind (ke x) k)
  end.

Lemma unfold_bind {E R S} (t : ctree E R) (k : R -> ctree E S)
  : bind t k ≅ bind_ t k.
Proof.
	now step.
Qed.

Notation iter_ step i :=
  (lr <- step%function i;;
   match lr with
   | inl l => TauI (iter step l)
   | inr r => Ret r
   end)%ctree.

Lemma unfold_iter {E R I} (step : I -> ctree E (I + R)) i:
	iter step i ≅ iter_ step i.
Proof.
	now step.
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

    Context {E: Type -> Type} {X X' Y Y': Type}.

(*|
Most general contextualisation function associated to [bind].
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
               (R: rel (ctree E X) (ctree E X'))
               (S: rel (X -> ctree E Y) (X' -> ctree E Y')):
      rel (ctree E Y) (ctree E Y') :=
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

    Context {E: Type -> Type} {X1 X2 Y1 Y2: Type}.

(*|
Specialization of [bind_ctx] to a function acting with [equ] on the bound value,
and with the argument (pointwise) on the continuation.
|*)
    Program Definition bind_ctx_equ SS: mon (rel (ctree E Y1) (ctree E Y2)) :=
      {|body := fun R => @bind_ctx E X1 X2 Y1 Y2 (equ SS) (pointwise SS R) |}.
    Next Obligation.
      intros ??? H. apply leq_bind_ctx. intros ?? H' ?? H''.
      apply in_bind_ctx. apply H'. intros t t' HS. apply H0, H'', HS.
    Qed.

(*|
The resulting enhancing function gives a valid up-to technique
|*)
    Lemma bind_ctx_equ_t (SS : rel X1 X2) (RR : rel Y1 Y2): bind_ctx_equ SS <= t_equ RR.
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
Lemma equ_clo_bind (E: Type -> Type) (X1 X2 Y1 Y2 : Type) :
	forall (t1 : ctree E X1) (t2 : ctree E X2) (k1 : X1 -> ctree E Y1) (k2 : X2 -> ctree E Y2)
    (S : rel X1 X2) (R : rel Y1 Y2) RR,
		equ S t1 t2 ->
    (forall x1 x2, S x1 x2 -> (t_equ R RR) (k1 x1) (k2 x2)) ->
    t_equ R RR (bind t1 k1) (bind t2 k2)
.
Proof.
  intros.
  apply (ft_t (bind_ctx_equ_t S R)).
  now apply in_bind_ctx.
Qed.

(*|
And in particular, we get the proper instance justifying rewriting [equ]
to the left of a [bind].
|*)
#[global] Instance bind_equ_cong :
 forall (E : Type -> Type) (X Y : Type) (R : rel Y Y) RR,
   Proper (equ (@eq X) ==> pointwise_relation X (t_equ R RR) ==> t_equ R RR) (@bind E X Y).
Proof.
  repeat red; intros; eapply equ_clo_bind; eauto.
  intros ? ? <-; auto.
Qed.

(*|
Monadic laws
------------
The three usual monadic laws can be estalished w.r.t. [equ eq].
|*)
Lemma bind_ret_l {E X Y} : forall (x : X) (k : X -> ctree E Y),
    Ret x >>= k ≅ k x.
Proof.
  intros.
  now rewrite unfold_bind.
Qed.

Lemma bind_ret_r {E X} : forall (t : ctree E X),
    x <- t;; Ret x ≅ t.
Proof.
  coinduction S CIH.
  intros t.
  rewrite unfold_bind.
  cbn; desobs t; constructor; auto.
Qed.

Lemma bind_bind {E X Y Z} : forall (t : ctree E X) (k : X -> ctree E Y) (l : Y -> ctree E Z),
    (t >>= k) >>= l ≅ t >>= (fun x => k x >>= l).
Proof.
  coinduction S CIH; intros.
  rewrite (ctree_eta t). cbn.
  desobs t; cbn.
  - reflexivity.
  - constructor; intros. apply CIH.
  - constructor; intros. apply CIH.
Qed.

