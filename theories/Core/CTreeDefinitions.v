(*|
============================================================
Core definition of the [ctrees] datatype and its combinators
============================================================

We develop a data-structure strongly inspired by Interaction Trees,
but offering native support for internal non-determinism: the [ctree]s.
Interaction trees took the position to not be the free monad per se,
but to give a special status to divergence by implementing it coinductively.
Here, we take a similar stance toward non-determinism by adding a new
constructor to the structure encoding (finite) non-deterministic branching.
These internal branching nodes are furthermore tagged by whether they can be
observed or not.

The resulting structure is still an iterative monad parametered by an
interface of interactions, supporting monadic interpretations of these
interfaces. But the equivalence relation over [ctree] is more complex, and
account natively for this non-determinism. More specifically, we provide
a structural, coinductive equality; a notion of strong bisimulation observing
visible internal choices; a notion of weak bisimulation observing no internal
choice.

.. coq:: none
|*)

From ITree Require Import Basics.Basics Core.Subevent Indexed.Sum.

From CTree Require Import
	   Core.Utils Core.Index.

From ExtLib Require Import
	   Structures.Functor
	   Structures.Monads.

Set Implicit Arguments.
Set Contextual Implicit.
Set Primitive Projections.

(*|
.. coq::
|*)

Section ctree.

  Context {E : Type -> Type} {C : Type -> Type} {R : Type}.

(*|
The type [ctree] is defined as the final coalgebra ("greatest fixed point") of the functor [ctreeF].
A [ctree] can locally provide three kind of observations:
- A pure value, terminating the computation
- An interaction with the environment, emitting the corresponding
indexed event and non-deterministically continuing indexed by the
value returned by the environment
- A (finite) internal non-deterministic choice

TODO YZ:

- Do we want non-uniform branching, modelling non-uniform random choices for instance?
- Could ctrees be parameterized by a bound on nested choices before reaching a Vis/Ret?

.. coq::
|*)

  Variant ctreeF (ctree : Type) :=
    | RetF (r : R)                                               (* a pure computation *)
    | VisF {X : Type} (e : E X) (k : X -> ctree)                 (* an external event *)
    | ChoiceF {X : Type} (vis : bool) (c : C X) (k : X -> ctree) (* an internal non-deterministic branching *)
  .

  CoInductive ctree : Type :=
    go { _observe : ctreeF ctree }.

End ctree.

(*|
.. coq:: none
|*)

Declare Scope ctree_scope.
Bind Scope ctree_scope with ctree.
Delimit Scope ctree_scope with ctree.
Local Open Scope ctree_scope.

Arguments ctree _ _ _ : clear implicits.
Arguments ctreeF _ _ _ : clear implicits.
Arguments ChoiceF {_ _ _} [_] {_} vis c k.

(*|
A [ctree'] is a "forced" [ctree]. It is the type of inputs
of [go], and outputs of [observe].

.. coq::
|*)

Notation ctree' E C R := (ctreeF E C R (ctree E C R)).

(*|
We wrap the primitive projection [_observe] in a function [observe].
|*)

Definition observe {E C R} (t : ctree E C R) : ctree' E C R := @_observe E C R t.

Notation Ret x        := (go (RetF x)).
Notation Vis e k      := (go (VisF e k)).
Notation Choice b c k := (go (ChoiceF b c k)).
Notation ChoiceV c k  := (go (ChoiceF true c k)).
Notation ChoiceI c k  := (go (ChoiceF false c k)).
Notation ChoiceVF c   := (ChoiceF true c).
Notation ChoiceIF c   := (ChoiceF false c).

Notation vis e k := (Vis (subevent _ e) k).
Notation choice b c k :=
	(Choice b (subevent _ c) k).
Notation choiceI c k := (choice false c k).
Notation choiceV c k := (choice true c k).
Notation choiceIF c := (ChoiceIF (subevent _ c)).
Notation choiceVF c := (ChoiceVF (subevent _ c)).

Section Choices.

  Context {E C : Type -> Type}.
  Context {R : Type}.

(*|
Silent failure: contrary to an event-based failure, this
stuck state cannot be observed, it will be indistinguishable
from [spin] w.r.t. the bisimulations introduced.
|*)
  Definition stuckI `{C0 -< C} : ctree E C R :=
    choiceI choice0 (fun x : void => match x with end).

  Definition stuckV `{C0 -< C} : ctree E C R :=
    choiceV choice0 (fun x : void => match x with end).

(*|
Guards similar to [itree]'s taus.
|*)
  Definition tauI `{C1 -< C} t : ctree E C R :=
    choiceI choice1 (fun _ => t).

  Definition tauV `{C1 -< C} t : ctree E C R :=
    choiceV choice1 (fun _ => t).

(*|
Bounded choices
|*)
  Definition chooseI2 `{C2 -< C} t u : ctree E C R :=
    choiceI choice2 (fun b => if b : bool then t else u).
  Definition chooseV2 `{C2 -< C} t u : ctree E C R :=
    choiceV choice2 (fun b => if b : bool then t else u).
  Definition chooseI3 `{C3 -< C} t u v : ctree E C R :=
    choiceI choice3 (fun n => match n with
                           | t31 => t
                           | t32 => u
                           | t33 => v
                           end).
  Definition chooseV3 `{C3 -< C} t u v : ctree E C R :=
    choiceV choice3 (fun n => match n with
                           | t31 => t
                           | t32 => u
                           | t33 => v
                           end).
  Definition chooseI4 `{C4 -< C} t u v w : ctree E C R :=
    choiceI choice4 (fun n => match n with
                           | t41 => t
                           | t42 => u
                           | t43 => v
                           | t44 => w
                           end).
  Definition chooseV4 `{C4 -< C} t u v w : ctree E C R :=
    choiceV choice4 (fun n => match n with
                           | t41 => t
                           | t42 => u
                           | t43 => v
                           | t44 => w
                           end).

(*|
Finite choice
|*)
  Definition chooseIn `{Cn -< C} n k : ctree E C R :=
    choiceI (choicen n) k.
  Definition chooseVn `{Cn -< C} n k : ctree E C R :=
    choiceV (choicen n) k.

(*|
Countable choice
|*)
  Definition chooseIN `{CN -< C} k : ctree E C R :=
    choiceI choiceN k.
  Definition chooseVN `{CN -< C} k : ctree E C R :=
    choiceV choiceN k.

End Choices.

(*|
Main operations on [ctree]
--------------------------

The core definitions are wrapped in a module for namespacing. They are meant to be used qualified (e.g., CTree.bind) or via notations (e.g., [>>=]).

Note on how to write cofixpoints
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
We define cofixpoints in two steps:

first a plain definition (prefixed with an [_], e.g., [_bind], [_iter]) defines the body of the function:

- it takes the recursive call ([bind]) as a parameter;
- if we are deconstructing an ctree, this body takes the unwrapped [ctreeF];

second the actual [CoFixpoint] (or, equivalently, [cofix]) ties the knot, applying [observe] to any [ctree] parameters.

This style allows us to keep [cofix] from ever appearing in proofs, which could otherwise get quite unwieldly.
For every [CoFixpoint] (such as [bind]), we prove an unfolding lemma to rewrite it as a term whose head is [_bind], without any [cofix] above it.


    unfold_bind : observe (bind t k)
                = observe (_bind (fun t' => bind t' k) t)

Note that this is an equality "up to" [observe]. It would not be provable if it were a plain equality:

    bind t k = _bind (...) t
    (cofix bind' t1 := _bind (...) t1) t = _bind (...) t1

The [cofix] is stuck, and can only be unstuck under the primitive projection [_observe] (which is wrapped by [observe]).

Definitions

These are meant to be imported qualified, e.g., [CTree.bind],
[CTree.trigger], to avoid ambiguity with identifiers of the same
name (some of which are overloaded generalizations of these).
|*)

Module CTree.

Section CTree.

  Context {E C : Type -> Type}.

(*|
[bind]: monadic composition, tree substitution, sequencing of
computations. [bind t k] is also denoted by [t >>= k] and using
"do-notation" [x <- t ;; k x].
|*)

(*|
[subst]: [bind] with its arguments flipped.
We keep the continuation [k] outside the cofixpoint.
In particular, this allows us to nest [bind] in other cofixpoints,
as long as the recursive occurences are in the continuation
(i.e., this makes it easy to define tail-recursive functions).
|*)
  Definition subst {T U : Type} (k : T -> ctree E C U)
    : ctree E C T -> ctree E C U :=
    cofix _subst (u : ctree E C T) : ctree E C U :=
      match observe u with
      | RetF r => k r
      | VisF e h => Vis e (fun x => _subst (h x))
      | ChoiceF b c h => Choice b c (fun x => _subst (h x))
      end.

  Definition bind {T U : Type} (u : ctree E C T) (k : T -> ctree E C U)
    : ctree E C U :=
    subst k u.

(*|
Monadic composition of continuations (i.e., Kleisli composition).
|*)

  Definition cat {T U V}
             (k : T -> ctree E C U) (h : U -> ctree E C V) :
    T -> ctree E C V :=
    fun t => bind (k t) h.

(*|
Functorial map ([fmap] in Haskell)
|*)

  Definition map {R S} (f : R -> S)  (t : ctree E C R) : ctree E C S :=
    bind t (fun x => Ret (f x)).

(*|
Atomic itrees triggering a single event.
|*)

  Definition trigger : E ~> ctree E C :=
    fun R e => Vis e (fun x => Ret x).

(*|
Atomic ctrees with choice.
|*)

  Definition choose {X : Type} : forall b (c : C X), ctree E C X :=
    fun b c => Choice b c (fun x => Ret x).

(*|
Ignore the result of a tree.
|*)

  Definition ignore {R} : ctree E C R -> ctree E C unit :=
    map (fun _ => tt).

End CTree.

Ltac fold_bind :=
  repeat match goal with
  | h: context [CTree.subst ?k ?t] |- _ => fold (CTree.bind t k) in h
  | |- context [CTree.subst ?k ?t] => fold (CTree.bind t k)
  end.

(*|
[on_left lr l t]: run a computation [t] if the first argument is an [inl l].
[l] must be a variable (used as a pattern), free in the expression [t]:

   - [on_left (inl x) l t = t{l := x}]
   - [on_left (inr y) l t = Ret y]
|*)

Notation on_left lr l t :=
  (match lr with
  | inl l => t
  | inr r => Ret r
  end) (only parsing).

(*|
Combinators for loops must be guarded, we hence assume that
unary choices are available.
|*)
Section withTau.

  Context {E C : Type -> Type}.
  Context `{C1 -< C}.

  CoFixpoint spinI {R} : ctree E C R := tauI spinI.
  CoFixpoint spinV {R} : ctree E C R := tauV spinV.

(*|
Repeat a computation infinitely.
|*)

  Definition forever {R S} (t : ctree E C R) : ctree E C S :=
    cofix forever_t := bind t (fun _ => tauI (forever_t)).

(*|
[iter]: See [Basics.Basics.MonadIter].
Note: here we must be careful to call [iter\_ l] under [Tau] to avoid an eager
infinite loop if [step i] is always of the form [Ret (inl _)] (cf. issue #182).
|*)

  Definition iter {R I: Type}
             (step : I -> ctree E C (I + R)) : I -> ctree E C R :=
    cofix iter_ i := bind (step i) (fun lr => on_left lr l (tauI (iter_ l))).

End withTau.

(*|
Infinite taus.
|*)

CoFixpoint spinI_gen {E C R X} (x : C X) : ctree E C R :=
	ChoiceI x (fun _ => spinI_gen x).
CoFixpoint spinV_gen {E C R X} (x : C X) : ctree E C R :=
	ChoiceV x (fun _ => spinV_gen x).

Ltac fold_subst :=
  repeat (change (CTree.subst ?k ?t) with (CTree.bind t k)).

Ltac fold_monad :=
  repeat (change (@CTree.bind ?E) with (@Monad.bind (ctree E) _));
  repeat (change (go (@RetF ?E _ _ _ ?r)) with (@Monad.ret (ctree E) _ _ r));
  repeat (change (@CTree.map ?E) with (@Functor.fmap (ctree E) _)).

End CTree.
Arguments CTree.choose {E C X} b c.
Notation trigger e := (CTree.trigger (subevent _ e)).
Notation choose b c := (CTree.choose b (subevent _ c)).

(*|
=========
Notations
=========

Sometimes it's more convenient to work without the type classes [Monad], etc. When functions using type classes are specialized,
they simplify easily, so lemmas without classes are easier to apply than lemmas with.

We can also make ExtLib's [bind] opaque, in which case it still doesn't hurt to have these notations around.
|*)

Module CTreeNotations.
Notation "t1 >>= k2" := (CTree.bind t1 k2)
  (at level 58, left associativity) : ctree_scope.
Notation "x <- t1 ;; t2" := (CTree.bind t1 (fun x => t2))
  (at level 62, t1 at next level, right associativity) : ctree_scope.
Notation "t1 ;; t2" := (CTree.bind t1 (fun _ => t2))
  (at level 62, right associativity) : ctree_scope.
Notation "' p <- t1 ;; t2" :=
  (CTree.bind t1 (fun x_ => match x_ with p => t2 end))
  (at level 62, t1 at next level, p pattern, right associativity) : ctree_scope.
(* Infix ">=>" := CTree.cat (at level 62, right associativity) : ctree_scope. *)
End CTreeNotations.

(*|
=========
Instances
=========
|*)

#[global] Instance Functor_ctree {E C} : Functor (ctree E C) :=
{ fmap := @CTree.map E C }.

#[global] Instance Monad_ctree {E C} : Monad (ctree E C) :=
{| ret := fun _ x => Ret x
;  bind := @CTree.bind E C
|}.

#[global] Instance MonadIter_ctree {E C} `{C1 -< C} : MonadIter (ctree E C) :=
  fun R I => @CTree.iter E C _ R I.

(* #[global] Instance MonadTrigger_ctree : MonadTrigger ctree := *)
(*   fun T => CTree.trigger. *)

#[global] Instance MonadChoice_ctree {E C} : MonadChoice (ctree E C) C :=
  fun b X => @CTree.choose E C X b.

(*|
====================================
Inversion lemma relying on [JMeq_eq]
====================================
Since the [Vis] and [Choice] constructors take dependent
pairs as argument, their inversion is not straightforward.
The ITree library goes to great length to avoid the use of
axioms where possible. Here for now we fully embrace [JMeq_eq]
-- it is introduced under the scene by [dependent destruction].
|*)

Lemma Vis_eq1 E C R T Y e k Z f h: @VisF E C R T Y e k = @VisF E C R T Z f h -> Y=Z.
Proof. intro H. now dependent destruction H. Qed.

Lemma Vis_eq2 E C R T Y e k f h: @VisF E C R T Y e k = @VisF E C R T Y f h -> e=f /\ k=h.
Proof. intro H. now dependent destruction H. Qed.

Lemma Choice_eq1 E C R T Y Z b b' c c' k h: @ChoiceF E C R T Y b c k = @ChoiceF E C R T Z b' c' h -> b = b' /\ Y=Z.
Proof. intro H. now dependent destruction H. Qed.

Lemma Choice_eq2 E C R T Y b c c' k h: @ChoiceF E C R T Y b c k = @ChoiceF E C R T Y b c' h -> c=c' /\ k=h.
Proof. intro H. now dependent destruction H. Qed.

(*|
=======
Tactics
=======
|*)

Tactic Notation "hinduction" hyp(IND) "before" hyp(H)
  := move IND before H; Tactics.revert_until IND; induction IND.

Ltac inv H := inversion H; clear H; subst.

Ltac rewrite_everywhere lem :=
  progress ((repeat match goal with [H: _ |- _] => rewrite lem in H end); repeat rewrite lem).

Ltac rewrite_everywhere_except lem X :=
  progress ((repeat match goal with [H: _ |- _] =>
                 match H with X => fail 1 | _ => rewrite lem in H end
             end); repeat rewrite lem).

Ltac genobs x ox := remember (observe x) as ox.
Ltac genobs_clear x ox := genobs x ox; match goal with [H: ox = observe x |- _] => clear H x end.
Ltac simpobs := repeat match goal with [H: _ = observe _ |- _] =>
                    rewrite_everywhere_except (@eq_sym _ _ _ H) H
                end.
Ltac desobs x := destruct (observe x) .

(*|
==================
Compute with fuel
==================

Remove [Tau]s from the front of an [itree].
|*)
Fixpoint burn (n : nat) {E C : Type -> Type} {R} (t : ctree E (C1 +' C) R) : ctree E (C1 +' C) R :=
  match n with
  | 0 => t
  | S n =>
      match observe t with
      | RetF r => Ret r
      | VisF e k => Vis e k
      | ChoiceF b (inl1 c) k =>
          match c in (C1 T) return (T -> _) -> _ with
          | choice1 => fun k => burn n (k tt)
          end k
      | ChoiceF b c k => Choice b c k
      end
  end.
