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
visible internal brs; a notion of weak bisimulation observing no internal
br.

.. coq:: none
|*)

From ITree Require Import Basics.Basics Core.Subevent Indexed.Sum.

From CTree Require Export
	   Core.Utils.
From CTree Require Import Core.Index.

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

  Context {E : Type -> Type} {B : Type -> Type} {R : Type}.

(*|
The type [ctree] is defined as the final coalgebra ("greatest fixed point") of the functor [ctreeF].
A [ctree] can locally provide three kind of observations:
- A pure value, terminating the computation
- An interaction with the environment, emitting the corresponding
indexed event and non-deterministically continuing indexed by the
value returned by the environment
- An internal non-deterministic branching
.. coq::
|*)

  Variant ctreeF (ctree : Type): Type :=
    | RetF   (r : R)                                      (* a pure computation *)
    | StuckF
    | StepF  (t : ctree)
    | GuardF (t : ctree)
    | VisF {X : Type} (e : E X) (k : X -> ctree)           (* an external event *)
    | BrF {X : Type} (c : B X) (k : X -> ctree)            (* an internal non-deterministic branching *)
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

Arguments ctree _ _ : clear implicits.
Arguments ctreeF _ _ : clear implicits.
Arguments BrF {E B R} [ctree] {X} c k.
Arguments StepF {E B R} [ctree] t.
Arguments GuardF {E B R} [ctree] t.

(*|
A [ctree'] is a "forced" [ctree]. It is the type of inputs
of [go], and outputs of [observe].

.. coq::
|*)

Notation ctree' E B R := (ctreeF E B R (ctree E B R)).

(*|
We wrap the primitive projection [_observe] in a function [observe].
|*)

Definition observe {E B R} (t : ctree E B R) : ctree' E B R := @_observe E B R t.

Notation Ret x        := (go (RetF x)).
Notation Stuck        := (go StuckF).
Notation Guard t      := (go (GuardF t)).
Notation Step t       := (go (StepF t)).
Notation Vis e k      := (go (VisF e k)).
Notation Br n k       := (go (BrF n k)).
Notation BrS n k      := (go (BrF n (fun x => Step (k x)))).

Notation vis e k      := (Vis (subevent _ e) k).
Notation br c k       := (Br (subevent _ c) k).
Notation brF c        := (BrF (subevent _ c)).
Notation brS c k      := (BrS (subevent _ c) k).

Section Branching.

  Context {E B : Type -> Type}.
  Context {R : Type}.

(*|
Bounded branching
|*)
  Definition br2 `{B2 -< B} t u : ctree E B R :=
    br branch2 (fun b => if b : bool then t else u).
  Definition brS2 `{B2 -< B} t u : ctree E B R :=
    brS branch2 (fun b => if b : bool then t else u).
  Definition br3 `{B3 -< B} t u v : ctree E B R :=
    br branch3 (fun n => match n with
                      | t31 => t
                      | t32 => u
                      | t33 => v
                      end).
  Definition brS3 `{B3 -< B} t u v : ctree E B R :=
    brS branch3 (fun n => match n with
                       | t31 => t
                       | t32 => u
                       | t33 => v
                       end).
  Definition br4 `{B4 -< B} t u v w : ctree E B R :=
    br branch4 (fun n => match n with
                      | t41 => t
                      | t42 => u
                      | t43 => v
                      | t44 => w
                      end).
  Definition brS4 `{B4 -< B} t u v w : ctree E B R :=
    brS branch4 (fun n => match n with
                       | t41 => t
                       | t42 => u
                       | t43 => v
                       | t44 => w
                       end).

(*|
Finite branch
|*)
  Definition brn `{Bn -< B} n k : ctree E B R :=
    br (branchn n) k.
  Definition brSn `{Bn -< B} n k : ctree E B R :=
    brS (branchn n) k.

(*|
Countable branch
|*)
  Definition brN `{BN -< B} k : ctree E B R :=
    br branchN k.
  Definition brSN `{BN -< B} k : ctree E B R :=
    brS branchN k.

End Branching.

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

    Context {E B : Type -> Type}.

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
    Definition subst {T U : Type} (k : T -> ctree E B U)
      : ctree E B T -> ctree E B U :=
      cofix _subst (u : ctree E B T) : ctree E B U :=
        match observe u with
        | RetF r => k r
        | StuckF  => Stuck
        | GuardF t => Guard (_subst t)
        | StepF t => Step (_subst t)
        | VisF e h => Vis e (fun x => _subst (h x))
        | BrF n h => Br n (fun x => _subst (h x))
        end.

    Definition bind {T U : Type} (u : ctree E B T) (k : T -> ctree E B U)
      : ctree E B U :=
      subst k u.

(*|
Monadic composition of continuations (i.e., Kleisli composition).
|*)

    Definition cat {T U V}
      (k : T -> ctree E B U) (h : U -> ctree E B V) :
      T -> ctree E B V :=
      fun t => bind (k t) h.

(*|
Functorial map ([fmap] in Haskell)
|*)

    Definition map {R S} (f : R -> S)  (t : ctree E B R) : ctree E B S :=
      bind t (fun x => Ret (f x)).

(*|
Atomic itrees triggering a single event.
|*)

    Definition trigger : E ~> ctree E B :=
      fun R e => Vis e (fun x => Ret x).

(*|
Atomic ctrees with choice.
|*)

    Definition branch {X : Type} : forall (c : B X), ctree E B X :=
      fun c => Br c (fun x => Ret x).

    Definition branchS {X : Type} : forall (c : B X), ctree E B X :=
      fun c => BrS c (fun x => Ret x).

(*|
Ignore the result of a tree.
|*)

    Definition ignore {R} : ctree E B R -> ctree E B unit :=
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
  Section withGuard.

    Context {E B : Type -> Type}.

    CoFixpoint spin  {R} : ctree E B R := Guard spin.
    CoFixpoint spinS {R} : ctree E B R := Step spinS.
(*|
Repeat a computation infinitely.
|*)

    Definition forever {E R} (k: R -> ctree E B R): R -> ctree E B R :=
      cofix F i := bind (k i) (fun i => Guard (F i)).

    Definition foreverS {E R} (k: R -> ctree E B R): R -> ctree E B R :=
      cofix F i := bind (k i) (fun i => Step (F i)).

(*|
[iter]: See [Basics.Basics.MonadIter].
Note: here we must be careful to call [iter\_ l] under [Tau] to avoid an eager
infinite loop if [step i] is always of the form [Ret (inl _)] (cf. issue #182).
|*)

    Definition iter {R I: Type}
      (step : I -> ctree E B (I + R)) : I -> ctree E B R :=
      cofix iter_ i := bind (step i) (fun lr => on_left lr l (Guard (iter_ l))).

    Definition iterS {R I: Type}
      (step : I -> ctree E B (I + R)) : I -> ctree E B R :=
      cofix iter_ i := bind (step i) (fun lr => on_left lr l (Step (iter_ l))).

  End withGuard.

(*|
Infinite taus.
|*)

  CoFixpoint spin_gen {E C R X} (x : C X) : ctree E C R :=
	  Br x (fun _ => spin_gen x).
  CoFixpoint spinS_gen {E C R X} (x : C X) : ctree E C R :=
	  BrS x (fun _ => spinS_gen x).

  Ltac fold_subst :=
    repeat (change (CTree.subst ?k ?t) with (CTree.bind t k)).

  Ltac fold_monad :=
    repeat (change (@CTree.bind ?E) with (@Monad.bind (ctree E) _));
    repeat (change (go (@RetF ?E _ _ _ ?r)) with (@Monad.ret (ctree E) _ _ r));
    repeat (change (@CTree.map ?E) with (@Functor.fmap (ctree E) _)).

End CTree.

Notation trigger e := (CTree.trigger (subevent _ e)).
Notation branch  e := (CTree.branch  (subevent _ e)).
Notation branchS e := (CTree.branchS (subevent _ e)).

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
End CTreeNotations.

(*|
=========
Instances
=========
|*)

#[global] Instance Functor_ctree {E B} : Functor (ctree E B) :=
{ fmap := @CTree.map E B }.

#[global] Instance Monad_ctree {E B} : Monad (ctree E B) :=
{| ret := fun _ x => Ret x
;  bind := @CTree.bind E B
|}.

#[global] Instance MonadIter_ctree {E B} : MonadIter (ctree E B) :=
  fun R I => @CTree.iter E B R I.

#[global] Instance MonadTrigger_ctree {E F B} `{E -< F} : MonadTrigger E (ctree F B) :=
  fun _ e => trigger e.

#[global] Instance MonadBr_ctree {E C D} `{C -< D} : MonadBr C (ctree E D) :=
  fun _ c => branch c.

#[global] Instance MonadStuck_ctree {E C} : MonadStuck (ctree E C) :=
  fun _ => Stuck.

#[global] Instance MonadStep_ctree {E C} : MonadStep (ctree E C) :=
  Step (Ret tt).

(*|
====================================
Inversion lemma relying on [JMeq_eq]
====================================
Since the [Vis] and [Br] constructors take dependent
pairs as argument, their inversion is not straightforward.
The ITree library goes to great length to avoid the use of
axioms where possible. Here for now we fully embrace [JMeq_eq]
-- it is introduced under the scene by [dependent destruction].
|*)

Lemma Vis_eq1 E C R T Y e k Z f h: @VisF E C R T Y e k = @VisF E C R T Z f h -> Y=Z.
Proof. intro H. now dependent destruction H. Qed.

Lemma Vis_eq2 E C R T Y e k f h: @VisF E C R T Y e k = @VisF E C R T Y f h -> e=f /\ k=h.
Proof. intro H. now dependent destruction H. Qed.

Lemma Br_eq1 E B R T Y Z c c' k h:
  @BrF E B R T Y c k = @BrF E B R T Z c' h -> Y = Z.
Proof. intro H. now dependent destruction H. Qed.

Lemma Br_eq2 E B R T Y c c' k h:
  @BrF E B R T Y c k = @BrF E B R T Y c' h -> c = c' /\ k = h.
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

Ltac fold_subst :=
  repeat (change (CTree.subst ?k ?t) with (CTree.bind t k)).


(*|
==================
Compute with fuel
==================

Remove [Guard]s and [Step]s from the front of an [ctree].
|*)
Fixpoint burn (n : nat) {E B : Type -> Type} {R} (t : ctree E B R) : ctree E B R :=
  match n with
  | 0 => t
  | S n =>
      match observe t with
      | RetF r => Ret r
      | StuckF => Stuck
      | GuardF t => burn n t
      | StepF t => burn n t
      | VisF e k => Vis e k
      | BrF c k => Br c (fun x => burn n (k x))
      end
  end.
