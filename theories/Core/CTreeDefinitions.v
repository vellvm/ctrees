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
visible internal brs; a notion of weak bisimulation observing no internal br.

.. coq:: none
|*)

From ITree Require Import Basics.Basics Core.Subevent.

From CTree Require Import
	   Core.Utils.

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

  Context {E : Type -> Type} {R : Type}.

(*|
The type [ctree] is defined as the final coalgebra ("greatest fixed point") of the functor [ctreeF].
A [ctree] can locally provide three kind of observations:
- A pure value, terminating the computation
- An interaction with the environment, emitting the corresponding
indexed event and non-deterministically continuing indexed by the
value returned by the environment
- A (finite) internal non-deterministic branching

.. coq::
|*)

  Variant ctreeF (ctree : Type) :=
    | RetF (r : R)                                   (* a pure computation *)
    | VisF {X : Type} (e : E X) (k : X -> ctree)      (* an external event *)
    | BrF (vis : bool) (n : nat) (k : fin n -> ctree)      (* an internal non-deterministic branching *)
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
Arguments BrF {_ _} [_] vis n.

(*|
A [ctree'] is a "forced" [ctree]. It is the type of inputs
of [go], and outputs of [observe].

.. coq::
|*)

Notation ctree' E R := (ctreeF E R (ctree E R)).

(*|
We wrap the primitive projection [_observe] in a function [observe].
|*)

Definition observe {E R} (t : ctree E R) : ctree' E R := @_observe E R t.

(*|
We encode [itree]'s [Tau] constructor as a unary delayed br.
|*)

Notation Ret x    := (go (RetF x)).
Notation Vis e k  := (go (VisF e k)).
Notation Guard t  := (go (BrF false 1 (fun _ => t))).
Notation Step t   := (go (BrF true 1 (fun _ => t))).
Notation Br b n k := (go (BrF b n k)).
Notation BrS n k  := (go (BrF true n k)).
Notation BrD n k  := (go (BrF false n k)).
Notation BrSF     := (BrF true).
Notation BrDF     := (BrF false).

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
|*)

Module CTree.

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
Definition subst {E : Type -> Type} {T U : Type} (k : T -> ctree E U)
  : ctree E T -> ctree E U :=
  cofix _subst (u : ctree E T) : ctree E U :=
    match observe u with
    | RetF r => k r
    | VisF e h => Vis e (fun x => _subst (h x))
    | BrF b n h => Br b n (fun x => _subst (h x))
    end.

Definition bind {E : Type -> Type} {T U : Type} (u : ctree E T) (k : T -> ctree E U)
  : ctree E U :=
  subst k u.

(*|
Monadic composition of continuations (i.e., Kleisli composition).
|*)

Definition cat {E T U V}
           (k : T -> ctree E U) (h : U -> ctree E V) :
  T -> ctree E V :=
  fun t => bind (k t) h.

(*|
Iteration
|*)

Notation on_left lr l t :=
  (match lr with
  | inl l => t
  | inr r => Ret r
  end) (only parsing).

Definition iter {E : Type -> Type} {R I: Type}
           (step : I -> ctree E (I + R)) : I -> ctree E R :=
  cofix iter_ i := bind (step i) (fun lr => on_left lr l (Guard (iter_ l))).

(*|
Functorial map ([fmap] in Haskell)
|*)

Definition map {E R S} (f : R -> S)  (t : ctree E R) : ctree E S :=
  bind t (fun x => Ret (f x)).

(*|
Atomic ctrees triggering a single event.
|*)

Definition trigger {E : Type -> Type} : E ~> ctree E :=
  fun R e => Vis e (fun x => Ret x).

(*|
Atomic ctrees with br over a finite arity.
|*)

Definition br {E : Type -> Type} : forall b n, ctree E (fin n) :=
  fun b n => Br b n (fun x => Ret x).

(*|
Silent failure: contrary to an event-based failure, this
stuck state cannot be observed, it will be indistinguishable
from [spin] w.r.t. the bisimulations introduced.
|*)
Definition stuck {E R} vis : ctree E R :=
  Br vis 0 (fun x : fin 0 => match x with end).

Notation stuckS := (stuck true).
Notation stuckD := (stuck false).

(*|
Ignores the result of a tree.
|*)

Definition ignore {E R} : ctree E R -> ctree E unit :=
  map (fun _ => tt).

(*|
Infinite trees --- warning, [spinD] for instance does not
"spin" in the traditional sense.
|*)

CoFixpoint spinD {E R} : ctree E R := Guard spinD.
CoFixpoint spinS {E R} : ctree E R := Step spinS.
CoFixpoint spinD_nary {E R} (n : nat) : ctree E R :=
	BrD n (fun _ => spinD_nary n).
CoFixpoint spinS_nary {E R} (n : nat) : ctree E R :=
	BrS n (fun _ => spinS_nary n).

(*|
Repeats a computation infinitely.
|*)

Definition forever {E R S} (t : ctree E R) : ctree E S :=
  cofix forever_t := bind t (fun _ => Guard (forever_t)).

Ltac fold_subst :=
  repeat (change (CTree.subst ?k ?t) with (CTree.bind t k)).

Ltac fold_monad :=
  repeat (change (@CTree.bind ?E) with (@Monad.bind (ctree E) _));
  repeat (change (go (@RetF ?E _ _ _ ?r)) with (@Monad.ret (ctree E) _ _ r));
  repeat (change (@CTree.map ?E) with (@Functor.fmap (ctree E) _)).

End CTree.
Arguments CTree.br {E} b n.

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

#[global] Instance Functor_ctree {E} : Functor (ctree E) :=
{ fmap := @CTree.map E }.

#[global] Instance Monad_ctree {E} : Monad (ctree E) :=
{| ret := fun _ x => Ret x
;  bind := @CTree.bind E
|}.

#[global] Instance MonadIter_ctree {E} : MonadIter (ctree E) :=
  fun _ _ => CTree.iter.

#[global] Instance MonadTrigger_ctree {E} : MonadTrigger E (ctree E) :=
  @CTree.trigger _.

#[global] Instance MonadBr_ctree {E} : MonadBr (ctree E) :=
  CTree.br.

Definition brS2 {E X} (t u : ctree E X) :=
 (BrS 2 (fun b =>
			   match b with | Fin.F1 => t | _ => u end)).

Definition brS3 {E X} (t u v : ctree E X) :=
 (BrS 3 (fun (b : fin 3) =>
			   match b with
			   | Fin.F1 => t
			   | Fin.FS Fin.F1 => u
			   | _ => v end)).

Definition brS4 {E X} (t u v w : ctree E X) :=
 (BrS 4 (fun (b : fin 4) =>
			   match b with
			   | Fin.F1 => t
			   | Fin.FS Fin.F1 => u
			   | Fin.FS (Fin.FS Fin.F1) => v
			   | _ => w end)).

Definition brD2 {E X} (t u : ctree E X) :=
 (BrD 2 (fun b =>
			   match b with | Fin.F1 => t | _ => u end)).

Definition brD3 {E X} (t u v : ctree E X) :=
 (BrD 3 (fun (b : fin 3) =>
			   match b with
			   | Fin.F1 => t
			   | Fin.FS Fin.F1 => u
			   | _ => v end)).

Definition brD4 {E X} (t u v w : ctree E X) :=
 (BrD 4 (fun (b : fin 4) =>
			   match b with
			   | Fin.F1 => t
			   | Fin.FS Fin.F1 => u
			   | Fin.FS (Fin.FS Fin.F1) => v
			   | _ => w end)).

Notation trigger e :=
	(CTree.trigger (subevent _ e)).
Notation vis e k := (Vis (subevent _ e) k).

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

Lemma Vis_eq1 E R T Y e k Z f h: @VisF E R T Y e k = @VisF E R T Z f h -> Y=Z.
Proof. intro H. now dependent destruction H. Qed.

Lemma Vis_eq2 E R T Y e k f h: @VisF E R T Y e k = @VisF E R T Y f h -> e=f /\ k=h.
Proof. intro H. now dependent destruction H. Qed.

Lemma Br_eq1 E R T b b' n m k h: @BrF E R T b n k = @BrF E R T b' m h -> b = b' /\ n=m.
Proof. intro H. now dependent destruction H. Qed.

Lemma Br_eq2 E R T b n k h: @BrF E R T b n k = @BrF E R T b n h -> k=h.
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

Remove [Guard]s and [Step]s from the front of an [ctree].
|*)

Fixpoint burn (n : nat) {E R} (t : ctree E R) :=
  match n with
  | O => t
  | S n =>
    match observe t with
    | RetF r => Ret r
    | VisF e k => Vis e k
    | @BrF _ _ _ _ 1 t' => burn n (t' Fin.F1)
    | BrF b n k => Br b n k
    end
  end.
