(* begin hide *)
From CTree Require Import 
	Utils.

From ExtLib Require Import  
	Structures.Functor
	Structures.Monads.

Set Implicit Arguments.
Set Contextual Implicit.
Set Primitive Projections.
(* end hide *)
	
(** * Core definition of the [ctrees] datatype and its combinators  *)

Section ctree.

  Context {E : Type -> Type} {R : Type}.

  (** The type [ctree] is defined as the final coalgebra ("greatest
      fixed point") of the functor [ctreeF].
			A [ctree] can locally provide three kind of observations:
			- A pure value, terminating the computation
			- An interaction with the environment, emitting the corresponding 
				indexed event and non-deterministically continuing indexed by the 
				value returned by the environment
			- A (finite) internal non-deterministic choice	
	*)
	(* TODO YZ:  
		- Do we want to name the sources of the forks?
			For instance if we want to support simultaneously different schedulers 
			for different kind of non-determinism in a language. 
		- Do we want non-finite internal branching? Indexed by arbitrary types?
    - Or crazier, do we want non-uniform branching, modelling non-uniform random choices for instance?
	 *)
	
  Variant ctreeF (ctree : Type) :=
  | RetF (r : R)
  | VisF {X : Type} (e : E X) (k : X -> ctree)
  | ForkF {n : nat} (k : fin n -> ctree)  
  .

  CoInductive ctree : Type := go
  { _observe : ctreeF ctree }.

End ctree.

(* begin hide *)

Declare Scope ctree_scope. 
Bind Scope ctree_scope with ctree.
Delimit Scope ctree_scope with ctree.
Local Open Scope ctree_scope.

Arguments ctree _ _ : clear implicits.
Arguments ctreeF _ _ : clear implicits.
(* end hide *)

(** A [ctree'] is a "forced" [ctree]. It is the type of inputs
    of [go], and outputs of [observe]. *)
Notation ctree' E R := (ctreeF E R (ctree E R)).

(** We wrap the primitive projection [_observe] in a function
    [observe]. *)
Definition observe {E R} (t : ctree E R) : ctree' E R := @_observe E R t.

(** We encode [itree]'s [Tau] constructor as a unary internal choice. *)
Notation Ret x := (go (RetF x)).
Notation Vis e k := (go (VisF e k)).
Notation Tau t := (go (ForkF (fun (_ : fin 1) => t))).
Notation Fork k := (go (ForkF k)).

(** ** Main operations on [ctree] *)

(** The core definitions are wrapped in a module for namespacing.
    They are meant to be used qualified (e.g., CTree.bind) or
    via notations (e.g., [>>=]). *)

(** *** How to write cofixpoints *)

(** We define cofixpoints in two steps: first a plain definition
    (prefixed with an [_], e.g., [_bind], [_iter]) defines the body
    of the function:

    - it takes the recursive call ([bind]) as a parameter;
    - if we are deconstructing an ctree, this body takes
      the unwrapped [ctreeF];

    second the actual [CoFixpoint] (or, equivalently, [cofix]) ties
    the knot, applying [observe] to any [ctree] parameters. *)

(** This style allows us to keep [cofix] from ever appearing in
    proofs, which could otherwise get quite unwieldly.
    For every [CoFixpoint] (such as [bind]), we prove an unfolding
    lemma to rewrite it as a term whose head is [_bind], without
    any [cofix] above it.
[[
    unfold_bind : observe (bind t k)
                = observe (_bind (fun t' => bind t' k) t)
]]
    Note that this is an equality "up to" [observe]. It would not be
    provable if it were a plain equality:
[[
    bind t k = _bind (...) t  (* unfold the definition of [bind]... *)
    (cofix bind' t1 := _bind (...) t1) t = _bind (...) t1
]]
    The [cofix] is stuck, and can only be unstuck under the primitive
    projection [_observe] (which is wrapped by [observe]).
 *)

(** *** Definitions *)

(** These are meant to be imported qualified, e.g., [CTree.bind],
    [CTree.trigger], to avoid ambiguity with identifiers of the same
    name (some of which are overloaded generalizations of these).
 *)
Module CTree.

(** [bind]: monadic composition, tree substitution, sequencing of
    computations. [bind t k] is also denoted by [t >>= k] and using
    "do-notation" [x <- t ;; k x]. *)

(* [subst]: [bind] with its arguments flipped.
   We keep the continuation [k] outside the cofixpoint.
   In particular, this allows us to nest [bind] in other cofixpoints,
   as long as the recursive occurences are in the continuation
   (i.e., this makes it easy to define tail-recursive functions). *)
Definition subst {E : Type -> Type} {T U : Type} (k : T -> ctree E U)
  : ctree E T -> ctree E U :=
  cofix _subst (u : ctree E T) : ctree E U :=
    match observe u with
    | RetF r => k r
    | VisF e h => Vis e (fun x => _subst (h x))
    | ForkF h => Fork (fun x => _subst (h x))
    end.

Definition bind {E : Type -> Type} {T U : Type} (u : ctree E T) (k : T -> ctree E U)
  : ctree E U :=
  subst k u.

(** Monadic composition of continuations (i.e., Kleisli composition).
 *)
Definition cat {E T U V}
           (k : T -> ctree E U) (h : U -> ctree E V) :
  T -> ctree E V :=
  fun t => bind (k t) h.

(** [iter]: See [Basics.Basics.MonadIter]. *)

(* [on_left lr l t]: run a computation [t] if the first argument is an [inl l].
   [l] must be a variable (used as a pattern), free in the expression [t]:
   - [on_left (inl x) l t = t{l := x}]
   - [on_left (inr y) l t = Ret y]
 *)
Notation on_left lr l t :=
  (match lr with
  | inl l => t
  | inr r => Ret r
  end) (only parsing).

(* Note: here we must be careful to call [iter_ l] under [Tau] to avoid an eager
   infinite loop if [step i] is always of the form [Ret (inl _)] (cf. issue #182). *)
Definition iter {E : Type -> Type} {R I: Type}
           (step : I -> ctree E (I + R)) : I -> ctree E R :=
  cofix iter_ i := bind (step i) (fun lr => on_left lr l (Tau (iter_ l))).

(** Functorial map ([fmap] in Haskell) *)
Definition map {E R S} (f : R -> S)  (t : ctree E R) : ctree E S :=
  bind t (fun x => Ret (f x)).

(** Atomic itrees triggering a single event. *)
Definition trigger {E : Type -> Type} : E ~> ctree E :=
  fun R e => Vis e (fun x => Ret x).

(** Atomic itrees forking over a finite arity. *)
Definition fork {E : Type -> Type} : forall n, ctree E (fin n) :=
  fun n => Fork (fun (x : Fin.t n) => Ret x).

(** Ignore the result of a tree. *)
Definition ignore {E R} : ctree E R -> ctree E unit :=
  map (fun _ => tt).

(** Infinite taus. *)
CoFixpoint spin {E R} : ctree E R := Tau spin.
CoFixpoint spin_nary {E R} (n : nat) : ctree E R :=
	Fork (fun _: fin n => spin_nary n).

(** Repeat a computation infinitely. *)
Definition forever {E R S} (t : ctree E R) : ctree E S :=
  cofix forever_t := bind t (fun _ => Tau (forever_t)).

Ltac fold_subst :=
  repeat (change (CTree.subst ?k ?t) with (CTree.bind t k)).

Ltac fold_monad :=
  repeat (change (@CTree.bind ?E) with (@Monad.bind (ctree E) _));
  repeat (change (go (@RetF ?E _ _ _ ?r)) with (@Monad.ret (ctree E) _ _ r));
  repeat (change (@CTree.map ?E) with (@Functor.fmap (ctree E) _)).

End CTree.

(** ** Notations *)

(** Sometimes it's more convenient to work without the type classes
    [Monad], etc. When functions using type classes are specialized,
    they simplify easily, so lemmas without classes are easier
    to apply than lemmas with.

    We can also make ExtLib's [bind] opaque, in which case it still
    doesn't hurt to have these notations around.
 *)

Module CTreeNotations.
Notation "t1 >>= k2" := (CTree.bind t1 k2)
  (at level 58, left associativity) : ctree_scope.
Notation "x <- t1 ;; t2" := (CTree.bind t1 (fun x => t2))
  (at level 61, t1 at next level, right associativity) : ctree_scope.
Notation "t1 ;; t2" := (CTree.bind t1 (fun _ => t2))
  (at level 61, right associativity) : ctree_scope.
Notation "' p <- t1 ;; t2" :=
  (CTree.bind t1 (fun x_ => match x_ with p => t2 end))
  (at level 61, t1 at next level, p pattern, right associativity) : ctree_scope.
Infix ">=>" := CTree.cat (at level 61, right associativity) : ctree_scope.
End CTreeNotations.

(** ** Instances *)

Instance Functor_ctree {E} : Functor (ctree E) :=
{ fmap := @CTree.map E }.

Instance Monad_ctree {E} : Monad (ctree E) :=
{| ret := fun _ x => Ret x
;  bind := @CTree.bind E
|}.

Instance MonadIter_ctree {E} : MonadIter (ctree E) :=
  fun _ _ => CTree.iter.

(** ** Tactics *)
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

(** ** Compute with fuel *)

(** Remove [Tau]s from the front of an [itree]. *)
Fixpoint burn (n : nat) {E R} (t : ctree E R) :=
  match n with
  | O => t
  | S n =>
    match observe t with
    | RetF r => Ret r
    | VisF e k => Vis e k
    | @ForkF _ _ _ 1 t' => burn n (t' Fin.F1)
    | ForkF k => Fork k
    end
  end.

