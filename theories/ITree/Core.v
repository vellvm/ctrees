#[global] Set Warnings "-intuition-auto-with-star".
From ExtLib Require Import
  Structures.Functor
  Structures.Applicative
  Structures.Monad.

From CTree Require Export
  Classes
  Events.Core.

From Coinduction Require Import
     coinduction.

Generalizable All Variables.

(*| Basically [itrees] with monomorphic effects and Damien Pous' coinduction |*)
Section ITree.
  Context {E: Type} `{Encode E} {X: Type}.
  Variant itreeF(itree: Type): Type :=
    | RetF (x: X)
    | TauF (t: itree)
    | VisF (e: E)(k: encode e -> itree).

  #[projections(primitive)] CoInductive itree: Type :=
    go { _observe: itreeF itree }.

End ITree.

Declare Scope itree_scope.
Bind Scope itree_scope with itree.
Delimit Scope itree_scope with itree.
Local Open Scope itree_scope.

Arguments itree E {H} X.
Arguments itreeF E {H} X.
Arguments TauF {E H X} [itree] t.
Arguments RetF {E H X} [itree] x.
Arguments VisF {E H X} [itree] e k.

Notation itree' E X := (itreeF E X (itree E X)).

(*| We wrap the primitive projection [_observe] in a function [observe]. |*)
Definition observe `{HE: Encode E} `(t : itree E X) : itree' E X := @_observe E HE X t.

Notation Ret x        := (go (RetF x)).
Notation Vis e k      := (go (VisF e k)).
Notation Tau t       := (go (TauF t)).

Module Itree.

  Definition subst' {E : Type@{eff}} {HE: Encode E} {R S : Type@{eff}}
    (k : R -> itree E S) : itree' E R -> itree E S  :=
    cofix _subst (ot : itree' E R) :=
      match ot with
      | RetF r => k r
      | TauF t => Tau (_subst (observe t))
      | VisF e k => Vis e (fun x => _subst (observe (k x)))
    end.

  (*| Monadic composition [bind] |*)
  Definition bind `{Encode E} {X Y} (t : itree E X) (k : X -> itree E Y) :=
    subst' k (observe t).

  (*| Monadic composition of continuations (i.e., Kleisli composition). |*)
  Definition cat `{Encode E} `(k : X -> itree E Y) `(h : Y -> itree E Z) :
    X -> itree E Z := fun t => bind (k t) h.

  (*| Functorial map ([fmap] in Haskell) |*)
  Definition map `{Encode E} `(f : X -> Y) (t : itree E X) : itree E Y :=
      bind t (fun x => Ret (f x)).

  (*| Atomic itrees triggering a single event. |*)
  Definition trigger {E1 E2 : Type@{eff}} `{ReSumRet E1 E2}
    (e : E1) : itree E2 (encode e) :=
    Vis (resum e) (fun x : encode (resum e) => Ret (resum_ret e x)).

  (*| Ignore the result of a itree. |*)
  Definition ignore `{Encode E} {R} : itree E R -> itree E unit :=
    map (fun _ => tt).

  CoFixpoint spin `{Encode E} {R} : itree E R := Tau spin.

  (*| [iter] |*)
  Definition iter `{Encode E} {R I: Type}
    (step : I -> itree E (I + R)) : I -> itree E R :=
    cofix iter_ i := bind (step i) (fun lr =>
                                      match lr with
                                      | inl l => (Tau (iter_ l))
                                      | inr r => Ret r
                                      end).

End Itree.

Ltac fold_bind :=
  repeat match goal with
    | h: context [Itree.subst' ?k ?t] |- _ => fold (Itree.bind (go t) k) in h
    | |- context [Itree.subst' ?k ?t] => fold (Itree.bind (go t) k)
    end.

#[global] Hint Extern 0 => fold_bind: core.

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

Ltac desobs t :=
  let H := fresh "Heqt" in destruct (observe t) eqn:H.

Module ITreeNotations.
  Declare Scope itree_scope.
  Bind Scope itree_scope with itree.
  Delimit Scope itree_scope with itree.
  Local Open Scope itree_scope.

  Notation "t1 >>= k2" := (Itree.bind t1 k2)
                            (at level 58, left associativity) : itree_scope.
  Notation "x <- t1 ;; t2" := (Itree.bind t1 (fun x => t2))
                               (at level 62, t1 at next level, right associativity) : itree_scope.
  Notation "t1 ;; t2" := (Itree.bind t1 (fun _ => t2))
                           (at level 62, right associativity) : itree_scope.
  Notation "' p <- t1 ;; t2" :=
    (Itree.bind t1 (fun x_ => match x_ with p => t2 end))
      (at level 62, t1 at next level, p pattern, right associativity) : itree_scope.
End ITreeNotations.

(*| Common instances for [itree] |*)
#[global] Instance Functor_itree `{Encode E} : Functor (itree E) :=
  { fmap := @Itree.map E _ }.

#[global] Instance Applicative_itree `{Encode E} : Applicative (itree E) :=
  {
    pure := fun _ x => Ret x;
    ap := fun _ _ f x =>
            Itree.bind f (fun f => Itree.bind x (fun x => Ret (f x)) );

  }.

#[global] Instance Monad_itree `{Encode E} : Monad (itree E) :=
  {
    ret := fun _ x => Ret x;
    bind := @Itree.bind E H;
  }.

#[global] Instance MonadIter_itree `{Encode E} : MonadIter (itree E) :=
  fun _ _ => Itree.iter.

(*| Export various useful Utils |*)
From CTree Require Export Utils.Utils.
