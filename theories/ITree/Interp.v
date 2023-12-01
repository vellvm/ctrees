From ExtLib Require Import
  Structures.MonadState
  Data.Monads.StateMonad
  Structures.Monad.

From CTree Require Import
  Classes
  ITree.Core
  ITree.Equ.

Set Implicit Arguments.

Import MonadNotation.
Open Scope monad_scope.

(** ** Interpret *)
(** An event handler [E ~> M] defines a monad morphism
    [ctree E ~> M] for any monad [M] with a loop operator. *)

Definition interp {E} {M : Type -> Type}
  {MM : Monad M} {MI : MonadIter M} (h: E ~> M) : forall X, itree E X -> M X :=
  fun R => iter (fun t =>
                match observe t with
                | RetF r => ret (inr r)
                | TauF t => ret (inl t)
                | VisF e k => x <- h.(handler) e ;; ret (inl (k x))
                end).

Arguments interp {E M MM MI} h [X].
