(*| Useful instructions: State |*)
From CTree Require Import
  Classes
  Events.Core
  ITree.Core.

From CTree Require Export
  Events.WriterE.

From ExtLib Require Import
  Monoid
  Monads
  PPair
  Structures.MonadWriter
  Data.Monads.WriterMonad.

Import MonadNotation.
Local Open Scope monad_scope.

Definition log {S}: S -> itree (writerE S) unit :=
  fun s => Itree.trigger (Log s).
