(*| Useful instructions: State |*)
From CTree Require Import
  Classes
  CTree.Core.

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

Definition log {S}: S -> ctree (writerE S) unit := fun s => Ctree.trigger (Log s).

#[global] Instance MonadBr_writerT {M Σ} {SM: Monoid Σ} {MM: Monad M} {AM: MonadBr M}
  : MonadBr (writerT SM M) :=
  fun n => @mkWriterT Σ SM M (fin (S n)) (f <- mbr n;; ret (ppair f (monoid_unit SM))).
