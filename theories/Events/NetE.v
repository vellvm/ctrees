From Coq Require Import
  Classes.DecidableClass
  Classes.SetoidDec
  Classes.RelationClasses
  List.

From CTree Require Import
  Events.Core
  Utils.Utils
  Utils.Vectors.

From ExtLib Require Import
  Structures.Monads
  Structures.MonadState
  Data.Monads.StateMonad.

From Coinduction Require Import lattice.

Import ListNotations.
Local Open Scope list_scope.

Set Implicit Arguments.
Generalizable All Variables.

(*| Unique thread identifiers |*)
Notation fin' n := (fin (S n)).
Notation vec' n t := (vec (S n) t).

(*| Message passing algebraic effects |*)
Section Messaging.
  Context (n: nat) (T: Type).

  (*| Network effects |*)
  Inductive netE: Type :=
  | Recv
  | Send(to: fin' n)(msg: T).

  #[global] Instance encode_netE: Encode netE :=
    fun e => match e with
          | Recv => option T
          | Send _ _ => unit
          end.

End Messaging.

Arguments Recv {n} {T}.
Arguments Send {n} {T}.
