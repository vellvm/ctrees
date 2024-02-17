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
Notation uid n := (fin n).

(*| Message passing algebraic effects |*)
Section Messaging.
  Context (n: nat) (T: Type).
  Notation uid := (uid n).

  (*| Network effects |*)
  Inductive netE: Type :=
  | Recv(me: uid)
  | Send(me to: uid)(msg: T).

  #[global] Instance encode_netE: Encode netE :=
    fun e => match e with
          | Recv _ => option T
          | Send _ _ _ => unit
          end.

End Messaging.

Arguments Recv {n} {T}.
Arguments Send {n} {T}.

(*| Many interpretations for network effects. |*)

(*| Bidirectional queues (input, output) interpretation
  of an event [netE] |*)
Section Messaging.
  Import MonadNotation.
  Local Open Scope monad_scope.

  Context (n: nat) (T: Type).
  Notation uid := (uid n).
  Notation LQs := (list T * list (uid * T)) (only parsing).
  Notation VQs := (vec n (list T)) (only parsing).
  Notation netE := (netE n T).

  Definition h_netE_l: netE ~> state LQs :=
      fun e =>
        '(inp, out) <- get ;;
        match e return state LQs (encode e) with
        | Recv me =>
            match inp with
            | [] => ret None
            | msg :: ts => put (ts, out) ;; ret (Some msg)
            end
        | Send _ to msg => put (inp, out ++ [(to, msg)])
        end.

  Definition h_netE_v: netE ~> state VQs :=
    fun e =>
        qs <- get;;
        match e return state VQs (encode e) with
        | Recv i =>
            match Vector.nth qs i with
            | [] => ret None
            | msg :: ts =>
                put (nth_map qs i (fun _ => ts));;
                ret (Some msg)
            end
        | Send i to msg => put (nth_map qs to (fun q => q ++ [msg]))
        end.

End Messaging.

