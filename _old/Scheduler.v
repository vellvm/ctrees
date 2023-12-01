From Coq Require Import
  List
  Classes.RelationPairs
  Classes.RelationClasses.

From CTree Require Import
  CTree
  KTree
  Events.Core
  Events.Net
  CTree.Events.State
  Utils.Utils
  Utils.Vectors.

Import ListNotations.
Local Open Scope list_scope.

Set Implicit Arguments.

Section Scheduler.
  Context (n: nat) {T: Type}.
  Notation netE := (netE n T).
  Notation uid := (uid n).
  Notation Qs := (list T * list (uid * T))%type (only parsing).
  Notation ktree X := (ktree netE X).
  Notation scheduleE X := (stateE (vec n (ktree X * Qs)))%type (only parsing).
  Import CTreeNotations.

  Local Open Scope ctree_scope.
  (*|
    Interference is how a local action affects the global state.
    It is the sharing is shared state concurrency. This will be specific to
    each type of effect and semantics.

    - Also this is probaly not a decidable function, but a relation.
      For example, consider output queues
        [0: [send 2 m], 1: [send 2 n], 2: []]
      What should the new state [σ'] of process 2 be?
         [m, n] or [n, m]

    - Another consideration is [fairness] of [interference]. We claim
    the scheduler is fair, but if [interference]
    drops the messages of the same process infinitely often,
    that violates the fairness property.

    -
   |*)
  Variable (interference: vec n Qs -> Qs -> Qs).


  Definition fair_copies{X} (t: ktree X): ctree (scheduleE X) void :=
    put (Vector.const (t, ([], [])) n) ;;
    Ctree.iter
      (fun _: unit =>
         ps <- get ;;
         let ps' := Vector.map (fun '(t, σ) => transF t σ) ps in
         let σs' := Vector.map snd ps' in
         put (Vector.map (fun '(t, σ) => (t, interference σs' σ)) ps') ;;
         CTree.Core.Ret (inl tt)
      ) tt.

End Scheduler.
