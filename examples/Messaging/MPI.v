From ITree Require Import
     Basics
     Subevent
     Events.State
     Indexed.Sum.

From Coq Require Import
     Fin
     Lia
     Vector
     String.

From ExtLib Require Import
     RelDec
     Functor
     Maps
     FMapAList
     Reducible
     Traversable
     Monad
     Option.

From Coinduction Require Import
     coinduction rel tactics.

From CTree Require Import
     CTree
     Interp
     Interp.State
     State
     Eq
     SBisim.

From DSL Require Import
     System
     Network
     Storage
     Log
     Utils
     Vectors.


Import Coq.Lists.List.ListNotations.
Open Scope fin_vector_scope.

Import CTreeNotations Log.
Local Open Scope ctree_scope.
Local Open Scope string_scope.
Local Open Scope vector_scope.

Set Implicit Arguments.
Set Maximal Implicit Insertion.
Set Asymmetric Patterns.

Module MPI.
  Module Network := Network(DistrSystem).
  Module Storage := Storage(DistrSystem).
  Import Monads Network Storage DistrSystem.

  (** ================================================================================ *)
  (** This is the top-level denotation of a distributed system to a ctree of behaviors *)
  Program Definition run{n}(v: vec n (ctree (Storage +' Net n) void)): heap -> ctree (logE heap) void :=
    fun st: heap => run_network (Vector.map swap (run_states_log v st)).

  (** ===================================================================== *)
  (** First system, experiment -- two agents sending messages to each other *)
  Program Definition alice : uid 2 := @of_nat_lt 0 2 _.
  Program Definition bob : uid 2 := @of_nat_lt 1 2 _.

  Definition example_bob: ctree (Storage +' Net 2) void :=
    daemon (
        m <- recv ;;
        match m with
        | None => ret tt
        | Some v => send (principal v) (S (payload v))
        end).

  Definition example_alice: ctree (Storage +' Net 2) void :=
    daemon (
        a <- load "a";;
        send bob (default a 0);;
        v <- recv;;
        match v with
        | None => ret tt
        | Some v => store "b" (payload v)
        end).

  Definition init_heap := (List.cons ("a", 0) List.nil).
  Definition C := run [example_alice; example_bob] init_heap.

  (** ===================================================================== *)
  (** Second system, control -- two agents without messaging *)
  Definition example_add: ctree (Storage +' Net 2) void :=
    daemon (
        a <- load "a";;
        store "b" (S (default a 0))
      ).

  Definition example_spin: ctree (Storage +' Net 2) void :=
    daemon (ret tt).

  Definition C' := run [example_add; example_spin] init_heap.

  Lemma correct_C_C': C ~ C'.
  Proof.
    red.
    coinduction S CIH.
    unfold C, C'.
    unfold example_alice, example_bob, example_add, example_spin, init_heap.
    cbn.
    unfold run, run_states, run_network.
    econstructor.

  Admitted.

End MPI.

