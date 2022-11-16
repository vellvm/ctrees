From ITree Require Import
     Basics
     Subevent
     Indexed.Sum.

From Coq Require Import
     Fin.

From ExtLib Require Import
     Monad
     Option.

From Coinduction Require Import
     coinduction rel tactics.

From CTree Require Import
     CTree
     Interp
     Interp.State
     Interp.Log
     Interp.Network
     Logic.Ltl
     Misc.Vectors
     Eq
     SBisim.

Import CTreeNotations VectorNotations LtlNotations Monads Log Network.

Local Open Scope fin_vector_scope.
Local Open Scope ctree_scope.

Set Implicit Arguments.
Set Maximal Implicit Insertion.
Set Asymmetric Patterns.

(** ================================================================================ *)
(** This is the top-level denotation *)
Program Definition run{n C S} `{B1 -< C} `{B2 -< C} `{Bn -< C}
        (v: vec n (ctree (Net n S +' stateE S) C void)): S -> ctree (frameE n +' logE S) C void :=
  fun st: S => run_network (run_states_log v st).
  
Module Toy.

  Notation heap := nat. 
  Notation Net := (Net 2 nat).
  Notation State := (stateE heap).
  Notation Sys := (vec 2 (ctree (Net +' State))).

  Section ParametricC.
    Context {C: Type -> Type} `{B0 -< C} `{B1 -< C} `{B2 -< C} `{Bn -< C}.

    (*| This is a simple two process [a, b] system with a [nat] state.

        For process (i in [a, b]) try to receive a number:
        - If timeout without receiving, send current state [v] to the other process
        - If [v] received, store [v] it and send [S v] to the other process 
    |*)
    Definition example(them: uid 2): ctree (Net +' State) C void :=
      daemon (
          m <- recv ;;
          match m with
          | None =>
              v <- get ;;
              send them v
          | Some (Build_req _ v) =>
              put v ;;
              send them (S v)
          end).
    
    Program Definition a : uid 2 := @of_nat_lt 0 2 _.
    Program Definition b : uid 2 := @of_nat_lt 1 2 _.

    Arguments label: clear implicits.

    (*| A context switch event predicate -- process [m] is scheduled *)
    Variant is_in_frame: uid 2 -> label (frameE 2 +' logE nat) -> Prop :=
      | ProcessEnter: forall m, is_in_frame m (obs (inl1 (Enter m)) tt).

    Variant is_eq: nat -> label (frameE 2 +' logE nat) -> Prop :=
      | IsEqualTo: forall n, is_eq n (obs (inr1 (Log n)) tt).

    Lemma liveness: forall i,
        let sys := run [example b; example a]%vector 0 in
        sys |= InfinitelyOften (Spec (is_in_frame i)) -> (* Axiomatize fairness *)
        sys |= Eventually (Spec (is_eq 2)).             (* Process [i] will count to 2 *)
    Proof.
      intros i sys Fair.
      (* WIP *)
    Admitted.
  End ParametricC.
End Toy.

