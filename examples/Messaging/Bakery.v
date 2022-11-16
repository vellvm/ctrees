From ITree Require Import
     Basics
     Subevent
     Events.State
     Indexed.Sum.

From Coq Require Import
     Fin
     Nat
     Vector
     Logic.Eqdep
     Classes.RelationClasses
     Program.Tactics.

From Equations Require Import Equations.

From ExtLib Require Import
     RelDec
     Monad
     Option.

From Coinduction Require Import
     coinduction rel tactics.

From CTree Require Import
     CTree
     Eq
     Interp
     Interp.State
     Interp.Log
     Interp.Network
     Logic.Ltl
     Misc.Vectors.

Import CTreeNotations VectorNotations Log LtlNotations Monads Network CTree.  
Local Open Scope fin_vector_scope.
Local Open Scope ctree_scope.

Set Implicit Arguments.
Set Maximal Implicit Insertion.
Set Asymmetric Patterns.

Module Bakery.
  Section ParametricN.
    Context {n: nat} {C: Type -> Type} {HasTau: B1 -< C}.

    Inductive msg :=
    | GetNumber
    | CS.

    Record agent_row := {
        in_cs: bool;
        ticket: option nat;
        id : uid n
      }.
   
    Notation heap := (nat * vec n agent_row)%type (only parsing).
    Notation Net := (Net n msg).
    Notation State := (stateE heap).
    Notation Sys := (vec n (ctree (Net +' State))).
    
    (** ===================================================================== *)
    (** Lamport's bakery algorithm *)

    (*| Utility function, find the agent with the earliest (min) issued ticket |*)
    Equations get_min_ticket'{n: nat}(v: vec n agent_row)(sm: option agent_row): option agent_row :=
      get_min_ticket' [] _ := sm;
      get_min_ticket' (h:: ts) None => get_min_ticket' ts (Some h);
      get_min_ticket' (h :: ts) (Some m) with (h.(ticket), m.(ticket)) => {
        | (Some ht, Some mt) with ht <? mt => {            
          | true := get_min_ticket' ts (Some h);
          | false := get_min_ticket' ts (Some m);
          };
        | (None, Some _) := get_min_ticket' ts (Some m);
        | (Some _, None) := get_min_ticket' ts (Some h);
        | (None, None) := get_min_ticket' ts None
        }.
    Definition get_min_ticket{n: nat}(v: vec n agent_row) := get_min_ticket' v None.

    Definition get_max {E} `{State -< E}: ctree E C nat :=
      get >>= fun p => ret (fst p).

    Definition get_agents {E} `{State -< E}: ctree E C (vec n agent_row) :=
      get >>= fun p => ret (snd p). 

    Definition update_agents {E} `{State -< E}(m: agent_row): ctree E C unit :=
      st <- get;;
      match st with
      | (cnt, v) => put (cnt, v @ m.(id) := m)
      end.

    (*| The baker process, synchronized access to CS through ticket |*)
    Definition baker: ctree (Net +' State) C void :=
      daemon (
          (* 1. Schedule a Critical Section (CS) if possible *)
          v <- get_agents;;
          match get_min_ticket v with
          | None => ret tt
          | Some st =>
              send st.(id) CS;; (* Baker sends [CS] msg to preempt clients to enter their CS *)
              update_agents {| in_cs := true; ticket := None; id := st.(id) |}
          end;;
          (* 2. Listen to issue new ticket number *)
          m <- recv;;
          match m with
          | Some (Build_req id GetNumber) =>
              st <- get;;
              match st with
              | (cnt, v) => (* Bump the counter after assigning a ticket to client [id] *)
                  put (S cnt, v @ id := {| in_cs := false; ticket := Some cnt; id := id |})
              end
          | Some (Build_req id CS) => (* Clients respond to the Baker's [CS] with [CS] when done *)
              update_agents {| in_cs := false; ticket := None; id := id |}
          | None =>
              ret tt
          end).                             
    
    (*| Client process |*)
    Definition client (id: uid n)(bakery: uid n) : ctree (Net +' State) C void :=
      daemon (
          (* 1. Ask for a ticket number *)
          send bakery GetNumber;;
          (* 2. Loop until received [CS] message *)
          CTree.iter (fun _: unit =>
                        m <- recv;;
                        match m with
                        | Some (Build_req _ CS) =>
                            (* ENTER CRITICAL SECTION *)
                            send bakery CS;;
                            (* When done send back [CS] to bakery and break inner loop *)
                            ret (inr tt)
                        | _ => ret (inl tt) (* Clients refuse to handle [GetNumber] *)
                        end) tt).

    (** ================================================================================ *)
    (** This is the top-level denotation *)
    Program Definition run_network_state{C} `{B1 -< C} `{B2 -< C} `{Bn -< C}
            (v: vec n (ctree (Net +' State) C void)): heap -> ctree (frameE n +' logE heap) C void :=
      fun st: heap => run_network (run_states_log v st).  
  End ParametricN.
End Bakery.

(*| Try out the bakery algorithm with 2 nodes and 1 baker |*)
Module TestBakery.
  Import Bakery.
  
  (*| First client [A] |*)
  Program Definition A : uid 3 := @of_nat_lt 0 _ _.
  (*| Second client [B] |*)
  Program Definition B : uid 3 := @of_nat_lt 1 _ _.
  (*| Baker |*)
  Program Definition bakery: uid 3 := @of_nat_lt 2 _ _.
  (*| Initial state of the baker, clients are stateless |*)
  Program Definition init_state :=
    (0, [
        {| in_cs := false; ticket := None; id := A |};
        {| in_cs := false; ticket := None; id := B |};
        {| in_cs := false; ticket := None; id := bakery |}]).

  (* Now we can generate all schedules for the bakery (slow) *)
  (* Compute run_network_state [baker; client A bakery; client B bakery] init_state. *)
  Notation heap := (nat * vec 3 (@agent_row 3))%type (only parsing).
  Notation Trace := (frameE 3 +' logE heap).

  Arguments label: clear implicits.

  (*| A context switch event predicate -- process [m] is scheduled *)
  Variant is_in_frame: uid 3 -> label Trace -> Prop :=
    | ProcessEnter: forall m, is_in_frame m (obs (inl1 (Enter m)) tt).
  
  (*| Is a process in their critical section? If yes, then safety property must be satisfied |*)
  Variant is_in_cs: uid 3 -> label Trace -> Prop :=
    | ProcessInCs: forall i agents a cnt,
        (agents $ i).(in_cs) = true ->                       (* [i] is in their CS *)
        get_min_ticket agents = Some a /\ a.(id) = i ->       (* [i] holds the min ticket *)
        (forall j, j <> i -> (agents $ j).(in_cs) = false) ->       (* nobody else is in the CS *)
        is_in_cs i (obs (inr1 (Log (cnt, agents))) tt).

  Lemma correctness_lemma: forall i,
      let sys :=  run_network_state [baker; client A bakery; client B bakery] init_state in
      sys |= InfinitelyOften (Spec (is_in_frame i)) ->      (* Axiomatize fairness *)
      sys |= Eventually (Spec (is_in_cs i)).               (* Liveness + safety *)
  Proof.
    (* WIP *)
  Admitted.
      
End TestBakery.

