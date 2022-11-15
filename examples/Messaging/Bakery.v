From ITree Require Import
     Basics
     Subevent
     Events.State
     Indexed.Sum.

From Coq Require Import
     Fin
     Lia
     Nat
     Vector
     Logic.Eqdep
     Classes.RelationClasses
     Program.Tactics.

From Equations Require Import Equations.

From ExtLib Require Import
     RelDec
     Functor
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
     Equ
     Eq.

From DSL Require Import
     System
     Network
     Storage
     Log
     LTL
     Utils
     Vectors.

Import Coq.Lists.List.ListNotations.
Open Scope fin_vector_scope.
  
Import CTreeNotations Log Ltl.
Local Open Scope ctree_scope.
Local Open Scope vector_scope.

Set Implicit Arguments.
Set Maximal Implicit Insertion.
Set Asymmetric Patterns.

Module Baker.
  Context {n: nat}.
  Notation uid := fin.
  Import CTree.  
  Module BakerSystem <: Systems.
    Inductive _msg_type :=
    | Ack
    | GetNumber
    | CS.

    Definition msg := _msg_type.

    Record agent_mem := { choosing : bool; number: nat; id : uid n }.
   
    Definition heap := (nat * vec n agent_mem)%type.

  End BakerSystem.

  Module NetworkM := Network(BakerSystem).                               
  Module StorageM := Storage(BakerSystem).
  Import Monads NetworkM StorageM BakerSystem.
  (** ===================================================================== *)
  (** Lamport's bakery algorithm *)

  Notation Sys := (vec n (ctree (Net n +' Storage heap))).

  Equations find_max_number{n: nat}(v: vec n agent_mem)(m: option agent_mem): option agent_mem :=
    find_max_number [] _ := m;
    find_max_number (h :: ts) (Some m)  with ((number h) <? (number m)) => {
        find_max_number _ _ false := find_max_number ts (Some m);
        find_max_number _ _ true := find_max_number ts (Some h);
      };
    find_max_number (h:: ts) None => find_max_number ts (Some h).

  Definition get_max {E} `{Storage -< E}: ctree E nat :=
    get >>= fun p => ret (fst p).

  Definition get_mem {E} `{Storage -< E}: ctree E (vec n agent_mem) :=
    get >>= fun p => ret (snd p). 

  Definition update_mem {E} `{Storage -< E}(i: uid n)(m: agent_mem): ctree E unit :=
    st <- get;;
    match st with
    | (a, v) => put (a, v @ i := m)
    end.
      
  Definition baker: ctree (Net n +' Storage) void :=
    daemon (
        (* schedule a CS if it exists *)
        v <- get_mem;;
        match find_max_number v None with
        | None => ret tt
        | Some st =>
            let i := id st in
            send i CS;;
            update_mem i {| choosing := true; number := 0; id := i |}
        end;;
        (* Issue new ticket number *)
        m <- recv;;
        match m with
        | Some (Build_req id GetNumber) =>
            st <- get;;
            match st with
            | (max, v) => 
                put (S max, v @ id := {| choosing := false; number := max; id := id |})
            end
        | Some (Build_req _ _) =>
            ret tt
        | None =>
            ret tt
        end).                             
            
  (** Client participates in the bakery algorithm *)
  Definition client(id: uid n)(bakery: uid n) : ctree (Net n) void :=
    daemon (
        (* number[i] := 1 + max(number) *)
        send bakery GetNumber;;
        (* Loop until their turn to run the critical section *)
        CTree.iter (fun _: unit =>
                      m <- recv;;
                      match m with
                      | Some (Build_req _ Ack) =>
                          ret (inl tt)
                      | Some (Build_req _ CS) =>
                          (** ENTER CRITICAL SECTION!!! *)
                          send (Done)
                          ret (inr tt)
                      | _ => ret (inl tt)
                      end) tt).
  
  Definition fair{S}: CProp S :=
    always (fun t => exists (k: fin n -> _), t ~ Br true n k).
  
End Baker.


Module RunBakery.
  Import Baker.

  Module NetworkM := Network(BakerSystem).                               
  Module StorageM := Storage(BakerSystem).
  Import Monads NetworkM StorageM BakerSystem.

  Program Definition A : uid 3 := @of_nat_lt 0 _ _.
  Program Definition B : uid 3 := @of_nat_lt 1 _ _.
  Program Definition bakery: uid 3 := @of_nat_lt 2 _ _.
  

  Compute run_storage_network [baker; client A bakery; client B bakery].




    Lemma liveness: forall id,
        let sys := run [client A; client B] in
        infinitely_often (lift (fun a => a = Start id)) sys -> (* fairness *)
        eventually (lift (fun a => a = Done id)) sys. (* liveness *)
    Proof.
      unfold run.
      intros.
      rewrite unfold_schedule.
      step in H.


      inv H.
      cbn*.
      unfold run, client; intros.
      rewrite unfold_schedule.
      cbn; econstructor.
      fold_subst; unfold observe; cbn.
      simp schedule_one; cbn.
      
    Admitted.
    

  (** ================================================================================ *)
  (** This is the top-level denotation of a distributed system to a ctree of behaviors *)
  Definition run E {n} (s: vec n (ctree (Net n +' E) void)): ctree E void :=
    schedule 0 (Vector.map (fun it => (it, {| choosing := false; number := 0 |}, []%list)) s).

    (** Utility to find next customer *)
    Check fold_left.
  
    Section N.
      Variable (n: nat).
      Inductive tr := Start(id: fin n) | Done(id: fin n).
      Arguments Net {n}.
      Notation start id := (log (Start id)).
      Notation done id := (log (Done id)).
      
      Definition baker: ctree (Net +' stateE (nat * vec n store_type) +' Success) void :=
        daemon (
            start bakery_uid;;
            forever (
                v <- get;;
                match find_max_number v None with
                | Some {| choosing := c; number := n |} => 
                let {| 
                st $
                m <- recv;;
                match m with
                | Some (Build_Msg id GetNumber) =>
                    (max, v) <- get;;
                    put (S max, v @ id := {| choosing := false; number := max |})
                | Some (Build_Msg _ _) =>
                    ret tt
                             
            
      (** Client participates in the bakery algorithm *)
      Definition client(id: uid n) : ctree (Net  +' logE tr) void :=
        daemon (
            (* To ensure fairness *)
            start id;;
            (* number[i] := 1 + max(number) *)
            send bakery_uid GetNumber;;
            (* Loop until their turn to run the critical section *)
            CTree.iter (fun _: unit =>
                          m <- recv;;
                          match m with
                          | Some (Build_Msg _ Ack) =>
                              ret (inl tt)
                          | Some (Build_Msg _ CS) =>
                              (** ENTER CRITICAL SECTION!!! *)
                              done id;;
                              ret (inr tt)
                          | _ => ret (inl tt)
                          end) tt).

      
    End N.

    Program Definition A : uid 2 := @of_nat_lt 0 _ _.
    Program Definition B : uid 2 := @of_nat_lt 1 _ _.
    
    Lemma liveness: forall id,
        let sys := run [client A; client B] in
        infinitely_often (lift (fun a => a = Start id)) sys -> (* fairness *)
        eventually (lift (fun a => a = Done id)) sys.
    Proof.
      unfold run.
      intros.
      rewrite unfold_schedule.
      step in H.


      inv H.
      cbn*.
      unfold run, client; intros.
      rewrite unfold_schedule.
      cbn; econstructor.
      fold_subst; unfold observe; cbn.
      simp schedule_one; cbn.
      
    Admitted.
      
End Baker.
