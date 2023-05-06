From ITree Require Import
     Subevent
     CategoryOps
     Indexed.Sum.

From Coq Require Import Nat List.

From Coq Require Import
     Vector
     List
     Arith.PeanoNat.

From ITree Require Import
     CategoryOps.

From ExtLib Require Import
     Structures.MonadState
     Data.Monads.StateMonad.

From CTree Require Import
     CTree
     Eq
     Interp.Preempt
     Interp.Network
     Logic.Kripke
     Logic.Ctl.

From Equations Require Import Equations.

Import CTreeNotations ListNotations VectorNotations CtlNotations.
Local Open Scope vector_scope.
Local Open Scope ctree_scope.
Local Open Scope ctl_scope.

Set Implicit Arguments.

Variant message :=
  | Candidate (u: nat)
  | Elected (u: nat).

(*| Client process |*)
Definition proc (id: uid)(n: nat): ctree (netE message +' parE) B01 unit :=
  let right := modulo (S id) n in
  (* 1. Send my [id] to the process on the right *)
  send right (Candidate id);;
  (* 2. Loop until we know the leader *)
  CTree.iter (fun _ =>
                m <- recv;;
                match m with
                | Some (Candidate candidate) =>
                    match Nat.compare candidate id with (* candidate < id *)
                    (* My [left] neighbor proposed a candate, I support that candidate *)
                    | Gt => send right (Candidate candidate) ;; Ret (inl tt)
                    (* My left neighbor proposed a candidate, I do not support him *)
                    | Lt => Ret (inl tt)
                    (* I am the leader, but only I know *)
                    | Eq => send right (Elected id) ;; Ret (inr tt)
                    end
                | Some (Elected x) =>
                    (* I know [x] is the leader *)
                    send right (Elected x) ;; Ret (inr tt)
                | None => Ret (inl tt) (* dropped packet *)
                end) tt.

(*| The mailbox of the leader will eventually have a message that he was elected. |*)
Lemma election_live:
  <( {rr [proc 0 1; proc 1 2; proc 2 0]},
     {([]%list, 0)} |= AF now {(fun '(qs,id) => nth_error qs id = Some [Elected id]%list)})>.
Proof.
  next.
Admitted.  

