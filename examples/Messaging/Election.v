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
  CTree.iter
    (fun _ =>
       m <- recv;;
       match m with
       | Some (Candidate candidate) =>
           match Nat.compare candidate id with (* candidate < id *)
           (* My [left] neighbor proposed a candidate, I support that candidate *)
           | Gt => send right (Candidate candidate) ;; Ret (inl tt)
           (* My left neighbor proposed a candidate, I do not support him *)
           | Lt => Ret (inl tt)
           (* I am the leader, but only I know *)
           | Eq => send right (Elected id) ;; Ret (inr tt)
           end
       | Some (Elected x) =>
           (* I know [x] is the leader *)
           send right (Elected x) ;; Ret (inr tt)
       | None => Ret (inl tt) (* Didn't receive anything *)
       end) tt.

(*
  For the system "sched {proc(id,n) | 0 <= id < n}"
  Soundness    :
 - If I exit the loop, it's because I have elected somebody
 - If two processes exit, they have elected the same person
  Termination :
 - Eventually, every process exit/elects
 - (?) AF now {(fun '(qs,id) => nth_error qs id = Some [Elected id]%list)}

Consequence of:
  Invariant (proc (id,n))
  Variant   (proc (id,n))
  Property about sched

On dynamic and logical state:
 Dynamic : one FIFO per process
 Logical (l) : uid -> (has_elected (id) | best_so_far (id))
 (* Could be sufficent to just remember elected or has_seen(n)?*)

The (global system) correctness is:
AF now (fun l => exists id, forall x, l x = has_elected id
                 /\ terminated x)

Let's look at one process: proc(i,n)  (i < n)

P (entry loop iteration) ===> Q (end loop iteration)
 - exists j, l i = best_so_far(j)
 - rcv (Elected k) -> k >= (>?) j
 - rcv (Elected k) -> k >= (>?) j

On the side of termination, let's define the variant:
 - global:
 V(l) =
  Lexicographic on
  + worth 2 if has_elected, worth 1 if has_seen(n)
  + Progresses if a [candidate(n)] or [elected] message gets closer to the head of a fifo (i.e. if I pop from a fifo containing such a message)

V(l) strictly increases if I received n (as candidate or elected)
V(l) remains equal otherwise

Assumption: could the fairness have the granularity of a loop iteration?

Question: how to lift this local obligation to global termination?
- At all time, (candidate(n) or elected(n)) is in a mailbox


We must exploit here the FIFO politics to express that if I rcv and send something having nothing to do with n, I don't push back the message in the queue

forall i, V /\ I ==> AX (proc i) |- V décroit strict ou I
exists j, V /\ I ==> AX (proc j) |- V décroit strict
----------------------------------------------------
V ==> AF (sched n proc) |- V décroit strict

 *)
