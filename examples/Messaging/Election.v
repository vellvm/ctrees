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

Import CTreeNotations ListNotations VectorNotations CtlNotations.
Local Open Scope vector_scope.
Local Open Scope ctree_scope.
Local Open Scope ctl_scope.

Set Implicit Arguments.

Variant csE: Type -> Type :=
  | In_CS: bool -> csE unit.

Definition enter_cs {E C} `{csE -< E}: ctree E C unit :=
  trigger (In_CS true). 
Definition exit_cs {E C} `{csE -< E}: ctree E C unit :=
  trigger (In_CS false). 

#[global] Instance handler_cs: csE ~~> state bool :=
  fun _ e => match e with In_CS b => put b end.

(*| Client process |*)
Definition proc (id: uid)(n: nat): ctree ((netE uid +' parE) +' csE) B01 unit :=
  let right := modulo (S id) n in
  CTree.forever (fun _ =>
      (* 1. Send my [id] to the process on the right *)
      send right id;;
      (* 2. Loop until received [CS] message *)
      CTree.iter (fun _ =>
                    m <- recv;;
                    match m with
                    | Some x =>
                        match Nat.compare x id with
                        (* Maybe my [right] neighbor is the leader *)
                        | Gt => send right x;; Ret (inr tt)
                        (* smaller [id] means definitely not the leader *)
                        | Lt => Ret (inr tt)
                        (* I am the leader! *)
                        | Eq => enter_cs ;; Ret (inr tt)
                        end                    
                    | None => Ret (inl tt)
                    end) tt) tt.

Lemma election_live: 
    <( {rr [proc 0 3; proc 1 3; proc 2 3]},
     {([]%list, 0, false)} |= AG (AF now {fun '(_, b) => b = true}) )>.
Proof.
  unfold rr.
  eapply ctl_forever_ar.
Admitted.  
