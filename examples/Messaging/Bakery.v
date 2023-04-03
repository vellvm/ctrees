From ITree Require Import
     Subevent
     CategoryOps
     Indexed.Sum.

From Coq Require Import Nat List.

From ExtLib Require Import
     Data.Nat
     Structures.Monad
     Structures.MonadState
     Data.Monads.StateMonad
     Structures.Maps
     Data.Map.FMapAList.

From CTree Require Import
     CTree
     Eq
     Interp.Network
     Logic.Kripke
     Logic.Ctl.

Import MonadNotation CtlNotations.
Local Open Scope list_scope.
Local Open Scope monad_scope.
Local Open Scope ctree_scope.

Set Implicit Arguments.

Variant csE: Type -> Type :=
  | In_CS: bool -> csE unit.

Definition enter_cs {E C} `{csE -< E}: ctree E C unit :=
  trigger (In_CS true). 
Definition exit_cs {E C} `{csE -< E}: ctree E C unit :=
  trigger (In_CS false). 

#[global] Instance handler_cs: csE ~~> state bool :=
  fun _ e => match e with
          | In_CS b => put b
          end.

From CTree Require Import FoldStateT.

(*| Client process |*)
Definition client (id: uid)(bakery: uid): ctree (netE uid +' csE) B1 void :=
  CTree.forever (
      (* 1. Ask for a ticket number *)
      send bakery id;;
      (* 2. Loop until received [CS] message *)
      CTree.iter (fun _ =>
                    m <- recv;;
                    match m with
                    | Some x => if x =? bakery then 
                                 enter_cs;;
                                 (* DO WORK HERE*)
                                 exit_cs;;
                                 Ret (inr tt)
                               else
                                 Ret (inl tt)                                 
                    | None => Ret (inl tt)
                    end) tt).

(* A finite map of [uid] to their number *)
Notation baker_map := (alist uid nat) (only parsing).

(* Find the minimum number *)
Definition alist_minv: baker_map -> option (uid * nat) :=
  fold_alist (fun k v acc => match acc with
                          | None => Some (k, v)
                          | Some (km, vm) => if v <? vm then Some (k, v) else Some (km, vm)
                          end) None.

(*| The baker process, synchronized access to CS through ticket |*)
Definition baker(bkid: uid): ctree (netE uid +' stateE (nat * baker_map)) B1 void :=
  CTree.forever (
      (* 1. Schedule a Critical Section (CS) if possible *)
      '(cnt, book) <- get ;;
      match alist_minv book with
      | None => Ret tt
      | Some (i, _) =>
          (* Remove picked user from the queue *)
          put (cnt, alist_remove _ i book) ;;
          (* Baker sends his own [bkid] for client [i] to enter CS *)
          send i bkid 
      end ;;
      (* 2. Listen to issue new ticket number *)
      CTree.iter (fun _: unit =>
                    m <- recv;;
                    match m with
                    | Some id =>
                        put (S cnt, alist_add _ id cnt book);;
                        Ret (inr tt)
                    | None =>
                        Ret (inl tt)
                    end) tt).

