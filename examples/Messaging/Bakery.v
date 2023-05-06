From ITree Require Import
     Subevent
     CategoryOps
     Indexed.Sum.

From Coq Require Import Nat List Vector.

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
     Interp.Preempt
     Logic.Kripke
     Logic.Ctl.

Import MonadNotation CtlNotations ListNotations VectorNotations.
Local Open Scope ctl_scope.
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

#[global] Instance handler_csE: csE ~~> state bool :=
  fun _ e => match e with
          | In_CS b => put b
          end.

From CTree Require Import FoldStateT.

(* A finite map of [uid] to their number *)
Notation baker_map := (alist uid nat) (only parsing).

Notation Client := (ctree ((netE uid +' parE) +' csE +' stateE (nat * baker_map)) B01 unit) (only parsing).

(*| Client process |*)
Definition client (baker: uid)(id: uid): Client :=
  CTree.forever (fun _ =>
      (* 1. Ask for a ticket number *)
      send baker id;;
      (* 2. Loop until received [CS] message *)
      CTree.iter (fun _ =>
                    m <- recv;;
                    match m with
                    | Some x => if x =? baker then 
                                 enter_cs;;
                                 (* DO WORK HERE*)
                                 exit_cs;;
                                 Ret (inr tt)
                               else
                                 Ret (inl tt)                                 
                    | None => Ret (inl tt)
                    end) tt) tt.

(* Find the minimum number *)
Definition alist_minv: baker_map -> option (uid * nat) :=
  fold_alist (fun k v acc => match acc with
                          | None => Some (k, v)
                          | Some (km, vm) => if v <? vm then Some (k, v) else Some (km, vm)
                          end) None.

(*| The baker process, synchronized access to CS through ticket |*)
Definition baker(bkid: uid): Client :=
  CTree.forever (fun _ =>
      (* 1. Schedule a Critical Section (CS) if possible *)
      '(cnt, book) <- get ;;
      (* 1.1. Pick the user with smallest ID, if exists *)
      match alist_minv book with
      | None => Ret tt
      | Some (i, _) =>
          (* Remove picked user from the queue *)
          put (cnt, alist_remove _ i book) ;;
          (* Baker sends his own [bkid] for client [i] to enter CS *)
          send i bkid 
      end ;;
      (* 2. Block to listen a new ticket number *)
      CTree.iter (fun _: unit =>
                    m <- recv;;
                    match m with
                    | Some id =>
                        put (S cnt, alist_add _ id cnt book);;
                        Ret (inr tt)
                    | None =>
                        Ret (inl tt)
                    end) tt) tt.

Fixpoint range{A} n (f: nat -> A): vec n A :=
  match n with
  | 0 => []%vector
  | S n' => (f n' :: range n' f)%vector
  end.

Notation requested_ticket bid i ts :=
  <( now {(fun '(qs, _, _, _, _) => nth_error qs bid = Some (ts ++ [i]))})>.

Notation entered_cs i :=
  <( now {(fun '(_, id, cs, _, _) => cs = true /\ i = id)} )>.

Check (rr (baker 0 :: range 3 (client 0))%vector).

Definition init_state : (list (list uid) * uid * bool * uid * alist uid uid) :=
  (List.nil, 0, false, 0, []%list).

Lemma bakery_live: forall n i ts,
    <( {rr (baker 0 :: range n (client 0))%vector},
       init_state |= AG ({requested_ticket 0 i ts} -> AF {entered_cs i}))>.
Proof.
  intros.  
  next.
  split.
  - intro H.
Admitted.  
