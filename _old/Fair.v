From Coq Require Import
  Vector
  List.

From CTree Require Import
  CTree.Core
  CTree.Equ
  Events.Core
  Events.Writer
  CTree.Events.State
  Utils.Vectors.

From ExtLib Require Import
  Structures.Monads
  Structures.MonadState
  Data.Monads.StateMonad.

Import VectorNotations MonadNotation.
Local Open Scope vector_scope.
Local Open Scope monad_scope.

Set Implicit Arguments.

(*| Fair distribution axiomatization |*)
Section Fair.
    (*
          (n: nat)  (* choose a number from [0, n) *)
          (m: nat). (* at most [m] consequent times the same one *)
    *)
  (*| Fair choice |*)
  Variant fairE(n: nat): Type@{eff} := FChoice: fairE n.

  Arguments FChoice {n}.
  #[global] Instance encode_fairE {n}: Encode (fairE n) :=
    fun '(FChoice) => fin' n.

  (*| Choice distribution counters |*)
  Notation distr n := (vec' n nat).

  #[global] Instance handler_uniformE{n}(m: nat):
    fairE n ~> stateT (distr n) (ctree (writerE (fin n * fin m))) := {
      handler 'FChoice :=
        vs <- get;;
        (* The index of all counters in [vs] which are [≤ m] *)
        match filter_to_indices vs (fun n => Nat.leb n m) with
        | List.nil =>
            (* Reached limit [m] for all counters, reset to [0] *)
            i <- Ctree.branch n ;;
            let zeroes := Vector.const 0 (S n) in
            put (Vector.replace zeroes i 1);;
            Ret i
        | List.cons h ts =>
            j <- Ctree.branch (List.length ts) ;;
            let i := safe_nth h ts j in
            (* How many times have we picked [i]? *)
            let cnt := Vector.nth vs i in
            (* Increase [i] by [1] *)
            put (Vector.replace vs i (S cnt));;
            Ret i
        end
    }.

End Fair.

Definition fchoice {n}: ctree (fairE n) (fin' n) :=
  Ctree.trigger (@FChoice n).

(*
(*| Need CTL here to prove fairness |*)
Definition fairness: forall {X} (t: ctree uniformE X) vs (x: X),
    Leaf (interp handler_uniformE t) (vs, x) -> Forall (fun n => n <= m) vs.
 *)
