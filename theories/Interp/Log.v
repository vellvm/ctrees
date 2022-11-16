From Coq Require Import
     Fin
     Relations.

From ITree Require Import
     Indexed.Sum
     Subevent
     CategoryOps.

From CTree Require Import
     CTree
     Vectors
     Interp.State.

From ExtLib Require Import
     Maps
     FMapAList
     RelDec
     String
     Monad.

Import MonadNotation.
Local Open Scope monad_scope.

Set Implicit Arguments.

(** This is not your standard state monad,
    as daemons do not return, ever. We instead interpret
    state *changes* as Visible log events. So this is a transformer
    from stateE S -> logE S *) 
Module Log.
  Import Monads.

  Inductive logE (S: Type): Type -> Type :=
  | Log: S -> logE S unit.

  Arguments Log {S}.
  Definition log {E C S} `{logE S -< E}: S -> ctree E C unit := fun s => trigger (Log s).
    
  Definition h_state_to_log {E C S}: stateE S ~> stateT S (ctree (E +' logE S) C) :=
    fun _ e s =>
      match e with
      | Get _ => Ret (s, s)
      | Put s' => Vis (inr1 (Log s')) (fun _: unit => Ret (s', tt))
      end.

  Definition pure_state_to_log {E C S} : E ~> stateT S (ctree (E +' logE S) C)
    := fun _ e s => Vis (inl1 e) (fun x => Ret (s, x)).

  Definition run_state_log {E C S} `{B1 -< C}: ctree (E +' stateE S) C ~> stateT S (ctree (E +' logE S) C)
    := fold_state (case_ pure_state_to_log h_state_to_log) (fun b => pure_state_choice b). 

  Definition run_states_log {n E C S} `{B1 -< C}(v: vec n (ctree (E +' stateE S) C void)):
    S -> vec n (ctree (E +' logE S) C void) :=
    fun st => Vector.map (fun a => CTree.map snd (run_state_log a st)) v.

End Log.

