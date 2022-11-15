From Coq Require Import
     Fin
     Relations.

From ITree Require Import
     Indexed.Sum
     Subevent
     Events.State
     CategoryOps.

From CTree Require Import
     CTree
     Interp.State.

From ExtLib Require Import
     Maps
     FMapAList
     RelDec
     String
     Monad.

From DSL Require Import
     Vectors Storage.

Import MonadNotation.
Local Open Scope monad_scope.

Set Implicit Arguments.

(** This is not your standard state monad,
    as daemons do not return, ever. We instead interpret
    state *changes* as Visible log events. So this is a transformer
    from stateE S -> logE S *) 
Module Log.
  Import Monads.

  Section ParametricS.
    Context {S: Type} {dec_S: RelDec (@eq S)}.

    Inductive logE (S: Type): Type -> Type :=
    | Log: S -> logE S unit.

    Arguments Log {S}.
    Definition log {E} `{logE S -< E}: S -> ctree E unit := fun s => trigger (Log s).
    
    Definition h_state_to_log {E}: stateE S ~> stateT S (ctree (logE S +' E)) :=
      fun _ e s =>
        match e with
        | Get _ => Ret (s, s)
        | Put _ s' => Vis (inl1 (Log s')) (fun _: unit => Ret (s', tt))
        end.

    Definition pure_state_to_log {E} : E ~> stateT S (ctree (logE S +' E))
      := fun _ e s => Vis (inr1 e) (fun x => Ret (s, x)).

    Definition run_state_log {E}: ctree (stateE S +' E) ~> stateT S (ctree (logE S +' E))
      := interp_state (case_ h_state_to_log pure_state_to_log).

    Definition run_states_log {n E}(v: vec n (ctree (stateE S +' E) void)):
      S -> vec n (ctree (logE S +' E) void) :=
      fun st => Vector.map (fun a => CTree.map snd (run_state_log a st)) v.

  End ParametricS.

End Log.

