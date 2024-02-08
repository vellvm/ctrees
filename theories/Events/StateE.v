From CTree Require Import
  Utils.Utils
  Classes
  Events.Core.

From ExtLib Require Import
  Structures.Monads
  Structures.MonadState
  Data.Monads.StateMonad.

Import MonadNotation.
Local Open Scope monad_scope.

Set Implicit Arguments.
Generalizable All Variables.

(*| State events |*)
Section State.
  Variable (S : Type).
  Variant stateE : Type :=
    | Get : stateE
    | Put : S -> stateE.

  #[global] Instance encode_stateE: Encode stateE :=
    fun e => match e with
          | Get => S
          | Put _ => unit
          end.

  #[global] Instance handler_stateE: stateE ~> state S :=
    {|
      Handler_Encode := encode_stateE;
      handler e := mkState
                     (fun s =>
                        match e return (encode e * S) with
                        | Get => (s, s)
                        | Put s' => (tt, s')
                        end)
    |}.

End State.

Arguments Get {S}.
Arguments Put {S}.

#[global] Existing Instance Monad_stateT.

#[global] Instance MonadIter_stateT {M S} {MM : Monad M} {AM : MonadIter M}
  : MonadIter (stateT S M) :=
  fun _ _ step i => mkStateT (fun s =>
    iter (fun is =>
      let i := fst is in
      let s := snd is in
      is' <- runStateT (step i) s ;;
      ret match fst is' with
          | inl i' => inl (i', snd is')
          | inr r => inr (r, snd is')
        end) (i, s)).

#[global] Instance MonadBr_stateT {S M} {MM : Monad M} {AM : MonadBr M}: MonadBr (stateT S M) :=
  fun n => mkStateT (fun s => f <- mbr n;; ret (f,s)).

#[global] Existing Instance Monad_stateT.
