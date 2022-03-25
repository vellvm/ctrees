From ExtLib Require Import
     Structures.Functor
     Structures.Monad.

From ITree Require Import
	ITree.

From CTree Require Import
     Utils CTrees Interp.

Import ITree.Basics.Basics.Monads.
Import MonadNotation.
Open Scope monad_scope.

(* Stateful handlers [E ~> stateT S (itree F)] and morphisms
   [E ~> state S] define stateful itree morphisms
   [itree E ~> stateT S (itree F)]. *)

#[global] Instance MonadChoice_stateT {M S} {MM : Monad M} {AM : MonadChoice M}: MonadChoice (stateT S M) :=
  fun b n s =>
    f <- choice b n;;
    ret (s, f).

Definition interp_state {E M S}
           {FM : Functor M} {MM : Monad M}
           {IM : MonadIter M}{MC: MonadChoice M} (h : E ~> stateT S M) :
  ctree E ~> stateT S M := interp h.

Arguments interp_state {E M S FM MM IM MC} h [T].

Section State.

  Variable (S : Type).

  Variant stateE : Type -> Type :=
  | Get : stateE S
  | Put : S -> stateE unit.

  Definition get {E} `{stateE -< E} : itree E S := embed Get.
  Definition put {E} `{stateE -< E} : S -> itree E unit := embed Put.

  Definition h_state {E} : stateE ~> stateT S (ctree E) :=
    fun _ e s =>
      match e with
      | Get => Ret (s, s)
      | Put s' => Ret (s', tt)
      end.

  Definition pure_state {S E} : E ~> stateT S (ctree E)
    := fun _ e s => Vis e (fun x => Ret (s, x)).

  Definition run_state {E}
    : ctree (stateE +' E) ~> stateT S (ctree E)
    := interp_state (case_ h_state pure_state).

End State.

Arguments get {S E _}.
Arguments put {S E _}.
Arguments run_state {S E} [_] _ _.
