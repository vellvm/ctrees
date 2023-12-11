From ExtLib Require Import
  Structures.Monad
  Structures.MonadState
  Data.Monads.IdentityMonad
  Data.Monads.StateMonad.

Import MonadNotation.
Local Open Scope monad_scope.

Generalizable All Variables.

Open Scope type_scope.

(*| Reified effects that have an encoding into the Coq type system |*)
Universe eff.
Class Encode E : Type :=
  encode: E -> Type@{eff}.

#[global] Instance Encode_Sum (E1 E2 : Type@{eff}) `{Encode E1} `{Encode E2} : Encode (E1 + E2) :=
  fun e12 => match e12 with 
          | inl e1 => encode e1
          | inr e2 => encode e2 end.

(*| Empty effect |*)
Variant void: Type :=.

#[global] Instance encode_void: Encode void :=
  fun e => match e with end.

(** Typeclasses designed to implement a subevent relation, relied on by the trigger function *)
Class ReSum (E1 E2 : Type@{eff}) : Type := resum : E1 -> E2.
Class ReSumRet E1 E2 `{Encode E1} `{Encode E2} `{ReSum E1 E2} : Type :=
  resum_ret : forall (e : E1), encode (resum e) -> encode e.

#[global] Instance ReSum_inl {E1 E2} : ReSum E1 (E1 + E2) := inl.
#[global] Instance ReSum_inr {E1 E2} : ReSum E2 (E1 + E2) := inr.

#[global] Instance ReSumRet_inl {E1 E2} `{Encode E1} `{Encode E2}: ReSumRet E1 (E1 + E2) :=
  fun _ e => e.
#[global] Instance ReSumRet_inr {E1 E2} `{Encode E1} `{Encode E2} : ReSumRet E2 (E1 + E2) :=
  fun _ e => e.

#[global] Instance ReSum_void {E} : ReSum void E := fun e => match e with end.

#[global] Instance ReSumRet_void {E} `{Encode E}: ReSumRet void E :=
  fun e _ => match e with end. 

#[global] Instance ReSum_refl {E} : ReSum E E := fun e => e.
#[global] Instance ReSumRet_refl {E} `{Encode E}: ReSumRet E E :=
  fun _ e => e.

(*| [Bar E] is the dependent product of an event
  [e: E] and its response (x: encode e) |*)
Variant Bar (E: Type) `{Encode E} :=
  | Obs (e: E) (x: encode e).

Arguments Obs {E} {_} e x.

(*| Defines a monad homomorphism from free monad with [E] to [M] |*)
Class Handler(E: Type) (M: Type -> Type): Type := {
    #[global] Handler_Encode :: Encode E;
    handler(e: E) : M (encode e)
  }.

Notation "E ~> M" := (Handler E M) (at level 68, right associativity). 

#[global] Instance handler_exfalso `{Monad M} {Σ : Type} : void ~> M  := {
    handler(e : void) := match e with end
  }.

#[global] Instance handler_plus{A B} `{Monad M} `{CA: A ~> M} `{CB: B ~> M}: A + B ~> M := {
    handler e :=
      match e with
      | inl e => handler e
      | inr e => handler e
      end
  }.
