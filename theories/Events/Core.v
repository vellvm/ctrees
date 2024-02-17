From ExtLib Require Import
  Structures.Monad
  Structures.MonadState
  Data.Monads.IdentityMonad
  Data.Monads.StateMonad.

From Coq Require Import Eqdep.

Import MonadNotation.
Local Open Scope monad_scope.

Generalizable All Variables.

Open Scope type_scope.
(*| Reified effects that have an encoding into the Coq type system |*)
Universe eff.

Class Encode E : Type :=
  encode: E -> Type@{eff}.

Arguments encode: simpl never.
#[global] Instance Encode_Sum (E1 E2 : Type@{eff}) `{Encode E1} `{Encode E2} : Encode (E1 + E2) :=
  fun e12 => match e12 with 
          | inl e1 => encode e1
          | inr e2 => encode e2 end.

(** Typeclasses designed to implement a subevent relation, relied on by the trigger function *)
Class ReSum (E1 E2 : Type@{eff}) : Type := resum : E1 -> E2.
Class ReSumRet E1 E2 `{Encode E1} `{Encode E2} `{ReSum E1 E2} : Type :=
  resum_ret : forall (e : E1), encode (resum e) -> encode e.

#[global] Instance ReSum_inl {E1 E2} : ReSum E1 (E1 + E2) :=
  inl.
#[global] Instance ReSum_inr {E1 E2} : ReSum E2 (E1 + E2) :=
  inr.

#[global] Instance ReSumRet_inl {E1 E2} `{Encode E1} `{Encode E2}: ReSumRet E1 (E1 + E2) := fun _ e => e.

#[global] Instance ReSumRet_inr {E1 E2} `{Encode E1} `{Encode E2} : ReSumRet E2 (E1 + E2) := fun _ e => e.

#[global] Instance ReSum_refl {E} : ReSum E E :=
  fun e => e.
#[global] Instance ReSumRet_refl {E} `{Encode E}:
  ReSumRet E E := fun _ e => e.

(*| Empty effect |*)
Variant void: Type :=.

#[global] Instance encode_void: Encode void :=
  fun e => match e with end.

#[global] Instance ReSum_void {E} : ReSum void E :=
  fun e => match e with end.

#[global] Instance ReSumRet_void {E} `{Encode E} :
  ReSumRet void E := fun e _ => match e with end. 

(*| Defines a monad homomorphism from free monad with [E]
  to monad [M] |*)
Definition Handler E M `{Encode E} `{Monad M}: Type :=
  forall (e: E), M (encode e).

Notation "E ~> M" := (Handler E M) (at level 68, right associativity). 

Definition h_void `{Monad M}: void ~> M :=
  fun (e : void) => match e with end.

Definition h_sum{A B} `{Monad M} `{Encode A} `{Encode B}
  (ha: A ~> M) (hb: B ~> M):
  A + B ~> M := fun e =>
                  match e with
                  | inl e => ha e
                  | inr e => hb e
                  end.

(*| Dependent observations require dependent equality |*)
Definition eq_dep_obs`{Encode E} {e e':E}(v: encode e)(v': encode e'): Prop :=
  eq_dep E encode e v e' v'.

Class Productive(E: Type) `{Encode E} :=  
  prod_wit(e: E) : encode e.
Arguments Productive E {H}.
Arguments prod_wit {E} {H} {_} e /.
