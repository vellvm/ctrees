From Coq Require Import
     Fin
     Nat
     List
     Relations.

From ITree Require Import
     Indexed.Sum
     CategoryOps.

From CTree Require Import
     CTree
     Eq.Equ
     Eq.Trans
     Interp.Uid
     Interp.FoldStateT
     Misc.Vectors
     Core.Utils.

From ExtLib Require Import
     Monad
     Functor.

From Coinduction Require Import
     rel coinduction tactics.

Set Implicit Arguments.

(*| A logic with explicit [uid n] path quantifiers, see [Interp/Uid.v] |*)
Module Etl.

  Section ETL.
    Context {C: Type -> Type} {X: Type} (S: Type) (n: nat) `{HasStuck: B0 -< C}.
    Notation T := (ctree (Uid n (stateE S)) C X).
    Notation SS := (@Trans.SS (Uid n (stateE S)) C X).    
    Notation SP := (S -> SS -> Prop).

    (*| Finitely many [tau] and [obs Get s] labels, before getting a [obs (Put s') tt] |*)
    Definition strans(i: uid n)(s s': S): srel SS SS :=
      (cup (trans tau) (trans (obs (Frame (@Get S) i) s)))^* ⋅ trans (obs (Frame (Put s') i) tt).

    Definition lift(p: S -> Prop): SP :=
      fun s _ => p s.

    (* Propositional *)
    Definition eimpl: SP -> SP -> SP :=
      fun a b t l => a t l -> b t l.

    Definition eand: SP -> SP -> SP :=
      fun a b t l => a t l /\ b t l.

    Definition eor: SP -> SP -> SP :=
      fun a b t l => a t l \/ b t l.

    Definition enot: SP -> SP :=
      fun a t l => not (a t l).    
  
    (** exists[i] s, s |= next p *)
    Definition iex(i: uid n)(p: SP): SP :=
      fun s t =>
        exists s' t', strans i s s' t t' /\ p s' t'.

    (** forall[i] s, s |= next p *)
    Definition iax(i: uid n)(p: SP): SP :=
      fun s t =>
        forall s' t', strans i s s' t t' -> p s' t'.

    (** exists[i] s, s |= eventually p *)
    Definition iex(i: uid n)(p: SP): SP :=
      fun s t => (exists s' t', strans i s s' t t' /\ p s' t').

End Etl.

