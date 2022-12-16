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

From RelationAlgebra Require Import
     rel srel.

Set Implicit Arguments.

(*| A logic with explicit [uid n] path quantifiers, see [Interp/Uid.v] |*)
Module Etl.

  Section ETL.
    Context {C: Type -> Type} {X: Type} (S: Type) (n: nat) `{HasStuck: B0 -< C}.
    (** ctree (Uid n (stateE S)) C X *)
    Notation SS := (ctree (Uid n (stateE S)) C X).
    Notation SP := (SS -> S -> Prop).

    Definition lift(p: S -> Prop): SP :=
      fun _ s => p s.

    Definition Top := lift (fun _ => True).
    Definition Bot := lift (fun _ => False).

    (* Propositional *)
    Definition eimpl: SP -> SP -> SP :=
      fun a b t l => a t l -> b t l.

    Definition eand: SP -> SP -> SP :=
      fun a b t l => a t l /\ b t l.

    Definition eor: SP -> SP -> SP :=
      fun a b t l => a t l \/ b t l.

    Definition enot: SP -> SP :=
      fun a t l => not (a t l).    
  
    (* exists[i] s, s |= next p *)
    Definition iex(i: uid n)(p: SP): SP :=
      fun t s =>
        exists t' s', strans i s s' t t' /\ p t' s'.

    (* forall[i] s, s |= next p *)
    Definition iax(i: uid n)(p: SP): SP :=
      fun t s =>
        forall t' s', strans i s s' t t' -> p t' s'.

    (* exists[i] strong until *)
    Inductive ieu(i: uid n)(p q: SP): SP :=
    | MatchE: forall t s,      (* Match state [t] and label [l] *)
        q t s -> ieu i p q t s
    | StepE: forall t s,       (* Matches all next states [t'] *)
        p t s ->
        (exists s' t', strans i s s' t t' /\
                    ieu i p q t' s') ->
        ieu i p q t s.

    (* Forall[i] strong until *)
    Inductive iau(i: uid n)(p q: SP): SP :=
    | MatchA: forall t s,      (* Match state [t] and label [l] *)
        q t s -> iau i p q t s
    | StepA: forall t s,       (* Matches all next states [t'] *)
        p t s ->
        (forall s' t', strans i s s' t t' ->
                    iau i p q t' s') ->
        iau i p q t s.
    
    (* Forall[i] finally *)
    Definition iaf i p := (iau i Top p).
  
    (* Exists finally *)
    Definition ief i p := (ieu i Top p).

    (*| Coinductives |*)  
    (* Forall global *)
    Definition iagF (R: SP -> SP): SP -> SP :=
      fun (p: SP) t l =>
        p t l /\
          (forall t' l', trans l' t t' -> R p t' l').

  (* Exists global *)
  Definition egF (R: SP -> SP): SP -> SP :=
    fun (p: SP) t l =>
      p t l /\
      (exists t' l', trans l' t t' /\ R p t' l').

  Hint Constructors eu au: core.
  Hint Unfold lift cand cor cimpl cnot af ef ax ex agF egF: core.
    
  Program Definition ag_: mon (SP -> SP) := {| body := agF  |}.
  Next Obligation.
    destruct H0; split; eauto.
  Qed.

  Program Definition eg_: mon (SP -> SP) := {| body := egF  |}.  
  Next Obligation.    
    destruct H0 as (A & t' & l' & Htr & ?); split; eauto.
  Qed.

  Definition ag := (gfp (@ag_)).
  Definition eg := (gfp (@eg_)).

End Etl.

