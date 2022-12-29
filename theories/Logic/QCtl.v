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

(*| A transition relation on Uid (state) |*)
Section Strans.
  From RelationAlgebra Require Import monoid.
  Context {C: Type -> Type} {X: Type} (S: Type) (n: nat) `{HasStuck: B0 -< C}.
  Notation SS := (@Trans.SS (Uid n (stateE S)) C X).    
  Notation SP := (S -> SS -> Prop).

  (*| Finitely many [tau] and [obs Get s] labels, before getting a [obs (Put s') tt] |*)
  Definition strans(i: uid n)(s s': S): srel SS SS :=
    (trans tau ⊔ trans (obs (Frame (@Get S) i) s))^* ⋅ trans (obs (Frame (Put s') i) tt).
End Strans.


(*| A logic with explicit [uid n] path quantifiers, see [Interp/Uid.v] |*)
Section QCTL.
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

  (* exists s, s |= next p *)
  Definition ex (p: SP): SP :=
    fun t s => forall i, iex i p t s.

  (* forall s, s |= next p *)
  Definition ax(p: SP): SP :=
    fun t s => forall i, iax i p t s.
  
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

  (* Exists s, s |= next p *)
  Definition eu (p q: SP): SP :=
    fun t s => forall i, ieu i p q t s.

  (* Forall s, s |= next p *)
  Definition au (p q: SP): SP :=
    fun t s => forall i, iau i p q t s.
  
  (* Forall finally *)
  Definition iaf i p := (iau i Top p).
  
  (* Exists[i] finally *)
  Definition ief i p := (ieu i Top p).
  
  (* Forall finally *)
  Definition af p := (au Top p).
  
  (* Exists[i] finally *)
  Definition ef p := (eu Top p).

  (*| Coinductives |*)  
  (* Forall[i] global *)
  Definition iagF (i: uid n) (R: SP -> SP): SP -> SP :=
    fun (p: SP) t s =>
      p t s /\
        (forall t' s', strans i s s' t t' -> R p t' s').

  (* Exists[i] global *)
  Definition iegF (i: uid n) (R: SP -> SP): SP -> SP :=
    fun (p: SP) t s =>
      p t s /\
        (exists t' s', strans i s s' t t' /\ R p t' s').

  Hint Constructors ieu iau: core.
  Hint Unfold lift eand eor eimpl enot iaf ief iax iex iagF iegF: core.
  
  Program Definition iag_(i: uid n): mon (SP -> SP) := {| body := (iagF i)  |}.
  Next Obligation.
    destruct H0; split; eauto.
  Qed.

  Program Definition ieg_ (i: uid n): mon (SP -> SP) := {| body := (iegF i)  |}.  
  Next Obligation.    
    destruct H0 as (A & t' & l' & Htr & ?); split; eauto.
  Qed.

  Definition iag (i: uid n) := (gfp (iag_ i)).
  Definition ieg (i: uid n) := (gfp (ieg_ i)).
  Definition ag p t s := forall i, iag i p t s.
  Definition eg p t s := forall i, ieg i p t s.
End QCTL.

Module QctlNotations.

  Notation "t , s |= p" := (p t s) (at level 90, left associativity, only parsing).
  
  Notation "'∃' i ',' 'X' p" := (iex i p) (at level 70).
  Notation "'∀' i ',' 'X' p" := (iax i p) (at level 70).
  Notation "'∃' i ',' 'F' p" := (ief i p) (at level 70).
  Notation "'∀' i ',' 'F' p" := (iaf i p) (at level 70).
  Notation "'∃' i ',' 'G' p" := (ieg i p) (at level 70).
  Notation "'∀' i ',' 'G' p" := (iag i p) (at level 70).

  Notation "'∃' i ',' p 'U' q" := (ieu i p q) (at level 50, left associativity).
  Notation "'∀' i ',' p 'U' q" := (iau i p q) (at level 50, left associativity).

  Notation "p '&&&' q" := (eand p q) (at level 89, left associativity).
  Notation "p '|||' q" := (eor p q) (at level 89, left associativity).
  Notation "p '->>' q" := (eimpl p q) (at level 99, right associativity).
  Notation "'!' p" := (enot p) (at level 89).

  Notation "[ '∃' i ',' 'G' ] p" := (ieg_ i _ p) (at level 40).
  Notation "[ '∀' i ',' 'G' ] p" := (iag_ i _ p) (at level 40).

  
  Notation "[[ '∃' i ',' 'G' ]] p" := (iegF i _ p) (at level 40).
  Notation "[[ '∀' i ',' 'G' ]] p" := (iagF i _ p) (at level 40).

  Notation "{ '∃' i ',' 'G' } p" := ((t (ieg_ i)) _ p) (at level 40).
  Notation "{ '∀' i ',' 'G' } p" := ((t (iag_ i)) _ p) (at level 40).

  Notation "{{ '∃' i ',' 'G' }} p" := ((bt (ieg_ i)) _ p) (at level 40).
  Notation "{{ '∀' i ',' 'G' }} p" := ((bt (iag_ i)) _ p) (at level 40).
    
  Notation "'EX' p" := (ex p) (at level 70).
  Notation "'AX' p" := (ax p) (at level 70).
  Notation "'EF' p" := (ef p) (at level 70).
  Notation "'AF' p" := (af p) (at level 70).
  Notation "'EG' p" := (eg p) (at level 70).
  Notation "'AG' p" := (ag p) (at level 70).
  Notation "p 'AU' q" := (au p q) (at level 50, left associativity).
  Notation "p 'EU' q" := (eu p q) (at level 50, left associativity). 

End QctlNotations.

Section Lemmas.

