(*|
=========================================
Modal logics over ctrees
=========================================
|*)
From Coq Require Import
     Lia
     Basics
     Fin
     RelationClasses
     Program.Equality
     Logic.Eqdep.

From Coinduction Require Import
     coinduction rel tactics.

From ITree Require Import Core.Subevent.

From CTree Require Import
     CTree
     Utils
     Interp.FoldStateT
     Eq
     Eq.Trans.

From RelationAlgebra Require Export
     rel srel.

Set Implicit Arguments.

(* TODO: Decide where to set this *)
Arguments trans : simpl never.

Section Ctl.
  Arguments label: clear implicits.
  Context {E C: Type -> Type} {X: Type} {HasStuck: B0 -< C}.
  Notation SS := (ctree E C X).
  Notation SP := (SS -> label E -> Prop).

  (* Lift label predicates to SP *)
  Definition lift(p: label E -> Prop): SP :=
    fun t l => p l.
  
  (* Propositional *)
  Definition cimpl: SP -> SP -> SP :=
    fun a b t l => a t l -> b t l.

  Definition cand: SP -> SP -> SP :=
    fun a b t l => a t l /\ b t l.

  Definition cor: SP -> SP -> SP :=
    fun a b t l => a t l \/ b t l.

  Definition cnot: SP -> SP :=
    fun a t l => not (a t l).
  
  (* Temporal *)
  
  (* Forall Next *)
  Definition ax: SP -> SP :=
    fun p t _ => forall l t', trans l t t' -> p t' l.

  (* Exists Next *)
  Definition ex: SP -> SP :=
    fun p t _ => exists l t', trans l t t' -> p t' l.
  
  (* Forall Finally *)
  Inductive af: SP -> SP :=
  | MatchA: forall t l (p: SP),      (* Match state [t] and label [l] *)
      p t l -> af p t l
  | StepA: forall t l (p: SP),       (* Matches all next states [t'] *)
      (forall l' t', trans l' t t' ->
               af p t' l') ->
      af p t l.

  (* Exists finally *)
  Inductive ef: SP -> SP :=
  | MatchE: forall t l (p: SP),        (* Match state [t] and label [l] *)
      p t l -> ef p t l
  | StepE: forall t l (p: SP),         (* Matches one next state [t'] *)
      (exists l' t', trans l' t t' ->
                ef p t' l') ->
      ef p t l.

  (* Coinductive -- Forall global *)
  Definition agF (R: SP -> SP): SP -> SP :=
    fun (p: SP) t l =>
      p t l /\
      (forall t' l', trans l' t t' -> R p t' l').

  (* Exists global *)
  Definition egF (R: SP -> SP): SP -> SP :=
    fun (p: SP) t l =>
      p t l /\
      (exists t' l', trans l' t t' -> R p t' l').

  Hint Constructors ef af: core.
  Hint Unfold lift cand cor cimpl cnot ax ex agF egF: core.
    
  Program Definition ag_: mon (SP -> SP) := {| body := agF  |}.
  Next Obligation.
    destruct H0; split; eauto.
  Qed.

  Program Definition eg_: mon (SP -> SP) := {| body := egF  |}.  
  Next Obligation.
    destruct H0 as (A & t' & l' & H'); split; eauto. 
  Qed.

  Definition ag := (gfp (@ag_)).
  Definition eg := (gfp (@eg_)).

End Ctl.

Module CtlNotations.

  Notation Top := (fun _ _ => True).
  Notation Bot := (fun _ _ => False).

  Notation "t , l |= p" := (p t l) (at level 90, left associativity, only parsing).
  
  Notation "'EX' p" := (ex p) (at level 70).
  Notation "'AX' p" := (ax p) (at level 70).
  Notation "'EF' p" := (ef p) (at level 70).
  Notation "'AF' p" := (af p) (at level 70).
  Notation "'EG' p" := (eg p) (at level 70).
  Notation "'AG' p" := (ag p) (at level 70).

  Notation "p '&&&' q" := (cand p q) (at level 89, left associativity).
  Notation "p '|||' q" := (cor p q) (at level 89, left associativity).
  Notation "p '->>' q" := (cimpl p q) (at level 89, left associativity).
  Notation "'!' p" := (cnot p) (at level 89).
  
  Notation "[ 'EG' ] p" := (eg_ p) (at level 40).
  
  Notation "[[ 'AG' ]] p" := (agF p) (at level 40).
  Notation "[[ 'EG' ]] p" := (egF p) (at level 40).
  
  Notation "{ 'AG' } p" := ((t ag_) p) (at level 40).
  Notation "{ 'EG' } p" := ((t eg_) p) (at level 40).
  
  Notation "{{ 'AG' }} p" := ((bt ag_) p) (at level 40).
  Notation "{{ 'EG' }} p" := ((bt eg_) p) (at level 40).
  
End CtlNotations.

Import CtlNotations.

Ltac fold_g :=
  repeat
    match goal with
    | h: context[@ag_ ?E ?C ?X ?HS ?R ] |- _ => fold (@ag E C X HS R) in h
    | |- context[@ag_ ?E ?C ?X ?HS ?R ]      => fold (@ag E C X HS R)
    | h: context[@eg_ ?E ?C ?X ?HS ?R ] |- _ => fold (@eg E C X HS R) in h
    | |- context[@eg_ ?E ?C ?X ?HS ?R ]      => fold (@eg E C X HS R)
    end.

Ltac __coinduction_g R H :=
  unfold ag, eg; apply_coinduction; fold_g; intros R H.

Tactic Notation "__step_g" :=
  match goal with
  | |- context[@ag ?E ?C ?X ?HasStuck ?p ?t ?q] =>
      unfold ag;
      step;
      fold (@ag E C X HasStuck p t q)
  | |- context[@eg ?E ?C ?X ?HasStuck ?p ?t ?q] =>
      unfold eg;
      step;
      fold (@eg E C X HasStuck p t q)
  | |- _ => step
  end.

(* #[local] Tactic Notation "step" := __step_entails. *)
#[local] Tactic Notation "coinduction" simple_intropattern(R) simple_intropattern(H) :=
  __coinduction_g R H.

Ltac __step_in_g H :=
  match type of H with
  | context [@ag ?E ?C ?X ?HasStuck ] =>
      unfold ag in H;
      step in H;
      fold (@ag E C X HasStuck) in H
  | context [@eg ?E ?C ?X ?HasStuck ] =>
      unfold eg in H;
      step in H;
      fold (@eg E C X HasStuck) in H
  end.

#[local] Tactic Notation "step" "in" ident(H) := __step_in_g H.

Section Lemmas.
  Arguments label: clear implicits.
  Context {E C: Type -> Type} {X: Type} {HasStuck: B0 -< C}
          (t: ctree E C X) (l: label E).

  (*| Top is True |*)
  Lemma ctl_top:
    t, l |= Top.
  Proof.  reflexivity. Qed.    

  (*| Bot is False |*)
  Lemma ctl_bot:
    ~ (t, l |= Bot).
  Proof.
    intro CONTRA.
    apply CONTRA.    
  Qed.

  (*| Ex-falso *)
  Lemma ctl_ex_falso: forall p,
      t,l |= Bot -> t,l |= p.
  Proof.
    intros p CONTRA.
    exfalso; now apply ctl_bot in CONTRA.
  Qed.

  (** Lemmas of CTL 

      AG φ ≡ φ ∧ AX AG φ
      EG φ ≡ φ ∧ EX EG φ
      AF φ ≡ φ ∨ AX AF φ
      EF φ ≡ φ ∨ EX EF φ
      A[φ U ψ] ≡ ψ ∨ (φ ∧ AX A[φ U ψ])
      E[φ U ψ] ≡ ψ ∨ (φ ∧ EX E[φ U ψ])
   *)
  Lemma af_ax: forall p,
      t,l |= AF p <-> t,l |= p ||| AX (AF p).
  Proof.
    split; intros; inv H.
    - now left.
    - now right. 
    - now left. 
    - now right.
  Qed.

  Lemma ef_ex: forall p,
      t,l |= EF p <-> t,l |= p ||| EX (EF p).
  Proof.
    split; intros; inv H.
    - now left.
    - now right. 
    - now left. 
    - now right.
  Qed.

  Lemma ag_ax: forall p,
      t,l |= AG p <-> t,l |= p &&& AX (AG p).
  Proof with auto.
    split; intros.
    - split; step in H.
      + now destruct H.
      + destruct H.
        unfold ax...
    - destruct H.
      red in H0.
      step.
      unfold ag_, agF; split; eauto; simpl.
      intros.
  Admitted.

End Lemmas.
