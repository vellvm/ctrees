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

(* Bounds *)
Notation Top := (fun _ _ => True).
Notation Bot := (fun _ _ => False).

Section Ctl.
  Arguments label: clear implicits.
  Context {E C: Type -> Type} {X: Type} {HasStuck: B0 -< C}.
  Notation SS := (ctree E C X).
  Notation SP := (SS -> label E -> Prop).

  (* Lift label predicates to SP *)
  Definition lift(p: label E -> Prop): SP :=
    fun _ l => p l.
  
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
    fun p t _ => exists l t', trans l t t' /\ p t' l.

  (* Forall strong until *)
  Inductive au: SP -> SP -> SP :=
  | MatchA: forall t l (p q: SP),      (* Match state [t] and label [l] *)
      q t l -> au p q t l
  | StepA: forall t l (p q: SP),       (* Matches all next states [t'] *)
      p t l ->
      (forall l' t', trans l' t t' ->                
                au p q t' l') ->
      au p q t l.

  (* Exists strong until *)
  Inductive eu: SP -> SP -> SP :=
  | MatchE: forall t l (p q: SP),      (* Match state [t] and label [l] *)
      q t l -> eu p q t l
  | StepE: forall t l (p q: SP),       (* Matches one next state [t'] *)
      p t l ->
      (exists l' t', trans l' t t' /\                
                eu p q t' l') ->
      eu p q t l.
  
  (* Forall finally *)
  Definition af p := (au Top p).
  
  (* Exists finally *)
  Definition ef p := (eu Top p).

  (*| Coinductives| *)  
  (* Forall global *)
  Definition agF (R: SP -> SP): SP -> SP :=
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

End Ctl.

Module CtlNotations.

  Notation "t , l |= p" := (p t l) (at level 90, left associativity, only parsing).
  
  Notation "'EX' p" := (ex p) (at level 70).
  Notation "'AX' p" := (ax p) (at level 70).
  Notation "'EF' p" := (ef p) (at level 70).
  Notation "'AF' p" := (af p) (at level 70).
  Notation "'EG' p" := (eg p) (at level 70).
  Notation "'AG' p" := (ag p) (at level 70).
  Notation "p 'AU' q" := (au p q) (at level 50, left associativity).
  Notation "p 'EU' q" := (eu p q) (at level 50, left associativity). 

  Notation "p '&&&' q" := (cand p q) (at level 89, left associativity).
  Notation "p '|||' q" := (cor p q) (at level 89, left associativity).
  Notation "p '->>' q" := (cimpl p q) (at level 99, right associativity).
  Notation "'!' p" := (cnot p) (at level 89).

  Notation "[ 'AG' ] p" := (ag_ _ p) (at level 40).
  Notation "[ 'EG' ] p" := (eg_ _ p) (at level 40).
  
  Notation "[[ 'AG' ]] p" := (agF _ p) (at level 40).
  Notation "[[ 'EG' ]] p" := (egF _ p) (at level 40).
  
  Notation "{ 'AG' } p" := ((t ag_) _ p) (at level 40).
  Notation "{ 'EG' } p" := ((t eg_) _ p) (at level 40).
  
  Notation "{{ 'AG' }} p" := ((bt ag_) _ p) (at level 40).
  Notation "{{ 'EG' }} p" := ((bt eg_) _ p) (at level 40).
  
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

  (*| Ex-falso |*)
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
  Lemma ctl_af_ax: forall p,
      t,l |= AF p <-> t,l |= p ||| AX (AF p).
  Proof.
    split; intros; inv H.
    - now left.
    - now right. 
    - now left. 
    - now right.
  Qed.

  Lemma ctl_ef_ex: forall p,
      t,l |= EF p <-> t,l |= p ||| EX (EF p).
  Proof.
    split; intros; inv H.
    - now left.
    - now right. 
    - now left. 
    - now right.
  Qed.

  Lemma ctl_ag_ax: forall p,
      t,l |= AG p <-> t,l |= p &&& AX (AG p).
  Proof. 
    split; intros.
    - split; step in H.
      + now destruct H.
      + destruct H.
        unfold ax; auto.
    - destruct H.
      red in H0.
      step.
      split; eauto; simpl.
      intros.
      now apply H0.
  Qed.

  Lemma ctl_eg_ex: forall p,
      t,l |= EG p <-> t,l |= p &&& EX (EG p).
  Proof. 
    split; intros.
    - split; step in H.
      + now destruct H.
      + destruct H as (? & t' & l' & ?).
        unfold ex; eauto.
    - destruct H as (? & t' & l' & ?).
      step.
      split; eauto.
  Qed.

  Lemma ctl_au_ax: forall p q,
      t,l |= p AU q <-> t,l |= q ||| (p &&& AX (p AU q)).
  Proof.
    split; intros.
    - inv H.
      + now left.
      + now right.
    - inv H.
      + now apply MatchA.
      + destruct H0.
        apply StepA; auto.
  Qed.
                   
End Lemmas.

Section Congruences.
  Arguments label: clear implicits.
  Context {E C: Type -> Type} {X: Type}.
  Notation SP := (SS -> label E -> Prop).

  (*| [lift] ignores trees and only looks at labels |*)
  #[global] Instance proper_lift_equ: forall (p: label E -> Prop) R,
      Proper (R ==> eq ==> iff) (@lift E C X p).
  Proof.
    unfold Proper, respectful, impl; cbn.      
    intros p R x y EQ ? l <-; split; unfold lift; auto. 
  Qed.

  #[global] Instance proper_ax_equ (P: SP) {HasStuck: B0 -< C} :
    Proper (@equ E C X X eq ==> eq ==> iff) (AX P).
  Proof.
    unfold Proper, respectful, impl; cbn.      
    intros x y EQ ? l <-; split; intro NEXT;
      unfold ax in *;
      intros; eapply NEXT.
    - now rewrite EQ.
    - now rewrite <- EQ.
  Qed.

  #[global] Instance proper_ex_equ (P: SP) {HasStuck: B0 -< C} :
    Proper (@equ E C X X eq ==> eq ==> iff) (EX P).
  Proof.
    unfold Proper, respectful, impl; cbn.      
    intros x y EQ ? l <-; split; intro NEXT;
      unfold ex in *; destruct NEXT as (l' & t' & NEXT & ?);
      do 2 eexists; split; eauto. 
    - now rewrite <- EQ.
    - now rewrite EQ.
  Qed.

  #[global] Instance proper_au_equ (P Q: SP) {HasStuck: B0 -< C}
   {PrP: Proper (@equ E C X X eq ==> eq ==> iff) P}
   {PrQ: Proper (@equ E C X X eq ==> eq ==> iff) Q}:
    Proper (@equ E C X X eq ==> eq ==> iff) (P AU Q).
  Proof.
    unfold Proper, respectful, impl; cbn.
    intros x y EQ ? l <-; split; intro au; induction au.
    (* -> *)
    - rewrite EQ in H; now apply MatchA.
    - eapply StepA.
      + now rewrite <- EQ.
      + intros l' t' TR.
        eapply H0.
        now rewrite EQ.
    (* -> *)
    - rewrite <- EQ in H; now apply MatchA.
    - eapply StepA.
      + now rewrite EQ.
      + intros l' t' TR.
        eapply H0.
        now rewrite <- EQ.
  Qed.  

  #[global] Instance proper_eu_equ (P Q: SP) {HasStuck: B0 -< C}
   {PrP: Proper (@equ E C X X eq ==> eq ==> iff) P}
   {PrQ: Proper (@equ E C X X eq ==> eq ==> iff) Q}:
    Proper (@equ E C X X eq ==> eq ==> iff) (P EU Q).
  Proof.
    unfold Proper, respectful, impl; cbn.
    intros x y EQ ? l <-; split; intro au; induction au.
    (* -> *)
    - rewrite EQ in H; now apply MatchE.
    - eapply StepE.
      + now rewrite <- EQ.
      + destruct H0 as (l' & t' & TR & ?).
        exists l', t'; split; trivial.
        * now rewrite <- EQ.
    (* -> *)
    - rewrite <- EQ in H; now apply MatchE.
    - eapply StepE.
      + now rewrite EQ.
      + destruct H0 as (l' & t' & TR & ?).
        exists l', t'; split; trivial.
        now rewrite EQ.
  Qed.
  
  #[global] Instance proper_ag_equ (P: SP) {HasStuck: B0 -< C}
   {PrP: Proper (@equ E C X X eq ==> eq ==> iff) P}:
    Proper (@equ E C X X eq ==> eq ==> iff) (AG P).
  Proof.
    unfold Proper, respectful, impl; cbn.
    intros x y EQ ? l <-; split; intro G; step in G; inv G;
      step; simpl; unfold agF; intros.
    - rewrite EQ in H.
      split; auto.
      intros t' l' TR.
      rewrite <- EQ in TR.
      now apply H0.
    - rewrite <- EQ in H.
      split; auto.
      intros t' l' TR.
      rewrite EQ in TR.
      now apply H0.
  Qed. 

  #[global] Instance proper_eg_equ (P: SP) {HasStuck: B0 -< C}
   {PrP: Proper (@equ E C X X eq ==> eq ==> iff) P}:
    Proper (@equ E C X X eq ==> eq ==> iff) (EG P).
  Proof.
    unfold Proper, respectful, impl; cbn.
    intros x y EQ ? l <-; split; intro G; step in G; inv G;
      step; simpl; unfold egF; intros.
    - rewrite EQ in H.
      split; auto.
      destruct H0 as (t' & l' & TR).
      exists t', l'. 
      now rewrite EQ in TR.
    - rewrite <- EQ in H.
      split; auto.
      destruct H0 as (t' & l' & TR).
      exists t', l'.
      now rewrite <- EQ in TR.
  Qed.
  
  #[global] Instance proper_cand_equ (P Q: SP) {HasStuck: B0 -< C}
   {PrP: Proper (@equ E C X X eq ==> eq ==> iff) P}
   {PrQ: Proper (@equ E C X X eq ==> eq ==> iff) Q}:
    Proper (@equ E C X X eq ==> eq ==> iff) (P &&& Q).
  Proof.
    unfold Proper, respectful, impl, cand; cbn.
    intros x y EQ ? l <-; split; intros (? & ?); split.
    - now rewrite <- EQ.
    - now rewrite <- EQ.
    - now rewrite EQ.
    - now rewrite EQ.
  Qed.    

    
  #[global] Instance proper_cor_equ (P Q: SP) {HasStuck: B0 -< C}
   {PrP: Proper (@equ E C X X eq ==> eq ==> iff) P}
   {PrQ: Proper (@equ E C X X eq ==> eq ==> iff) Q}:
    Proper (@equ E C X X eq ==> eq ==> iff) (P ||| Q).
  Proof.
    unfold Proper, respectful, impl, cand; cbn.
    intros x y EQ ? l <-; split; intros [? | ?].
    - left; now rewrite <- EQ.
    - right; now rewrite <- EQ.
    - left; now rewrite EQ.
    - right; now rewrite EQ.
  Qed.
  
  #[global] Instance proper_cimpl_equ (P Q: SP) {HasStuck: B0 -< C}
   {PrP: Proper (@equ E C X X eq ==> eq ==> iff) P}
   {PrQ: Proper (@equ E C X X eq ==> eq ==> iff) Q}:
    Proper (@equ E C X X eq ==> eq ==> iff) (P ->> Q).
  Proof.
    unfold Proper, respectful, impl, cimpl; cbn.
    intros x y EQ ? l <-; split; intros G HP.
    - rewrite <- EQ; apply G.
      now rewrite EQ.
    - rewrite EQ; apply G.
      now rewrite <- EQ.
  Qed.    
  
End Congruences.
