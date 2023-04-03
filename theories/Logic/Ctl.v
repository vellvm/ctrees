(*|
=========================================
Modal logics over ctrees
=========================================
|*)

From ITree Require Import
     Events.State
     CategoryOps.

From CTree Require Import
     Eq
     CTree
     Logic.Kripke
     FoldStateT.

From Coq Require Import
     Classes.SetoidClass
     Classes.RelationPairs.

From ExtLib Require Import
     Data.Monads.StateMonad.

Set Implicit Arguments.

(*| CTL logic based on kripke semantics of ctrees |*)
Section Ctl.

  Context {E C: Type -> Type} {X S: Type}
          `{h: E ~~> state S} `{HasStuck: B0 -< C}.
  Notation SP := (ctree E C X -> S -> Prop).

  (* Forall strong until *)
  Inductive cau: SP -> SP -> SP :=
  | MatchA: forall t s (p q: SP),       
      q t s ->  (* Matches [q] now; done *)
      cau p q t s
  | StepA:  forall t s (p q: SP),       
      p t s ->    (* Matches [p] now; steps to (t', s') *)
      (forall t' s', ktrans (t,s) (t',s') -> cau p q t' s') ->
      cau p q t s.

  (* Exists strong until *)
  Inductive ceu: SP -> SP -> SP :=
  | MatchE: forall t s (p q: SP),
      q t s ->       (* Matches [q] now; done *)
      ceu p q t s
  | StepE: forall t s (p q: SP),
      p t s ->    (* Matches [p] now; steps to (t', s') *)
      (exists t' s', ktrans (t,s) (t',s') /\ ceu p q t' s') ->
      ceu p q t s.

  (* Forall release *)
  Variant carF R: SP -> SP -> SP :=
  | RMatchA: forall t s (p q: SP),       
      q t s ->  (* Matches [q] now; done *)
      p t s ->  (* Matches [p] as well *)
      carF R p q t s
  | RStepA:  forall t s (p q: SP),       
      q t s ->    (* Matches [p] now; steps to (t', s') *)
      (forall t' s', ktrans (t,s) (t',s') -> R t' s') ->
      carF R p q t s.
                          
  (* Exists release *)
  Variant cerF R : SP -> SP -> SP :=
  | RMatchE: forall t s (p q: SP),
      q t s ->       (* Matches [q] now; done *)
      p t s ->       (* Matches [p] as well *)
      cerF R p q t s
  | RStepE: forall t s (p q: SP),
      q t s ->    (* Matches [p] now; steps to (t', s') *)
      (exists t' s', ktrans (t,s) (t',s') /\ R t' s') ->
      cerF R p q t s.

  Hint Constructors cau ceu carF cerF: core.
  
  (*| Global (coinductives) |*)
  Program Definition car p q: mon SP :=
    {| body := fun R t s => carF R p q t s |}.
  Next Obligation. destruct H0; auto. Qed.
  
  Program Definition cer p q: mon SP :=
    {| body := fun R t s => cerF R p q t s |}.
  Next Obligation. destruct H0; [eauto | destruct H1 as (t' & s' & TR & ?)]; apply RStepE; eauto. Qed.
  
  Inductive CtlFormula: Type :=
  | CNowS (p : S -> Prop): CtlFormula
  | CNowR (p : X -> S -> Prop): CtlFormula
  | CAnd    : CtlFormula -> CtlFormula -> CtlFormula
  | COr     : CtlFormula -> CtlFormula -> CtlFormula
  | CImpl   : CtlFormula -> CtlFormula -> CtlFormula
  | CAX     : CtlFormula -> CtlFormula
  | CEX     : CtlFormula -> CtlFormula
  | CAU     : CtlFormula -> CtlFormula -> CtlFormula
  | CEU     : CtlFormula -> CtlFormula -> CtlFormula
  | CAR     : CtlFormula -> CtlFormula -> CtlFormula
  | CER     : CtlFormula -> CtlFormula -> CtlFormula.

  (* Entailment inductively on formulas *)
  Fixpoint entailsF (φ: CtlFormula): ctree E C X -> S -> Prop :=
    match φ with
    | CNowS p   => fun _ s => p s
    | CNowR q   => fun t s => exists (x: X), t ≅ Ret x /\ q x s
    | CAnd  φ ψ => fun t s => (entailsF φ t s) /\ (entailsF ψ t s)
    | COr   φ ψ => fun t s => (entailsF φ t s) \/ (entailsF ψ t s)
    | CImpl φ ψ => fun t s => (entailsF φ t s) -> (entailsF ψ t s)
    | CAX   φ   => fun t s =>  forall t' s', ktrans (t,s) (t',s') -> entailsF φ t' s'
    | CEX   φ   => fun t s =>  exists t' s', ktrans (t,s) (t',s') /\ entailsF φ t' s'
    | CAU   φ ψ => cau (entailsF φ) (entailsF ψ)
    | CEU   φ ψ => ceu (entailsF φ) (entailsF ψ)
    | CAR   φ ψ  => gfp (car (entailsF φ) (entailsF ψ))
    | CER   φ ψ  => gfp (cer (entailsF φ) (entailsF ψ))
    end.

End Ctl.

Module CtlNotations.

  Declare Custom Entry ctl.
  Declare Scope ctl_scope.
  Delimit Scope ctl_scope with ctl.
  
  Section SC.
    Context {E C: Type -> Type} {X S: Type}.
    Notation SP := (ctree E C X -> S -> Prop).
    Definition ctl_of_Prop (P : Prop) : @CtlFormula X S := CNowS (fun (_: S) => P).
    Coercion ctl_of_Prop : Sortclass >-> CtlFormula. 
  End SC.
  
  Notation "<( e )>" := e (at level 0, e custom ctl at level 95) : ctl_scope.
  Notation "( x )" := x (in custom ctl, x at level 99) : ctl_scope.
  Notation "{ x }" := x (in custom ctl at level 0, x constr): ctl_scope.
  Notation "x" := x (in custom ctl at level 0, x constr at level 0) : ctl_scope.
  Notation "t , s |= φ " := (entailsF φ t s) (in custom ctl at level 80,
                                                 φ custom ctl,
                                                 right associativity): ctl_scope.

  Notation "|- φ " := (entailsF φ) (in custom ctl at level 80,
                                       φ custom ctl, only parsing): ctl_scope.

  (* Temporal *)
  Notation "'now' p" := (CNowS p) (in custom ctl at level 79): ctl_scope.
  Notation "'ret' p" := (CNowR p) (in custom ctl at level 79): ctl_scope.
  Notation "'EX' p" := (CEX p) (in custom ctl at level 75): ctl_scope.
  Notation "'AX' p" := (CAX p) (in custom ctl at level 75): ctl_scope.
  Notation "'EF' p" := (CEU True p) (in custom ctl at level 74): ctl_scope.
  Notation "'AF' p" := (CAU True p) (in custom ctl at level 74): ctl_scope.
  Notation "'EG' p" := (CER False p) (in custom ctl at level 74): ctl_scope.
  Notation "'AG' p" := (CAR False p) (in custom ctl at level 74): ctl_scope.
  Notation "p 'EU' q" := (CEU p q) (in custom ctl at level 75): ctl_scope.
  Notation "p 'AU' q" := (CAU p q) (in custom ctl at level 75): ctl_scope.
  Notation "p 'ER' q" := (CER p q) (in custom ctl at level 75): ctl_scope.
  Notation "p 'AR' q" := (CAR p q) (in custom ctl at level 75): ctl_scope.

  (* Propositional *)
  Notation "p '/\' q" := (CAnd p q) (in custom ctl at level 77, left associativity): ctl_scope.
  Notation "p '\/' q" := (COr p q) (in custom ctl at level 77, left associativity): ctl_scope.
  Notation "p '->' q" := (CImpl p q) (in custom ctl at level 78, right associativity): ctl_scope.
  Notation "p '<->' q" := (CAnd (CImpl p q) (CImpl q p)) (in custom ctl at level 77): ctl_scope.

  (* Companion notations *)
  Notation cart p q := (t (car p q)).
  Notation carbt p q := (bt (car p q)).
  Notation cert p q := (t (cer p q)).
  Notation cerbt p q := (bt (cer p q)).
  Notation carT p q := (T (car p q)).
  Notation cerT p q := (T (cer p q)).
  Notation carbT p q := (bT (car p q)).
  Notation cerbT p q := (bT (cer p q)).

  (* TODO: Think proof lemmas so these don't escape to the user? *)
  Notation "p [ 'AR' ] q" := (car p q _) (in custom ctl at level 75,
                                             p custom ctl, q custom ctl): ctl_scope.
  Notation "p [ 'ER' ] q" := (cer p q _) (in custom ctl at level 75,
                                             p custom ctl, q custom ctl): ctl_scope.
  
  Notation "p [[ 'AR' ]] q" := (car.(body) p q _) (in custom ctl at level 75,
                                                      p custom ctl, q custom ctl): ctl_scope.
  Notation "p [[ 'ER' ]] q" := (cer.(body) p q _) (in custom ctl at level 75,
                                                      p custom ctl, q custom ctl): ctl_scope.
  
  Notation "p { 'AR' } q" := (cart p q _) (in custom ctl at level 75,
                                              p custom ctl, q custom ctl): ctl_scope.
  Notation "p { 'ER' } q" := (cert p q _) (in custom ctl at level 75,
                                              p custom ctl, q custom ctl): ctl_scope.
  
  Notation "p {{ 'AR' }} q" := (carbt p q _) (in custom ctl at level 75,
                                                 p custom ctl, q custom ctl): ctl_scope.
  Notation "p {{ 'ER' }} q" := (cerbt p q _) (in custom ctl at level 75,
                                                 p custom ctl, q custom ctl): ctl_scope.

  #[global] Hint Constructors ceu cau: core.
  Arguments entailsF: simpl never.
End CtlNotations.

(* Properness lemmas/ Up-to proofs *)
Tactic Notation "step_entails" :=
  match goal with
  | |- context[@entailsF ?E ?C ?X ?Σ ?h ?HasStuck] =>
      progress (unfold entailsF; cbn; fold (@entailsF E C X Σ h HasStuck))
  end.
Tactic Notation "step_entails" "in" ident(H) :=
  match type of H with
  | context[@entailsF ?E ?C ?X ?Σ ?h ?HasStuck] =>
      progress (unfold entailsF in H; cbn in H; fold (@entailsF E C X Σ h HasStuck) in H)
  end.

(* these acrobatics are because Ltac does not make it easy to match a [fix] *)
Tactic Notation "fold_entails" :=
  match goal with
  | |- ?F ?φ ?t ?s => 
      match type of F with
      | (@CtlFormula ?X ?Σ) -> (ctree ?E ?C ?X) -> ?Σ -> Prop =>
          is_fix F; progress fold (@entailsF E C X Σ _ _ φ t s)
      end
  end.

Tactic Notation "fold_entails" "in" ident(H) :=
  match type of H with
  | ?F ?φ ?t ?s => 
      match type of F with
      | (@CtlFormula ?X ?Σ) -> (ctree ?E ?C ?X) -> ?Σ -> Prop =>
          is_fix F; progress fold (@entailsF E C X Σ _ _ φ t s) in H
      end
  end.

(*| Equations of CTL |*)
Section Equivalences.
  Import CtlNotations.
  Local Open Scope ctl_scope.
  Context {E C: Type -> Type} {X Σ: Type} `{h: E ~~> state Σ} `{HasStuck: B0 -< C}.

  (* SP is proper setoid *)
  Program Instance SpSetoid: Setoid CtlFormula :=
    {| equiv := fun P Q => forall (t: ctree E C X) (s:Σ),
                    <( t, s |= P )> <-> <( t, s |= Q )> |}.
  Next Obligation.
    split.
    - intros P x; reflexivity.
    - intros P Q H' x s; symmetry; auto.
    - intros P Q R H0' H1' x s; etransitivity; auto.
  Qed.

  #[global] Instance proper_equiv_equiv:
    Proper (SpSetoid.(equiv) ==> SpSetoid.(equiv) ==> iff) SpSetoid.(equiv).
  Proof.
    do 3 red; split; intros; do 2 red in H, H0, H1; do 2 red; split; intros.
    - now rewrite <- H0, <- H1, H. 
    - now rewrite <- H, H1, H0.
    - now rewrite H0, <- H1, <- H.
    - now rewrite H, H1, <- H0.
  Qed.
  
  (*| Top is True |*)
  Lemma ctl_top: forall (t: ctree E C X) (s: Σ),
    <( t, s |= True )>.
  Proof. reflexivity. Qed.    

  (*| Bot is False |*)
  Lemma ctl_bot: forall (t: ctree E C X) (s: Σ),
    ~ <(t, s |= False)>.
   Proof.
    intros * CONTRA; apply CONTRA.
  Qed.

  (*| Ex-falso |*)
  Lemma ctl_ex_falso: forall (t: ctree E C X) (s: Σ) p,
      <( t,s |= False -> p )>.
  Proof.
    intros; unfold entailsF; intro CONTRA; contradiction.
  Qed.

  Lemma ctl_au_ax: forall p q,
      <( p AU q )> == <( q \/ (p /\ AX (p AU q)) )>.
  Proof.
    split; intros.
    - inv H; [now left | now right].
    - destruct H; [now apply MatchA | now apply StepA].
  Qed.

  Lemma ctl_eu_ex: forall p q,
      <( p EU q )> == <( q \/ (p /\ EX (p EU q)) )>.
  Proof.
    split; cbn; intros.
    - inv H; [now left | now right].
    - inv H; [now apply MatchE | now apply StepE].
  Qed.
  
  Lemma ctl_af_ax: forall p,
      <( AF p )> == <( p \/ AX (AF p) )>.
  Proof.
    split; intros; inv H.
    1,3 : now left.
    all: now right. 
  Qed.

  Lemma ctl_ef_ex: forall p,
      <( EF p )> == <( p \/ EX (EF p) )>.
  Proof.
    split; intros; inv H.
    1,3: now left.
    all: now right.
  Qed.

   Lemma ctl_ar_ax: forall p q,
      <( p AR q )> == <( q /\ (p \/ AX (p AR q)) )>.
   Proof. 
     split; intros.
     - split; step in H; inv H; auto.
     - step_entails.
       destruct H  as (? & [? | ?]).
       + step; now apply RMatchA.
       + step; apply RStepA; auto.
  Qed.

   Lemma ctl_er_ex: forall p q,
      <( p ER q )> == <( q /\ (p \/ EX (p ER q)) )>.
   Proof. 
     split; intros.
     - split; step in H; inv H; auto.
     - step_entails.
       destruct H  as (? & [? | ?]).
       + step; now apply RMatchE.
       + step; apply RStepE; auto.
  Qed.

   Lemma ctl_ag_ax: forall p,
       <( AG p )> == <( p /\ AX (AG p) )>.
   Proof. 
     split; intros.
     - split; step in H; now inv H.
     - destruct H; step; now apply RStepA.
   Qed.

  Lemma ctl_eg_ex: forall p,
      <( EG p )> == <( p /\ EX (EG p) )>.
  Proof. 
    split; intros.
    - split; step in H; now inv H.
    - destruct H as (? & ? & ? & ? & ?); step; apply RStepE; eauto.
  Qed.
  
  (** Inductive lemmas for AU, EU *)
  Lemma AU_ind' :
    forall [φ ψ: CtlFormula] (P : ctree E C X -> Σ -> Prop),
      (forall t s, <(t, s |= ψ)> -> P t s) -> (* base *)
      (forall (t: ctree E C X) (s : Σ),
         <(t, s |= φ )> ->          (* φ now*)
         (forall t' s', ktrans (t,s) (t',s') -> <(t',s' |= φ AU ψ)>) ->
         (forall t' s', ktrans (t,s) (t',s') -> P t' s') ->
         P t s) ->
      forall t s, <( t, s |= φ AU ψ )> -> P t s.
  Proof.
    intros φ ψ P Hbase Hstep.
    refine (fix F (t : ctree E C X)(s: Σ) (H : <( t, s |= φ AU ψ)>) : P t s := _).
    remember (entailsF φ) as p.
    remember (entailsF ψ) as q.
    step_entails in H.
    dependent destruction H; subst.
    - now apply Hbase.
    - apply Hstep; auto.
      intros.
      specialize (H0 _ _ H1).
      apply F.
      now step_entails.
  Qed.  

  Lemma AF_ind' :
    forall [φ: CtlFormula] (P : ctree E C X -> Σ -> Prop),
      (forall t s, <(t, s |= φ)> -> P t s) -> (* base *)
      (forall (t: ctree E C X) (s : Σ),
          (forall t' s', ktrans (t,s) (t',s') -> <(t',s' |= AF φ)>) ->
          (forall t' s', ktrans (t,s) (t',s') -> P t' s') ->
          P t s) ->
      forall t s, <( t, s |= AF φ )> -> P t s.
  Proof.
    intros φ ψ P Hbase Hstep.
    eapply AU_ind'; eauto.
  Qed.

  Lemma EU_ind' :
    forall [φ ψ: CtlFormula] (P : ctree E C X -> Σ -> Prop),
      (forall t s, <(t, s |= ψ)> -> P t s) -> (* base *)
      (forall (t: ctree E C X) (s : Σ),
          <(t, s |= φ )> ->          (* φ now*)
          (exists t' s', ktrans (t,s) (t',s') /\ <(t',s' |= φ EU ψ)>) ->
          (exists t' s', ktrans (t,s) (t',s') /\ P t' s') ->
         P t s) ->
      forall t s, <( t, s |= φ EU ψ )> -> P t s.
  Proof.
    intros φ ψ P Hbase Hstep.
    refine (fix F (t : ctree E C X)(s: Σ) (H : <( t, s |= φ EU ψ)>) : P t s := _).
    remember (entailsF φ) as p.
    remember (entailsF ψ) as q.
    step_entails in H.
    dependent destruction H; subst.
    - now apply Hbase.
    - apply Hstep; auto.
      destruct H0 as (t' & s' & TR & ?).
      exists t', s'; split; auto.
  Qed.

  Lemma EF_ind' :
    forall [φ: CtlFormula] (P : ctree E C X -> Σ -> Prop),
      (forall t s, <(t, s |= φ)> -> P t s) -> (* base *)
      (forall (t: ctree E C X) (s : Σ),
          (exists t' s', ktrans (t,s) (t',s') /\ <(t',s' |= EF φ)>) ->
          (exists t' s', ktrans (t,s) (t',s') /\ P t' s') ->
          P t s) ->
      forall t s, <( t, s |= EF φ )> -> P t s.
  Proof.
    intros φ ψ P Hbase Hstep.
    eapply EU_ind'; eauto.
  Qed.  
  
  (*| [now] ignores trees and only looks at labels |*)
  #[global] Instance proper_now: forall (p: Σ -> Prop),
      Proper (@equ E C X X eq ==> eq ==> iff) <( |- now p )>.
  Proof.
    unfold Proper, respectful, impl; cbn.      
    intros p x y EQ ? l <-; split; auto.
  Qed.

  #[global] Instance proper_ret: forall (p: X -> Σ -> Prop),
      Proper (@equ E C X X eq ==> eq ==> iff) (entailsF (CNowR p)).
  Proof.
    unfold Proper, respectful, impl; cbn.
    intros; split; subst; intro; unfold entailsF in *;
      destruct H0 as (v & ? & ?); exists v; split; auto; now rewrite <- H0.
  Qed.
  
  (*| Up-to-sbisim enhancing function |*)
  Variant unary_sbisim_clos_body (R: rel (ctree E C X) Σ) : rel (ctree E C X) Σ :=
    | uSbisim_clos : forall t t' s s'
                  (Agt : t ~ t')
                  (HR : R t' s')
                  (Agu : s' = s),
        unary_sbisim_clos_body R t s.

  Program Definition unary_sbisim_clos: mon (rel (ctree E C X) Σ) :=
    {| body := unary_sbisim_clos_body |}.
  Next Obligation. destruct H0; econstructor; eauto. Qed.

  (** Rewrite [t ~ u] in a CTL context t,s |= p <-> u,s |= p] *)
  Section gProperSbisim.
    Context {P Q: rel (ctree E C X) Σ}
            {PrP: Proper (@sbisim E E C C X X _ _ eq ==> eq ==> iff) P}
            {PrQ: Proper (@sbisim E E C C X X _ _ eq ==> eq ==> iff) Q}.
    
    Lemma sbisim_clos_car:
      unary_sbisim_clos <= cart P Q.
    Proof.    
      apply Coinduction; cbn.
      intros R t0 s0 [t1 t2 s1 s2 EQt HH]; inv HH.
      - now apply RMatchA; rewrite EQt. 
      - apply RStepA; [now rewrite EQt|].
        intros t' s' Fwd.
        eapply (f_Tf (car P Q)).
        destruct (ktrans_sbisim_l Fwd EQt) as (? & ? & ?); eauto.        
        econstructor.
        + apply H2.
        + apply H0; eassumption.
        + reflexivity.
    Qed.

    Lemma sbisim_clos_cer:
      unary_sbisim_clos <= cert P Q.
    Proof.    
      apply Coinduction; cbn.
      intros R t0 s0 [t1 t2 s1 s2 EQt HH]; inv HH.
      - now apply RMatchE; rewrite EQt. 
      - destruct H0 as (t2' & s2' & TR2 & ?).
        symmetry in EQt.
        destruct (ktrans_sbisim_l TR2 EQt) as (t1' & TR1' & EQt1'); eauto.
        apply RStepE.
        + now rewrite <- EQt.
        + exists t1', s2'; intuition.
          eapply (f_Tf (cer P Q)).
          symmetry in EQt1'.
          econstructor; eauto.
    Qed.

    #[global] Instance proper_ewt_sbisim RR:
      Proper (sbisim eq ==> eq ==> iff) (cert P Q RR).
    Proof.
      unfold Proper, respectful, impl; cbn.
      intros x y EQ ? l <-; split; intro G; apply (ft_t sbisim_clos_cer); econstructor;
        [symmetry | apply G | reflexivity | | apply G | reflexivity]; assumption.
    Qed.

    #[global] Instance proper_ewT_sbisim RR f:
      Proper (sbisim eq ==> eq ==> iff) (cerT P Q f RR).
    Proof.
      unfold Proper, respectful, impl; cbn.
      intros x y EQ ? l <-; split; intro G; apply (fT_T sbisim_clos_cer); econstructor;
        [symmetry | apply G | reflexivity | | apply G | reflexivity]; assumption.
    Qed.
        
    #[global] Instance proper_awt_sbisim RR:
      Proper (sbisim eq ==> eq ==> iff) (cart P Q RR).
    Proof.
      unfold Proper, respectful, impl; cbn.
      intros x y EQ ? l <-; split; intro G; apply (ft_t sbisim_clos_car); econstructor;
        [symmetry | apply G | reflexivity | | apply G | reflexivity]; assumption.
    Qed.

    #[global] Instance proper_awT_sbisim RR f:
      Proper (sbisim eq ==> eq ==> iff) (carT P Q f RR).
    Proof.
      unfold Proper, respectful, impl; cbn.
      intros x y EQ ? l <-; split; intro G; apply (fT_T sbisim_clos_car); econstructor;
        [symmetry | apply G | reflexivity | | apply G | reflexivity]; assumption.
    Qed.

    #[global] Instance proper_cer_sbisim:
      Proper (sbisim eq ==> eq ==> iff) (gfp (cer P Q)).
    Proof.
      unfold Proper, respectful, impl; cbn.
      intros x y EQ ? l <-; split; intro G; apply (ft_t sbisim_clos_cer); econstructor;
        [symmetry | apply G | reflexivity | | apply G | reflexivity]; assumption.
    Qed.

    #[global] Instance proper_car_sbisim:
      Proper (sbisim eq ==> eq ==> iff) (gfp (car P Q)).
    Proof.
      unfold Proper, respectful, impl; cbn.
      intros x y EQ ? l <-; split; intro G; apply (ft_t sbisim_clos_car); econstructor;
        [symmetry | apply G | reflexivity | | apply G | reflexivity]; assumption.
    Qed.

  End gProperSbisim.

    (*| Up-to-eq enhancing function |*)
  Variant unary_equ_clos_body (R : rel (ctree E C X) Σ) : rel (ctree E C X) Σ :=
    | uEqu_clos : forall t t' s s'
                  (Agt : t ≅ t')
                  (HR : R t' s')
                  (Agu : s' = s),
        unary_equ_clos_body R t s.

  Program Definition unary_equ_clos: mon (rel (ctree E C X) Σ) :=
    {| body := unary_equ_clos_body |}.
  Next Obligation. destruct H0; econstructor; eauto. Qed.

  (*| Rewrite [t ≅ u] in a CTL context t,s |= p <-> u,s |= p] |*)
  Section gProperEqu.
    Context {P Q: rel (ctree E C X) Σ}
            {PrP: Proper (@equ E C X X eq ==> eq ==> iff) P}
            {PrQ: Proper (@equ E C X X eq ==> eq ==> iff) Q}.    
    Lemma equ_clos_car:
      unary_equ_clos <= cart P Q.
    Proof.    
      apply Coinduction; cbn.
      intros R t0 s0 [t1 t2 s1 s2 EQt HH]; inv HH.
      - apply RMatchA; now rewrite EQt. 
      - apply RStepA; intros.
        + now rewrite EQt.
        + eapply (f_Tf (car P Q)).
          econstructor; eauto.
          apply H0.
          now rewrite <- EQt.
    Qed.

    Lemma equ_clos_cer:
      unary_equ_clos <= cert P Q.
    Proof.    
      apply Coinduction; cbn.
      intros R t0 s0 [t1 t2 s1 s2 EQt HH]; inv HH. 
      - apply RMatchE; now rewrite EQt. 
      - destruct H0 as (u & x & TR2 & ?).
        apply RStepE.
        + now rewrite EQt.
        + exists u, x; intuition.
          now rewrite EQt.
          eapply (f_Tf (cer P Q)).
          econstructor; eauto. 
    Qed.

    #[global] Instance proper_cart_equ RR:
      Proper (@equ E C X X eq ==> eq ==> iff) (cart P Q RR).
    Proof.
      unfold Proper, respectful, impl; cbn.
      intros x y EQ ? l <-; split; intro G; apply (ft_t equ_clos_car); econstructor;
        [symmetry | apply G | reflexivity | | apply G | reflexivity]; assumption.
    Qed.

    #[global] Instance proper_carT_equ RR f:
      Proper (@equ E C X X eq ==> eq ==> iff) (carT P Q f RR).
    Proof.
      unfold Proper, respectful, impl; cbn.
      intros x y EQ ? l <-; split; intro G; apply (fT_T equ_clos_car); econstructor;
        [symmetry | apply G | reflexivity | | apply G | reflexivity]; assumption.
    Qed.
    
    #[global] Instance proper_cert_equ RR:
      Proper (@equ E C X X eq ==> eq ==> iff) (cert P Q RR).
    Proof.
      unfold Proper, respectful, impl; cbn.
      intros x y EQ ? l <-; split; intro G; apply (ft_t equ_clos_cer); econstructor;
        [symmetry | apply G | reflexivity | | apply G | reflexivity]; assumption.
    Qed.

    #[global] Instance proper_cerT_equ RR f:
      Proper (@equ E C X X eq ==> eq ==> iff) (cerT P Q f RR).
    Proof.
      unfold Proper, respectful, impl; cbn.
      intros x y EQ ? l <-; split; intro G; apply (fT_T equ_clos_cer); econstructor;
        [symmetry | apply G | reflexivity | | apply G | reflexivity]; assumption.
    Qed.

    #[global] Instance proper_cer_equ:
      Proper (@equ E C X X eq ==> eq ==> iff) (gfp (cer P Q)).
    Proof.
      unfold Proper, respectful, impl; cbn.
      intros x y EQ ? l <-; split; intro G; apply (ft_t equ_clos_cer); econstructor;
        [symmetry | apply G | reflexivity | | apply G | reflexivity]; assumption.
    Qed.

    #[global] Instance proper_car_equ:
      Proper (@equ E C X X eq ==> eq ==> iff) (gfp (car P Q)).
    Proof.
      unfold Proper, respectful, impl; cbn.
      intros x y EQ ? l <-; split; intro G; apply (ft_t equ_clos_car); econstructor;
        [symmetry | apply G | reflexivity | | apply G | reflexivity]; assumption.
    Qed.

    #[global] Instance proper_cau_equ:
      Proper (@equ E C X X eq ==> eq ==> iff) (cau P Q).
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

    #[global] Instance proper_ceu_equ:
      Proper (@equ E C X X eq ==> eq ==> iff) (ceu P Q).
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
    
  End gProperEqu.
  
  (*| Combined Properness lemma without the properness requirements, by induction on formulas |*)
  #[global] Instance proper_equiv_equ:
    Proper (equiv ==> equ eq ==> eq ==> iff) (@entailsF E C X Σ h HasStuck).
  Proof.
    do 4 red; intro x; induction x; intros y Hy t u EQt s s' <-; rewrite <- (Hy u s); clear Hy; step_entails; auto;
    try (specialize (IHx1 x1 (setoid_refl _ x1));        
         replace (forall x y : ctree E C X, x ≅ y -> forall x0 y0 : Σ, x0 = y0 -> <( x, x0 |= x1 )> <-> <( y, y0 |= x1 )>) with
           (Proper (equ eq ==> eq ==> iff) (@entailsF E C X Σ h HasStuck x1)) in IHx1 by reflexivity);
    try (specialize (IHx2 x2 (setoid_refl _ x2));        
         replace (forall x y : ctree E C X, x ≅ y -> forall x0 y0 : Σ, x0 = y0 -> <( x, x0 |= x2 )> <-> <( y, y0 |= x2 )>) with
           (Proper (equ eq ==> eq ==> iff) (@entailsF E C X Σ h HasStuck x2)) in IHx2 by reflexivity).
    - (* ret *)
      split; intros (? & ? & ?); eauto. 
      + exists x; rewrite EQt in H; intuition.
      + exists x; rewrite EQt; intuition.
    - (* /\ *)
      split; intros (? & ?); split.
      + now rewrite <- EQt. 
      + now rewrite <- EQt. 
      + now rewrite EQt. 
      + now rewrite EQt. 
    - (* \/ *)
      split; intros [? | ?].
      + now left; rewrite <- EQt. 
      + now right; rewrite <- EQt. 
      + now left; rewrite EQt. 
      + now right; rewrite EQt. 
    - (* -> *)
      split; intros.
      + rewrite <- EQt; rewrite <- EQt in H0; auto.
      + rewrite EQt; rewrite EQt in H0; auto.
    - (* ax *)
      split; intros.
      + now rewrite <- EQt in H0; apply H in H0.
      + now rewrite EQt in H0; apply H in H0.
    - (* ex *)
      split; intros (t' & x' & ? & ?); do 2 eexists; split; eauto.
      + now rewrite <- EQt.
      + now rewrite EQt.
    - (* au *)
      now rewrite EQt.
    - (* eu *)
      now rewrite EQt.
    - (* aw *)
      now rewrite EQt.
    - (* ew *)
      now rewrite EQt.
  Qed.

  (* TODO: This one needs some effort to prove *)
  #[global] Instance proper_equiv_sbisim:
    Proper (equiv ==> sbisim eq ==> eq ==> iff) (@entailsF E C X Σ h HasStuck).
  Admitted.
   
  (*| Up-to-bind ag |*)
  Definition bind_clos {Y}
             (R: rel (ctree E C X) Σ)
             (Rk: (X -> ctree E C Y) -> Prop):
      rel (ctree E C Y) Σ :=
      sup_all (fun t => sup (R t)
                         (fun s' => sup Rk
                                     (fun k => pairH (CTree.bind t k) s'))).
  
    (*| Specialization of [bind_ctx] to a function acting with [equ] on the bound value,
        and with the argument (pointwise) on the continuation. |*)
    Program Definition bind_clos_ag Y p q: mon (rel (ctree E C Y) Σ) :=
      {| body := fun R => bind_clos (gfp (car p q)) (fun k => forall x s, R (k x) s) |}.
    Next Obligation.
      (* TODO *)
      (* unfold bind_clos.
      apply leq_bind_ctx. intros ?? H' ?? H''.
      apply in_bind_ctx. apply H'. intros t t' HS. apply H0, H'', HS. *)
    Admitted.
End Equivalences.

(*| Ltac Tactics |*)
#[local] Ltac __step_formula E C X S h HasStuck φ :=
  lazymatch φ with
  | context[CAU ?p ?q] => lazymatch eval cbv in p with
                         | CNowS (fun _ => True) => rewrite (@ctl_af_ax E C X S h HasStuck)
                         | _ => rewrite (@ctl_au_ax E C X S h HasStuck)
                         end
  | context[CEU ?p ?q] => lazymatch eval cbv in p with
                         | CNowS (fun _ => True) => rewrite (@ctl_ef_ex E C X S h HasStuck)
                         | _ => rewrite (@ctl_eu_ex E C X S h HasStuck)
                         end
  | context[CAR ?p ?q] => lazymatch eval cbv in p with
                         | CNowS (fun _ => False) => rewrite (@ctl_ag_ax E C X S h HasStuck)
                         | _ => rewrite (@ctl_ar_ax E C X S h HasStuck)
                         end
  | context[CER ?p ?q] => lazymatch eval cbv in p with
                         | CNowS (fun _ => False) => rewrite (@ctl_eg_ex E C X S h HasStuck)
                         | _ => rewrite (@ctl_er_ex E C X S h HasStuck)
                         end
  | CAX ?p => step_entails;
             let t_ := fresh "t" in
             let s_ := fresh "s" in
             let TR_ := fresh "TR" in
             intros t_ s_ TR_
  | CEX ?p => step_entails
  | ?ptrivial => lazymatch eval compute in ptrivial with
                | CNowS ?f => step_entails
                | _ => fail "Cannot step formula " φ
                end
  end.

#[local] Ltac __step_formula_in H E C X S h HasStuck φ :=
  lazymatch φ with
  | context[CAU ?p ?q] => lazymatch eval cbv in p with
                         | CNowS (fun _ => True) => rewrite (@ctl_af_ax E C X S h HasStuck) in H
                         | _ => rewrite (@ctl_au_ax E C X S h HasStuck) in H
                         end
  | context[CEU ?p ?q] => lazymatch eval cbv in p with
                         | CNowS (fun _ => True) => rewrite (@ctl_ef_ex E C X S h HasStuck) in H
                         | _ => rewrite (@ctl_eu_ex E C X S h HasStuck) in H
                         end
  | context[CAR ?p ?q] => lazymatch eval cbv in p with
                         | CNowS (fun _ => False) => rewrite (@ctl_ag_ax E C X S h HasStuck) in H
                         | _ => rewrite (@ctl_ar_ax E C X S h HasStuck) in H
                         end
  | context[CER ?p ?q] => lazymatch eval cbv in p with
                         | CNowS (fun _ => False) => rewrite (@ctl_eg_ex E C X S h HasStuck) in H
                         | _ => rewrite (@ctl_er_ex E C X S h HasStuck) in H
                         end
  | CAX ?p => step_entails in H
  | CEX ?p =>
      let t_ := fresh "t" in
      let s_ := fresh "s" in
      let TR_ := fresh "TR" in
      let NOW_ := fresh "Hnow" in
      destruct H as (t_ & s_ & TR_ & NOW_);
      fold (@entailsF E C X S h HasStuck) in NOW_
  | ?ptrivial => lazymatch eval compute in ptrivial with
                | CNowS ?f => step_entails in H
                | _ => fail "Cannot step formula " φ " in " H
                end
  end.

#[local] Ltac __coinduction_g R H :=
  step_entails; coinduction R H.

(** Re-export [Eq.v] tactics *)
#[global] Tactic Notation "step" :=
  lazymatch goal with
  | |- context[@entailsF ?E ?C ?X ?S ?h ?HasStuck ?p ?t ?s] =>
      __step_formula E C X S h HasStuck p
  end || step.

#[global] Tactic Notation "coinduction" simple_intropattern(R) simple_intropattern(H) :=
  __coinduction_g R H || coinduction R H.

#[global] Tactic Notation "step" "in" ident(H) :=
  lazymatch type of H with
  | context[@entailsF ?E ?C ?X ?S ?h ?HasStuck ?p ?s ?t] =>
      __step_formula_in H E C X S h HasStuck p
  end || step_in H.

Section UsefulLemmas.
  Import CtlNotations CTreeNotations.
  Local Open Scope ctl_scope.
  
  Lemma ctl_ret_au_inv {E C X Σ} `{h: E ~~> state Σ}
        `{HasStuck: B0 -< C} : forall x s (p q: Σ -> Prop),
      <( {Ret x: ctree E C X}, s |= (now p) AU (now q)  )> -> p s \/ q s.
  Proof.
    intros; inv H; [now right | now left].
  Qed.

  Lemma ctl_bind_au_inv{E C X Σ Y} `{h: E ~~> state Σ} `{HasStuck: B0 -< C} : forall (φ ψ: Σ -> Prop) (t: ctree E C Y) (s: Σ) (k: Y -> ctree E C X),
      <( {x <- t ;; k x}, s |= (now φ) AU (now ψ) )> <->
      <( t,s |= (now φ) AU (ret {fun x s => <( {k x}, s |= (now φ) AU (now ψ) )>}) )> \/ 
        <( t,s |= (now φ) AU (now ψ) )>.
  Proof.
    intros.
    remember (CNowS φ).
    remember (CNowS ψ).
  Admitted.

  Lemma ctl_bind_ag_goal{E C X Σ Y} `{h: E ~~> state Σ} `{HasStuck: B0 -< C} : forall φ (t: ctree E C Y) (s: Σ) (k: Y -> ctree E C X),
      <( {x <- t ;; k x}, s |= AG (now φ) )> <->
      <( t,s |= (ret {fun x s => <( {k x}, s |= AG (now φ) )>}) AR (now φ) )>.
  Proof.
    intros.
    remember (CNowS φ).
  Admitted.

  Lemma ctl_forever_ag{E C X Σ} `{h: E ~~> state Σ} `{HasStuck: B0 -< C} `{HasTau: B1 -< C}: forall φ (t: ctree E C X) (s: Σ),
      <( {CTree.forever t: ctree E C void}, s |= AG (now φ) )> <->
      <( t,s |= (ret {fun _ s => φ s}) AR (now φ) )>. (* [t] can return -- as long as ϕ is satisfied *)
  Proof.
    intros.
    remember (CNowS φ).
    split.
    - intro H.
      rewrite unfold_forever in H.
  Admitted.

End UsefulLemmas.


Module Experiments.

  Import CTree CTreeNotations CtlNotations.
  Local Open Scope ctl_scope.
  Context {E C: Type -> Type} {S: Type} {HasStuck: B0 -< C}.
  Definition stuck: ctree E C unit := stuckD.
    
  Definition ctl_of_State {X}(s: nat): @CtlFormula X nat := CNowS (fun x => x = s).
  Arguments ctl_of_State /.
  Coercion ctl_of_State : nat >-> CtlFormula.

  Lemma writes_23: forall s,
      <( {put 2 ;; put 3 : ctree (stateE nat) B0 unit}, s |= AX 2 /\ (AX (AX 3)) )>.
  Proof.
    split; intros; fold_entails.
    - step.
      apply ktrans_trigger_inv in H as ([] & ? & ->).
      cbn; auto.
    - step.  
      apply ktrans_trigger_inv in H as ([] & ? & ->).
      rewrite H in *; clear H.
      apply ktrans_vis_inv in H0 as ([] & ? & ->).
      cbn; auto.
  Qed.      

  Lemma is_stuck_ax: forall (s: S) `{h: E ~~> state S},
      <( stuck, s |= (AX False) )>.
  Proof.
    intros.
    step.
    now apply ktrans_stuck_inv in TR.
  Qed.

  (* Terminating [ret x] programs *)
  Lemma maybebad: forall n,
      ~ <( {put 2: ctree (stateE nat) C unit}, n |= AX 3 )>.
  Proof.
    intros * CONTRA.
    step in CONTRA.
    assert (TR: @ktrans _ C _ _ _ _ (put 2, n) (Ret tt, 2)).
    eapply ktrans_vis_goal; intuition.
    apply CONTRA in TR.
    discriminate TR.
  Qed.

  Lemma maybegood: forall n,
      <( {put 2: ctree (stateE nat) C unit}, n |= AF 2 )>.
  Proof.
    intros.
    step; right; intros.
    apply MatchA; cbn.
    apply ktrans_vis_inv in H as ([] & ? & ->).
    reflexivity.
  Qed.

  Lemma maybegood': 
    <( {put 2: ctree (stateE nat) C unit}, 2 |= AG 2 )>.
  Proof.
    step.
    split; auto; cbn.
    intros.
    apply ktrans_vis_inv in H as ([] & ? & ->).
    (* Why this instance cannot be found ? *)
    pose proof (@proper_car_equ (stateE nat) C unit nat _ _ <( |- now {fun _ => False} )> <( |- now {fun s => s = 2} )> (proper_now _) (proper_now _)).
    rewrite H.
    coinduction R CIH.
    
    apply RStepA; auto; cbn in *.
    intros.
    apply ktrans_ret in H1 as (? & <-).
    pose proof (@proper_cart_equ (stateE nat) C unit nat _ _ <( |- now {fun _ => False} )> <( |- now {fun s => s = 2} )> (proper_now _) (proper_now _) R).
    rewrite H1.
    apply CIH.
    exact t'.
  Qed.

  Lemma maybegood'': 
    ~ <( {put 2: ctree (stateE nat) C unit}, 2 |= AG 3 )>.
  Proof.
    unfold not.
    intro CONTRA.
    step in CONTRA; inv CONTRA.
    inv H.
  Qed.

End Experiments.

