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

From RelationAlgebra Require Import
     monoid rel.

From ExtLib Require Import
     Data.Monads.StateMonad.

Set Implicit Arguments.

(*| CTL logic based on kripke semantics of ctrees |*)
Section Ctl.

  Context {E C: Type -> Type} {X S: Type}
          `{h: E ~~> state S} `{HasStuck: B0 -< C}.
  Notation SP := (ctree E C X -> S -> Prop).

  (* Forall strong until *)
  Inductive cau(p q: SP): SP :=
  | MatchA: forall t s,       
      q t s ->  (* Matches [q] now; done *)
      cau p q t s
  | StepA:  forall t s,
      p t s ->    (* Matches [p] now; steps to (t', s') *)
      (forall t' s', ktrans (t,s) (t',s') -> cau p q t' s') ->
      cau p q t s.

  (* Exists strong until *)
  Inductive ceu(p q: SP): SP :=
  | MatchE: forall t s,
      q t s ->       (* Matches [q] now; done *)
      ceu p q t s
  | StepE: forall t s,
      p t s ->    (* Matches [p] now; steps to (t', s') *)
      (exists t' s', ktrans (t,s) (t',s') /\ ceu p q t' s') ->
      ceu p q t s.

  (* Forall release *)
  Variant carF R (p q: SP): SP :=
  | RMatchA: forall t s,       
      q t s ->  (* Matches [q] now; done *)
      p t s ->  (* Matches [p] as well *)
      carF R p q t s
  | RStepA:  forall t s,
      p t s ->    (* Matches [p] now; steps to (t', s') *)
      (forall t' s', ktrans (t,s) (t',s') -> R t' s') ->
      carF R p q t s.
                          
  (* Exists release *)
  Variant cerF R (p q: SP): SP :=
  | RMatchE: forall t s,
      q t s ->       (* Matches [q] now; done *)
      p t s ->       (* Matches [p] as well *)
      cerF R p q t s
  | RStepE: forall t s,
      p t s ->    (* Matches [p] now; steps to (t', s') *)
      (exists t' s', ktrans (t,s) (t',s') /\ R t' s') ->
      cerF R p q t s.

  Hint Constructors cau ceu carF cerF: core.
  
  (*| Global (coinductives) |*)
  Program Definition car_ p q: mon SP :=
    {| body := fun R t s => carF R p q t s |}.
  Next Obligation. destruct H0; auto. Qed.
  
  Program Definition cer_ p q: mon SP :=
    {| body := fun R t s => cerF R p q t s |}.
  Next Obligation. destruct H0; [eauto | destruct H1 as (t' & s' & TR & ?)]; apply RStepE; eauto. Qed.
  
  Inductive CtlFormula: Type :=
  | CNowS (p : S -> Prop): CtlFormula
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
  Fixpoint entailsF (φ: CtlFormula)(t: ctree E C X)(s: S): Prop :=
    match φ with
    | CNowS p   => p s
    | CAnd  φ ψ => (entailsF φ t s) /\ (entailsF ψ t s)
    | COr   φ ψ => (entailsF φ t s) \/ (entailsF ψ t s)
    | CImpl φ ψ => (entailsF φ t s) -> (entailsF ψ t s)
    | CAX   φ   => forall t' s', ktrans (t,s) (t',s') -> entailsF φ t' s'
    | CEX   φ   => exists t' s', ktrans (t,s) (t',s') /\ entailsF φ t' s'
    | CAU   φ ψ => cau (entailsF φ) (entailsF ψ) t s
    | CEU   φ ψ => ceu (entailsF φ) (entailsF ψ) t s
    | CAR   φ ψ  => gfp (car_ (entailsF φ) (entailsF ψ)) t s
    | CER   φ ψ  => gfp (cer_ (entailsF φ) (entailsF ψ)) t s
    end.
  Arguments entailsF: simpl never.
End Ctl.

Module CtlNotations.

  Declare Custom Entry ctl.
  Declare Scope ctl_scope.
  Delimit Scope ctl_scope with ctl.
  
  Section SC.
    Context {E C: Type -> Type} {X S: Type}.
    Notation SP := (ctree E C X -> S -> Prop).
    Definition ctl_of_Prop (P : Prop) : @CtlFormula S := CNowS (fun (_: S) => P).
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
  Notation "'EX' p" := (CEX p) (in custom ctl at level 75): ctl_scope.
  Notation "'AX' p" := (CAX p) (in custom ctl at level 75): ctl_scope.

  Notation "p 'EU' q" := (CEU p q) (in custom ctl at level 75): ctl_scope.
  Notation "p 'AU' q" := (CAU p q) (in custom ctl at level 75): ctl_scope.
  Notation "p 'ER' q" := (CER p q) (in custom ctl at level 75): ctl_scope.
  Notation "p 'AR' q" := (CAR p q) (in custom ctl at level 75): ctl_scope.
  Notation "'EF' p" := (CEU (ctl_of_Prop True) p) (in custom ctl at level 74): ctl_scope.
  Notation "'AF' p" := (CAU (ctl_of_Prop True) p) (in custom ctl at level 74): ctl_scope.
  Notation "'EG' p" := (CER p (ctl_of_Prop False)) (in custom ctl at level 74): ctl_scope.
  Notation "'AG' p" := (CAR p (ctl_of_Prop False)) (in custom ctl at level 74): ctl_scope.
  
  (* Propositional *)
  Notation "p '/\' q" := (CAnd p q) (in custom ctl at level 77, left associativity): ctl_scope.
  Notation "p '\/' q" := (COr p q) (in custom ctl at level 77, left associativity): ctl_scope.
  Notation "p '->' q" := (CImpl p q) (in custom ctl at level 78, right associativity): ctl_scope.
  Notation " ¬ p" := (CImpl p (ctl_of_Prop False)) (in custom ctl at level 76): ctl_scope.
  Notation "p '<->' q" := (CAnd (CImpl p q) (CImpl q p)) (in custom ctl at level 77): ctl_scope.

  (* Companion notations *)
  Notation car p q := (gfp (car_ p q)).
  Notation cer p q := (gfp (cer_ p q)).
  Notation cart p q := (t (car_ p q)).
  Notation carbt p q := (bt (car_ p q)).
  Notation cert p q := (t (cer_ p q)).
  Notation cerbt p q := (bt (cer_ p q)).
  Notation carT p q := (T (car_ p q)).
  Notation cerT p q := (T (cer_ p q)).
  Notation carbT p q := (bT (car_ p q)).
  Notation cerbT p q := (bT (cer_ p q)).

  (* Shallow syntax. Think proof lemmas so these don't escape to the user? *)
  Notation "p 'ar' q" := (car p q) (in custom ctl at level 75,
                                             p custom ctl, q custom ctl): ctl_scope.
  Notation "p 'er' q" := (cer p q) (in custom ctl at level 75,
                                             p custom ctl, q custom ctl): ctl_scope.
  Notation "'ag' p" := (car p (fun _ _ => False)) (in custom ctl at level 74,
                                             p custom ctl): ctl_scope.
  Notation "'eg' p" := (cer p (fun _ _ => False)) (in custom ctl at level 74,
                                                     p custom ctl): ctl_scope.
  
  Notation "p [ 'ar' ] q" := (car_ p q _) (in custom ctl at level 75,
                                             p custom ctl, q custom ctl): ctl_scope.
  Notation "p [ 'er' ] q" := (cer_ p q _) (in custom ctl at level 75,
                                             p custom ctl, q custom ctl): ctl_scope.
  Notation "[ 'ag' ] p" := (car_ p (fun _ _ => False) _) (in custom ctl at level 74,
                                             p custom ctl): ctl_scope.
  Notation "[ 'eg' ] p" := (cer_ p (fun _ _ => False) _) (in custom ctl at level 74,
                                             p custom ctl): ctl_scope.
  
  Notation "p [[ 'ar' ]] q" := (car_.(body) p q _) (in custom ctl at level 75,
                                                      p custom ctl, q custom ctl): ctl_scope.
  Notation "p [[ 'er' ]] q" := (cer_.(body) p q _) (in custom ctl at level 75,
                                                      p custom ctl, q custom ctl): ctl_scope.
  Notation "[[ 'ag' ]] p" := (car_.(body) p (fun _ _ => False) _) (in custom ctl at level 74,
                                                      p custom ctl): ctl_scope.
  Notation "[[ 'eg' ]] p" := (cer_.(body) p (fun _ _ => False) _) (in custom ctl at level 74,
                                                      p custom ctl): ctl_scope.

  
  Notation "p { 'ar' } q" := (cart p q _) (in custom ctl at level 75,
                                              p custom ctl, q custom ctl): ctl_scope.
  Notation "p { 'er' } q" := (cert p q _) (in custom ctl at level 75,
                                              p custom ctl, q custom ctl): ctl_scope.
  Notation "{ 'ag' } p" := (cart p (fun _ _ => False) _) (in custom ctl at level 74,
                                              p custom ctl): ctl_scope.
  Notation "{ 'eg' } p" := (cert p (fun _ _ => False) _) (in custom ctl at level 74,
                                              p custom ctl): ctl_scope.
  
  Notation "p {{ 'ar' }} q" := (carbt p q _) (in custom ctl at level 75,
                                                 p custom ctl, q custom ctl): ctl_scope.
  Notation "p {{ 'er' }} q" := (cerbt p q _) (in custom ctl at level 75,
                                                 p custom ctl, q custom ctl): ctl_scope.
  Notation "{{ 'ag' }} p" := (carbt p (fun _ _ => False) _) (in custom ctl at level 74,
                                                         p custom ctl): ctl_scope.
  Notation "{{ 'eg' }} p" := (cerbt p (fun _ _ => False) _) (in custom ctl at level 74,
                                                         p custom ctl): ctl_scope.

  #[global] Hint Constructors ceu cau: core.
End CtlNotations.

(*| Equations of CTL |*)
Section Congruences.
  Import CtlNotations.
  Local Open Scope ctl_scope.
  Context {Σ : Type}.
  Definition sem_equiv: rel (@CtlFormula Σ) (@CtlFormula Σ) :=
    fun p q =>
      forall (E C: Type -> Type) (X: Type) (HasStuck: B0 -< C) (h: E ~~> state Σ) (t: ctree E C X) (s:Σ),
        <( t, s |= p )> <-> <( t, s |= q )>.
  
  Definition sem_equiv_refl: Reflexive sem_equiv.
  Proof.  intros P x; reflexivity. Qed.
  Definition sem_equiv_sym: Symmetric sem_equiv.
  Proof.  intros P Q H' x s; symmetry; auto. Qed.
  Definition sem_equiv_trans: Transitive sem_equiv.
  Proof.  intros P Q R H0' H1' x s; etransitivity; auto. Qed.

  Global Add Parametric Relation: CtlFormula sem_equiv
      reflexivity proved by sem_equiv_refl
      symmetry proved by sem_equiv_sym
      transitivity proved by sem_equiv_trans as sem_equiv_rel.

  Global Add Parametric Morphism : sem_equiv                                        
      with signature sem_equiv ==> sem_equiv ==> iff as sem_equiv_equiv.
  Proof.
    intros p q EQpq p' q' EQpq'; split;
      intros EQpp'; split; intro BASE; unfold sem_equiv in *.
    - now rewrite <- EQpq', <- EQpp', EQpq.
    - now rewrite <- EQpq, EQpp', EQpq'.
    - now rewrite EQpq', <- EQpp', <- EQpq.
    - now rewrite EQpq, EQpp', <- EQpq'.
  Qed.

  Global Add Parametric Morphism {E C X} `{h: E ~~> state Σ} `{HasStuck: B0 -< C} {φ: Σ -> Prop}:
    (fun (_: ctree E C X) s => φ s)
      with signature (@equ E C X X eq) ==> eq ==> iff as fun_proper_equ.
  Proof.
    intros; split; subst; intro; unfold entailsF in *; auto.
  Qed.

  Global Add Parametric Morphism {E C X} `{h: E ~~> state Σ} `{HasStuck: B0 -< C} {φ: X -> Σ -> Prop}:
    (fun (t: ctree E C X) s => exists x, t ≅ Ret x /\ φ x s)
      with signature (@equ E C X X eq) ==> eq ==> iff as fun_ret_proper_equ.
  Proof.
    intros; split; subst; intro; unfold entailsF in *;
      destruct H0 as (v & ? & ?); exists v; split; auto; now rewrite <- H0.
  Qed.

  Global Add Parametric Morphism {E C X} `{h: E ~~> state Σ} `{HasStuck: B0 -< C}(p: Σ -> Prop): <( |- now p )>                                        
      with signature (@equ E C X X eq) ==> eq ==> iff as now_proper_equ.
  Proof.
    unfold entailsF; intros; eapply fun_proper_equ; eauto.
  Qed.

  (** Rewrite [t ~ u] in a CTL context t,s |= p <-> u,s |= p] *)
  Section gProperSbisim.
    Context {E C: Type -> Type} {X:Type}
            {h: E ~~> state Σ} {HasStuck: B0 -< C}.
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
        eapply (f_Tf (car_ P Q)).
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
          eapply (f_Tf (cer_ P Q)).
          symmetry in EQt1'.
          econstructor; eauto.
    Qed.
    
    Global Add Parametric Morphism RR: (cert P Q RR)
        with signature (sbisim eq ==> eq ==> iff) as proper_ert_sbisim.
    Proof.    
      intros x y EQ l; split; intro G; apply (ft_t sbisim_clos_cer); econstructor;
        [symmetry | apply G | reflexivity | | apply G | reflexivity]; assumption.
    Qed.

    Global Add Parametric Morphism RR f: (cerT P Q f RR)
        with signature (sbisim eq ==> eq ==> iff) as proper_erT_sbisim.
    Proof.
      intros x y EQ l; split; intro G; apply (fT_T sbisim_clos_cer); econstructor;
        [symmetry | apply G | reflexivity | | apply G | reflexivity]; assumption.
    Qed. 

    Global Add Parametric Morphism: (cer P Q)
        with signature (sbisim eq ==> eq ==> iff) as proper_er_sbisim.
    Proof.
      intros x y EQ l; split; intro G; apply (ft_t sbisim_clos_cer); econstructor;
        [symmetry | apply G | reflexivity | | apply G | reflexivity]; assumption.
    Qed.

    Global Add Parametric Morphism RR: (cart P Q RR)
        with signature (sbisim eq ==> eq ==> iff) as proper_art_sbisim.
    Proof.
      intros x y EQ l; split; intro G; apply (ft_t sbisim_clos_car); econstructor;
        [symmetry | apply G | reflexivity | | apply G | reflexivity]; assumption.
    Qed.
    
    Global Add Parametric Morphism RR f: (carT P Q f RR)
        with signature (sbisim eq ==> eq ==> iff) as proper_arT_sbisim.
    Proof.
      intros x y EQ l; split; intro G; apply (fT_T sbisim_clos_car); econstructor;
        [symmetry | apply G | reflexivity | | apply G | reflexivity]; assumption.
    Qed.

    Global Add Parametric Morphism: (car P Q)
        with signature (sbisim eq ==> eq ==> iff) as proper_ar_sbisim.
    Proof.
      intros x y EQ l; split; intro G; apply (ft_t sbisim_clos_car); econstructor;
        [symmetry | apply G | reflexivity | | apply G | reflexivity]; assumption.
    Qed.

  End gProperSbisim.

  (** Rewrite [t ≅ u] in a CTL context t,s |= p <-> u,s |= p] *)
  Section gProperEqu.
    Context {E C: Type -> Type} {X: Type}
            {h: E ~~> state Σ} {HasStuck: B0 -< C}.
    
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
        + eapply (f_Tf (car_ P Q)).
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
          eapply (f_Tf (cer_ P Q)).
          econstructor; eauto. 
    Qed.

    Global Add Parametric Morphism RR: (cart P Q RR)
        with signature (equ eq ==> eq ==> iff) as proper_art_equ.
    Proof.
      intros x y EQ l; split; intro G; apply (ft_t equ_clos_car); econstructor;
        [symmetry | apply G | reflexivity | | apply G | reflexivity]; assumption.
    Qed.

    Global Add Parametric Morphism RR f: (carT P Q f RR)
        with signature (equ eq ==> eq ==> iff) as proper_arT_equ.
    Proof.
      intros x y EQ l; split; intro G; apply (fT_T equ_clos_car); econstructor;
        [symmetry | apply G | reflexivity | | apply G | reflexivity]; assumption.
    Qed.
    
    Global Add Parametric Morphism: (car P Q)
        with signature (equ eq ==> eq ==> iff) as proper_ar_equ.
    Proof.
      intros x y EQ l; split; intro G; apply (ft_t equ_clos_car); econstructor;
        [symmetry | apply G | reflexivity | | apply G | reflexivity]; assumption.
    Qed.

    Global Add Parametric Morphism RR: (cert P Q RR)
        with signature (equ eq ==> eq ==> iff) as proper_ert_equ.
    Proof.
      intros x y EQ l; split; intro G; apply (ft_t equ_clos_cer); econstructor;
        [symmetry | apply G | reflexivity | | apply G | reflexivity]; assumption.
    Qed.

    Global Add Parametric Morphism RR f: (cerT P Q f RR)
        with signature (equ eq ==> eq ==> iff) as proper_erT_equ.
    Proof.
      intros x y EQ l; split; intro G; apply (fT_T equ_clos_cer); econstructor;
        [symmetry | apply G | reflexivity | | apply G | reflexivity]; assumption.
    Qed.
    
    Global Add Parametric Morphism: (cer P Q)
        with signature (equ eq ==> eq ==> iff) as proper_er_equ.
    Proof.
      intros x y EQ l; split; intro G; apply (ft_t equ_clos_cer); econstructor;
        [symmetry | apply G | reflexivity | | apply G | reflexivity]; assumption.
    Qed.

    Global Add Parametric Morphism: (cau P Q)
        with signature (equ eq ==> eq ==> iff) as proper_au_equ.
    Proof.
      intros x y EQ l; split; intro au; induction au.
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

    Global Add Parametric Morphism: (ceu P Q)
        with signature (equ eq ==> eq ==> iff) as proper_eu_equ.
    Proof.
      unfold Proper, respectful, impl; cbn.
      intros x y EQ l; split; intro au; induction au.
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
  Global Add Parametric Morphism {E C X} {h: E ~~> state Σ} {HasStuck: B0 -< C}: (@entailsF E C X Σ h HasStuck)
        with signature (sem_equiv ==> equ eq ==> eq ==> iff) as proper_equiv_equ.
  Proof with eauto.
    intro x; induction x; intros y Hy t u EQt s; unfold sem_equiv in *;
      rewrite <- Hy; clear Hy; unfold entailsF; auto;
      try (specialize (IHx1 x1 (sem_equiv_refl x1));
           assert (HP: Proper (@equ E C X X eq ==> eq ==> iff) (entailsF x1)) by
             (do 3 red; intros; subst; apply IHx1; eauto));
      try ( specialize (IHx2 x2 (sem_equiv_refl x2));        
            assert (HP': Proper (@equ E C X X eq ==> eq ==> iff) (entailsF x2)) by
              (do 3 red; intros; subst; apply IHx2; eauto)).          
    - (* /\ *)
      split; intros (? & ?); split.
      + rewrite IHx1; symmetry in EQt...
      + rewrite IHx2; symmetry in EQt... 
      + rewrite IHx1... 
      + rewrite IHx2... 
    - (* \/ *)
      split; intros [? | ?].
      + left; rewrite IHx1; symmetry in EQt... 
      + right; rewrite IHx2; symmetry in EQt...
      + left; rewrite IHx1...
      + right; rewrite IHx2...
    - (* -> *)
      split; intros.
      + rewrite IHx2; [eapply H; rewrite IHx1| symmetry in EQt]; eauto.
      + rewrite IHx2; [eapply H; rewrite IHx1; symmetry in EQt|]; eauto.
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
    - (* ar *)
      now rewrite EQt. 
    - (* er *)
      now rewrite EQt.
  Qed.
  
  (* TODO: This one needs some effort to prove 
  Global Add Parametric Morphism {E C X} {h: E ~~> state Σ} {HasStuck: B0 -< C}: (@entailsF E C X Σ h HasStuck)
        with signature (sem_equiv ==> sbisim eq ==> eq ==> iff) as proper_equiv_sbisim.
  Proof.
  *)
  Section gProperBind.
    Context {E C: Type -> Type} {X Y: Type} {h: E ~~> state Σ} {HasStuck: B0 -< C}.
    (*| Up-to-bind ag |*)
    Definition bind_clos (R: rel (ctree E C X) Σ)
             (Rk: (X -> ctree E C Y) -> Prop):
      rel (ctree E C Y) Σ :=
      sup_all (fun t => sup (R t)
                         (fun s' => sup Rk
                                     (fun k => pairH (CTree.bind t k) s'))).
  
    (*| Specialization of [bind_ctx] to a function acting with [equ] on the bound value,
        and with the argument (pointwise) on the continuation. |*)
    Program Definition bind_clos_ag p q : mon (rel (ctree E C Y) Σ) :=
      {| body := fun R => bind_clos (car p q) (fun k => forall x s, R (k x) s) |}.
    Next Obligation.
      unfold bind_clos, sup_all, sup; cbn.
      eexists; auto.
      eexists.
      (* unfold bind_clos.
      apply leq_bind_ctx. intros ?? H' ?? H''.
      apply in_bind_ctx. apply H'. intros t t' HS. apply H0, H'', HS. *)
    Admitted.
  End gProperBind.
End Congruences.

Section transitive_closure_of_ktrans.
  Import CtlNotations.
  Local Open Scope ctl_scope.
  Context {E C: Type -> Type} {X S: Type} {HasStuck: B0 -< C} {h: E ~~> state S}.

  Notation TS := (@TS E C X S).
  Program Definition ktrans_inv (φ: CtlFormula): srel TS TS :=
    {| hrel_of '(t, s) '(t',s') := ktrans (t,s) (t',s') /\ <( t', s' |= φ )> |}. 
  Next Obligation.
    destruct H as (HA & HB);
      unfold RelCompFun in HA, HB; cbn in HA, HB.
    destruct H0 as (HA' & HB');
      unfold RelCompFun in HA', HB'; cbn in HA', HB'.
    subst; rewrite HA; rewrite HA'; intuition.
  Qed.

  Lemma ktrans_inv_true: forall (w w': ctree E C X * S),
    ktrans_inv True w w' <-> ktrans w w'.
  Proof.
    split; destruct w, w'.
    - now intros (? & ?).
    - intros; cbn in *; intuition.
  Qed.

  (* TODO: Make this proof more reasonable? *)
  Lemma ktrans_star_inv_true: forall (w w': ctree E C X * S),
      (ktrans_inv True)^* w w' <-> ktrans^* w w'.
  Proof.
    Opaque str.
    pose proof (@str_weq _ srel_monoid_ops (srel_monoid_laws) _ TS).
    unfold Proper, respectful, weq in H; cbn in H.
    exact (H (ktrans_inv True) (ktrans) ktrans_inv_true).
  Qed.

End transitive_closure_of_ktrans.


Notation "w '⇓{' φ '}' '(' x ',' s ')'" := ((ktrans_inv φ)^* w (Ret x, s)) (at level 50, φ custom ctl, left associativity).            
Infix "⩸" := (sem_equiv) (at level 40, left associativity).

Import CtlNotations.
Local Open Scope ctl_scope.

Ltac csplit :=
  match goal with
  | |- <( ?t, ?s |= ?φ /\ ?ψ )> => cut (<( t, s |= φ )> /\ <( t, s |= ψ )>); [auto | split]
  end.

Ltac cright :=
  match goal with
  | |- <( ?t, ?s |= ?φ \/ ?ψ )> => cut (<( t, s |= ψ )> ); [intros; right; auto|]
  end.
Ltac cleft :=
  match goal with
  | |- <( ?t, ?s |= ?φ \/ ?ψ )> => cut (<( t, s |= φ )> ); [intros; left; auto|]
  end.

Ltac cdestruct H0 :=
  match type of H0 with
  | @entailsF ?E ?C ?X ?S ?h ?HasStuck (CAnd ?φ ?ψ) ?t ?s =>
      replace (@entailsF E C X S h HasStuck (CAnd φ ψ) t s)
      with (<( t, s |= φ)> /\ <( t, s |= ψ )>) in H0 by reflexivity;
      destruct H0
  | @entailsF ?E ?C ?X ?S ?h ?HasStuck (COr ?φ ?ψ) ?t ?s =>
      replace (@entailsF E C X S h HasStuck (COr φ ψ) t s)
      with (<( t, s |= φ)> \/ <( t, s |= ψ )>) in H0 by reflexivity;
      destruct H0              
  end.

#[global] Tactic Notation "split" := (csplit || split).
#[global] Tactic Notation "right" := (cright || right).
#[global] Tactic Notation "left" := (cleft || left).
#[global] Tactic Notation "destruct" ident(H) := (cdestruct H || destruct H).

(*| Deeply embed constructors of [cau, ceu, car, cer] |*)
Section Constructors.

  Context {E C: Type -> Type} {X Σ: Type}
          `{h: E ~~> state Σ} `{HasStuck: B0 -< C}
          (t: ctree E C X) (s: Σ) (p q: @CtlFormula Σ).

  Lemma ctl_ax:
    <( t, s |= AX p )> <->
    (forall (t' : ctree E C X) (s' : Σ), ktrans (t, s) (t', s') -> <( t', s' |= p )>).
  Proof. unfold entailsF; split; intros; now apply H. Qed.

  Lemma ctl_ex:
    <( t, s |= EX p )> <->
      (exists (t' : ctree E C X) (s' : Σ), ktrans (t, s) (t', s') /\ <( t', s' |= p )>).
  Proof. unfold entailsF; split; intros; now apply H. Qed.
  
  Lemma ctl_match_au: 
      <( t, s |= q )> -> <( t, s |= p AU q )>.
  Proof. intros; unfold entailsF; now apply MatchA. Qed.
  
  Lemma ctl_step_au: 
      <( t, s |= p )> ->
      (forall (t' : ctree E C X) (s' : Σ), ktrans (t, s) (t', s') -> <( t', s' |= p AU q)>) ->
      <( t, s |= p AU q )>.
  Proof. intros; unfold entailsF; now apply StepA. Qed.
  
  Lemma ctl_match_eu: 
      <( t, s |= q )> -> <( t, s |= p EU q )>.
  Proof. intros; unfold entailsF; now apply MatchE. Qed.
  
  Lemma ctl_step_eu: 
      <( t, s |= p )> ->
      (exists (t' : ctree E C X) (s' : Σ), ktrans (t, s) (t', s') /\ <( t', s' |= p EU q)>) ->
      <( t, s |= p EU q )>.
  Proof. intros; unfold entailsF; now apply StepE. Qed.

  Lemma ctl_match_ar: 
      <( t, s |= q )> -> <( t, s |= p )> -> <( t, s |= p AR q )>.
  Proof. intros; unfold entailsF; step; now apply RMatchA. Qed.

  Lemma ctl_step_ar: 
      <( t, s |= p )> ->
      (forall (t' : ctree E C X) (s' : Σ), ktrans (t, s) (t', s') -> <( t', s' |= p AR q)>) ->
      <( t, s |= p AR q )>.
  Proof. intros; unfold entailsF; step; now apply RStepA. Qed.
  
  Lemma ctl_match_er: 
      <( t, s |= q )> -> <( t, s |= p )> -> <( t, s |= p ER q )>.
  Proof. intros; unfold entailsF; step; now apply RMatchE. Qed.

  Lemma ctl_step_er: 
      <( t, s |= p )> ->
      (exists (t' : ctree E C X) (s' : Σ), ktrans (t, s) (t', s') /\ <( t', s' |= p ER q)>) ->
      <( t, s |= p ER q )>.
  Proof. intros; unfold entailsF; step; now apply RStepE. Qed.

  (*| Inversion lemmas |*)
  Lemma ctl_inv_au: 
    <( t, s |= p AU q )> ->
    <( t, s |= q )> \/
      (<( t, s |= p )> /\
         (forall (t' : ctree E C X) (s' : Σ), ktrans (t, s) (t', s') -> <( t', s' |= p AU q)>)).
  Proof. intro H; inv H; intuition. Qed.

  Lemma ctl_inv_eu: 
    <( t, s |= p EU q )> ->
    <( t, s |= q )> \/
      (<( t, s |= p )> /\
         (exists (t' : ctree E C X) (s' : Σ), ktrans (t, s) (t', s') /\ <( t', s' |= p EU q)>)).
  Proof. intro H; inv H; intuition. Qed.

  Lemma ctl_inv_ar: 
    <( t, s |= p AR q )> ->
    <( t, s |= p /\ q)> \/
      (<( t, s |= p )> /\
         (forall (t' : ctree E C X) (s' : Σ), ktrans (t, s) (t', s') -> <( t', s' |= p AR q)>)).
  Proof.
    intro H. step in H; inv H; [left | right]; split; auto.
  Qed.
  
  Lemma ctl_inv_er: 
    <( t, s |= p ER q )> ->
    <( t, s |= p /\ q)> \/
      (<( t, s |= p )> /\
         (exists (t' : ctree E C X) (s' : Σ), ktrans (t, s) (t', s') /\ <( t', s' |= p ER q)>)).
  Proof.
    intro H. step in H; inv H; [left | right]; split; auto.
  Qed.
  
End Constructors.

Ltac cinv H0 :=
  match type of H0 with
  | @entailsF ?E ?C ?X ?S ?h ?HasStuck (CAnd ?φ ?ψ) ?t ?s =>
      replace (@entailsF E C X S h HasStuck (CAnd φ ψ) t s)
      with (<( t, s |= φ)> /\ <( t, s |= ψ )>) in H0 by reflexivity;
      destruct H0
  | @entailsF ?E ?C ?X ?S ?h ?HasStuck (COr ?φ ?ψ) ?t ?s =>
      replace (@entailsF E C X S h HasStuck (COr φ ψ) t s)
      with (<( t, s |= φ)> \/ <( t, s |= ψ )>) in H0 by reflexivity;
      destruct H0        
  | @entailsF ?E ?C ?X ?S ?h ?HasStuck (CAU ?φ ?ψ) ?t ?s =>
      apply ctl_inv_au in H0; destruct H0
  | @entailsF ?E ?C ?X ?S ?h ?HasStuck (CEU ?φ ?ψ) ?t ?s =>
      apply ctl_inv_eu in H0; destruct H0
  | @entailsF ?E ?C ?X ?S ?h ?HasStuck (CAR ?φ ?ψ) ?t ?s =>
      apply ctl_inv_ar in H0; destruct H0
  | @entailsF ?E ?C ?X ?S ?h ?HasStuck (CER ?φ ?ψ) ?t ?s =>
      apply ctl_inv_er in H0; destruct H0
  end.

#[global] Tactic Notation "inv" ident (H) := (cinv H || inv H).

(*| Laws of CTL |*)
Section Equalities.

  Context {E C: Type -> Type} {X Σ: Type}
          `{h: E ~~> state Σ} `{HasStuck: B0 -< C}.
  Notation CtlFormula := (@CtlFormula Σ).
  
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
 
  
  Lemma ctl_au_ax: forall (p q: CtlFormula),
      <( p AU q )> ⩸ <( q \/ (p /\ AX (p AU q)) )>.
  Proof.
    split; intros.
    - inv H; [now left | now right].
    - destruct H.
      + now apply ctl_match_au.
      + destruct H.
        now apply ctl_step_au.
  Qed.

  Lemma ctl_eu_ex: forall (p q: CtlFormula),
      <( p EU q )> ⩸ <( q \/ (p /\ EX (p EU q)) )>.
  Proof.
    split; cbn; intros.
    - inv H; [now left | now right].
    - destruct H.
      + now apply ctl_match_eu.
      + destruct H.
        now apply ctl_step_eu.
  Qed.
  
  Lemma ctl_af_ax: forall (p: CtlFormula),
      <( AF p )> ⩸ <( p \/ AX (AF p) )>.
  Proof.
    split; intros; inv H.
    1,3 : now left.
    all: now right. 
  Qed.

  Lemma ctl_ef_ex: forall (p: CtlFormula),
      <( EF p )> ⩸ <( p \/ EX (EF p) )>.
  Proof.
    split; intros; inv H.
    1,3: now left.
    all: now right.
  Qed.

  Lemma ctl_ar_ax: forall (p q: CtlFormula),
      <( p AR q )> ⩸ <( p /\ (q \/ AX (p AR q)) )>.
   Proof. 
     split; intros.
     - split; inv H; destruct H.
       + assumption.
       + assumption.
       + now left.
       + now right.
     - destruct H.
       destruct H0.
       + now apply ctl_match_ar.
       + now apply ctl_step_ar.
   Qed.

   Lemma ctl_er_ex: forall (p q: CtlFormula),
      <( p ER q )> ⩸ <( p /\ (q \/ EX (p ER q)) )>.
   Proof. 
     split; intros.
     - split; inv H; destruct H.
       + assumption.
       + assumption.
       + now left.
       + now right.
     - destruct H.
       destruct H0.
       + now apply ctl_match_er.
       + now apply ctl_step_er.
  Qed.

   Lemma ctl_ag_ax: forall (p: CtlFormula),
       <( AG p )> ⩸ <( p /\ AX (AG p) )>.
   Proof.
     intro p.
     split; intros.
     - apply ctl_ar_ax in H.
       destruct H; destruct H0; try contradiction.
       split; auto.
     - destruct H.
       apply ctl_ar_ax.
       split; auto.
       now right.
   Qed.

   Lemma ctl_eg_ex: forall (p: CtlFormula),
      <( EG p )> ⩸ <( p /\ EX (EG p) )>.
  Proof. 
    split; intros.
    - split; step in H; now inv H.
    - destruct H; step; apply RStepE; eauto.
  Qed.

  Lemma ctl_ag_involutive: forall (p: CtlFormula),
      <( AG p )> ⩸ <( AG (AG p) )>.
  Proof.
    split; intros; unfold entailsF;
      revert H; revert t s; coinduction R CIH; intros.  
    - apply RStepA; auto.
      intros.
      apply CIH.
      rewrite ctl_ag_ax in H.
      destruct H. 
      specialize (H1 _ _ H0).
      now unfold entailsF.
    - apply RStepA.
      rewrite ctl_ag_ax in H;
        destruct H.      
      + change (<( {?F ?p} ar {?F ?q} )> ?t ?s) with
          <( t, s |= p AR q )> in H.
        rewrite ctl_ag_ax in H.
        destruct H.
        exact H.
      + intros.
        apply CIH.
        rewrite ctl_ag_ax in H.
        destruct H.
        change (<( {?F ?p} ar {?F ?q} )> ?t ?s) with
          <( t, s |= p AR q )> in H.
        specialize (H1 _ _ H0).
        change (<( ({?F ?p} ar {?F ?q}) ar {?F ?k} )> ?t ?s) with
          <( t, s |= (p AR q) AR k )> in H1.
        exact H1.
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
    unfold entailsF in H.
    dependent destruction H; subst.
    - now apply Hbase.
    - apply Hstep; auto.
      intros.
      specialize (H0 _ _ H1).
      apply F.
      now unfold entailsF.
  Qed.

  Lemma AR_coind' (φ ψ: CtlFormula)(R : ctree E C X -> Σ -> Prop):
    (forall t s,
        R t s ->
        <( t, s |= φ )> /\
          (<(t, s |= ψ )> \/ forall t' s', ktrans (t,s) (t',s') -> R t' s')) ->
    forall t s, R t s -> <( t, s |= φ AR ψ )>.
  Proof.
    intros * stable.
    unfold entailsF.
    coinduction r CIH.
    intros * HR.
    edestruct (stable t s HR) as (Hφ & [Hψ | H]).
    - apply RMatchA; eauto.
    - apply RStepA; eauto.
  Qed.

  Lemma AG_coind' (φ: CtlFormula)(R : ctree E C X -> Σ -> Prop):
    (forall t s,
        R t s ->
        <(t, s |= φ )> /\
          forall t' s', ktrans (t,s) (t',s') -> R t' s') ->
    forall t s, R t s -> <( t, s |= AG φ )>.
  Proof.
    intros stable.
    apply AR_coind'.
    intros t s HR.
    edestruct (stable t s HR); intuition.
  Qed.
  
  Lemma AG_coind'' (φ: CtlFormula):
    forall (t: ctree E C X) (s: Σ),
    (<( t, s |= AG φ )> -> (forall t' s', ktrans (t, s) (t', s') -> <( t', s' |= AG φ)>)) ->
    <( t, s |= AG φ )>.
  Proof.
    intros * stable.
    unfold entailsF.
    revert stable. revert t s.
    coinduction R CIH; intros.
    apply RStepA.
    admit.
    intros.
    eapply CIH.
  Admitted.

  Lemma ER_coind' (φ ψ: CtlFormula)(R : ctree E C X -> Σ -> Prop):
    (forall t s ,
        R t s ->
        <( t, s |= φ )> /\
          ( <(t, s |= ψ )> \/ exists t' s', ktrans (t,s) (t',s') /\ R t' s')) ->
    forall t s, R t s -> <( t, s |= φ ER ψ )>.
  Proof.
    intros stable.
    unfold entailsF.
    coinduction r CIH.
    intros * HR.
    edestruct (stable t s HR) as (Hφ & [H | (t' & s' & TR & HR')]).
    - apply RMatchE; eauto.
    - apply RStepE; eauto.
  Qed.
  
  Lemma EG_coind' (φ: CtlFormula) :
    forall (R : ctree E C X -> Σ -> Prop),
      (forall t s,
          R t s ->
          <( t, s |= φ )> /\
            exists t' s', ktrans (t,s) (t',s') /\ R t' s') ->
      forall t s, R t s -> <( t, s |= EG φ )>.
  Proof.
    intros * stable.
    apply ER_coind'.
    intros * HR.
    edestruct (stable t s HR) as (Hψ & t' & s' & TR & HH); intuition.
    right; eauto.
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
    unfold entailsF in H.
    dependent destruction H; subst.
    - now apply Hbase.
    - apply Hstep; auto.
      edestruct H0 as (t' & s' & TR & ?).
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
   
End Equalities.

Import CtlNotations.
Local Open Scope ctl_scope.

(*| Ltac Tactics |*)
#[global] Tactic Notation "next" :=
  lazymatch goal with
  | |- context[@entailsF ?E ?C ?X ?S ?h ?HasStuck ?φ ?t ?s] =>
      lazymatch φ with
      | CAU ?p ?q => lazymatch eval cbv in p with
                    | CNowS (fun _ => True) => rewrite (@ctl_af_ax S q)
                    | _ => rewrite (@ctl_au_ax S p q)
                    end
      | CEU ?p ?q => lazymatch eval cbv in p with
                    | CNowS (fun _ => True) => rewrite (@ctl_ef_ex S q)
                    | _ => rewrite (@ctl_eu_ex S p q)
                    end
      | CAR ?p ?q => lazymatch eval cbv in q with
                    | CNowS (fun _ => False) =>
                        rewrite (@ctl_ag_ax S p)
                    | _ => rewrite (@ctl_ar_ax S p q)
                    end
      | CER ?p ?q => lazymatch eval cbv in q with
                    | CNowS (fun _ => False) => rewrite (@ctl_eg_ex S p)
                    | _ => rewrite (@ctl_er_ex S p q)
                    end
      | CAX ?p =>
          cut (forall t' s', ktrans (t, s) (t',s') -> <( t', s' |= p )>); [eauto |]
      | CEX ?p =>
          cut (exists t' s', ktrans (t, s) (t',s') /\ <( t', s' |= p )>); [eauto |]
      | ?ptrivial => lazymatch eval compute in ptrivial with
                    | CNowS ?f => unfold entailsF
                    | _ => fail "Cannot step formula " φ
                    end
      end
  end.

#[global] Tactic Notation "next" "in" ident(H) :=
  lazymatch type of H with
  | context[@entailsF ?E ?C ?X ?S ?h ?HasStuck ?φ ?t ?s] =>
      lazymatch φ with
      | context[CAU ?p ?q] => lazymatch eval cbv in p with
                             | CNowS (fun _ => True) => rewrite (@ctl_af_ax S q) in H
                             | _ => rewrite (@ctl_au_ax S p q) in H
                             end
      | context[CEU ?p ?q] => lazymatch eval cbv in p with
                             | CNowS (fun _ => True) => rewrite (@ctl_ef_ex S q) in H
                             | _ => rewrite (@ctl_eu_ex S p q) in H
                             end
      | context[CAR ?p ?q] => lazymatch eval cbv in q with
                             | CNowS (fun _ => False) => rewrite (@ctl_ag_ax S p) in H
                             | _ => rewrite (@ctl_ar_ax S p q) in H
                             end
      | context[CER ?p ?q] => lazymatch eval cbv in q with
                             | CNowS (fun _ => False) => rewrite (@ctl_eg_ex S p) in H
                             | _ => rewrite (@ctl_er_ex S p q) in H
                             end
      | CAX ?p =>
          replace (@entailsF E C X S h HasStuck (CAX p) t s) with
          (forall t' s', ktrans (t, s) (t',s') -> <( t', s' |= p )>) in H by reflexivity
      | CEX ?p =>
          replace (@entailsF E C X S h HasStuck (CEX p) t s) with
          (exists t' s', ktrans (t, s) (t',s') /\ <( t', s' |= p )>) in H by reflexivity
      | ?ptrivial => lazymatch eval compute in ptrivial with
                    | CNowS ?f => unfold entailsF in H
                    | _ => fail "Cannot step formula " φ " in " H
                    end
      end
  end.

Ltac fold_au IH :=
  match type of IH with
  | forall (t: ctree ?E ?C ?X) (s: ?S),
      hrel_of ktrans (?t0, ?s0) (?t1, ?s1) ->
      cau (?F ?ψ) (?F ?φ) _ _ => 
      assert (HEQ: forall t' s', cau (F ψ) (F φ) t' s' = <( t', s' |= ψ AU φ )>) by reflexivity;
      setoid_rewrite HEQ in IH;
      clear HEQ
  end.

Ltac cinduction H :=
  match type of H with
  | @entailsF ?E ?C ?X ?S ?h ?HasStuck (CAU ?ψ ?φ) ?ts ?ss =>
      let t' := fresh "t" in
      let s' := fresh "s" in
      let Heqt := fresh "Heqt" in
      let Heqs := fresh "Heqs" in
      remember ts as t' eqn: Heqt;
      remember ss as s' eqn: Heqs;
      unfold entailsF in H;
      induction H as [t' s' H' | t' s' Hbase IH HH];
      rewrite !Heqt, !Heqs in *;
      clear Heqt Heqs;
      fold (@entailsF E C X S h HasStuck) in *;
      fold_au IH
  end.

Tactic Notation "induction" ident(H) := (cinduction H || induction H).

#[local] Ltac __coinduction_g R H :=
  unfold entailsF; coinduction R H.

#[global] Tactic Notation "coinduction" simple_intropattern(R) simple_intropattern(H) :=
  __coinduction_g R H || coinduction R H.

Section UsefulLemmas.
  Import CtlNotations CTreeNotations.
  Local Open Scope ctl_scope.
  Context {E C: Type -> Type} {X Σ: Type} {h: E ~~> state Σ}
          {HasStuck: B0 -< C}.
  
  Lemma ctl_ret_au_inv : forall x s (p q: Σ -> Prop),
      <( {Ret x: ctree E C X}, s |= (now p) AU (now q)  )> -> p s \/ q s.
  Proof.
    intros; inv H; [now right | now left].
  Qed.
  
  Lemma ctl_bind_af_match{Y}: forall ψ (t: ctree E C Y) (s: Σ) (k: Y -> ctree E C X),
      <( t, s |= AF (now ψ) )> ->  (* either [t] satisfies [φ AU ψ] (finite) *)
      <( {x <- t ;; k x}, s |= AF (now ψ) )>. (* or it big-steps to a value [x: X] and state [s'], while maitaining [φ] *)
  Proof.
    intros.
    revert k.
    induction H; intros.
    - next.
      left.
      now unfold entailsF in *.
    - next.
      right.
      next.
      intros u su TRbind.
      apply ktrans_bind_inv in TRbind as [(NRet & t' & TRt & EQt) | (x & TRt & TRk)].
      + cbn in EQt.
        rewrite EQt.
        now apply H1.
      + specialize (H0 _ _ TRt).
        (* WHY DO YOU SUCK SO BAD at infering constraints *)
        replace (@cau E C Y Σ h HasStuck (entailsF True) (entailsF <( now ψ )>) (Ret x) s) with
          (<({Ret x: ctree E C Y}, s |= AF (now ψ))>) in H0 by reflexivity.
  Admitted.

  Lemma ctl_bind_af_inv{Y}: forall ψ (t: ctree E C Y) (s: Σ) (k: Y -> ctree E C X),
      <( {x <- t ;; k x}, s |= AF (now ψ) )> ->
      <( t, s |= AF (now ψ) )> \/
      (forall x s', ktrans^* (t,s) (Ret x, s') /\ <( {k x}, s' |= AF (now ψ) )>).
  Proof.
    intros ? t s k H *.
    unfold entailsF in H.
    induction H.
    - now left; next; left; unfold entailsF.
    - clear H.
      cbn in H0.
      eapply H1.
      Check @ktrans_steps.
      destruct (@ktrans_steps E C X Σ
                              h HasStuck t0 s).
      destruct H.
      Fail apply H.
  Admitted.
  
  Lemma ctl_bind_af_next{Y}: forall ψ (t: ctree E C Y) (s: Σ) (k: Y -> ctree E C X),
      (forall x s', ktrans^* (t,s) (Ret x, s') /\ <( {k x}, s' |= AF (now ψ) )>) ->
      <( {x <- t ;; k x}, s |= AF (now ψ) )>.
  Proof.
    intros.
    edestruct H, H0.
    generalize dependent t.
    generalize dependent s.
    induction x; intros.
    - (* refl *)
      cbn in H2.
      unfold fst, snd, RelCompFun in H2.
      destruct H2.
      rewrite H2 in *; clear H2.
      rewrite <- H3 in *; clear H3.      
      now rewrite bind_ret_l.
    - (* step *)
      next; right; next.
      intros u su TRbind.
      apply ktrans_bind_inv in TRbind as [(NRet & t'' & TRt'' & EQt') | (x' & TRt'' & TRk)].
      + cbn in EQt'.
        rewrite EQt' in *; clear EQt'.        
        eapply IHx.
        * admit. (* provable, t != Ret x, so [H0 -> TRt'' -> ktrans^* (t'', su) (Ret ?x, su) *)
  Admitted.

  
  Lemma ctl_bind_eu{Y}: forall (φ ψ: CtlFormula) (t: ctree E C Y) (s: Σ) (k: Y -> ctree E C X),
      <( {x <- t ;; k x}, s |= φ EU ψ )> <->
        <( t, s |= φ EU ψ )> \/      (* either [t] satisfies [φ AU ψ] (finite) *)
           (exists x s', (t,s) ⇓{ φ } (x, s') /\ <( {k x}, s' |= φ EU ψ )>).  (* or it big-steps to a value [x: X] and state [s'], while maitaining [φ] *)                          
  Proof.
    intros.
    split; intros.
  Admitted.

  (** TODO: These lemmas are not useful, need a lemma that allows me to do coinduction
      under the hood *)
  Lemma ctl_bind_ar{Y}: forall (φ ψ: CtlFormula) (t: ctree E C Y) (s: Σ) (k: Y -> ctree E C X),
      <( {x <- t ;; k x}, s |= φ AR ψ )> <->
        <( t,s |= φ AR ψ )> \/      (* either [t] satisfies [φ AR ψ] (maybe infinite) *)
          (forall x s', (t,s) ⇓{ φ } (x, s') /\ <( {k x}, s' |= φ AR ψ )>).   (* or it big-steps to a value [x: X] and state [s'], while maitaining [φ] *)
  Proof.
    intros.
  Admitted.

  Lemma ctl_bind_er{Y}: forall (φ ψ: CtlFormula) (t: ctree E C Y) (s: Σ) (k: Y -> ctree E C X),
      <( {x <- t ;; k x}, s |= φ ER ψ )> <->
        <( t,s |= φ ER ψ )> \/      (* either [t] satisfies [φ AR ψ] (maybe infinite) *)
          (exists x s', (t,s) ⇓{ φ } (x, s') /\ <( {k x}, s' |= φ ER ψ )>).   (* or it big-steps to a value [x: X] and state [s'], while maitaining [φ] *)
  Proof.
    intros.
  Admitted.

  (** TODO: This is also weak... *)
  Lemma ctl_forever_ar `{HasTau: B1 -< C}:
    forall (φ ψ: CtlFormula) (k: X -> ctree E C X) (s: Σ) (i: X),
      <( {CTree.forever k i}, s |= φ AR ψ )> ->
        <( {k i}, s |= φ AR ψ )> \/
          (forall x s', (k i, s) ⇓{ φ } (x, s') -> <( {k x}, s' |= φ AR ψ )>).
  Admitted.


  (** [Ret x, s] does not change s, so everything that is true for [s] remains true forever *)
  Lemma ctl_ax_ret: forall (x:X) φ s,
      <( {Ret x: ctree E C X}, s |=  AX φ )> <-> <( {Ret x: ctree E C X}, s |= φ )>.
  Proof.
    split; intros.
    - next in H.
      exact (H _ _ ktrans_ret_refl).
    - next.
      intros.
      now apply ktrans_ret in H0 as (-> & <-).
  Qed.      
  
  Lemma ctl_ar_ret: forall (x:X) φ ψ s,
      <( {Ret x: ctree E C X}, s |=  φ AR ψ )> <-> <( {Ret x: ctree E C X}, s |= φ \/ (φ /\ ψ) )>.
  Proof.
    split; intros.
    - step in H; inv H; left; auto.
    - destruct H; generalize dependent x; revert s; coinduction R CIH; intros. 
      + apply RStepA; auto.
        intros t' s' TR.
        specialize (CIH _ _ H).
        apply ktrans_ret in TR as (Heq & <-).
        now rewrite Heq.
        exact t'.
      + destruct H.
        apply RMatchA; auto.
  Qed.

  (** [Ret x, s] does not change s, so everything that is true for [s] remains true forever *)
  Lemma ctl_au_ret: forall (x:X) s ψ φ,
      <( {Ret x: ctree E C X}, s |=  ψ AU φ )> <-> <( {Ret x: ctree E C X}, s |= φ )>.
  Proof.
    split; intros.
    - induction H.
      + auto.
      + pose proof (@ktrans_ret_refl E C X Σ h HasStuck x s) as HTrRefl.
        admit.
    - now apply ctl_match_au.
  Admitted.

End UsefulLemmas.

Module Experiments.
  Import CTree CTreeNotations CtlNotations.
  Local Open Scope ctl_scope.
  Context {E C: Type -> Type} {S: Type} {HasStuck: B0 -< C}.
  Definition stuck: ctree E C unit := stuckD.
    
  Definition ctl_of_State (s: nat): @CtlFormula nat := CNowS (fun x => x = s).
  Arguments ctl_of_State /.
  Coercion ctl_of_State : nat >-> CtlFormula.

  Opaque ktrans.
  Lemma writes_23: forall s,
      <( {put 2 ;; put 3 : ctree (stateE nat) B0 unit}, s |= AX 2 /\ (AX (AX 3)) )>.
  Proof.
    split; next; intros. 
    - apply ktrans_trigger_inv in H as ([] & ? & ->).
      cbn; auto.
    - apply ktrans_trigger_inv in H as ([] & ? & ->).
      rewrite H in *; clear H.
      cbn; auto.
      intros.
      apply ktrans_vis_inv in H as ([] & ? & ->).
      cbn; auto.
  Qed.      

  Lemma is_stuck_ax: forall s `{h: E ~~> state S},
      <( stuck, s |= (AX False) )>.
  Proof.
    intros.
    next.
    intros t' s' TR.
    now apply ktrans_stuck_inv in TR.
  Qed.

  (* Terminating [ret x] programs *)
  Lemma maybebad: forall n,
      ~ <( {put 2: ctree (stateE nat) C unit}, n |= AX 3 )>.
  Proof.
    intros * CONTRA.
    next in CONTRA.
    assert (TR: @ktrans _ C _ _ _ _ (put 2, n) (Ret tt, 2))
      by (eapply ktrans_vis_goal; intuition).
    apply CONTRA in TR.
    discriminate TR.
  Qed.

  Lemma maybegood: forall n,
      <( {put 2: ctree (stateE nat) C unit}, n |= AF 2 )>.
  Proof.
    intros.
    next; right; intros.
    next.
    intros.
    apply ktrans_vis_inv in H as ([] & -> & ->).
    unfold entailsF; apply MatchA.
    reflexivity.
  Qed.

  Lemma maybegood': 
    <( {put 2: ctree (stateE nat) C unit}, 2 |= AG 2 )>.
  Proof.
    next.
    split; auto.
    next; intros.
    apply ktrans_vis_inv in H as ([] & ? & ->).
    rewrite H.
    coinduction R CIH.
    apply RStepA; auto. 
    intros.
    apply ktrans_ret in H0 as (? & <-).
    rewrite H0.
    apply CIH.
    exact t'0.
  Qed.

  Lemma maybegood'': 
    <( {put 2: ctree (stateE nat) C unit}, 2 |= ¬ AG 3 )>.
  Proof.
    unfold entailsF.
    intro CONTRA.
    step in CONTRA; inv CONTRA.
    + discriminate H0.
    + discriminate H.
  Qed.

End Experiments.
