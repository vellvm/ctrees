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
     Interp.Par
     Logic.Kripke
     FoldStateT.

From Coq Require Import
     Classes.SetoidClass
     Classes.RelationPairs.

Set Implicit Arguments.
Typeclasses eauto := 6.

(*| CTL logic based on kripke semantics of ctrees |*)
Section Ctl.
  
  Context {E C: Type -> Type} {X S: Type}
          {h: Handler E S} {HasStuck: B0 -< C}.
  Notation SP := (ctree E C X -> S -> Prop).
  
  (* Lift label predicates to SP *)
  Definition nowS(p: S -> Prop): SP :=
    fun _ s => p s.

  (* Predicate on return value *)
  Definition nowR(p: X -> S -> Prop): SP :=
    fun t s => exists x, t ≅ Ret x /\ p x s.

  (* Propositional *)
  Definition cimpl: SP -> SP -> SP :=
    fun a b t l => a t l -> b t l.

  Definition cand: SP -> SP -> SP :=
    fun a b t l => a t l /\ b t l.

  Definition cor: SP -> SP -> SP :=
    fun a b t l => a t l \/ b t l.

  Definition cnot: SP -> SP :=
    fun a t l => not (a t l).
  
  (*| Temporal, inductives |*)
  (* Forall Next *)
  Definition ax : SP -> SP :=
    fun p t s => forall t' s', ktrans (t,s) (t',s') -> p t' s'.
  
  (* Forall Next *)
  Definition ex : SP -> SP :=
    fun p t s => exists t' s', ktrans (t,s) (t',s') /\ p t' s'.

  (* Forall strong until *)
  Inductive au: SP -> SP -> SP :=
  | MatchA: forall t s (p q: SP),       
      q t s ->  (* Matches [q] now; done *)
      au p q t s
  | StepA:  forall t s (p q: SP),       
      p t s ->    (* Matches [p] now; steps to (t', s') *)
      (forall t' s', ktrans (t,s) (t',s') -> au p q t' s') ->
      au p q t s.
      
  (* Exists strong until *)
  Inductive eu: SP -> SP -> SP :=
  | MatchE: forall t s (p q: SP),
      q t s ->       (* Matches [q] now; done *)
      eu p q t s
  | StepE: forall t s (p q: SP),
      p t s ->    (* Matches [p] now; steps to (t', s') *)
      (exists t' s', ktrans (t,s) (t',s') /\ eu p q t' s') ->
      eu p q t s.
  
  (*| Temporal, Coinductives |*)  
  (* Forall global *)
  Definition agF (p: SP)(R: SP): SP :=
    fun t s => p t s /\ (forall t' s', ktrans (t,s) (t',s') -> R t' s').

  (* Exists global *)
  Definition egF (p: SP) (R: SP): SP :=
    fun t s => p t s /\ (exists t' s', ktrans (t,s) (t',s') /\ R t' s').

  Definition entails(p: SP) (t: ctree E C X)(s: S): Prop := p t s.
 
  Arguments agF /.
  Arguments egF /.
    
  Program Definition ag_ p: mon SP := {| body := agF p |}.
  Program Definition eg_ p: mon SP := {| body := egF p |}.  
  Next Obligation. esplit; eauto. Qed.

  Definition ag p := (gfp (@ag_ p)).
  Definition eg p := (gfp (@eg_ p)).
End Ctl.

Module CtlNotations.

  Declare Custom Entry ctl.
  Declare Scope ctl_scope.

  Section SC.
    Context {E C: Type -> Type} {X S: Type}.
    Notation SP := (ctree E C X -> S -> Prop).
    Definition ctl_of_Prop (P : Prop) : SP := nowS (fun (_: S) => P).
    Definition ctl_of_State (s: S): SP := nowS (fun (x: S) => x = s).
    Coercion ctl_of_Prop : Sortclass >-> Funclass. 
    Coercion ctl_of_State : S >-> Funclass.
  End SC.
  
  Notation "<( e )>" := e (at level 0, e custom ctl at level 95) : ctl_scope.
  Notation "( x )" := x (in custom ctl, x at level 99) : ctl_scope.
  Notation "{ x }" := x (in custom ctl at level 0, x constr): ctl_scope.
  Notation "x" := x (in custom ctl at level 0, x constr at level 0) : ctl_scope.
  Notation "t , s |= p " := (entails p t s) (in custom ctl at level 80,
                                                p custom ctl,
                                                right associativity): ctl_scope.
  (* Temporal *)
  Notation "'now' p" := (nowS p) (in custom ctl at level 79): ctl_scope.
  Notation "'ret' p" := (nowR p) (in custom ctl at level 79): ctl_scope.
  Notation "'EX' p" := (ex p) (in custom ctl at level 75): ctl_scope.
  Notation "'AX' p" := (ax p) (in custom ctl at level 75): ctl_scope.
  Notation "p 'EU' q" := (eu p q) (in custom ctl at level 75): ctl_scope.
  Notation "p 'AU' q" := (au p q) (in custom ctl at level 75): ctl_scope.
  Notation "'EF' p" := (eu True p) (in custom ctl at level 75): ctl_scope.
  Notation "'AF' p" := (au True p) (in custom ctl at level 75): ctl_scope.
  Notation "'EG' p" := (eg p) (in custom ctl at level 75): ctl_scope.
  Notation "'AG' p" := (ag p) (in custom ctl at level 75): ctl_scope.

  (* Propositional *)
  Notation "p '/\' q" := (cand p q) (in custom ctl at level 77, left associativity): ctl_scope.
  Notation "p '\/' q" := (cor p q) (in custom ctl at level 77, left associativity): ctl_scope.
  Notation "p '->' q" := (cimpl p q) (in custom ctl at level 78, right associativity): ctl_scope.
  Notation "p '<->' q" := (cand (cimpl p q) (cimpl q p))
                            (in custom ctl at level 77): ctl_scope.

  (* Companion notations *)
  Notation agt p := (t (ag_ p)).
  Notation agbt p := (bt (ag_ p)).
  Notation egt p := (t (eg_ p)).
  Notation egbt p := (bt (eg_ p)).
  Notation agT p := (T (ag_ p)).
  Notation egT p := (T (eg_ p)).
  Notation agbT p := (bT (ag_ p)).
  Notation egbT p := (bT (eg_ p)).

  (* TODO: Think proof lemmas so these don't escape to the user? *)
  Notation "[ 'AG' ] p" := (ag_ p _) (in custom ctl at level 75, p custom ctl): ctl_scope.
  Notation "[ 'EG' ] p" := (eg_ p _) (in custom ctl at level 75, p custom ctl): ctl_scope.
  
  Notation "[[ 'AG' ]] p" := (agF p _) (in custom ctl at level 75, p custom ctl): ctl_scope.
  Notation "[[ 'EG' ]] p" := (egF p _) (in custom ctl at level 75, p custom ctl): ctl_scope.
  
  Notation "{ 'AG' } p" := (agt p _) (in custom ctl at level 75, p custom ctl): ctl_scope.
  Notation "{ 'EG' } p" := (egt p _) (in custom ctl at level 75, p custom ctl): ctl_scope.
  
  Notation "{{ 'AG' }} p" := (agbt p _) (in custom ctl at level 75, p custom ctl): ctl_scope.
  Notation "{{ 'EG' }} p" := (egbt p _) (in custom ctl at level 75, p custom ctl): ctl_scope.
  
End CtlNotations.
  
Import CtlNotations.

#[global] Hint Constructors eu au: core.
#[global] Hint Unfold cand cor cimpl ax ex nowS nowR: core.
Arguments cand /.
Arguments cor /.
Arguments cimpl /.
Arguments ax /.
Arguments ex /.
Arguments agF /.
Arguments egF /.
Arguments nowS /.
Arguments nowR /.
Arguments entails: simpl never.

(*| Equations of CTL |*)
Section Equivalences.
  Local Open Scope ctl_scope.
  Context {E C: Type -> Type} {X S: Type} {HasStuck: B0 -< C} {h: Handler E S}.

  (* Kripke state predicates *)
  Notation SP := (ctree E C X -> S -> Prop).

  (* SP is proper setoid *)
  Program Instance SpSetoid : Setoid SP :=
    {| equiv := fun P Q => forall (t: ctree E C X) (s:S), P t s <-> Q t s |}.
  Next Obligation.
    split.
    - intros P x; reflexivity.
    - intros P Q H x s; symmetry; auto.
    - intros P Q R H0 H1 x s; transitivity (Q x s); auto.
  Qed.

  (*| Top is True |*)
  Lemma ctl_top: forall (t: ctree E C X) (s: S),
    <( t, s |= True )>.
  Proof. reflexivity. Qed.    

  (*| Bot is False |*)
  Lemma ctl_bot: forall (t: ctree E C X) (s: S),
    ~ <(t, s |= False)>.
  Proof.
    intros * CONTRA; apply CONTRA.
  Qed.

  (*| Ex-falso |*)
  Lemma ctl_ex_falso: forall (t: ctree E C X) (s: S) p,
      <( t,s |= False -> p )>.
  Proof.
    intros * CONTRA; contradiction.
  Qed.

  Lemma ctl_af_ax: forall (p: SP),
      <( AF p )> == <( p \/ AX (AF p) )>.
  Proof.
    split; intros; inv H.
    - now left.
    - now right. 
    - now left. 
    - now right.
  Qed.

  Lemma ctl_ef_ex: forall (p: SP),
      <( EF p )> == <( p \/ EX (EF p) )>.
  Proof.
    split; intros; inv H.
    - now left.
    - now right. 
    - now left. 
    - now right.
  Qed.

  Lemma ctl_ag_ax: forall (p: SP),
      <( AG p )> == <( p /\ AX (AG p) )>.
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
  Qed.

  Lemma ctl_eg_ex: forall (p: SP),
      <( EG p )> == <( p /\ EX (EG p) )>.
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

  Lemma ctl_au_ax: forall (p q: SP),
      <( p AU q )> == <( q \/ (p /\ AX (p AU q)) )>.
  Proof.
    split; intros.
    - inv H.
      + now left.
      + now right.
    - inv H.
      + now apply MatchA.
      + destruct H0; auto.
  Qed.

  Lemma ctl_eu_ex: forall (p q: SP),
      <( p EU q )> == <( q \/ (p /\ EX (p EU q)) )>.
  Proof.
    split; cbn; intros.
    - inv H.
      + now left.
      + now right.
    - inv H.
      + now apply MatchE.
      + destruct H0; auto.
  Qed.

  (*| [now] ignores trees and only looks at labels |*)
  #[global] Instance proper_now: forall (p: S -> Prop) (R: relation (ctree E C X)),
      Proper (R ==> eq ==> iff) <( now p )>.
  Proof.
    unfold Proper, respectful, impl; cbn.      
    intros p R x y EQ ? l <-; split; auto.
  Qed.

  #[global] Instance proper_cand_equ (P Q: SP)
   {PrP: Proper (@equ E C X X eq ==> eq ==> iff) P}
   {PrQ: Proper (@equ E C X X eq ==> eq ==> iff) Q}:
    Proper (@equ E C X X eq ==> eq ==> iff) <(P /\ Q)>.
  Proof.
    unfold Proper, respectful, impl, cand; cbn.
    intros x y EQ ? l <-; split; intros (? & ?); split.
    - now rewrite <- EQ.
    - now rewrite <- EQ.
    - now rewrite EQ.
    - now rewrite EQ.
  Qed.    
    
  #[global] Instance proper_cor_equ (P Q: SP)
   {PrP: Proper (@equ E C X X eq ==> eq ==> iff) P}
   {PrQ: Proper (@equ E C X X eq ==> eq ==> iff) Q}:
    Proper (@equ E C X X eq ==> eq ==> iff) <(P \/ Q)>.
  Proof.
    unfold Proper, respectful, impl, cand; cbn.
    intros x y EQ ? l <-; split; intros [? | ?].
    - left; now rewrite <- EQ.
    - right; now rewrite <- EQ.
    - left; now rewrite EQ.
    - right; now rewrite EQ.
  Qed.
  
  #[global] Instance proper_cimpl_equ (P Q: SP)
   {PrP: Proper (@equ E C X X eq ==> eq ==> iff) P}
   {PrQ: Proper (@equ E C X X eq ==> eq ==> iff) Q}:
    Proper (@equ E C X X eq ==> eq ==> iff) <(P -> Q)>.
  Proof.
    unfold Proper, respectful, impl, cimpl; cbn.
    intros x y EQ ? l <-; split; intros G HP.
    - rewrite <- EQ; apply G.
      now rewrite EQ.
    - rewrite EQ; apply G.
      now rewrite <- EQ.
  Qed.
  
  #[global] Instance proper_ax_equ (P: SP):
    Proper (@equ E C X X eq ==> eq ==> iff) <( AX P )>.
  Proof.
    unfold Proper, respectful, impl; cbn.      
    intros x y EQ ? l <-; split; intro NEXT;
      unfold ax in *;
      intros; eapply NEXT.
    - now rewrite EQ.
    - now rewrite <- EQ.
  Qed.

  #[global] Instance proper_ex_equ (P: SP):
    Proper (@equ E C X X eq ==> eq ==> iff) <( EX P )>.
  Proof.
    unfold Proper, respectful, impl; cbn.      
    intros x y EQ ? l <-; split; intro NEXT;
      unfold ex in *; destruct NEXT as (l' & t' & NEXT & ?);
      do 2 eexists; split; eauto. 
    - now rewrite <- EQ.
    - now rewrite EQ.
  Qed.

  #[global] Instance proper_au_equ (P Q: SP)
   {PrP: Proper (@equ E C X X eq ==> eq ==> iff) P}
   {PrQ: Proper (@equ E C X X eq ==> eq ==> iff) Q}:
    Proper (@equ E C X X eq ==> eq ==> iff) <(P AU Q)>.
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

  #[global] Instance proper_eu_equ (P Q: SP)
   {PrP: Proper (@equ E C X X eq ==> eq ==> iff) P}
   {PrQ: Proper (@equ E C X X eq ==> eq ==> iff) Q}:
    Proper (@equ E C X X eq ==> eq ==> iff) <(P EU Q)>.
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

  (*| Up-to-eq enhancing function |*)
  Variant unary_equ_clos_body (R : SP) : SP :=
    | uEqu_clos : forall t t' s s'
                  (Agt : t ≅ t')
                  (HR : R t' s')
                  (Agu : s' = s),
        unary_equ_clos_body R t s.

  Program Definition unary_equ_clos: mon SP :=
    {| body := unary_equ_clos_body |}.
  Next Obligation. destruct H0; econstructor; eauto. Qed.

  (*| Rewrite [t ≅ u] in a CTL context t,s |= p <-> u,s |= p] |*)
  Section gProperEqu.
    Context {P: SP} {PrP: Proper (@equ E C X X eq ==> eq ==> iff) P}.    
    Lemma equ_clos_ag:
      unary_equ_clos <= agt P.
    Proof.    
      apply Coinduction; cbn.
      intros R t0 s0 [t1 t2 s1 s2 EQt [Fwd Back] <-]; split.
      - rewrite EQt; apply Fwd.
      - intros. 
        eapply (f_Tf (ag_ P)).
        rewrite EQt in H.
        apply Back in H.
        econstructor; eauto.
    Qed.

    Lemma equ_clos_eg:
      unary_equ_clos <= egt P.
    Proof.    
      apply Coinduction; cbn.
      intros R t0 s0 [t1 t2 s1 s2 EQt [Fwd (t2' & s2' & TR & Back)] <-]; split.
      - rewrite EQt; apply Fwd.
      - exists t2', s2'; split.
        + now rewrite EQt.
        + eapply (f_Tf (eg_ P)).
          econstructor; eauto. 
    Qed.

    #[global] Instance proper_agt_equ RR:
      Proper (@equ E C X X eq ==> eq ==> iff) (agt P RR).
    Proof.
      unfold Proper, respectful, impl; cbn.
      intros x y EQ ? l <-; split; intro G; apply (ft_t equ_clos_ag); econstructor;
        [symmetry | apply G | reflexivity | | apply G | reflexivity]; assumption.
    Qed.

    #[global] Instance proper_agT_equ RR f:
      Proper (@equ E C X X eq ==> eq ==> iff) (agT P f RR).
    Proof.
      unfold Proper, respectful, impl; cbn.
      intros x y EQ ? l <-; split; intro G; apply (fT_T equ_clos_ag); econstructor;
        [symmetry | apply G | reflexivity | | apply G | reflexivity]; assumption.
    Qed.

    #[global] Instance proper_ag_equ:
      Proper (@equ E C X X eq ==> eq ==> iff) <( AG P )>.
    Proof.
      unfold Proper, respectful, impl; cbn.
      intros x y EQ ? l <-; split; intro G; apply (ft_t equ_clos_ag); econstructor;
        [symmetry | apply G | reflexivity | | apply G | reflexivity]; assumption.
    Qed.
    
    #[global] Instance proper_egt_equ RR:
      Proper (@equ E C X X eq ==> eq ==> iff) (egt P RR).
    Proof.
      unfold Proper, respectful, impl; cbn.
      intros x y EQ ? l <-; split; intro G; apply (ft_t equ_clos_eg); econstructor;
        [symmetry | apply G | reflexivity | | apply G | reflexivity]; assumption.
    Qed.

    #[global] Instance proper_egT_equ RR f:
      Proper (@equ E C X X eq ==> eq ==> iff) (egT P f RR).
    Proof.
      unfold Proper, respectful, impl; cbn.
      intros x y EQ ? l <-; split; intro G; apply (fT_T equ_clos_eg); econstructor;
        [symmetry | apply G | reflexivity | | apply G | reflexivity]; assumption.
    Qed.

    #[global] Instance proper_eg_equ:
      Proper (@equ E C X X eq ==> eq ==> iff) <( EG P )>.
    Proof.
      unfold Proper, respectful, impl; cbn.
      intros x y EQ ? l <-; split; intro G; apply (ft_t equ_clos_eg); econstructor;
        [symmetry | apply G | reflexivity | | apply G | reflexivity]; assumption.
    Qed.

    (* Allow rewriting under entailment *)
    #[global] Instance proper_entails_equ:
      Proper (@equ E C X X eq ==> @eq S ==> iff) (entails P). 
    Proof.
      unfold Proper, respectful, iff;
        intros x y EQx a ? <-; split; intro G; unfold entails in *; [now rewrite <- EQx | now rewrite EQx].
    Qed.
  End gProperEqu.
                
  (*| Up-to-sbisim enhancing function |*)
  Variant unary_sbisim_clos_body (R : SP) : SP :=
    | uSbisim_clos : forall t t' s s'
                  (Agt : t ~ t')
                  (HR : R t' s')
                  (Agu : s' = s),
        unary_sbisim_clos_body R t s.

  Program Definition unary_sbisim_clos: mon SP :=
    {| body := unary_sbisim_clos_body |}.
  Next Obligation. destruct H0; econstructor; eauto. Qed.

  (*| Rewrite [t ~ u] in a CTL context t,s |= p <-> u,s |= p] |*)
  Section gProperSbisim.
    Context {P: SP} {PrP: Proper (@sbisim E E C C X X _ _ eq ==> eq ==> iff) P}.
    
    Lemma sbisim_clos_ag:
      unary_sbisim_clos <= agt P.
    Proof.    
      apply Coinduction; cbn.
      intros R t0 s0 [t1 t2 s1 s2 EQt [Fwd Back] <-]; split.
      - rewrite EQt; apply Fwd.
      - intros. 
        eapply (f_Tf (ag_ P)).
        rewrite <- EQt in Fwd.
        destruct (ktrans_sbisim_l H EQt) as (? & ? & ?); eauto.
        econstructor.
        + apply H1.
        + apply Back.
          apply H0.
        + reflexivity.
    Qed.

    Lemma sbisim_clos_eg:
      unary_sbisim_clos <= egt P.
    Proof.    
      apply Coinduction; cbn.
      intros R t0 s0 [t1 t2 s1 s2 EQt [Fwd Back] <-]; split.
      - rewrite EQt; apply Fwd.
      - destruct Back as (t2' & s2' & TR2 & ?).
        symmetry in EQt.
        destruct (ktrans_sbisim_l TR2 EQt) as (? & ? & ?); eauto.
        exists x, s2'; intuition.
        eapply (f_Tf (eg_ P)).
        symmetry in H1.
        econstructor; eauto.
    Qed.
    
    #[global] Instance proper_egt_sbisim RR:
      Proper (sbisim eq ==> eq ==> iff) (egt P RR).
    Proof.
      unfold Proper, respectful, impl; cbn.
      intros x y EQ ? l <-; split; intro G; apply (ft_t sbisim_clos_eg); econstructor;
        [symmetry | apply G | reflexivity | | apply G | reflexivity]; assumption.
    Qed.

    #[global] Instance proper_egT_sbisim RR f:
      Proper (sbisim eq ==> eq ==> iff) (egT P f RR).
    Proof.
      unfold Proper, respectful, impl; cbn.
      intros x y EQ ? l <-; split; intro G; apply (fT_T sbisim_clos_eg); econstructor;
        [symmetry | apply G | reflexivity | | apply G | reflexivity]; assumption.
    Qed.

    #[global] Instance proper_eg_sbisim:
      Proper (sbisim eq ==> eq ==> iff) <( EG P )>.
    Proof.
      unfold Proper, respectful, impl; cbn.
      intros x y EQ ? l <-; split; intro G; apply (ft_t sbisim_clos_eg); econstructor;
        [symmetry | apply G | reflexivity | | apply G | reflexivity]; assumption.
    Qed.
        
    #[global] Instance proper_agt_sbisim RR:
      Proper (sbisim eq ==> eq ==> iff) (agt P RR).
    Proof.
      unfold Proper, respectful, impl; cbn.
      intros x y EQ ? l <-; split; intro G; apply (ft_t sbisim_clos_ag); econstructor;
        [symmetry | apply G | reflexivity | | apply G | reflexivity]; assumption.
    Qed.

    #[global] Instance proper_agT_sbisim RR f:
      Proper (sbisim eq ==> eq ==> iff) (agT P f RR).
    Proof.
      unfold Proper, respectful, impl; cbn.
      intros x y EQ ? l <-; split; intro G; apply (fT_T sbisim_clos_ag); econstructor;
        [symmetry | apply G | reflexivity | | apply G | reflexivity]; assumption.
    Qed.

    #[global] Instance proper_ag_sbisim:
      Proper (sbisim eq ==> eq ==> iff) <( AG P )>.
    Proof.
      unfold Proper, respectful, impl; cbn.
      intros x y EQ ? l <-; split; intro G; apply (ft_t sbisim_clos_ag); econstructor;
        [symmetry | apply G | reflexivity | | apply G | reflexivity]; assumption.
    Qed.

    (* Allow rewriting under entailment *)
    #[global] Instance proper_entails_sbisim:
      Proper (sbisim eq ==> eq ==> iff) (entails P). 
    Proof.
      unfold Proper, respectful, iff;
        intros x y EQx a ? <-; split; intro G; unfold entails in *; [now rewrite <- EQx | now rewrite EQx].
    Qed.
  End gProperSbisim.

  (*| Up-to-bind ag |*)
  Section gProperBind.
    Context {Y: Type}.

    Print SP.
    Print ag.
    (*| Up-to-bind enchancing function (unary context) |*)
    Definition bind_clos
               (R: rel (ctree E C X) S)
               (Rk: (X -> ctree E C Y) -> Prop):
      rel (ctree E C Y) S :=
      sup_all (fun t => sup (R t)
                         (fun s' => sup Rk
                                     (fun k => pairH (CTree.bind t k) s'))).
  
    (*| Specialization of [bind_ctx] to a function acting with [equ] on the bound value,
        and with the argument (pointwise) on the continuation. |*)
    Program Definition bind_clos_ag p: mon (rel (ctree E C Y) S) :=
      {| body := fun R => bind_clos (ag p) (fun k => forall x s, R (k x) s) |}.
    Next Obligation.
      (* TODO *)
      (* unfold bind_clos.
      apply leq_bind_ctx. intros ?? H' ?? H''.
      apply in_bind_ctx. apply H'. intros t t' HS. apply H0, H'', HS. *)
    Admitted.
  End gProperBind.
End Equivalences.

(*| Ltac Tactics |*)
#[local] Ltac __fold_g :=
  repeat
    match goal with
    | h: context[@ag_ ?E ?C ?S ?X ?h ?HS ?R ] |- _ => fold (@ag E C S X h HS R) in h
    | |- context[@ag_ ?E ?C ?S ?X ?h ?HS ?R ]      => fold (@ag E C S X h HS R)
    | h: context[@eg_ ?E ?C ?S ?X ?h ?HS ?R ] |- _ => fold (@eg E C S X h HS R) in h
    | |- context[@eg_ ?E ?C ?S ?X ?h ?HS ?R ]      => fold (@eg E C S X h HS R)
    end.

#[local] Ltac __fold_entails :=  
  lazymatch goal with
  | |- context[entails ?ϕ ?t ?s] => fail "Already in [t, s |= p] form"
  | |- context[?ϕ ?t ?s] =>
      match type of ϕ with
      |_ -> _ -> Prop =>
         match type of t with
         | ctree ?E ?C ?X =>
             replace (ϕ t s) with (entails ϕ t s) by reflexivity
         end
      end                
  end.

#[local] Ltac __fold_entails_in H :=
  lazymatch type of H with
  | context[entails ?ϕ ?t ?s] => fail "Already in [t, s |= p] form"
  | context[?ϕ ?t ?s] =>
       match type of ϕ with
       |ctree ?E ?C ?X -> ?S -> Prop =>
         match type of t with
         | ctree ?E ?C ?X =>
             match type of s with
             | ?S => replace (ϕ t s) with (entails ϕ t s) in H by reflexivity
             end
         end
      end                
  end.

#[local] Tactic Notation "__step_x" :=
  lazymatch goal with
  | |- entails (@ax ?E ?C ?X ?S ?h ?HasStuck ?p) ?t ?s =>
      unfold entails, ax;
      repeat (
          let t_ := fresh "t" in
          let s_ := fresh "s" in
          let TR_ := fresh "TR" in
          intros t_ s_ TR_)
  | |- entails (@ex ?E ?C ?X ?S ?h ?HasStuck ?p) ?t ?s =>
      unfold entails, ex; do 2 eexists
  end; __fold_entails.

#[local] Ltac __step_in_x H :=
  lazymatch type of H with
  | entails (@ax ?E ?C ?X ?S ?h ?HasStuck ?p) ?t ?s =>
      unfold entails, ax in H;
      lazymatch goal with
      | H: forall t' : ctree ?E ?C ?X, forall s': ?S, ktrans ?L (t', s') -> ?ϕ t' s' |- _ => 
          lazymatch type of ϕ with
          |_ -> _ -> Prop =>
             replace (forall (t' : ctree E C X) (s': S) , ktrans L (t', s') -> ϕ t' s') with
             (forall (t' : ctree E C X) (s': S) , ktrans L (t', s') -> entails ϕ t' s') in H by reflexivity
          end
      end
  | entails (@ex ?E ?C ?X ?S ?h ?HasStuck ?p) ?t ?s =>
      let t_ := fresh "t" in
      let s_ := fresh "s" in
      let TR_ := fresh "TR" in
      let NOW_ := fresh "Hnow" in
      unfold entails, ex in H; destruct H as (t_ & s_ & TR_ & NOW_);
      replace (p t_ s_) with (entails p t_ s_) in NOW_ by reflexivity
  end.

#[local] Tactic Notation "__step_u" :=
  lazymatch goal with
  | |- entails (@au ?E ?C ?X ?S ?h ?HasStuck ?p ?q) ?t ?s =>
      unfold entails; apply ctl_au_ax
  | |- entails (@eu ?E ?C ?X ?S ?h ?HasStuck ?p ?q) ?t ?s =>
      unfold entails; apply ctl_eu_ex
  end; __fold_entails.

#[local] Ltac __step_in_u H :=
  lazymatch type of H with
  | entails (@au ?E ?C ?X ?S ?h ?HasStuck ?p ?q) ?t ?s =>
      let NOW_ := fresh "Hnow" in
      unfold entails; apply ctl_au_ax in H; destruct H;
      [|destruct H as (NOW_ & ?); __fold_entails_in NOW_]
  | entails (@eu ?E ?C ?X ?S ?h ?HasStuck ?p ?q) ?t ?s =>
      unfold entails, ex; apply ctl_eu_ex in H
  end; __fold_entails_in H.

#[local] Tactic Notation "__step_g" :=
  lazymatch goal with
  | |- entails (@ag ?E ?C ?S ?X ?h ?HasStuck ?p) ?t ?q =>
      unfold entails, ag;
      step;
      fold (@ag E C S X h HasStuck p t q)
  | |- entails (@eg ?E ?C ?S ?X ?h ?HasStuck ?p) ?t ?q =>
      unfold entails,eg;
      step;
      fold (@eg E C S X h HasStuck p t q)
  end;  __fold_entails.

#[local] Ltac __step_in_g H :=
  lazymatch type of H with
  | entails (@ag ?E ?C ?S ?X ?h ?HasStuck ?p) ?t ?s =>
      unfold entails, ag in H;
      step in H;
      fold (@ag E C S X h HasStuck) in H
  | entails (@eg ?E ?C ?S ?X ?h ?HasStuck ?p) ?t ?s =>
      unfold entails, eg in H;
      step in H;
      fold (@eg E C S X h HasStuck) in H
  end; __fold_entails_in H.

#[local] Ltac __coinduction_g R H :=
  unfold entails, ag, eg; coinduction R H; __fold_g; __fold_entails.

(** Re-export [Eq.v] tactics *)
#[global] Tactic Notation "step" :=
  __step_x || __step_u || __step_g || step.

#[global] Tactic Notation "coinduction" simple_intropattern(R) simple_intropattern(H) :=
  __coinduction_g R H || coinduction R H.

#[global] Tactic Notation "step" "in" ident(H) :=
  __step_in_x H || __step_in_u H || __step_in_g H || step_in H.

Tactic Notation "right" := right; try progress __fold_entails.
Tactic Notation "left" := left; try progress __fold_entails.
Tactic Notation "split" := split; try progress __fold_entails.

Section UsefulLemmas.
  Import CtlNotations CTreeNotations.
  Local Open Scope ctl_scope.

  Context {E C: Type -> Type} {X S: Type} {HasStuck: B0 -< C} {h: Handler E S}.
  Notation SP := (ctree E C X -> S -> Prop).
  
  Lemma ctl_ret_au_inv: forall x s (p q: S -> Prop),
      <( {Ret x: ctree E C X}, s |= (now p) AU (now q) )> -> p s \/ q s.
  Proof.
    intros.
    step in H; [now right | now left].
  Qed.

  Lemma ctl_bind_au_inv: forall p q (t: ctree E C X) (s: S) (k: X -> ctree E C X),
      <( {x <- t ;; k x}, s |= (now p) AU (now q) )> ->
      <( t,s |= (now p) AU (ret {fun x s => <( {k x}, s |= (now p) AU (now q) )>}) )> \/
        <( t,s |= (now p) AU (now q) )>.
  Proof.
    intros.
    unfold entails in H.
    inv H.
    - admit.
    - admit.
  Admitted.
End UsefulLemmas.

(* Examples *)
From CTree Require Import
     FoldStateT.

Module Experiments.

  Import CTree CTreeNotations CtlNotations.
  Local Open Scope ctl_scope.

  (* Dummy program *)
  Definition dummy_23 : ctree (stateE nat) B0 unit :=
    put 2 ;;
    put 3.

  (* Why ctl_of_State did not register? Nvm, it's too general... *)
  Print Coercions.
  Section COERC.
    Context {C: Type -> Type} {X: Type}.
    Notation SP := (ctree (stateE nat) C X -> nat -> Prop).
    Definition ctl_of_State (s: nat): SP := nowS (fun x => x = s).
    Arguments ctl_of_State /.
    Coercion ctl_of_State : nat >-> Funclass.
  End COERC.

  Lemma writes_23: forall s,
      <( dummy_23, s |= AX 2 /\ (AX (AX 3)) )>.
  Proof.
    unfold dummy_23.
    split.
    - step.
      apply ktrans_trigger_inv in TR as ([] & ? & ->).
      cbn; auto.
    - step.  
      apply ktrans_trigger_inv in TR as ([] & ? & ->).
      rewrite H in *; clear H.
      apply ktrans_vis_inv in TR0 as ([] & -> & ->).
      cbn; auto.
  Qed.      

  Context {E C: Type -> Type} {X S: Type} {HasStuck: B0 -< C} {h: Handler E S}.
  Definition stuck: ctree E C X := stuckD.
    
  Ltac shallow_inv_trans H1 := unfold trans,transR in H1; cbn in H1; dependent destruction H1.
  
  Lemma is_stuck_ax: forall (s: S),
      <( stuck, s |= (AX False) )>.
  Proof.
    unfold cimpl, ax, entails. intros.
    inv H.
    1,2: shallow_inv_trans H1; contradiction.
    all: shallow_inv_trans H3; contradiction. 
  Qed.

  (* Terminating [ret x] programs *)
  Definition put2: ctree (stateE nat) C unit := put 2.
  
  Lemma maybebad: forall n,
      <( put2, n |= AF 3 )>.
  Proof.
    unfold entails.
    right; eauto.
    intros.
    inv H.
    - shallow_inv_trans H1.
    - apply trans_vis_inv in H1 as ([] & ? & ?).
      dependent destruction H0.
      cbn.
      rewrite H.
      (* Ret tt *)
      right; eauto.
      intros; clear H t'.
      apply ktrans_ret in H0 as (-> & <-).
      apply StepA; auto.
      intros.
      (* Same [Ret tt] as before, and it will keep being [Ret tt] *)
   Abort.

  Lemma maybegood: forall n,
      <( put2, n |= AF 2 )>.
  Proof.
    unfold entails.
    right; eauto.
    intros.
    inv H.
    - shallow_inv_trans H1.
    - apply trans_vis_inv in H1 as ([] & ? & ?).
      dependent destruction H0.      
      rewrite H.
      left; cbn.
      trivial.
    - inv H3.
  Qed.
  
  Lemma maybegood': 
    <( put2, 2 |= AG 2 )>.
  Proof.
    unfold entails.
    apply ctl_ag_ax; split.
    - trivial.
    - unfold put2; step.
      apply ktrans_vis_inv in TR as ([] & -> & ->).
      cbn.
      coinduction R CIH.
      econstructor; trivial.
      intros.
      apply ktrans_ret in H as (-> & <-).
      apply CIH.
      auto.
  Qed.

  Lemma maybegood'': 
    ~ <( put2, 2 |= AG 3 )>.
  Proof.
    unfold entails.
    unfold not.
    intro CONTRA.
    step in CONTRA; inv CONTRA.
    inv H.
  Qed.

  Lemma ag_forever': forall (t: ctree E C X) (s: S) p {HasTau: B1 -< C},
      <( t, s |= now p )> -> <( {forever t: ctree E C X},s |= AG now p )>.
  Proof.
    unfold entails; intros; coinduction R CIH.
    - econstructor.
      rewrite unfold_forever.

  Admitted.

End Experiments.

