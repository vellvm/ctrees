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
     FoldStateT.

From Coq Require Import
     Classes.SetoidClass
     Classes.RelationPairs.

Set Implicit Arguments.
Typeclasses eauto := 6.

(* From ctree labels to kripke states *)
Class Handler (E: Type -> Type) (S: Type) := {
    hfold: forall X, E X -> X -> S -> S;
  }.

#[global] Instance Handler_state S: Handler (stateE S) S :=
  {|
    hfold _ e _ s :=
    match e with
    | Put s => s
    | Get _ => s
    end
  |}.

#[global] Instance Handler_par: Handler parE nat := 
  {| hfold _ e _ s := match e with Switch i => i end |}.

(* LEF: Why does this loop [cequiv]? *)
#[global] Instance Handler_plus{E F: Type -> Type}{S T}
 (h: Handler E S) (g: Handler F T) : Handler (E+'F) (S*T) :=
  {|
    hfold _ ef x '(s,t) := 
    match ef with
    | inl1 e => (h.(hfold) e x s, t)
    | inr1 f => (s, g.(hfold) f x t)
    end
  |}.



Section Ctl.
  Context {E C: Type -> Type} {X S: Type}
          {h: Handler E S} {HasStuck: B0 -< C}.

  (* Kripke state predicates *)
  Notation SP := (ctree E C X -> S -> Prop).
    
  (* Kripke transition given a handler *)
  Inductive ktrans: (ctree E C X * S) -> (ctree E C X * S) -> Prop :=
  | kTau (t u: ctree E C X) (s: S):
    trans tau t u ->
    ktrans (t, s) (u, s)
  | kVis (t u: ctree E C X) {Y} (x: Y) (e: E Y) (s: S):
    trans (obs e x) t u ->
    ktrans (t, s) (u, h.(hfold) e x s).

  (* Lift label predicates to SP *)
  Definition lift(p: S -> Prop): SP :=
    fun _ s => p s.
  
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
    Definition ctl_of_Prop (P : Prop) : SP := lift (fun (_: S) => P).
    Definition ctl_of_State (s: S): SP := lift (fun (x: S) => x = s).
    Coercion ctl_of_Prop : Sortclass >-> Funclass. 
    Coercion ctl_of_State : S >-> Funclass.
  End SC.
  
  Notation "<( e )>" := e (at level 0, e custom ctl at level 99) : ctl_scope.
  Notation "( x )" := x (in custom ctl, x at level 99) : ctl_scope.
  Notation "x" := x (in custom ctl at level 0, x constr at level 0) : ctl_scope.
  Notation "t , s |= p " := (entails p t s) (in custom ctl at level 99, p custom ctl,
                                                right associativity): ctl_scope.
  (* Temporal *)
  Notation "'EX' p" := (ex p) (in custom ctl at level 70): ctl_scope.
  Notation "'AX' p" := (ax p) (in custom ctl at level 70): ctl_scope.
  Notation "p 'EU' q" := (eu p q) (in custom ctl at level 70): ctl_scope.
  Notation "p 'AU' q" := (au p q) (in custom ctl at level 70): ctl_scope.
  Notation "'EF' p" := (eu True p) (in custom ctl at level 70): ctl_scope.
  Notation "'AF' p" := (au True p) (in custom ctl at level 70): ctl_scope.
  Notation "'EG' p" := (eg p) (in custom ctl at level 70): ctl_scope.
  Notation "'AG' p" := (ag p) (in custom ctl at level 70): ctl_scope.

  (* Propositional *)
  Notation "p '/\' q" := (cand p q) (in custom ctl at level 89, left associativity): ctl_scope.
  Notation "p '\/' q" := (cor p q) (in custom ctl at level 89, left associativity): ctl_scope.
  Notation "p '->' q" := (cimpl p q) (in custom ctl at level 99, right associativity): ctl_scope.
  Notation "p '<->' q" := (cand (cimpl p q) (cimpl q p))
                            (in custom ctl at level 99, right associativity): ctl_scope.

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
  Notation "[ 'AG' ] p" := (ag_ p _) (in custom ctl at level 70, p custom ctl): ctl_scope.
  Notation "[ 'EG' ] p" := (eg_ p _) (in custom ctl at level 70, p custom ctl): ctl_scope.
  
  Notation "[[ 'AG' ]] p" := (agF p _) (in custom ctl at level 70, p custom ctl): ctl_scope.
  Notation "[[ 'EG' ]] p" := (egF p _) (in custom ctl at level 70, p custom ctl): ctl_scope.
  
  Notation "{ 'AG' } p" := (agt p _) (in custom ctl at level 70, p custom ctl): ctl_scope.
  Notation "{ 'EG' } p" := (egt p _) (in custom ctl at level 70, p custom ctl): ctl_scope.
  
  Notation "{{ 'AG' }} p" := (agbt p _) (in custom ctl at level 70, p custom ctl): ctl_scope.
  Notation "{{ 'EG' }} p" := (egbt p _) (in custom ctl at level 70, p custom ctl): ctl_scope.
  
End CtlNotations.
  
Import CtlNotations.

#[global] Hint Constructors eu au: core.
#[global] Hint Unfold ax ex lift: core.
Arguments lift /.
Arguments ax /.
Arguments ex /.
Arguments agF /.
Arguments egF /.

(*| Tactics |*)
Ltac fold_g :=
  repeat
    match goal with
    | h: context[@ag_ ?E ?C ?S ?X ?h ?HS ?R ] |- _ => fold (@ag E C S X h HS R) in h
    | |- context[@ag_ ?E ?C ?S ?X ?h ?HS ?R ]      => fold (@ag E C S X h HS R)
    | h: context[@eg_ ?E ?C ?S ?X ?h ?HS ?R ] |- _ => fold (@eg E C S X h HS R) in h
    | |- context[@eg_ ?E ?C ?S ?X ?h ?HS ?R ]      => fold (@eg E C S X h HS R)
    end.

Check @ag.
#[local] Tactic Notation "__step_g" :=
  match goal with
  | |- context[@ag ?E ?C ?S ?X ?h ?HasStuck ?p ?t ?q] =>
      unfold ag;
      step;
      fold (@ag E C S X h HasStuck p t q)
  | |- context[@eg ?E ?C ?S ?X ?h ?HasStuck ?p ?t ?q] =>
      unfold eg;
      step;
      fold (@eg E C S X h HasStuck p t q)
  | |- _ => step
  end.

#[local] Ltac __step_in_g H :=
  match type of H with
  | context [@ag ?E ?C ?S ?X ?h ?HasStuck ] =>
      unfold ag in H;
      step in H;
      fold (@ag E C S X h HasStuck) in H
  | context [@eg ?E ?C ?S ?X ?h ?HasStuck ] =>
      unfold eg in H;
      step in H;
      fold (@eg E C S X h HasStuck) in H
  end.

#[local] Ltac __coinduction_g R H :=
  unfold ag, eg; coinduction R H; fold_g.

(** Re-export [Eq.v] tactics *)
#[global] Tactic Notation "step" :=
  __step_g || step.
#[global] Tactic Notation "coinduction" simple_intropattern(R) simple_intropattern(H) :=
  __coinduction_g R H || coinduction R H.

#[global] Tactic Notation "step" "in" ident(H) :=
  __step_in_g H || step_in H.

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
End Equivalences.

(*| Antitone functions are monotone in the dual lattice |*)
Section anti.
 Context {X} {L: CompleteLattice X}.

 (** antitone endofunctions *)
 Record anti := { inner:> X -> X; Hinner: Proper (Dual.(leq) ==> Dual.(leq)) inner }.
End anti.

Section Congruences.
  Local Open Scope ctl_scope.
  Context {E C: Type -> Type} {X S: Type} {HasStuck: B0 -< C} {h: Handler E S}.

  Notation SP := (ctree E C X -> S -> Prop).

  (*| [lift] ignores trees and only looks at labels |*)
  #[global] Instance proper_lift_equ: forall (p: S -> Prop) R,
      Proper (R ==> eq ==> iff) (@lift E C X S p).
  Proof.
    unfold Proper, respectful, impl; cbn.      
    intros p R x y EQ ? l <-; split; unfold lift; auto. 
  Qed.

  #[global] Instance proper_ktrans_equ:
    Proper (equ eq * eq ==> equ eq * eq ==> iff) (@ktrans E C X S _ _).
  Proof.
    unfold Proper, respectful, impl; cbn.
    intros [t s] [u x] [EQt ?] [t' s'] [u' x'] [EQt' H3]; simpl in *.
    unfold RelCompFun in *; cbn in *; subst.    
    split; intro H; inv H.
    - rewrite EQt, EQt' in H1.
      now apply kTau.
    - rewrite EQt, EQt' in H1.
      now apply kVis.
    - rewrite <- EQt, <- EQt' in H1.
      now apply kTau.
    - rewrite <- EQt, <- EQt' in H1.
      now apply kVis.
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

  (*| Up-to-ag enhancing function |*)
  Variant unary_equ_clos_body (R : SP) : SP :=
    | uEqu_clos : forall t t' s s'
                  (Agt : t ≅ t')
                  (HR : R t' s')
                  (Agu : s' = s),
        unary_equ_clos_body R t s.

  Program Definition unary_equ_clos: mon SP :=
    {| body := unary_equ_clos_body |}.
  Next Obligation. destruct H0; econstructor; eauto. Qed.

  Section gProper.
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
    
    #[global] Instance proper_egt_equ RR:
      Proper (@equ E C X X eq ==> eq ==> iff) (egt P RR).
    Proof.
      unfold Proper, respectful, impl; cbn.
      intros x y EQ ? l <-; split; intro G; apply (ft_t equ_clos_eg); econstructor;
        [symmetry | apply G | reflexivity | | apply G | reflexivity]; assumption.
    Qed.

    #[global] Instance proper_agT_equ RR f:
      Proper (@equ E C X X eq ==> eq ==> iff) (egT P f RR).
    Proof.
      unfold Proper, respectful, impl; cbn.
      intros x y EQ ? l <-; split; intro G; apply (fT_T equ_clos_eg); econstructor;
        [symmetry | apply G | reflexivity | | apply G | reflexivity]; assumption.
    Qed.

    #[global] Instance proper_ag_equ:
      Proper (@equ E C X X eq ==> eq ==> iff) <( EG P )>.
    Proof.
      unfold Proper, respectful, impl; cbn.
      intros x y EQ ? l <-; split; intro G; apply (ft_t equ_clos_eg); econstructor;
        [symmetry | apply G | reflexivity | | apply G | reflexivity]; assumption.
    Qed.
  End gProper.
  
End Congruences.

(* TODO: Prove guard lemmas *)
Lemma ctl_af_guard{E C X}`{B0 -< C}`{B1 -< C}: forall (t: ctree E C X) (l: @label E) p,
    Guard t, l |= AF (lift p) <-> t, l |= AF (lift p).
Proof.
  split; intros; inv H1; apply ctl_af_ax.
  - left; now unfold lift in *.
  - right; unfold ax; intros.
    apply H3.
    now apply trans_guard.
  - left; now unfold lift in *.
  - right; unfold ax; intros.
    apply trans_guard_inv in H1.
    apply H3 in H1.
    eauto.
Qed.

Lemma ctl_t_ag_af_guard{E C X}`{B0 -< C}`{B1 -< C}
      `{R: rel (ctree E C X) (@label E) -> rel (ctree E C X) (@label E)}
  : forall (x: ctree E C X) (l: @label E) p,
  Guard x, l |= ((t ag_) R (AF (lift p))) <-> x, l |= ((t ag_) R (AF (lift p))).
Proof.
Admitted.
