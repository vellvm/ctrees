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

(* WHY this loops during instance resolution *)
#[global] Instance Handler_plus{E F: Type -> Type}{S T}
 (h: Handler E S) (g: Handler F T) : Handler (E+'F) (S*T) :=
  {|
    hfold _ ef x '(s,t) := 
    match ef with
    | inl1 e => (h.(hfold) e x s, t)
    | inr1 f => (s, g.(hfold) f x t)
    end
  |}.

Section Kripke.
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
    ktrans (t, s) (u, h.(hfold) e x s)
  (* LEF: [t] could be any [brD ... (ret x)] chain *)
  | kRet (t u: ctree E C X) (x: X) (s: S):
    u ≅ t ->
    trans (val x) t stuckD ->
    ktrans (t, s) (u, s). 

  Hint Constructors ktrans: core.

  #[global] Instance proper_ktrans_equ:
    Proper (equ eq * eq ==> equ eq * eq ==> iff) ktrans.
  Proof.
    unfold Proper, respectful, impl; cbn.
    intros [t s] [u x] [EQt ?] [t' s'] [u' x'] [EQt' H3]; simpl in *.
    unfold RelCompFun in *; cbn in *; subst.    
    split; intro H; inv H.
    - rewrite EQt, EQt' in H1.
      now apply kTau.
    - rewrite EQt, EQt' in H1.
      now apply kVis.
    - rewrite <- H3 in H5. 
      eapply kRet;
        [now rewrite <- EQt, <- EQt' |
          rewrite <- EQt, <- H3; eassumption].
    - rewrite <- EQt, <- EQt' in H1.
      now apply kTau.
    - rewrite <- EQt, <- EQt' in H1.
      now apply kVis.
    - rewrite <- H3 in H5. 
      eapply kRet;
        [now rewrite EQt, EQt' |
          rewrite EQt, <- H3; eassumption].
  Qed.

  Lemma trans_val_sbisim: forall (t u: ctree E C X) (x: X),
      trans (val x) t stuckD ->
      t ~ u ->
      trans (val x) u stuckD.
  Proof.
    intros.
    remember (val x) as l.
    induction H; intros; eauto; try solve [inv Heql].
    (* Ah lost [observe t] *)
  Admitted.

  Lemma ktrans_sbisim_l: forall (t1 t2 t1': ctree E C X) s s',
      ktrans (t1,s) (t1',s') ->
      t1 ~ t2 ->
      exists t2', ktrans (t2,s) (t2',s') /\ t1' ~ t2'.
  Proof.
    intros * TR  Hsb.
    inv TR; intros.
    1,2: step in Hsb; apply Hsb in H0 as (l2 & t2' & TR2 & ? & <-); exists t2'; split; eauto.
    exists t2; rewrite H2; split; eauto.
    apply kRet with x; [reflexivity|].
    now apply trans_val_sbisim with (u:=t2) in H4.
  Qed.

End Kripke.

(*| CTL logic based on kripke semantics of ctrees |*)
Section Ctl.
  
  Context {E C: Type -> Type} {X S: Type}
          {h: Handler E S} {HasStuck: B0 -< C}.
  Notation SP := (ctree E C X -> S -> Prop).
  
  (* Lift label predicates to SP *)
  Definition now(p: S -> Prop): SP :=
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
    Definition ctl_of_Prop (P : Prop) : SP := now (fun (_: S) => P).
    Definition ctl_of_State (s: S): SP := now (fun (x: S) => x = s).
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
  Notation "'EX' p" := (ex p) (in custom ctl at level 75): ctl_scope.
  Notation "'AX' p" := (ax p) (in custom ctl at level 75): ctl_scope.
  Notation "p 'EU' q" := (eu p q) (in custom ctl at level 75): ctl_scope.
  Notation "p 'AU' q" := (au p q) (in custom ctl at level 75): ctl_scope.
  Notation "'EF' p" := (eu True p) (in custom ctl at level 75): ctl_scope.
  Notation "'AF' p" := (au True p) (in custom ctl at level 75): ctl_scope.
  Notation "'EG' p" := (eg p) (in custom ctl at level 75): ctl_scope.
  Notation "'AG' p" := (ag p) (in custom ctl at level 75): ctl_scope.

  (* Propositional *)
  Notation "p '/\' q" := (cand p q) (in custom ctl at level 78, left associativity): ctl_scope.
  Notation "p '\/' q" := (cor p q) (in custom ctl at level 78, left associativity): ctl_scope.
  Notation "p '->' q" := (cimpl p q) (in custom ctl at level 79, right associativity): ctl_scope.
  Notation "p '<->' q" := (cand (cimpl p q) (cimpl q p))
                            (in custom ctl at level 78): ctl_scope.

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
#[global] Hint Unfold cand cor cimpl ax ex now: core.
Arguments entails /.
Arguments cand /.
Arguments cor /.
Arguments cimpl /.
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

Section Congruences.
  Local Open Scope ctl_scope.
  Context {E C: Type -> Type} {X S: Type} {HasStuck: B0 -< C} {h: Handler E S}.

  Notation SP := (ctree E C X -> S -> Prop).

  (*| [now] ignores trees and only looks at labels |*)
  #[global] Instance proper_now: forall (p: S -> Prop) R,
      Proper (R ==> eq ==> iff) (@now E C X S p).
  Proof.
    unfold Proper, respectful, impl; cbn.      
    intros p R x y EQ ? l <-; split; unfold now; auto. 
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
End Congruences.

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

  (* Why ctl_of_State did not register? *)
  Print Coercions.
  Section COERC.
    Context {C: Type -> Type} {X: Type}.
    Notation SP := (ctree (stateE nat) C X -> nat -> Prop).
    Definition ctl_of_State (s: nat): SP := now (fun x => x = s).
    Arguments ctl_of_State /.
    Coercion ctl_of_State : nat >-> Funclass.
  End COERC.

  Lemma writes_23: forall s,
      <( dummy_23, s |= AX 2 /\ (AX (AX 3)) )>.
  Proof.
    split;unfold dummy_23; unfold ax, ctl_of_State, now; intros; inv H.
    - inv H1. 
    - apply trans_trigger_inv in H1 as (? & ? & ?).
      dependent destruction H0.
      reflexivity.
    - inv H5.
    - inv H2.
    - apply trans_trigger_inv in H2 as ([] & ? & ?).
      dependent destruction H1; cbn in *.
      rewrite H in H0.
      inv H0.
      + inv H2.
      + apply trans_vis_inv in H2 as ([] & ? & ?).
        dependent destruction H1.
        reflexivity.
      + inv H6.
    - inv H6.
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
    all: shallow_inv_trans H5; contradiction. 
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
      inv H0; try solve [inv H1].
      (* Same [Ret tt] as before, and it will keep being [Ret tt] *)
      right; eauto; intros; rewrite H3 in *; destruct x; clear H3 t'0.
      inv H; try solve [inv H0]; right; eauto; intros.
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
    - inv H5.
  Qed.
  
  Lemma maybegood': 
    <( put2, 2 |= AG 2 )>.
  Proof.
    unfold entails.
    apply ctl_ag_ax; split.
    - trivial.
    - unfold ax; intros.
      inv H; try solve [inv H1].
      + shallow_inv_trans H1; cbn; apply observe_equ_eq in x; rewrite <- x, <- H; clear H x t'.
        coinduction R CIH.
        econstructor; trivial.
        * intros.
          inv H; repeat shallow_inv_trans H1.
          rewrite H3.
          apply CIH.
      + inv H5.
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
  
  (* Useful equivalences *)

  Lemma ag_bind: forall (t: ctree E C X) (s: S) (k: X -> ctree E C X) (x: X) p,
      <( t,s |= AG p )> /\ <( {k x}, s |= AG p )> ->
      <( { x <- t ;; k x }, s |= AG p )>.
  Proof.
    unfold entails; intros * (? & ?).
    coinduction R CIH.
    split.
    - unfold now; cbn.

  Admitted.
  
  Lemma ag_forever: forall (t: ctree E C X) (s: S) p {HasTau: B1 -< C}
                      {HP: Proper (sbisim eq ==> eq ==> iff) p},
      <( t, s |= AG p )> <-> <( {forever t},s |= AG p )>.
  Proof.
    unfold entails; split; intros. 
    - apply ctl_ag_ax in H; destruct H.
      rewrite unfold_forever.
      
      unfold ax in H0.
      apply ctl_ag_ax; split.
      rewrite <- unfold_forever.

      (* Hm looks unlikely *)
  Admitted.

  Lemma ag_forever': forall (t: ctree E C X) (s: S) p {HasTau: B1 -< C},
      <( t, s |= {now p} )> -> <( {forever t: ctree E C X},s |= AG {now p} )>.
  Proof.
    unfold entails; intros; coinduction R CIH.
    - econstructor.
      rewrite unfold_forever.

  Admitted.

End Experiments.

