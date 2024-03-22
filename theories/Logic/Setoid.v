(*|
=================================================
Congruence [general] and specialized to [equ eq]
=================================================
|*)
From Coq Require Import
  Basics
  Classes.SetoidClass
  Classes.Morphisms.

From Coinduction Require Import
  coinduction lattice tactics.

From CTree Require Import
  Utils.Utils
  Events.Core
  Logic.Kripke
  Logic.Semantics
  Logic.Tactics.

Import CtlNotations.
Local Open Scope ctl_scope.
Local Open Scope type_scope.

Generalizable All Variables.

(*| Relation [meq] over [M X] is a Kripke setoid if
    the following square commutes

   [s, w]   ↦   [s', w']
     |             |
   meq s t     exists t', meq s' t'
     |             |
     v             v
   [t, w]   ↦   [t', w']
|*)  
Class KripkeSetoid M W {HW: Encode W} {K: Kripke M W}
  X (meq: relation (M X)) {Eqm: Equivalence meq} :=
  ktrans_semiproper : forall (t s s': M X) w w',
    meq s t ->
    ktrans s w s' w' ->
    exists t', ktrans t w t' w' /\ meq s' t'.

Ltac ktrans_equ TR :=
    match type of TR with
      | @ktrans ?M ?E ?HE ?KMS ?X ?y ?s ?z ?w =>
          match goal with
          | [HS: KripkeSetoid ?M ?W ?X ?meq, 
                H: ?meq ?y ?x |- _] => 
              symmetry in H;
              let TR_ := fresh "TR" in
              let EQ_ := fresh "EQ" in
              let z_ := fresh "z" in
              destruct (ktrans_semiproper _ _ _ _ _
                          H TR) as (z_ & TR_ & EQ_)
          | [HS: KripkeSetoid ?M ?W ?X ?meq,
                H: ?meq ?x ?y |- _] =>
              let TR_ := fresh "TR" in
              let EQ_ := fresh "EQ" in
              let z_ := fresh "z" in
              destruct (ktrans_semiproper _ _ _ _ _ H TR) as (z_ & TR_ & EQ_)
          end
    end.

(*| Models are setoids over CTL |*)
Section EquivSetoid.
  Context `{HW: Encode W} {M: Type -> Type} {K: Kripke M W}
    {X} {meq: relation (M X)} {Eqm: Equivalence meq}
    {KS: KripkeSetoid M W X meq}.

  Notation MP := (M X -> World W -> Prop).
  Notation equiv_ctl := (equiv_ctl (K:=K) (X:=X)).

  Global Add Parametric Morphism: can_step
    with signature meq ==> eq ==> iff as proper_can_step.
  Proof.
    intros t t' Heqt w;
      split; intros; subst; destruct H as (t_ & w_ & ?).
    - destruct (ktrans_semiproper t' t _ _ w_ Heqt H) as (y' & TR' & EQ').
      now (exists y', w_).
    - symmetry in Heqt.
      destruct (ktrans_semiproper _ _ _ _ w_ Heqt H) as (y' & TR' & EQ').
      now (exists y', w_).
  Qed.

  (*| Start building the proof that
      [entailsF] is a congruence with regards to [meq] |*)
  Global Add Parametric Morphism {φ: World W -> Prop}: (fun _ => φ)
      with signature meq ==> eq ==> iff as fun_proper_now.
  Proof. intros; split; auto. Qed.
  
  Global Add Parametric Morphism p : <( |- {CBase p} )>
        with signature meq ==> eq ==> iff as now_proper_equ.
  Proof.
    unfold entailsF; intros; eapply fun_proper_now; eauto.
  Qed.

  Context {P: MP} {HP: Proper (meq ==> eq ==> iff) P}.
  Global Add Parametric Morphism: (cax P)
         with signature (meq ==> eq ==> iff) as proper_ax_equ.
  Proof.
    intros x y Heqt w; split; intros [Hs HN]. 
    - split; [now rewrite <- Heqt|].
      intros u z TR.
      ktrans_equ TR.
      apply HN in TR0.
      now rewrite EQ.
    - split; [now rewrite Heqt|].
      intros u z TR.
      ktrans_equ TR.
      apply HN in TR0.
      now rewrite EQ.
  Qed.      
    
  Global Add Parametric Morphism: (cex P)
         with signature (meq ==> eq ==> iff) as proper_ex_equ.
  Proof.
    intros x y Heqt w; split; intros (x' & z & TR & HP').  
    all: ktrans_equ TR;
      exists z0,z; split; [| rewrite <- EQ]; auto.
  Qed.

  Context {Q: MP} {HQ: Proper (meq ==> eq ==> iff) Q}.
  Global Add Parametric Morphism: (cau P Q)
        with signature (meq ==> eq ==> iff) as proper_au_equ.
  Proof.
    intros x y EQ; split; intros * au.
    (* -> *)
    - generalize dependent y.
      induction au; intros y EQ.
      + rewrite EQ in H; now apply MatchA.
      + eapply StepA; try now rewrite <- EQ.
        destruct H0, H1; split; [ now rewrite <- EQ|].
        intros y' w' TR.
        ktrans_equ TR.
        eapply H3; [apply TR0|].
        now symmetry.
    (* <- *)
    - generalize dependent x.
      induction au; intros x EQ.
      + rewrite <- EQ in H; now apply MatchA.
      + eapply StepA; try now rewrite EQ.
        destruct H0, H1; split; [now rewrite EQ|].
        intros x' w' TR.
        ktrans_equ TR.
        eapply H3; [apply TR0|].
        now symmetry.
  Qed.

  Global Add Parametric Morphism: (ceu P Q)
        with signature (meq ==> eq ==> iff) as proper_eu_equ.
  Proof.
    intros x y EQ; split; intro eu.
    (* -> *)
    - generalize dependent y.
      induction eu; intros.    
      + rewrite EQ in H; now apply MatchE.
      + eapply StepE.
        * now rewrite <- EQ.
        * destruct H1 as (t1 & w1 & TR1 & EQ1).
          destruct H0 as (t0 & w0 & TR0 & ?).
          ktrans_equ TR1.
          exists z, w1; auto.
    - generalize dependent x.
      induction eu; intros.
      + rewrite <- EQ in H; now apply MatchE.
      + eapply StepE.
        * now rewrite EQ.
        * destruct H1 as (t1 & w1 & TR1 & EQ1).
          destruct H0 as (t0 & w0 & TR0 & ?).
          ktrans_equ TR1.
          exists z, w1; split; eauto.
          apply EQ1; symmetry; auto.
  Qed.
    
  (*| [meq] closure enchancing function |*)
  Variant mequ_clos_body(R : MP -> MP -> MP) : MP -> MP -> MP :=
    | mequ_clos_ctor : forall t0 w0 t1 w1
                         (Heqm : meq t0 t1)
                         (Heqw : w0 = w1)
                         (HR : R P Q t1 w1),
        mequ_clos_body R P Q t0 w0.
  Hint Constructors mequ_clos_body: core.

  Arguments impl /.
  Program Definition mequ_clos: mon (MP -> MP -> MP) :=
    {| body := mequ_clos_body |}.
  Next Obligation. repeat red; intros; destruct H0; subst; eauto. Qed.

  Lemma mequ_clos_car:
    mequ_clos <= cart.
  Proof.
    apply Coinduction; cbn.
    intros R p q t0 w0 [t1 w1 t2 w2 Heq -> ?];  inv HR. 
    - apply RMatchA; now rewrite Heq.
    - apply RStepA; intros.
      + now rewrite Heq. 
      + unfold cax; destruct H0 as [Hsm2 TR2]; split; cbn; cbn in Hsm2.
        * now rewrite Heq. 
        * intros t' w' TR.
          eapply (f_Tf car_). 
          ktrans_equ TR.
          eapply mequ_clos_ctor with (t1:=z); eauto. 
  Qed.

  Lemma mequ_clos_cer:
    mequ_clos <= cert.
  Proof.    
    apply Coinduction; cbn.
    intros R p q t0 w0 [t1 w1 t2 w2 Heq -> ?]; inv HR. 
    - apply RMatchE; now rewrite Heq. 
    - destruct H0 as (t' & w' & TR2 & ?).
      apply RStepE.
      + now rewrite Heq.
      + ktrans_equ TR2.
        exists z, w'; split; auto. 
        eapply (f_Tf cer_).       
        eapply mequ_clos_ctor with (t1:=t') (w1:=w'); eauto.
        now symmetry.
  Qed.

  Global Add Parametric Morphism RR: (cart RR P Q) with signature
         (meq ==> eq ==> iff) as proper_art_equ.
  Proof.
    intros t t' Heqm w'; split; intro G; apply (ft_t mequ_clos_car).
    - eapply mequ_clos_ctor with (t1:=t); eauto.
      now symmetry.
    - eapply mequ_clos_ctor with (t1:=t'); eauto.
  Qed.
  
  Global Add Parametric Morphism RR f: (carT f RR P Q)
         with signature (meq ==> eq ==> iff) as proper_arT_equ.
  Proof.
    intros t t' Heqt w'; split; intro G; apply (fT_T mequ_clos_car).
    - eapply mequ_clos_ctor with (t1:=t); eauto.
      now symmetry.
    - eapply mequ_clos_ctor with (t1:=t'); eauto.
  Qed.
  
  Global Add Parametric Morphism: (car P Q)
         with signature (meq ==> eq ==> iff) as proper_ar_equ.
  Proof.
    intros t t' Heqt w'; split; intro G; apply (ft_t mequ_clos_car).
    - eapply mequ_clos_ctor with (t1:=t); eauto.
      now symmetry.
    - eapply mequ_clos_ctor with (t1:=t'); eauto.
  Qed.      

  Global Add Parametric Morphism RR: (cert RR P Q)
         with signature (meq ==> eq ==> iff) as proper_ert_equ.
  Proof.
    intros t t' Heqt w'; split; intro G; apply (ft_t mequ_clos_cer).
    - eapply mequ_clos_ctor with (t1:=t); eauto.
      now symmetry.
    - eapply mequ_clos_ctor with (t1:=t'); eauto.
  Qed.

  Global Add Parametric Morphism RR f: (cerT f RR P Q)
         with signature (meq ==> eq ==> iff) as proper_erT_equ.
  Proof.
    intros t t' Heqt w'; split; intro G; apply (fT_T mequ_clos_cer).
    - eapply mequ_clos_ctor with (t1:=t); eauto.
      now symmetry.
    - eapply mequ_clos_ctor with (t1:=t'); eauto.
  Qed.
  
  Global Add Parametric Morphism: (cer P Q)
         with signature (meq ==> eq ==> iff) as proper_er_equ.
  Proof.
    intros t t' Heqt w'; split; intro G; apply (ft_t mequ_clos_cer).
    - eapply mequ_clos_ctor with (t1:=t); eauto.
      now symmetry.
    - eapply mequ_clos_ctor with (t1:=t'); eauto.
  Qed.
End EquivSetoid.

Global Add Parametric Morphism `{KS: KripkeSetoid M W X meq} φ : <( |- φ )>
       with signature (meq ==> eq  ==> iff) as proper_entailsF_.
Proof.
  induction φ; intros * Heq w. 
  - (* Now *) rewrite Heq; reflexivity.
  - (* /\ *) split; intros [Ha Hb]; split.
    + now rewrite <- (IHφ1 _ _ Heq).
    + now rewrite <- (IHφ2 _ _ Heq).
    + now rewrite (IHφ1 _ _ Heq).
    + now rewrite (IHφ2 _ _ Heq).
  - (* \/ *) split; intros [H' | H']. 
    + now left; rewrite <- (IHφ1 _ _ Heq).
    + now right; rewrite <- (IHφ2 _ _ Heq).
    + now left; rewrite (IHφ1 _ _ Heq).
    + now right; rewrite (IHφ2 _ _ Heq).
  - (* -> *)
    split; intros; cbn; intro HI;
      apply (IHφ1 _ _ Heq) in HI;
      apply (IHφ2 _ _ Heq); auto.
  - (* ax *)
    refine (@proper_ax_equ W HW M K X meq Eqm KS (entailsF φ) _ _ _ Heq _ _ eq_refl).
    unfold Proper, respectful; intros; subst; now apply IHφ.
  - (* ex *)
    refine (@proper_ex_equ W HW M K X meq Eqm KS (entailsF φ) _ _ _ Heq _ _ eq_refl).
    unfold Proper, respectful; intros; subst; now apply IHφ.
  - (* au *)
    refine (@proper_au_equ W HW M K X meq Eqm KS (entailsF φ1) _ (entailsF φ2) _ _ _ Heq _ _ eq_refl);
      unfold Proper, respectful; intros; subst; auto.
  - (* eu *)
    refine (@proper_eu_equ W HW M K X meq Eqm KS (entailsF φ1) _ (entailsF φ2) _ _ _ Heq _ _ eq_refl);
      unfold Proper, respectful; intros; subst; auto.
  - (* ar *)
    refine (@proper_ar_equ W HW M K X meq Eqm KS (entailsF φ1) _ (entailsF φ2) _ _ _ Heq _ _ eq_refl);
      unfold Proper, respectful; intros; subst; auto.
  - (* er *)
    refine (@proper_er_equ W HW M K X meq Eqm KS (entailsF φ1) _ (entailsF φ2) _ _ _ Heq _ _ eq_refl);
      unfold Proper, respectful; intros; subst; auto.
Qed.
