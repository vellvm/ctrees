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
  Logic.Semantics
  Logic.Tactics.

Import CtlNotations.
Local Open Scope ctl_scope.
Local Open Scope type_scope.

Set Implicit Arguments.
Generalizable All Variables.

(*| Equations of CTL |*)
Section MequCongruences.
  Context `{K: Kripke M mequ W} {X: Type}.
  Notation MP := (M X -> World W -> Prop).
  Notation equiv_ctl := (equiv_ctl (K:=K) (X:=X)).

  Global Instance Equivalence_equiv_ctl: Equivalence equiv_ctl.
  Proof.
    constructor.
    - intros P x; reflexivity.
    - intros P Q H' x; symmetry; auto.
    - intros P Q R H0' H1' x; etransitivity; auto.
  Defined.

  (*| [equiv_ctl] proper under [equiv_ctl] |*)
  Global Add Parametric Morphism : equiv_ctl with signature
         equiv_ctl ==> equiv_ctl ==> iff as equiv_ctl_equiv.
  Proof.
    intros p q EQpq p' q' EQpq'; split;
      intros EQpp'; split; intro BASE; cbn in *.
    - symmetry in EQpq'; apply EQpq'.
      symmetry in EQpp'; apply EQpp'.
      now apply EQpq.
    - symmetry in EQpq'; apply EQpq.
      apply EQpp'.
      now apply EQpq'.
    - apply EQpq'.
      symmetry in EQpp'; apply EQpp'.
      symmetry in EQpq; now apply EQpq.
    - apply EQpq.
      apply EQpp'.
      symmetry in EQpq'; now apply EQpq'.
  Qed.

  (*| At this point we start building the proof that [entailsF] is
    a congruence on all of its arguments.

    We first prove congruence with [mequ X * eq] for each formula separately,
    then do an induction proof on all formulas. |*)
  Global Add Parametric Morphism: (fun _ _ => False)
      with signature mequ (X:=X) ==> @eq W ==> iff as fun_proper_false.
  Proof. intros; split; contradiction. Qed.
  
  Global Add Parametric Morphism: (fun _ _ => True)
      with signature mequ (X:=X) ==> @eq W ==> iff as fun_proper_true.
  Proof. intros; split; auto. Qed.

  Global Add Parametric Morphism {φ: World W -> Prop}: (fun (t: M X) (w: World W) => φ w)
      with signature mequ (X:=X) ==> eq ==> iff as fun_proper_equ.
  Proof.
    intros; split; intros; auto.
  Qed.

  Global Add Parametric Morphism (p: World W -> Prop): <( |- {CBase p} )>
        with signature mequ (X:=X) ==> eq ==> iff as now_proper_equ.
  Proof. unfold entailsF; intros; eapply fun_proper_equ; eauto. Qed.

  Context {P: MP} {HP: Proper (mequ (X:=X) ==> eq ==> iff) P} {strong: bool}.
  Global Add Parametric Morphism: (cax strong P)
         with signature (mequ (X:=X) ==> eq ==> iff) as proper_ax_equ.
  Proof.
    intros x y Heqt w; split; intros [Hs HN]; destruct strong.
    - split; [now rewrite <- Heqt|].
      intros u z TR.
      ktrans_equ TR.
      apply HN in TR0.
      now rewrite EQ.
    - split; trivial. 
      intros u z TR.
      ktrans_equ TR.
      apply HN in TR0.
      now rewrite EQ.
    - split; [now rewrite Heqt|].
      intros u z TR.
      ktrans_equ TR.
      apply HN in TR0.
      now rewrite EQ.
    - split; trivial.
      intros u z TR.
      ktrans_equ TR.
      apply HN in TR0.
      now rewrite EQ.
  Qed.      
    
  Global Add Parametric Morphism: (cex P)
         with signature (mequ (X:=X) ==> eq ==> iff) as proper_ex_equ.
  Proof.
    intros x y Heqt w; split; intros (x' & z & TR & HP').  
    all: ktrans_equ TR;
      exists z0,z; split; [| rewrite <- EQ]; auto.
  Qed.

  Context {Q: MP} {HQ: Proper (mequ (X:=X) ==> eq ==> iff) Q}.
  Global Add Parametric Morphism: (cau strong P Q)
        with signature (mequ (X:=X) ==> eq ==> iff) as proper_au_equ.
  Proof.
    intros x y EQ; split; intros * au.
    (* -> *)
    - generalize dependent y.
      induction au; intros y EQ.
      + rewrite EQ in H; now apply MatchA.
      + destruct strong; eapply StepA; try now rewrite <- EQ.
        * destruct H0, H1; split; [ now rewrite <- EQ|].
          intros y' w' TR.
          ktrans_equ TR.
          eapply H3; [apply TR0|].
          now symmetry.
        * destruct H0, H1; split; trivial.
          intros y' w' TR.
          ktrans_equ TR.
          eapply H3; [apply TR0|].
          now symmetry.
    (* <- *)
    - generalize dependent x.
      induction au; intros x EQ.
      + rewrite <- EQ in H; now apply MatchA.
      + destruct strong; eapply StepA; try now rewrite EQ.
        * destruct H0, H1; split; [now rewrite EQ|].
          intros x' w' TR.
          ktrans_equ TR.
          eapply H3; [apply TR0|].
          now symmetry.
        * destruct H0, H1; split; trivial.
          intros y' w' TR.
          ktrans_equ TR.
          eapply H3; [apply TR0|].
          now symmetry.
  Qed.

  Global Add Parametric Morphism: (ceu P Q)
        with signature (mequ (X:=X) ==> eq ==> iff) as proper_eu_equ.
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
    
  (*| [mequ (X:=X) * eq] closure enchancing function |*)
  Variant mequ_clos_body(R : MP -> MP -> MP) : MP -> MP -> MP :=
    | mequ_clos_ctor : forall t0 w0 t1 w1
                         (Heqm : mequ (X:=X) t0 t1)
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
          eapply (f_Tf (car_ true)).
          ktrans_equ TR.
          eapply mequ_clos_ctor with (t1:=z);eauto. 
  Qed.

  Lemma mequ_clos_cwr:
    mequ_clos <= cwrt.
  Proof.
    apply Coinduction; cbn.
    intros R p q t0 w0 [t1 w1 t2 w2 Heq -> ?]; inv HR. 
    - apply RMatchA; now rewrite Heq.
    - apply RStepA; intros.
      + now rewrite Heq. 
      + unfold cax; destruct H0 as [Hsm2 TR2]; split; cbn; cbn in Hsm2.
        * trivial.
        * intros t' w' TR.
          eapply (f_Tf (car_ false)).
          ktrans_equ TR.
          eapply mequ_clos_ctor with (t1:=z);eauto. 
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
         (mequ (X:=X) ==> eq ==> iff) as proper_art_equ.
  Proof.
    intros t t' Heqm w'; split; intro G; apply (ft_t mequ_clos_car).
    - eapply mequ_clos_ctor with (t1:=t); eauto.
      now symmetry.
    - eapply mequ_clos_ctor with (t1:=t'); eauto.
  Qed.
  
  Global Add Parametric Morphism RR f: (carT f RR P Q)
         with signature (mequ (X:=X) ==> eq ==> iff) as proper_arT_equ.
  Proof.
    intros t t' Heqt w'; split; intro G; apply (fT_T mequ_clos_car).
    - eapply mequ_clos_ctor with (t1:=t); eauto.
      now symmetry.
    - eapply mequ_clos_ctor with (t1:=t'); eauto.
  Qed.
  
  Global Add Parametric Morphism: (car P Q)
         with signature (mequ (X:=X) ==> eq ==> iff) as proper_ar_equ.
  Proof.
    intros t t' Heqt w'; split; intro G; apply (ft_t mequ_clos_car).
    - eapply mequ_clos_ctor with (t1:=t); eauto.
      now symmetry.
    - eapply mequ_clos_ctor with (t1:=t'); eauto.
  Qed.      

  Global Add Parametric Morphism RR: (cwrt RR P Q) with signature
         (mequ (X:=X) ==> eq ==> iff) as proper_wrt_equ.
  Proof.
    intros t t' Heqt w'; split; intro G; apply (ft_t mequ_clos_cwr).
    - eapply mequ_clos_ctor with (t1:=t); eauto.
      now symmetry.
    - eapply mequ_clos_ctor with (t1:=t'); eauto.
  Qed.
  
  Global Add Parametric Morphism RR f: (cwrT f RR P Q)
         with signature (mequ (X:=X) ==> eq ==> iff) as proper_wrT_equ.
  Proof.
    intros t t' Heqt w'; split; intro G; apply (fT_T mequ_clos_cwr).
    - eapply mequ_clos_ctor with (t1:=t); eauto.
      now symmetry.
    - eapply mequ_clos_ctor with (t1:=t'); eauto.
  Qed.
  
  Global Add Parametric Morphism: (cwr P Q)
         with signature (mequ (X:=X) ==> eq ==> iff) as proper_wr_equ.
  Proof.
    intros t t' Heqt w'; split; intro G; apply (ft_t mequ_clos_cwr).
    - eapply mequ_clos_ctor with (t1:=t); eauto.
      now symmetry.
    - eapply mequ_clos_ctor with (t1:=t'); eauto.
  Qed.
  
  Global Add Parametric Morphism RR: (cert RR P Q)
         with signature (mequ (X:=X) ==> eq ==> iff) as proper_ert_equ.
  Proof.
    intros t t' Heqt w'; split; intro G; apply (ft_t mequ_clos_cer).
    - eapply mequ_clos_ctor with (t1:=t); eauto.
      now symmetry.
    - eapply mequ_clos_ctor with (t1:=t'); eauto.
  Qed.

  Global Add Parametric Morphism RR f: (cerT f RR P Q)
         with signature (mequ (X:=X) ==> eq ==> iff) as proper_erT_equ.
  Proof.
    intros t t' Heqt w'; split; intro G; apply (fT_T mequ_clos_cer).
    - eapply mequ_clos_ctor with (t1:=t); eauto.
      now symmetry.
    - eapply mequ_clos_ctor with (t1:=t'); eauto.
  Qed.
  
  Global Add Parametric Morphism: (cer P Q)
         with signature (mequ (X:=X) ==> eq ==> iff) as proper_er_equ.
  Proof.
    intros t t' Heqt w'; split; intro G; apply (ft_t mequ_clos_cer).
    - eapply mequ_clos_ctor with (t1:=t); eauto.
      now symmetry.
    - eapply mequ_clos_ctor with (t1:=t'); eauto.
  Qed.
End MequCongruences.

Global Add Parametric Morphism `{K: Kripke M mequ W} {X: Type} φ : <( |- φ )>
       with signature (mequ X ==> eq  ==> iff) as proper_entailsF_.
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
    refine (@proper_ax_equ _ mequ _ K X (entailsF φ) _ _ _ _ Heq _ _ eq_refl).
    unfold Proper, respectful; intros; subst; now apply IHφ.
  - (* wx *)
    refine (@proper_ax_equ _ mequ _ K X (entailsF φ) _ _ _ _ Heq _ _ eq_refl).
    unfold Proper, respectful; intros; subst; now apply IHφ.
  - (* ex *)
    refine (@proper_ex_equ _ mequ _ K X (entailsF φ) _ _ _ Heq _ _ eq_refl).
    unfold Proper, respectful; intros; subst; now apply IHφ.
  - (* au *)
    refine (@proper_au_equ _ mequ _ K X (entailsF φ1) _ _ (entailsF φ2) _ _ _ Heq _ _ eq_refl);
      unfold Proper, respectful; intros; subst; auto.
  - (* wu *)
    refine (@proper_au_equ _ mequ _ K X (entailsF φ1) _ _ (entailsF φ2) _ _ _ Heq _ _ eq_refl);
      unfold Proper, respectful; intros; subst; auto.
  - (* eu *)
    refine (@proper_eu_equ _ mequ _ K X (entailsF φ1) _ (entailsF φ2) _ _ _ Heq _ _ eq_refl);
      unfold Proper, respectful; intros; subst; auto.
  - (* ar *)
    refine (@proper_ar_equ _ mequ _ K X (entailsF φ1) _ (entailsF φ2) _ _ _ Heq _ _ eq_refl);
      unfold Proper, respectful; intros; subst; auto.
  - (* wr *)
    refine (@proper_wr_equ _ mequ _ K X (entailsF φ1) _ (entailsF φ2) _ _ _ Heq _ _ eq_refl);
      unfold Proper, respectful; intros; subst; auto.
  - (* er *)
    refine (@proper_er_equ _ mequ _ K X (entailsF φ1) _ (entailsF φ2) _ _ _ Heq _ _ eq_refl);
      unfold Proper, respectful; intros; subst; auto.
Qed.

(*| Combined Properness lemma by induction on formulas |*)
Global Add Parametric Morphism `{K: Kripke M mequ W} {X: Type}: entailsF
       with signature (equiv_ctl (X:=X) ==> mequ X ==> eq ==> iff)
         as proper_entailsF.
Proof.
  intro x; induction x; intros y Hy t u EQt w;
    rewrite EQt; apply Hy.
Qed.

Section EquivCtlFormulas.
  Context `{K: Kripke M mequ W}.
  Notation MP X := (M X -> World W -> Prop).
  
  (*| Now we start proving congruence on formulas (2nd argument) |*)
  Variant equiv_ctl_clos_body {X} (R : MP X -> MP X -> MP X) : MP X -> MP X -> MP X :=
    | equiv_ctl_clos_ctor : forall t0 w0 p0 p1 q0 q1
                              (Heqp: forall t w, p0 t w <-> p1 t w)
                              (Heqq: forall t w, q0 t w <-> q1 t w)
                              (HR : R p1 q1 t0 w0),
        equiv_ctl_clos_body R p0 q0 t0 w0.
  Hint Constructors equiv_ctl_clos_body: core. 

  Arguments impl /.
  Program Definition equiv_ctl_clos X: mon (MP X -> MP X -> MP X) :=
    {| body := equiv_ctl_clos_body |}.
  Next Obligation. repeat red; intros; destruct H0; eauto. Qed.

  Lemma equiv_ctl_clos_car {X}:
    equiv_ctl_clos X <= cart.
  Proof.    
    apply Coinduction; cbn.
    intros R p q t0 w0 [t1 t2 p1 p2 q1 q2]; inv HR. 
    - apply RMatchA.
      + now rewrite Heqq. 
      + now rewrite Heqp.
    - apply RStepA; intros.
      + now rewrite Heqp.
      + unfold cax; destruct H0 as [Hsm2 TR2]; split; cbn; cbn in Hsm2; auto.
        intros t' w' TR.
        eapply (f_Tf (car_ true)).        
        eapply equiv_ctl_clos_ctor; eauto. 
  Qed.

  Lemma equiv_ctl_clos_cwr {X}:
    equiv_ctl_clos X <= cwrt.
  Proof.    
    apply Coinduction; cbn.
    intros R p q t0 w0 [t1 t2 p1 p2 q1 q2]; inv HR. 
    - apply RMatchA.
      + now rewrite Heqq. 
      + now rewrite Heqp.
    - apply RStepA; intros.
      + now rewrite Heqp.
      + unfold cax; destruct H0 as [Hsm2 TR2]; split; cbn; cbn in Hsm2; auto.
        intros t' w' TR.
        eapply (f_Tf (car_ false)).        
        eapply equiv_ctl_clos_ctor; eauto. 
  Qed.
  
  Lemma equiv_ctl_clos_cer {X}:
    equiv_ctl_clos X <= cert.
  Proof.    
    apply Coinduction; cbn.
    intros R p q t0 w0 [t1 t2 p1 p2 q1 q2]; inv HR.
    - apply RMatchE.
      + now rewrite Heqq.
      + now rewrite Heqp.
    - destruct H0 as (t' & w' & TR2 & ?).
      apply RStepE.
      + now rewrite Heqp.
      + exists t', w'; split; auto. 
        eapply (f_Tf cer_).       
        eapply equiv_ctl_clos_ctor; eauto. 
  Qed.

  Arguments CAnd {W} {HW}.
  (*| Congruences over equiv_ctl |*)
  Global Add Parametric Morphism {X}: CAnd
         with signature equiv_ctl (X:=X) ==> equiv_ctl (X:=X) ==> equiv_ctl (X:=X)
           as equiv_ctl_equiv_and.
  Proof.
    intros p q EQpq p' q' EQpq'; split;
      intros EQpp'; split; destruct EQpp'.
    + now apply EQpq.
    + now apply EQpq'.
    + now apply EQpq in H.
    + now apply EQpq' in H0.
  Qed.

  Arguments COr {W} {HW}.
  Global Add Parametric Morphism {X}: COr
         with signature equiv_ctl (X:=X)  ==> equiv_ctl (X:=X) ==> equiv_ctl (X:=X)
           as equiv_ctl_equiv_or.
  Proof.
    intros p q EQpq p' q' EQpq'; split;
      intros EQpp'; destruct EQpp'.
    + left; now apply EQpq.
    + right; now apply EQpq'.
    + left; now apply EQpq in H.
    + right; now apply EQpq' in H.
  Qed.

  Arguments CImpl {W} {HW}.
  Global Add Parametric Morphism {X}: CImpl
         with signature equiv_ctl (X:=X) ==> equiv_ctl (X:=X) ==> equiv_ctl (X:=X)
           as equiv_ctl_equiv_impl.
  Proof.
    intros p q EQpq p' q' EQpq'; split;
      intros EQpp'; intro HH; apply EQpq'; apply EQpq in HH;
      now apply EQpp'.
  Qed.

  Arguments CAX {W} {HW}.
  Global Add Parametric Morphism {X}: CAX
      with signature equiv_ctl (X:=X) ==> equiv_ctl (X:=X) as equiv_ctl_equiv_ax.
  Proof.
    intros p q EQpq; split; intros [Hdone TR]; split; auto; intros.
    - rewrite <- EQpq; auto.
    - rewrite EQpq; auto.
  Qed.

  Arguments CEX {W} {HW}.
  Global Add Parametric Morphism {X}: CEX
      with signature equiv_ctl (X:=X) ==> equiv_ctl (X:=X) as equiv_ctl_equiv_ex.
  Proof.
    intros p q EQpq; split; intros (t' & w' & TR & Hdone);
      cbn; exists t', w'; split; auto.
    - now rewrite <- EQpq.
    - now rewrite EQpq. 
  Qed.

  Arguments CAU {W} {HW}.
  Global Add Parametric Morphism {X}: CAU
         with signature equiv_ctl (X:=X) ==> equiv_ctl (X:=X) ==> equiv_ctl (X:=X)
           as equiv_ctl_equiv_au.
  Proof.
    intros p q EQpq p' q' EQpq'.
    split; intros Hau; induction Hau.
    - apply MatchA; now rewrite <- EQpq'.
    - apply StepA; auto; now rewrite <- EQpq.
    - apply MatchA; now rewrite EQpq'.
    - apply StepA; auto; now rewrite EQpq.
  Qed.

  Arguments CEU {W} {HW}.
  Global Add Parametric Morphism {X}: CEU
         with signature equiv_ctl (X:=X) ==> equiv_ctl (X:=X) ==> equiv_ctl (X:=X)
           as equiv_ctl_equiv_eu.
  Proof.
    intros p q EQpq p' q' EQpq'.
    split; intros Heu; induction Heu.
    - apply MatchE; now rewrite <- EQpq'.
    - apply StepE; destruct H0 as (m' & TR & Heu).
      + now rewrite <- EQpq.
      + exact H1. 
    - apply MatchE; now rewrite EQpq'.
    - apply StepE; destruct H0 as (m' & TR & Heu).
      + now rewrite EQpq.
      + exact H1.
  Qed.

  Global Add Parametric Morphism {X} (t: M X) (w: World W) RR:
    (fun p q => cart RR (entailsF p) (entailsF q) t w) with signature
         (equiv_ctl (X:=X) ==> equiv_ctl (X:=X) ==> iff) as proper_equivctl_art.
  Proof.
    intros p q Hpq p' q' Hpq'; split; intro G;
    eapply (ft_t equiv_ctl_clos_car). 
    - eapply equiv_ctl_clos_ctor with (p1:=entailsF p) (q1:=entailsF p');
        auto; now symmetry.
    - eapply equiv_ctl_clos_ctor with (p1:=entailsF q) (q1:=entailsF q');
        auto; now symmetry.
  Qed.

  Global Add Parametric Morphism {X} (t: M X) w:
    (fun p q => car (entailsF p) (entailsF q) t w) with signature
         (equiv_ctl (X:=X) ==> equiv_ctl (X:=X) ==> iff) as proper_equivctl_ar.
  Proof.
    intros p q Hpq p' q' Hpq'; split; intro G;
    eapply (ft_t equiv_ctl_clos_car). 
    - eapply equiv_ctl_clos_ctor with (p1:=entailsF p) (q1:=entailsF p');
        auto; now symmetry.
    - eapply equiv_ctl_clos_ctor with (p1:=entailsF q) (q1:=entailsF q');
        auto; now symmetry.
  Qed.
  
  Global Add Parametric Morphism {X} (t: M X) w RR f:
     (fun p q => carT f RR (entailsF p) (entailsF q) t w) with signature
         (equiv_ctl (X:=X) ==> equiv_ctl (X:=X) ==> iff) as proper_equivctl_arT.
  Proof.
    intros p q Hpq p' q' Hpq'; split; intro G;
    eapply (fT_T equiv_ctl_clos_car). 
    - eapply equiv_ctl_clos_ctor with (p1:=entailsF p) (q1:=entailsF p');
        auto; now symmetry.
    - eapply equiv_ctl_clos_ctor with (p1:=entailsF q) (q1:=entailsF q');
        auto; now symmetry.
  Qed.

  Arguments CAR {W} {HW}.
  Global Add Parametric Morphism {X}: CAR with signature
         (equiv_ctl (X:=X) ==> equiv_ctl (X:=X) ==> equiv_ctl (X:=X)) as proper_equivctl_AR.
  Proof.
    intros.
    unfold equiv_ctl, entailsF.
    intros t w.
    apply proper_equivctl_ar; auto.
  Qed.
  
  Global Add Parametric Morphism {X} (t: M X) w RR:
    (fun p q => cert RR (entailsF p) (entailsF q) t w) with signature
         (equiv_ctl (X:=X) ==> equiv_ctl (X:=X) ==> iff) as proper_equivctl_ert.
  Proof.
    intros p q Hpq p' q' Hpq'; split; intro G;
    eapply (ft_t equiv_ctl_clos_cer). 
    - eapply equiv_ctl_clos_ctor with (p1:=entailsF p) (q1:=entailsF p');
        auto; now symmetry.
    - eapply equiv_ctl_clos_ctor with (p1:=entailsF q) (q1:=entailsF q');
        auto; now symmetry.
  Qed.

  Global Add Parametric Morphism {X} (t: M X) w:
    (fun p q => cer (entailsF p) (entailsF q) t w) with signature
         (equiv_ctl (X:=X) ==> equiv_ctl (X:=X) ==> iff) as proper_equivctl_er.
  Proof.
    intros p q Hpq p' q' Hpq'; split; intro G;
    eapply (ft_t equiv_ctl_clos_cer). 
    - eapply equiv_ctl_clos_ctor with (p1:=entailsF p) (q1:=entailsF p');
        auto; now symmetry.
    - eapply equiv_ctl_clos_ctor with (p1:=entailsF q) (q1:=entailsF q');
        auto; now symmetry.
  Qed.

  Global Add Parametric Morphism {X} (t: M X) w RR f:
     (fun p q => cerT f RR (entailsF p) (entailsF q) t w) with signature
         (equiv_ctl (X:=X) ==> equiv_ctl (X:=X) ==> iff) as proper_equivctl_erT.
  Proof.
    intros p q Hpq p' q' Hpq'; split; intro G;
    eapply (fT_T equiv_ctl_clos_cer). 
    - eapply equiv_ctl_clos_ctor with (p1:=entailsF p) (q1:=entailsF p');
        auto; now symmetry.
    - eapply equiv_ctl_clos_ctor with (p1:=entailsF q) (q1:=entailsF q');
        auto; now symmetry.
  Qed.

  Arguments CER {W} {HW}.
  Global Add Parametric Morphism{X}: CER with signature
         (equiv_ctl (X:=X) ==> equiv_ctl (X:=X) ==> equiv_ctl (X:=X))
           as proper_equivctl_ER.
  Proof.
    intros.
    unfold equiv_ctl, entailsF.
    intros t w.
    apply proper_equivctl_er; auto.
  Qed.
End EquivCtlFormulas.

(*| Equations of CTL |*)
Section CtlEquations.
  Context `{KMS: Kripke M mequ W} {X: Type}.
  Notation MP := (M X * World W -> Prop).  
  Infix "⩸" := (equiv_ctl (K:=KMS) (X:=X)) (at level 58, left associativity).

  Lemma ctl_au_ax: forall p q,
      <( p AU q )> ⩸ <( q \/ (p /\ AX (p AU q)) )>.
  Proof.
    intros p q; split; intro Hind.
    - unfold entailsF in Hind; induction Hind.
      + now left.
      + destruct H1 as ([? ?] & ?).
        right; split; auto.
    - destruct Hind.
      + now apply MatchA.
      + destruct H.
        rewrite ctl_ax in H0.
        destruct H0 as (? & ?).
        destruct H0 as (? & ? & ?).
        apply StepA; auto.
        split; auto.
        exists x, x0; auto.
  Qed.

  Lemma ctl_wu_wx: forall p q,
      <( p WU q )> ⩸ <( q \/ (p /\ WX (p WU q)) )>.
  Proof.
    intros p q; split; intro Hind.
    - unfold entailsF in Hind; induction Hind.
      + now left.
      + destruct H1 as ([] & ?).
        right; split; auto.
    - destruct Hind.
      + now apply MatchA.
      + destruct H.
        rewrite ctl_wx in H0.
        apply StepA; auto.
        split; auto.
  Qed.
  
  Lemma ctl_eu_ex: forall p q,
      <( p EU q )> ⩸ <( q \/ (p /\ EX (p EU q)) )>.
  Proof.
    intros p q; split; intro Hind.
    - unfold entailsF in Hind; induction Hind.
      + now left.
      + destruct H1 as (? & [? ?]).
        right; split; auto.
    - destruct Hind.
      + now apply MatchE.
      + destruct H as (? & ? & ? & ? & ?). 
        apply StepE; auto.
        exists x, x0; auto.
  Qed.
  
  Lemma ctl_and_idL: forall (p: ctlf W),
      <( ⊤ /\ p )> ⩸ <( p )>.
  Proof.
    split; intros * Hp.
    - now destruct Hp.
    - split; auto.
  Qed.

  Lemma ctl_and_idR: forall (p: ctlf W),
      <( p /\ ⊤ )> ⩸ <( p )>.
  Proof.
    split; intros * Hp.
    - now destruct Hp.
    - split; auto.
  Qed.

  Lemma ctl_or_idL: forall (p: ctlf W),
      <( ⊥ \/ p )> ⩸ <( p )>.
  Proof.
    split; intros * Hp.
    - now destruct Hp.
    - now right. 
  Qed.

  Lemma ctl_or_idR: forall (p: ctlf W),
      <( p \/ ⊥ )> ⩸ <( p )>.
  Proof.
    split; intros * Hp.
    - now destruct Hp.
    - now left.
  Qed.

  Lemma ctl_af_ax: forall (p: ctlf W),
      <( AF p )> ⩸ <( p \/ AX (AF p) )>.
  Proof.
    intros.
    etransitivity.
    apply ctl_au_ax.
    now rewrite ctl_and_idL.
  Qed.

  Lemma ctl_wf_wx: forall (p: ctlf W),
      <( WF p )> ⩸ <( p \/ WX (WF p) )>.
  Proof.
    intros.
    etransitivity.
    apply ctl_wu_wx.
    now rewrite ctl_and_idL.
  Qed.
  
  Lemma ctl_ef_ex: forall (p: ctlf W),
      <( EF p )> ⩸ <( p \/ EX (EF p) )>.
  Proof.
    intros.
    etransitivity.
    apply ctl_eu_ex.
    now rewrite ctl_and_idL.
  Qed.

  Lemma ctl_ar_ax: forall (p q: ctlf W),
      <( p AR q )> ⩸ <( p /\ (q \/ AX (p AR q)) )>.
   Proof. 
     split; intros * Hp.
     - split; step in Hp; inv Hp.
       + assumption.
       + assumption.
       + now left. 
       + now right.
     - destruct Hp.
       destruct H0; step; now constructor.
   Qed.

   Lemma ctl_wr_wx: forall (p q: ctlf W),
      <( p WR q )> ⩸ <( p /\ (q \/ WX (p WR q)) )>.
   Proof. 
     split; intros * Hp.
     - split; step in Hp; inv Hp.
       + assumption.
       + assumption.
       + now left. 
       + now right.
     - destruct Hp.
       destruct H0; step; now constructor.
   Qed.
   
   Lemma ctl_er_ex: forall (p q: ctlf W),
      <( p ER q )> ⩸ <( p /\ (q \/ EX (p ER q)) )>.
   Proof. 
     split; intros * Hp.
     - split; step in Hp; inv Hp.
       + assumption.
       + assumption.
       + now left.
       + now right.
     - destruct Hp.
       destruct H0; step; now constructor.
   Qed.

   Lemma ctl_ag_ax: forall (p: ctlf W),
       <( AG p )> ⩸ <( p /\ AX (AG p) )>.
   Proof.
     etransitivity.
     - apply ctl_ar_ax.
     - now rewrite ctl_or_idL.
   Qed.

   Lemma ctl_wg_wx: forall (p: ctlf W),
       <( WG p )> ⩸ <( p /\ WX (WG p) )>.
   Proof.
     etransitivity.
     - apply ctl_wr_wx.
     - now rewrite ctl_or_idL.
   Qed.
   
   Lemma ctl_eg_ex: forall (p: ctlf W),
       <( EG p )> ⩸ <( p /\ EX (EG p) )>.
   Proof.
     etransitivity.
     - apply ctl_er_ex.
     - now rewrite ctl_or_idL.
   Qed.
   
   Lemma ctl_ag_involutive: forall (p: ctlf W),
       <( AG p )> ⩸ <( AG (AG p) )>.
   Proof.
     split; intros;
       revert H; revert t w; coinduction R CIH;
       intros t' w' Hag.     
     - apply RStepA; auto;
         apply ctl_ag_ax in Hag as (? & ?).
       inv H0; split; auto. 
       intros.
       apply CIH.
       now apply H2.
     - assert(Hag': <( t', w' |= AG AG p )>) by apply Hag.
       clear Hag.
       rewrite ctl_ag_ax in Hag'.       
       destruct Hag'.
       inv H0.
       rewrite ctl_ag_ax in H.
       destruct H.
       apply RStepA; auto.
       split; auto; intros.       
       apply CIH.
       now apply H2.
   Qed.

   Lemma ctl_wg_involutive: forall (p: ctlf W),
       <( WG p )> ⩸ <( WG (WG p) )>.
   Proof.
     split; intros;
       revert H; revert t w; coinduction R CIH;
       intros t' w' Hag.     
     - apply RStepA; auto.
       apply ctl_wg_wx in Hag as (? & ?).
       inv H0; split; auto. 
       intros.
       apply CIH.
       now apply H2.
     - assert(Hag': <( t', w' |= WG WG p )>) by apply Hag.
       clear Hag.
       rewrite ctl_wg_wx in Hag'.       
       destruct Hag'.
       inv H0.
       rewrite ctl_wg_wx in H.
       destruct H.
       apply RStepA; auto.
       split; auto; intros.       
       apply CIH.
       now apply H2.
   Qed.
   
End CtlEquations.

(*| Ltac Tactic [next], rewrite au, af, ag, ar, eu, ef, er, eg
    to a disjunction/conjucntion with ax, ex respectively |*)
#[global] Tactic Notation "next" :=
  lazymatch goal with
  | |- context[@entailsF ?M ?meq ?W ?KMS ?X ?φ ?t ?w] =>
      lazymatch φ with
      | CAX ?p => apply (@ctl_ax M meq W KMS X)
      | CWX ?p => apply (@ctl_wx M meq W KMS X)                       
      | CEX ?p => apply (@ctl_ex M meq W KMS X)
      | CAU ?p ?q => lazymatch eval cbv in p with
                    | CBase (fun _ => True) => apply (@ctl_af_ax M meq W KMS X)
                    | _ => apply (@ctl_au_ax M meq W KMS X)
                    end
      | CWU ?p ?q => lazymatch eval cbv in p with
                    | CBase (fun _ => True) => apply (@ctl_wf_wx M meq W KMS X)
                    | _ => apply (@ctl_wu_wx M meq W KMS X)
                    end                                            
      | CEU ?p ?q => lazymatch eval cbv in p with
                    | CBase (fun _ => True) => apply (@ctl_ef_ex M meq W KMS X)
                    | _ => apply (@ctl_eu_ex M meq W KMS X)
                    end
      | CAR ?p ?q => lazymatch eval cbv in q with
                    | CBase (fun _ => False) =>
                        apply (@ctl_ag_ax M meq W KMS X)
                    | _ => apply (@ctl_ar_ax M meq W KMS X)
                    end
      | CWR ?p ?q => lazymatch eval cbv in q with
                    | CBase (fun _ => False) =>
                        apply (@ctl_wg_wx M meq W KMS X)
                    | _ => apply (@ctl_wr_wx M meq W KMS X)
                    end                      
      | CER ?p ?q => lazymatch eval cbv in q with
                    | CBase (fun _ => False) => apply (@ctl_eg_ex M meq W KMS X)
                    | _ => apply (@ctl_er_ex M meq W KMS X)
                    end
      | CER ?p ?q => lazymatch eval cbv in q with
                    | CBase (fun _ => False) => apply (@ctl_eg_ex M meq W KMS X)
                    | _ => apply (@ctl_er_ex M meq W KMS X)
                    end
      | ?ptrivial => fail "Cannot step formula " ptrivial
      end
  end.

#[global] Tactic Notation "next" "in" ident(H) :=
  lazymatch type of H with
  | context[@entailsF ?M ?meq ?W ?KMS ?X ?φ ?t ?w] =>
      lazymatch φ with
      | CAX ?p => rewrite (@ctl_ax M meq W KMS X) in H
      | CWX ?p => rewrite (@ctl_wx M meq W KMS X) in H
      | CEX ?p => rewrite (@ctl_ex M meq W KMS X) in H
      | context[CAU ?p ?q] => lazymatch eval cbv in p with
                             | CBase (fun _ => True) =>
                                 rewrite (@ctl_af_ax M meq W KMS X q) in H
                             | _ => rewrite (@ctl_au_ax M meq W KMS X q) in H
                             end
      | context[CWU ?p ?q] => lazymatch eval cbv in p with
                             | CBase (fun _ => True) =>
                                 rewrite (@ctl_wf_wx M meq W KMS X q) in H
                             | _ => rewrite (@ctl_wu_wx M meq W KMS X q) in H
                             end                               
      | context[CEU ?p ?q] => lazymatch eval cbv in p with
                             | CBase (fun _ => True) => rewrite (@ctl_ef_ex M meq W KMS X q) in H
                             | _ => rewrite (@ctl_eu_ex M meq W KMS X q) in H
                             end
      | context[CAR ?p ?q] => lazymatch eval cbv in q with
                             | CBase (fun _ => False) => rewrite (@ctl_ag_ax M meq W KMS X p) in H
                             | _ => rewrite (@ctl_ar_ax M meq W KMS X p) in H
                             end
      | context[CWR ?p ?q] => lazymatch eval cbv in q with
                             | CBase (fun _ => False) => rewrite (@ctl_wg_wx M meq W KMS X p) in H
                             | _ => rewrite (@ctl_wr_wx M meq W KMS X p) in H
                             end                               
      | context[CER ?p ?q] => lazymatch eval cbv in q with
                             | CBase (fun _ => False) => rewrite (@ctl_eg_ex M meq W KMS X p) in H
                             | _ => rewrite (@ctl_er_ex M meq W KMS X p) in H
                             end
      | ?ptrivial => fail "Cannot step formula " ptrivial " in " H
      end
  end.
