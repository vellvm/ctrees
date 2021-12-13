(*|
==============================
Equational Theory for [ctrees]
==============================

.. coq::none
|*)
From Coq Require Import
     Program
     Setoid
     Morphisms
     RelationClasses.

From Coinduction Require Import
	   coinduction rel tactics.

From RelationAlgebra Require Import
     monoid
     kat
     kat_tac
     prop
     rel
     srel
     comparisons
     rewriting
     normalisation.

From CTree Require Import
	   Utils CTrees Shallow Trans Equ Bisim.

Obligation Tactic := idtac.

Import CTree.
Import CTreeNotations.
Open Scope ctree.


(*|
Up-to [equ eq] bisimulations
----------------------------
We have proved in the module [Bisim] that [sbisim] and [wbisim] are closed under [equ eq].
We prove here more generally that strong and weak bisimulation up-to [equ eq] are valid
reasoning principles.

Note: Should probably refactor things to prove this first and derive the particular case as
a consequence.
|*)

(*|
Definition of the enhancing function
|*)
Variant equ_clos_body {E X1 X2} (R : rel (ctree E X1) (ctree E X2)) : (rel (ctree E X1) (ctree E X2)) :=
  | Equ_clos : forall t t' u' u
                 (Equt : t ≅ t')
                 (HR : R t' u')
                 (Equu : u' ≅ u),
      equ_clos_body R t u.

Program Definition equ_clos {E X1 X2} : mon (rel (ctree E X1) (ctree E X2)) :=
  {| body := @equ_clos_body E X1 X2 |}.
Next Obligation.
  intros * ?? LE t u EQ; inv EQ.
  econstructor; eauto.
  apply LE; auto.
Qed.

(*|
Sufficient condition to prove compatibility only over the simulation
|*)
Lemma equ_clos_sym {E X} : compat converse (@equ_clos E X X).
Proof.
  intros R t u EQ; inv EQ.
  apply Equ_clos with u' t'; intuition.
Qed.

(*|
Strong bisimulation up-to [equ] is valid
|*)
Lemma equ_clos_st {E X} : @equ_clos E X X <= st.
Proof.
  apply Coinduction, by_Symmetry; [apply equ_clos_sym |].
  intros R t u EQ l t1 TR; inv EQ.
  destruct HR as [F _]; cbn in *.
  rewrite Equt in TR.
  apply F in TR.
  destruct TR as [? ? ?].
  eexists.
  rewrite <- Equu; eauto.
  apply (f_Tf sb).
  econstructor; intuition.
  auto.
Qed.

(*|
TODO: Can we afford to make [wtrans] opaque? If so, where?
|*)
Opaque wtrans.
(*|
Weak bisimulation up-to [equ] is valid
|*)
Lemma equ_clos_wt {E X} : @equ_clos E X X <= wt.
Proof.
  apply Coinduction, by_Symmetry; [apply equ_clos_sym |].
  intros R t u EQ l t1 TR; inv EQ.
  destruct HR as [F _]; cbn in *.
  rewrite Equt in TR.
  apply F in TR.
  destruct TR as [? ? ?].
  eexists.
  rewrite <- Equu; eauto.
  apply (f_Tf wb).
  econstructor; intuition.
  auto.
Qed.

(*|
Up-to [bind] context bisimulations
----------------------------------
We have proved in the module [Equ] that up-to bind context is
a valid enhancement to prove [equ].
We now prove the same result, but for strong and weak bisimulation.
|*)

Section bind.


(*|
Specialization of [bind_ctx] to the [sbisim]-based closure we are
looking for, and the proof of validity of the principle. 
|*)
   Section Sbisim_Bind_ctx.

    Context {E: Type -> Type} {X Y: Type}.

(*|
Specialization of [bind_ctx] to a function acting with [sbisim] on the bound value,
and with the argument (pointwise) on the continuation.
|*)
    Program Definition bind_ctx_sbisim : mon (rel (ctree E Y) (ctree E Y)) :=
      {|body := fun R => @bind_ctx E X X Y Y sbisim (pointwise eq R) |}.
    Next Obligation.
      intros ?? H. apply leq_bind_ctx. intros ?? H' ?? H''.
      apply in_bind_ctx. apply H'. intros t t' HS. apply H, H'', HS.
    Qed.


(*|
Sufficient condition to exploit symmetry
|*)
    Lemma bind_ctx_sbisim_sym: compat converse bind_ctx_sbisim.
    Proof.
      intro R. simpl. apply leq_bind_ctx. intros. apply in_bind_ctx.
      symmetry; auto.
      intros ? ? ->.
      apply H0; auto.
    Qed.

(*|
The resulting enhancing function gives a valid up-to technique
|*)
    Lemma bind_ctx_sbisim_t : bind_ctx_sbisim <= st.
    Proof.
      apply Coinduction, by_Symmetry.
      apply bind_ctx_sbisim_sym.
      intros R. apply (leq_bind_ctx _).
      intros t1 t2 tt k1 k2 kk.
      step in tt; destruct tt as (F & B); cbn in *.
      cbn in *; intros l u STEP.
      apply trans_bind_inv in STEP as [(H & t' & STEP & EQ) | (v & STEPres & STEP)]; cbn in *.
      - apply F in STEP as [u' STEP EQ'].
        eexists.
        apply trans_bind_l; eauto.
        apply (fT_T equ_clos_st).
        econstructor; [exact EQ | | reflexivity].
        apply (fTf_Tf sb).
        apply in_bind_ctx; auto.
        intros ? ? ->.
        apply (b_T sb).
        apply kk; auto.
      - apply F in STEPres as [u' STEPres EQ'].
        pose proof (trans_val_inv _ _ _ STEPres) as EQ.
        rewrite EQ in STEPres.
        specialize (kk v v eq_refl) as [Fk Bk].
        apply Fk in STEP as [u'' STEP EQ'']; cbn in *.
        eexists.
        eapply trans_bind_r; cbn in *; eauto.
        eapply (id_T sb); cbn; auto.
    Qed.

   End Sbisim_Bind_ctx.

   Section Wbisim_Bind_ctx.

    Context {E: Type -> Type} {X Y: Type}.

(*|
Specialization of [bind_ctx] to a function acting with [sbisim] on the bound value,
and with the argument (pointwise) on the continuation.
|*)
    Program Definition bind_ctx_wbisim :  mon (rel (ctree E Y) (ctree E Y)) :=
      {|body := fun R => @bind_ctx E X X Y Y wbisim (pointwise eq R) |}.
    Next Obligation.
      intros ???? H. apply leq_bind_ctx. intros ?? H' ?? H''.
      apply in_bind_ctx. apply H'. intros t t' HS. apply H0, H'', HS.
    Qed.

(*|
Sufficient condition to exploit symmetry
|*)
    Lemma bind_ctx_wbisim_sym: compat converse bind_ctx_wbisim.
    Proof.
      intro R. simpl. apply leq_bind_ctx. intros. apply in_bind_ctx.
      symmetry; auto.
      intros ? ? ->.
      apply H0; auto.
    Qed.


(*|
The resulting enhancing function gives a valid up-to technique
|*)
    Lemma bind_ctx_wbisim_t : bind_ctx_wbisim <= wt.
    Proof.
      apply Coinduction, by_Symmetry.
      apply bind_ctx_wbisim_sym.
      intros R. apply (leq_bind_ctx _).
      intros t1 t2 tt k1 k2 kk.
      step in tt; destruct tt as (F & B); cbn in *.
      cbn in *; intros l u STEP.
      apply trans_bind_inv in STEP as [(H & t' & STEP & EQ) | (v & STEPres & STEP)]; cbn in *.
      - apply F in STEP as [u' STEP EQ'].
        eexists.
        (* TODO: wtrans bind lemmas *)
(*
        apply trans_bind_l; eauto.
        apply (fT_T equ_clos_t).
        econstructor; [exact EQ | | reflexivity].
        apply (fTf_Tf sb).
        apply in_bind_ctx; auto.
        intros ? ? ->.
        apply (b_T sb).
        apply kk; auto.
      - apply F in STEPres as [u' STEPres EQ'].
        pose proof (trans_val_inv _ _ _ STEPres) as EQ.
        rewrite EQ in STEPres.
        specialize (kk v v eq_refl) as [Fk Bk].
        apply Fk in STEP as [u'' STEP EQ'']; cbn in *.
        eexists.
        eapply trans_bind_r; cbn in *; eauto.
        eapply (id_T sb); cbn; auto.
    Qed.
 *)
        Admitted.


    (* this gives a valid up-to technique *)
    (* research question: is there a meaningful way do deal with bind_ctx in general? *)
    Lemma bind_ctx_equ_t (SS : rel X X') (RR : rel Y Y'): bind_ctx' SS <= t_equ RR.
    Proof.
      apply Coinduction. intros R. apply (leq_bind_ctx _).
      intros x x' xx' k k' kk'.
      apply (gfp_pfp (fequ _)) in xx'.
      cbn; unfold observe; cbn.
      destruct xx'.
      - cbn in *.
        generalize (kk' _ _ REL).
        apply (fequ RR).
        apply id_T.
      - constructor; intros ?. apply (fTf_Tf (fequ _)).
        apply in_bind_ctx. apply REL.
        red; intros. apply (b_T (fequ _)), kk'; auto.
      - constructor. intro a. apply (fTf_Tf (fequ _)).
        apply in_bind_ctx. apply REL.
        red; intros. apply (b_T (fequ _)), kk'; auto.
    Qed.

  End Wbisim_Bind_ctx.


End bind.


    (* specialisation to a function acting with [sbisim] on the bound value, and with the argument (pointwise) on the continuation *)
    Program Definition bind_ctx_sbisim : mon (rel (ctree E Y1) (ctree E Y1)) :=
      {|body := fun R => @bind_ctx E X1 X1 Y1 Y1 sbisim (pointwise eq R) |}.
    Next Obligation.
      intros ?? H. apply leq_bind_ctx. intros ?? H' ?? H''.
      apply in_bind_ctx. apply H'. intros t t' HS. apply H, H'', HS.
    Qed.

    (* Inverting transitions from binds *)
    (* this gives a valid up-to technique *)
    Lemma bind_ctx_sbisim_t : bind_ctx_sbisim <= st.
    Proof.
      apply Coinduction. intros R. apply (leq_bind_ctx _).
      intros x x' xx' k k' kk'.
      step in xx'; destruct xx' as (F & B); cbn in *.
      split.
      - cbn; intros l t' STEP. 
      destruct xx'.
      - cbn in *.
        generalize (kk' _ _ REL).
        apply (fequ RR).
        apply id_T.
      - constructor; intros ?. apply (fTf_Tf (fequ _)).
        apply in_bind_ctx. apply REL.
        red; intros. apply (b_T (fequ _)), kk'; auto.
      - constructor. intro a. apply (fTf_Tf (fequ _)).
        apply in_bind_ctx. apply REL.
        red; intros. apply (b_T (fequ _)), kk'; auto.
    Qed.

    (* specialisation to a function acting with [sbisim] on the bound value, and with the argument (pointwise) on the continuation *)
    Program Definition bind_ctx_wbisim {E X Y1 Y2}: mon (rel (ctree E Y1) (ctree E Y2)) :=
      {|body := fun R => @bind_ctx E X X Y1 Y2 wbisim (pointwise eq R) |}.
    Next Obligation.
      intros ?????? H. apply leq_bind_ctx. intros ?? H' ?? H''.
      apply in_bind_ctx. apply H'. intros t t' HS. apply H, H'', HS.
    Qed.

    (* this gives a valid up-to technique *)
    (* research question: is there a meaningful way do deal with bind_ctx in general? *)
    Lemma bind_ctx_equ_t (SS : rel X X') (RR : rel Y Y'): bind_ctx' SS <= t_equ RR.
    Proof.
      apply Coinduction. intros R. apply (leq_bind_ctx _).
      intros x x' xx' k k' kk'.
      apply (gfp_pfp (fequ _)) in xx'.
      cbn; unfold observe; cbn.
      destruct xx'.
      - cbn in *.
        generalize (kk' _ _ REL).
        apply (fequ RR).
        apply id_T.
      - constructor; intros ?. apply (fTf_Tf (fequ _)).
        apply in_bind_ctx. apply REL.
        red; intros. apply (b_T (fequ _)), kk'; auto.
      - constructor. intro a. apply (fTf_Tf (fequ _)).
        apply in_bind_ctx. apply REL.
        red; intros. apply (b_T (fequ _)), kk'; auto.
    Qed.

