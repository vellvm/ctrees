(* begin hide *)
From Coq Require Import
     Program
     Setoid
     Morphisms
     RelationClasses.

From Coinduction Require Import
	   coinduction rel tactics.

From CTree Require Import
	   Utils CTrees Shallow Trans Equ Bisim.

Obligation Tactic := idtac.
(* end hide *)

Import CTree.
Import CTreeNotations.
Open Scope ctree.


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

Lemma equ_clos_sym {E X} : compat converse (@equ_clos E X X).
Proof.
  intros R t u EQ; inv EQ. 
  apply Equ_clos with u' t'; intuition. 
Qed.

Lemma equ_clos_t {E X} : @equ_clos E X X <= st.
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

Section bind.

  Section Concrete_Bind_ctx.

    Context {E: Type -> Type} {X1 X2 Y1 Y2: Type}.

    (* specialisation to a function acting with [sbisim] on the bound value, and with the argument (pointwise) on the continuation *)
    Program Definition bind_ctx_sbisim : mon (rel (ctree E Y1) (ctree E Y1)) :=
      {|body := fun R => @bind_ctx E X1 X1 Y1 Y1 sbisim (pointwise eq R) |}.
    Next Obligation.
      intros ?? H. apply leq_bind_ctx. intros ?? H' ?? H''.
      apply in_bind_ctx. apply H'. intros t t' HS. apply H, H'', HS.
    Qed.

    (* this gives a valid up-to technique *)
    Lemma bind_ctx_equ_t (SS : rel X1 X2) (RR : rel Y1 Y2): @bind_ctx_equ E _ _ _ _ SS <= t_equ RR.
    Proof.
      apply Coinduction. intros R. apply (leq_bind_ctx _).
      intros x x' xx' k k' kk'.
      step in xx'.
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

    Lemma bind_ctx_sym: compat converse bind_ctx_sbisim.
    Proof. intro R. simpl. apply leq_bind_ctx. intros. apply in_bind_ctx.
           symmetry; auto.
           intros ? ? ->.
           apply H0; auto.
    Qed.

    (* this gives a valid up-to technique *)
    Lemma bind_ctx_sbisim_t : bind_ctx_sbisim <= st.
    Proof.
      apply Coinduction, by_Symmetry.
      apply bind_ctx_sym.
      intros R. apply (leq_bind_ctx _).
      intros t1 t2 tt k1 k2 kk.
      step in tt; destruct tt as (F & B); cbn in *.
      cbn in *; intros l u STEP.
      apply trans_bind_inv in STEP as [(H & t' & STEP & EQ) | (v & STEPres & STEP)]; cbn in *.
      - apply F in STEP as [u' STEP EQ'].
        eexists.
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



  End Concrete_Bind_ctx.


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

