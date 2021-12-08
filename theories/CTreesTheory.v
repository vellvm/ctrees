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

Program Definition equ_clos {E X1 X2} : mon (rel (ctree E X1) (ctree E X2)) :=
  {| body := fun R t u => exists t' u', t' ≅ t /\ R t u /\ u ≅ u' |}.
Next Obligation.
  intros * ?? LE t u (t' & u' & eqt & eqtu & equ).
  do 2 eexists; repeat split; auto.
  apply LE; auto.
Qed.

Lemma equ_clos_sym {E X} : compat converse (@equ_clos E X X).
Proof.
  intros R t u (t' & u' & eq1 & eq2 & eq3).
  exists u', t'; intuition.
Qed.

Lemma equ_clos_t {E X} : @equ_clos E X X <= st.
Proof.
  apply Coinduction, by_Symmetry; [apply equ_clos_sym |].
  intros R t u (t' & u' & eq1 & [F B] & eq3) l t1 TR; cbn in *.
  apply F in TR as [u1 TR ?].
  eexists.
  eauto.
  apply (f_Tf sb).
  do 2 eexists; intuition.
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
      apply trans_bind_inv in STEP as [(H & t' & STEP & EQ) | ?]; cbn in *.
      - apply F in STEP as [u' STEP EQ'].
        eexists.
        apply trans_bind_l; eauto.
        apply (@fT_T _ _ sb equ_clos foo).


        apply (fTf_Tf sb).
        eapply (fT_T sb).
        apply (fTf_Tf sb).
        apply in_bind_ctx. apply REL.
        red in kk.
        generalize (kk _ _ REL).
        apply id_T.
        apply in_bind_ctx. apply REL.
        apply (b_T sb).
        split.
        rewrite EQ.

          intros ?. ? ?. exists. cbn. cbv. red. kk'; auto.

      destruct xx' .
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

