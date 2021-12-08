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

Section bind.

  Definition pointwise {X X' Y Y'} (SS : rel X X')
    : rel Y Y' -> rel (X -> Y) (X' -> Y') :=
    fun R k k' => forall x x', SS x x' -> R (k x) (k' x').
  (* Heterogeneous [pair], todo move to library *)
  Definition pairH {A B : Type} (x : A) (y : B) : A -> B -> Prop :=
    fun x' y' => x = x' /\ y = y'.

  Lemma leq_pairH : forall {A B : Type} (x : A) (y : B) (R : rel A B),
      R x y <-> pairH x y <= R.
  Proof.
    firstorder congruence.
  Qed.

  Section Bind_ctx.

    Context {E: Type -> Type} {X X' Y Y': Type}.

    (* Most general contextualisation function associated to [bind]
	   Can be read more digestly as, where R is a relation on ctrees (the prefixes of the binds) and S on the continuations:
		 bind_ctx R S = {(bind t k, bind t' k') | R t t' /\ S k k'}

		 This definition could actually be generalized,
     the same way the Coinduction library provides generic binary contexts ([binary_ctx]).
	   *)

    (* The most general context:
    bind_ctx R S ≜ {(bind x k, bind x' k') | R x x' /\ S k k'}
     *)
    Definition bind_ctx
               (R: rel (ctree E X) (ctree E X'))
               (S: rel (X -> ctree E Y) (X' -> ctree E Y')):
      rel (ctree E Y) (ctree E Y') :=
      sup_all (fun x => sup (R x) (fun x' =>
                                  sup_all (fun k => sup (S k) (fun k' => pairH (bind x k) (bind x' k'))))).

    (* Two lemmas to interact with [bind_ctx]:
     - [leq_bind_ctx] specifies relations above the context
     - [in_bind_ctx] specifies how to populate it *)
    Lemma leq_bind_ctx:
      forall R S S', bind_ctx R S <= S' <->
                  (forall x x', R x x' -> forall k k', S k k' -> S' (bind x k) (bind x' k')).
    Proof.
      intros.
      unfold bind_ctx.
      setoid_rewrite sup_all_spec.
      setoid_rewrite sup_spec.
      setoid_rewrite sup_all_spec.
      setoid_rewrite sup_spec.
      setoid_rewrite <-leq_pairH.
      firstorder.
    Qed.

    Lemma in_bind_ctx (R S :rel _ _) x x' y y':
      R x x' -> S y y' -> bind_ctx R S (bind x y) (bind x' y').
    Proof. intros. now apply ->leq_bind_ctx. Qed.
    Global Opaque bind_ctx.

  End Bind_ctx.

  Section Concrete_Bind_ctx.

    Context {E: Type -> Type} {X1 X2 Y1 Y2: Type}.

    (* specialisation to a function acting with [equ] on the bound value, and with the argument (pointwise) on the continuation *)
    Program Definition bind_ctx_equ SS: mon (rel (ctree E Y1) (ctree E Y2)) :=
      {|body := fun R => @bind_ctx E X1 X2 Y1 Y2 (equ SS) (pointwise SS R) |}.
    Next Obligation.
      intros ??? H. apply leq_bind_ctx. intros ?? H' ?? H''.
      apply in_bind_ctx. apply H'. intros t t' HS. apply H, H'', HS.
    Qed.

    (* this gives a valid up-to technique *)
    Lemma bind_ctx_equ_t (SS : rel X1 X2) (RR : rel Y1 Y2): bind_ctx_equ SS <= t_equ RR.
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

