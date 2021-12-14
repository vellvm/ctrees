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
     RelationClasses
     Psatz.

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
We can therefore rewrite [equ] in the middle of bisimulation proofs
|*)
#[global] Instance equ_clos_st_proper {E R} RR : Proper (gfp (@fequ E R R eq) ==> equ eq ==> iff) (st RR).
Proof.
  unfold Proper, respectful; intros.
  split; intros.
  - apply (ft_t equ_clos_st).
    econstructor; [symmetry; eauto | | eauto]; auto.
  - apply (ft_t equ_clos_st).
    econstructor; [eauto | | symmetry; eauto]; auto.
Qed.

#[global] Instance equ_clos_wt_proper {E R} RR : Proper (gfp (@fequ E R R eq) ==> equ eq ==> iff) (wt RR).
Proof.
  unfold Proper, respectful; intros.
  split; intros.
  - apply (ft_t equ_clos_wt).
    econstructor; [symmetry; eauto | | eauto]; auto.
  - apply (ft_t equ_clos_wt).
    econstructor; [eauto | | symmetry; eauto]; auto.
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
        pose proof (trans_val_inv STEPres) as EQ.
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

  End Wbisim_Bind_ctx.

End bind.

(*|
Expliciting the reasoning rule provided by the up-to principles.
|*)
Lemma sbisim_clo_bind (E: Type -> Type) (X Y : Type) :
	forall (t1 t2 : ctree E X) (k1 k2 : X -> ctree E Y) RR,
		t1 ~ t2 ->
    (forall x, (st RR) (k1 x) (k2 x)) ->
    st RR (t1 >>= k1) (t2 >>= k2)
.
Proof.
  intros.
  apply (ft_t (@bind_ctx_sbisim_t E X Y)).
  apply in_bind_ctx; auto.
  intros ? ? <-; auto.
Qed.

Lemma wbisim_clo_bind (E: Type -> Type) (X Y : Type) :
	forall (t1 t2 : ctree E X) (k1 k2 : X -> ctree E Y) RR,
		t1 ≈ t2 ->
    (forall x, (wt RR) (k1 x) (k2 x)) ->
    wt RR (t1 >>= k1) (t2 >>= k2)
.
Proof.
  intros.
  apply (ft_t (@bind_ctx_wbisim_t E X Y)).
  apply in_bind_ctx; auto.
  intros ? ? <-; auto.
Qed.

(*|
And in particular, we get the proper instance justifying rewriting [~]
and [≈] to the left of a [bind].
|*)
#[global] Instance bind_sbisim_cong :
 forall (E : Type -> Type) (X Y : Type) (R : rel Y Y) RR,
   Proper (sbisim ==> pointwise_relation X (st RR) ==> st RR) (@bind E X Y).
Proof.
  repeat red; intros; eapply sbisim_clo_bind; eauto.
Qed.

#[global] Instance bind_wbisim_cong :
 forall (E : Type -> Type) (X Y : Type) (R : rel Y Y) RR,
   Proper (wbisim ==> pointwise_relation X (wt RR) ==> wt RR) (@bind E X Y).
Proof.
  repeat red; intros; eapply wbisim_clo_bind; eauto.
Qed.

(*|
Sanity checks
=============
|*)

Module Sanity.

(*|
Note that with visible schedules, nary-spins are equivalent only
if neither are empty, or if both are empty: they match each other's
tau challenge infinitely often.
With invisible schedules, they are always equivalent: neither of them
produce any challenge for the other.
|*)
  Lemma spinV_nary_n_m : forall {E R} n m, n>0 -> m>0 -> @spinV_nary E R n ≈ spinV_nary m.
  Proof.
    intros E R.
    coinduction S CIH; symmetric.
    intros * ? ? l p' TR.
    destruct m as [|m]; [lia |].
    rewrite ctree_eta in TR; cbn in TR.
    apply trans_ChoiceV_inv in TR as (_ & EQ & ->).
    eexists.
    apply trans_wtrans; rewrite ctree_eta; cbn.
    econstructor. exact Fin.F1.
    reflexivity.
    rewrite EQ; eauto.
  Qed.

  Lemma spinV_nary_0 : forall {E R}, @spinV_nary E R 0 ≈ spinV_nary 0.
  Proof.
    intros E R.
    coinduction S _; symmetric.
    cbn; intros * TR.
    rewrite ctree_eta in TR; cbn in TR.
    apply trans_ChoiceV_inv in TR as (abs & _ & _); inv abs.
  Qed.

  Lemma spinI_nary_n_m : forall {E R} n m, @spinI_nary E R n ≈ spinI_nary m.
  Proof.
    intros E R.
    coinduction S _; symmetric.
    cbn; intros * TR.
    exfalso; eapply spinI_nary_is_stuck, TR.
  Qed.

  Import Fin.

  Ltac inv_trans_one :=
    match goal with
    | h : transR _ ?t _ |- _ =>
        match t with
        | TauI _            => apply trans_TauI_inv in h as h
        | choiceI2 _ _      => apply trans_ChoiceI_inv in h as [[|] h]
        | choiceI3 _ _ _    => apply trans_ChoiceI_inv in h as [[| ? [|]] h]
        | ChoiceF false _ _ => idtac
        end; cbn in h
    | h : hrel_of (trans _) ?t _ |- _ => idtac
    end.

  Ltac inv_trans := repeat inv_trans_one.
  Ltac reach_core :=
    lazymatch goal with
      | [|- transR _ (choiceI2 _ _) _] =>
        first [eapply (trans_ChoiceI F1); [ | reflexivity]; cbn; first [easy | reach_core] |
               eapply (trans_ChoiceI (FS F1)); [ | reflexivity]; cbn; first [easy | reach_core]]
      | [|- transR _ (choiceI3 _ _ _) _] =>
        first [eapply (trans_ChoiceI F1); [ | reflexivity]; cbn; first [easy | reach_core]      |
               eapply (trans_ChoiceI (FS F1)); [ | reflexivity]; cbn; first [easy | reach_core] |
               eapply (trans_ChoiceI (FS (FS F1))); [ | reflexivity]; cbn; first [easy | reach_core]]
     end.
  Ltac reach := eexists; [| reflexivity]; reach_core.

  Ltac steps := step; split; cbn; intros ? ? ?TR.

(*|
TODO: automate
Note: with choiceI2, these relations hold up-to strong bisimulation.
With choiceV2 however they don't even hold up-to weak bisimulation.
|*)
  Lemma choiceI2_assoc {E X} : forall (t u v : ctree E X),
	    choiceI2 (choiceI2 t u) v ~ choiceI2 t (choiceI2 u v).
  Proof.
    intros.
    steps; inv_trans; reach.
  Qed.

  Lemma choiceI2_commut {E X} : forall (t u : ctree E X),
	    choiceI2 t u ~ choiceI2 u t.
  Proof.
(*|
Note: could use a symmetry argument here as follows to only play one direction of the game.
[coinduction ? _; symmetric.]
but automation just handles it...
|*)
    intros.
    steps; inv_trans; reach.
  Qed.

  Lemma choiceI_merge {E X} : forall (t u v : ctree E X),
	    choiceI2 (choiceI2 t u) v ~ choiceI3 t u v.
  Proof.
    intros.
    steps; inv_trans; reach.
  Qed.

(*
  Lemma choice2_spin : forall {E X} (t : ctree E X),
	  choiceV2 t spin ≈ t.
  Proof.
    intros. unfold bisim. step. constructor.
    - intros. exists u'. split.
      2: { apply matching_active_refl; auto. eapply scheduled_active_; eauto. }
      inv H. apply inj_pair2 in H3. subst. remember 2. destruct x; inv Heqn; auto.
      exfalso. eapply schedule_spin; eauto.
    - intros. exists t'. split.
      2: { apply matching_active_refl; auto. eapply scheduled_active_; eauto. }
      apply SchedChoice with (x:=Fin.F1); auto.
  Qed.

  Lemma choice2_equ : forall {E X} (t u : ctree E X),
	  t ≅ u ->
	  choiceV2 t u ≈ t.
  Proof.
    intros. unfold bisim. step. constructor.
    - intros. exists u'. split.
      2: { apply matching_active_refl; auto. eapply scheduled_active_; eauto. }
      inv H0. apply inj_pair2 in H4. subst. remember 2. destruct x; inv Heqn; auto.
      (* We should be able to use something like equ_schedule for
         this, but we need a version with schedule_ *)
      admit.
    - intros. exists t'. split.
      2: { apply matching_active_refl; auto. eapply scheduled_active_; eauto. }
      apply SchedChoice with (x:=Fin.F1); auto.
  Abort.

  Lemma choice0_spin : forall {E X},
    ChoiceV 0 (fun x:fin 0 => match x with end) ≈ @spin E X.
  Proof.
    intros; unfold bisim; step; constructor; intros * SCHED.
    inv SCHED; inv x.
    exfalso; eapply schedule_spin; eauto.
  Qed.
 *)

End Sanity.

