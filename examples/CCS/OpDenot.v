From CTree Require Import
	Utils
	CTrees
	Interp
	Equ
	Bisim
  Trans.

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

From CTreeCCS Require Import
	Syntax
	Denotation
	Operational.

Import CCSNotations.
Import DenNotations.
Import OpNotations.
Open Scope ccs_scope.

Set Implicit Arguments.
Set Contextual Implicit.

Lemma SRep': forall P a P'
               (STEP : step P a P'),
    step (!P) a (P' ∥ !P).
Proof.
  intros * TR; apply SRep,SParL; auto.
Qed.

Lemma trans_nil_inv : forall l p, ~ trans l nil p.
Proof.
  intros * abs; eapply stuckV_is_stuck; apply abs.
Qed.

Definition ι : option action -> @label ccsE :=
  fun a => match a with
        | None => tau
        | Some a => comm a
        end.

Definition γ : @label ccsE -> option action :=
  fun l => match l with
        | val x => None
        | tau   => None
        | obs (Act a) _ => Some a
        end.

Lemma are_opposite_op : forall a, are_opposite a (op a).
Proof.
  unfold op, are_opposite.
  intros []; cbn; rewrite eqb_refl; auto.
Qed.

Lemma are_opposite_are_op : forall a b,
    are_opposite a b ->
    a = op b.
Proof.
  unfold are_opposite,op; intros [] []; cbn; intuition.
  all:destruct (c =? c0)%string eqn:EQ; try easy.
  all:apply eqb_eq in EQ; subst; auto.
Qed.

Lemma use_channel_can_comm : forall c a,
  use_channel c a = false <->
  can_comm c (ι a) = true.
Proof.
  unfold can_comm, use_channel.
  intros ? [[]|]; cbn; split; auto.
  all:match goal with |- context[if ?b then _ else _] => destruct b; easy end.
Qed.

(* More general (?) notions of simulations *)
Definition forward (R : term -> ccs -> Prop) : Prop :=
  forall P P' q a,
		R P q ->
		P ⊢ a →op P' ->
	  exists q', trans (ι a) q q' /\ R P' q'.

Definition backward (R : term -> ccs -> Prop) : Prop :=
  forall P q q' l,
		R P q ->
    trans l q q' ->
	  exists P', P ⊢ γ l →op P' /\ R P' q'.

Definition bisim := exists R, forward R /\ backward R.

Definition bisim_model := fun P q => ⟦P⟧ ~ q.

Lemma complete : forward bisim_model.
Proof.
  unfold bisim_model; red.
  intros * HR TR.
  revert q HR.
  induction TR; intros * HR; cbn in *.
  - step in HR; edestruct HR as [[? TR EQ] _].
    apply trans_prefix.
    cbn in *; eauto.
  - step in HR; edestruct HR as [[? TR EQ] _].
    cbn; apply trans_TauV.
    cbn in *; eauto.
  - edestruct IHTR as (q1 & TR1 & EQ1); eauto.
    step in HR; edestruct HR as [[q' TR' EQ'] _].
    apply trans_plusL; apply TR1. (* Need to fix automation w.r.t. trans/transR *)
    eexists; split; [apply TR' |].
    cbn; rewrite <- EQ', <- EQ1; auto.
  - edestruct IHTR as (q2 & TR2 & EQ2); eauto.
    step in HR; edestruct HR as [[q' TR' EQ'] _].
    apply trans_plusR; apply TR2. (* Need to fix automation w.r.t. trans/transR *)
    eexists; split; [apply TR' |].
    cbn; rewrite <- EQ', <- EQ2; auto.
  - edestruct IHTR as (q1 & TR1 & EQ1); eauto.
    step in HR; edestruct HR as [[q' TR' EQ'] _].
    pL; apply TR1. (* Need to fix automation w.r.t. trans/transR *)
    eexists; split; [apply TR' |].
    cbn; rewrite <- EQ', <- EQ1; auto.
  - edestruct IHTR as (q2 & TR2 & EQ2); eauto.
    step in HR; edestruct HR as [[q' TR' EQ'] _].
    pR; apply TR2. (* Need to fix automation w.r.t. trans/transR *)
    eexists; split; [apply TR' |].
    cbn; rewrite <- EQ', <- EQ2; auto.
  - edestruct IHTR1 as (q1 & TR1' & EQ1); eauto.
    edestruct IHTR2 as (q2 & TR2' & EQ2); eauto.
    step in HR; edestruct HR as [[q' TR' EQ'] _].
    pS; [apply TR1' | apply TR2' | apply are_opposite_op]. (* Need to fix automation w.r.t. trans/transR *)
    eexists; split; [apply TR' |].
    cbn; rewrite <- EQ', <- EQ1, <- EQ2; auto.
  - edestruct IHTR as (q' & TR' & EQ'); eauto.
    eapply trans_new in TR' as (q'' & TR' & EQ''); [| apply use_channel_can_comm; eauto].
    step in HR; edestruct HR as [[q''' TR'' EQ'''] _].
    apply TR'.
    eexists; split.
    apply TR''.
    rewrite <- EQ''', EQ'', <- EQ'; auto.
  - rewrite unfold_bang', paraC in HR.
    exact (IHTR _ HR).
Qed.

Lemma correct : backward bisim_model.
Proof.
  unfold bisim_model; red.
  induction P; intros * HR TR; copy TR; step in HR; destruct HR as [_ B]; apply B in TR as [? TR' EQ']; clear B; cbn in *.
  - exfalso; eapply trans_nil_inv,TR'.
  - apply trans_TauV_inv in TR' as [EQ ->].
    eexists; split; [constructor |].
    rewrite <- EQ',EQ; auto.
  - apply trans_prefix_inv in TR' as [EQ ->].
    eexists; split; [constructor |].
    rewrite <- EQ',EQ; auto.
  - trans_para_invT TR'.
    + edestruct IHP1 as (P' & STEP & EQ''); [reflexivity | apply TRp |].
      eexists; split.
      apply SParL; eauto.
      rewrite <- EQ',EQ,<-EQ''.
      auto.
    + edestruct IHP2 as (P' & STEP & EQ''); [reflexivity | apply TRq |].
      eexists; split.
      apply SParR; eauto.
      rewrite <- EQ',EQ,<-EQ''.
      auto.
    + edestruct IHP1 as (P' & STEP & EQ''); [reflexivity | apply TRp |].
      edestruct IHP2 as (P'' & STEP' & EQ'''); [reflexivity | apply TRq |].
      eexists; split.
      apply SPar with a.
      apply STEP.
      apply are_opposite_sym in Op.
      rewrite <- (are_opposite_are_op _ Op).
      apply STEP'.
      rewrite <- EQ',EQ,<-EQ'',<-EQ'''.
      auto.
  - apply trans_plus_inv in TR' as [(? & TRp & EQ) | (? & TRq & EQ)].
    + edestruct IHP1 as (P' & STEP & EQ''); [reflexivity | apply TRp |].
      eexists; split.
      apply SSumL; eauto.
      rewrite <- EQ',EQ,<-EQ''.
      auto.
    + edestruct IHP2 as (P' & STEP & EQ''); [reflexivity | apply TRq |].
      eexists; split.
      apply SSumR; eauto.
      rewrite <- EQ',EQ,<-EQ''.
      auto.
  - apply trans_new_inv in TR' as (p' & COM & TR & EQ).
    edestruct IHP as (P' & STEP & EQ''); [reflexivity | apply TR |].
    exists (P' ∖ c); split.
    apply SRes; auto.
    rewrite use_channel_can_comm.
    destruct l; auto; destruct e; auto.
    rewrite <- EQ',EQ,TauI_sb, <-EQ''; auto.
  - trans_parabang_invT TR'.
    + edestruct IHP as (P' & STEP & EQ''); [reflexivity | apply TRp' |].
      exists (P' ∥ !P); split.
      apply SRep, SParL; auto.
      rewrite <- EQ',EQ,<-EQ''.
      rewrite parabang_eq.
      reflexivity.
    + edestruct IHP as (P' & STEP & EQ''); [reflexivity | apply TRq' |].
      rewrite EQ in EQ'; clear x EQ.
      exists (P' ∥ !P); split.
      apply SRep, SParL; auto.
      rewrite <- EQ', <-EQ''.
      cbn.
      rewrite (paraC ⟦P⟧), parabang_aux, parabang_eq.
      auto.
    + edestruct IHP as (P' & STEP & EQ''); [reflexivity | apply TRp' |].
      edestruct IHP as (P'' & STEP' & EQ'''); [reflexivity | apply TRq' |].
      exists (P' ∥ (P'' ∥ !P)).
      split.
      apply SRep.
      apply SPar with a.
      apply STEP.
      apply are_opposite_sym in Op.
      rewrite <- (are_opposite_are_op _ Op). 
      apply SRep', STEP'.
      rewrite <- EQ',EQ,<-EQ'',<-EQ'''.
      rewrite parabang_eq.
      cbn.
      rewrite paraA; auto.
    + edestruct IHP as (P' & STEP & EQ''); [reflexivity | apply TRq' |].
      edestruct IHP as (P'' & STEP' & EQ'''); [reflexivity | apply TRq'' |].
      rewrite EQ in EQ'; clear x EQ.
      rewrite <- EQ'', <- EQ''' in EQ'.
      rewrite paraC, parabang_aux, parabang_eq in EQ'.
      exists (P' ∥ (P'' ∥ !P)).
      split.
      apply SRep.
      apply SPar with a.
      apply STEP.
      apply are_opposite_sym in Op.
      rewrite <- (are_opposite_are_op _ Op).
      apply SRep', STEP'.
      rewrite <- EQ'; cbn; rewrite paraA; auto.
Qed.

Theorem is_bisim : bisim.
Proof.
  exists bisim_model; auto using correct,complete.
Qed.

(* We depend currently on
   - [Eqdep.Eq_rect_eq.eq_rect_eq]
   - [JMeq_eq]
 *)
Print Assumptions is_bisim.

(* bisim_sem ⟦u⟧ ⟦v⟧ <-> bisim_op u v *)
