From CTree Require Import
     CTree
	   Eq
	   Interp.Interp.

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
               (STEP : step a P P'),
    step a (!P) (P' ∥ !P).
Proof.
  intros * TR; apply SRep,SParL; auto.
Qed.

Lemma trans_nil_inv : forall l p, ~ trans l nil p.
Proof.
  intros * abs; eapply stuckS_is_stuck; apply abs.
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

Definition bisim R := forward R /\ backward R.
Definition bisimilar P q := exists R, bisim R /\ R P q.

Lemma bisimilar_bisim : bisim bisimilar.
Proof.
  split; red; intros * (R & BIS & HR) TR;
    pose proof BIS as [F B].
  - edestruct F as (? & ? & ?); eauto; eexists; split; eauto.
    exists R; split; auto.
  - edestruct B as (? & ? & ?); eauto; eexists; split; eauto.
    exists R; split; auto.
Qed.

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
    cbn; apply trans_step.
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
  - apply trans_step_inv in TR' as [EQ ->].
    eexists; split; [constructor |].
    rewrite <- EQ',EQ; auto.
  - apply trans_prefix_inv in TR' as [EQ ->].
    eexists; split; [constructor |].
    rewrite <- EQ', EQ.
    auto.
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
    rewrite <- EQ',EQ,sb_guard, <-EQ''; auto.
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

Theorem term_model_bisimilar : forall P, bisimilar P ⟦P⟧.
Proof.
  exists bisim_model; split; red; auto using correct,complete.
Qed.

(* We depend currently on
   - [Eqdep.Eq_rect_eq.eq_rect_eq]
 *)
Print Assumptions term_model_bisimilar.

Definition forward_inv (R : ccs -> term -> Prop) : Prop :=
  forall p p' Q l,
		R p Q ->
		trans l p p' ->
	  exists Q', Q ⊢ γ l →op Q' /\ R p' Q'.

Definition backward_inv (R : ccs -> term -> Prop) : Prop :=
  forall p Q Q' a,
		R p Q ->
    Q ⊢ a →op Q' ->
	  exists p', trans (ι a) p p' /\ R p' Q'.

Definition bisim_inv R := forward_inv R /\ backward_inv R.
Definition bisimilar_inv t u := exists R, bisim_inv R /\ R t u.

Lemma bisimilar_inv_bisim_inv : bisim_inv bisimilar_inv.
Proof.
 split; red; intros * (R & BIS & HR) TR;
    pose proof BIS as [F B].
  - edestruct F as (? & ? & ?); eauto; eexists; split; eauto.
    exists R; split; auto.
  - edestruct B as (? & ? & ?); eauto; eexists; split; eauto.
    exists R; split; auto.
Qed.

Definition rev {A B} (R : A -> B -> Prop) : B -> A -> Prop := fun b a => R a b.

Lemma bisim_bisim_inv : forall R, bisim R -> bisim_inv (rev R).
Proof.
  intros ? [F B]; split; red; unfold rev; cbn; intros * HR TR.
  edestruct B; eauto.
  edestruct F; eauto.
Qed.

Lemma term_model_bisimilar_inv : forall P, bisimilar_inv ⟦P⟧ P.
Proof.
  intros P; edestruct (@term_model_bisimilar P) as (R & BIS & HR); eauto.
  eexists; split.
  apply bisim_bisim_inv; eauto.
  auto.
Qed.

Lemma ιγ : forall l (t u : ccs),
    trans l t u ->
    ι (γ l) = l.
Proof.
  intros [] ? ? TR; cbn; auto.
  destruct e,v; auto.
  eapply trans_val_invT in TR; subst; destruct v.
Qed.

Lemma γι : forall l,
    γ (ι l) = l.
Proof.
  intros []; auto.
Qed.

Lemma cross_model_compose : forall T t u U,
    bisimilar t T ->
    Operational.bisim t u ->
    bisimilar u U ->
    T ~ U.
Proof.
  coinduction ? ?.
  intros * EQtT EQtu EQuU.
  pose proof bisimilar_bisim as [F B].
  step in EQtu; destruct EQtu as [F' B'].
  split; intros ? ? TRTt.
  - edestruct B as (T' & TRT' & ?); [apply EQtT | |]; eauto.
    edestruct F' as [U' TRU' ?]; eauto.
    edestruct F as (u' & TRu' & ?); [apply EQuU | |]; eauto.
    erewrite ιγ in TRu'; eauto.
  - edestruct B as (T' & TRT' & ?); [apply EQuU | |]; eauto.
    edestruct B' as [U' TRU' ?]; eauto.
    edestruct F as (u' & TRu' & ?); [apply EQtT | |]; eauto.
    erewrite ιγ in TRu'; eauto.
    cbn in *; eauto.
Qed.

Lemma cross_model_compose' : forall T t u U,
    bisimilar t T ->
    T ~ U ->
    bisimilar u U ->
    Operational.bisim t u.
Proof.
  coinduction ? ?.
  intros * EQtT EQtu EQuU.
  pose proof bisimilar_bisim as [F B].
  step in EQtu; destruct EQtu as [F' B'].
  split; intros ? ? TRTt.
  - edestruct F as (T' & TRT' & ?); [apply EQtT | |]; eauto.
    edestruct F' as [U' TRU' ?]; eauto.
    edestruct B as (u' & TRu' & ?); [apply EQuU | |]; eauto.
    erewrite γι in TRu'; eauto.
  - edestruct F as (T' & TRT' & ?); [apply EQuU | |]; eauto.
    edestruct B' as [U' TRU' ?]; eauto.
    edestruct B as (u' & TRu' & ?); [apply EQtT | |]; eauto.
    erewrite γι in TRu'; eauto.
    cbn in *; eauto.
Qed.

Lemma bisimilar_bisimilar_inv : forall t T,
    bisimilar_inv t T -> bisimilar T t.
Proof.
  intros * (R & [F B] & HR).
  exists (rev R); split; [| apply HR].
  split.
  red; intros; edestruct B; eauto.
  red; intros; edestruct F; eauto.
Qed.

Lemma embed_sound : forall t u, Operational.bisim t u -> ⟦t⟧ ~ ⟦u⟧.
Proof.
  intros * BIS.
  apply (gfp_fp b t u) in BIS; destruct BIS as [F B]; cbn in *.
  step; split.
  - intros ? T' TR.
    pose proof (@term_model_bisimilar t) as BISt.
    pose proof (@term_model_bisimilar u) as BISu.
    pose proof bisimilar_bisim as [F' B'].
    edestruct B' as (t' & TRt & EQTt); [apply BISt | ..]; eauto.
    edestruct F as [u' TR'' EQtu]; eauto.
    edestruct F' as (U' & TRu & EQuU); [apply BISu |..]; eauto.
    erewrite ιγ in TRu; eauto.
    eexists. apply TRu.
    eapply cross_model_compose; eauto.
  - intros ? U' TR.
    pose proof (@term_model_bisimilar_inv u) as BISu.
    pose proof (@term_model_bisimilar_inv t) as BISt.
    pose proof bisimilar_inv_bisim_inv as [F' B'].
    cbn.
    edestruct F' as (u' & TRu & EQuU); [apply BISu |..]; eauto.
    edestruct B as [t' TR'' EQtu]; eauto.
    edestruct B' as (T' & TRT & EQuT); [apply BISt |..]; eauto.
    erewrite ιγ in TRT; eauto.
    eexists. apply TRT.
    apply bisimilar_bisimilar_inv in EQuU, EQuT.
    eapply cross_model_compose; eauto.
Qed.

Lemma embed_complete : forall t u, ⟦t⟧ ~ ⟦u⟧ -> Operational.bisim t u.
Proof.
  intros * BIS.
  step in BIS; destruct BIS as [F B]; cbn in *.
  step; split.
  - intros ? T' TR.
    pose proof (@term_model_bisimilar t) as BISt.
    pose proof (@term_model_bisimilar u) as BISu.
    pose proof bisimilar_bisim as [F' B'].
    edestruct F' as (t' & TRt & EQTt); [apply BISt | ..]; eauto.
    edestruct F as [u' TR'' EQtu]; eauto.
    edestruct B' as (U' & TRu & EQuU); [apply BISu |..]; eauto.
    erewrite γι in TRu; eauto.
    eexists. apply TRu.
    eapply cross_model_compose'; eauto.
  - intros ? U' TR.
    pose proof (@term_model_bisimilar_inv u) as BISu.
    pose proof (@term_model_bisimilar_inv t) as BISt.
    pose proof bisimilar_inv_bisim_inv as [F' B'].
    cbn.
    edestruct B' as (u' & TRu & EQuU); [apply BISu |..]; eauto.
    edestruct B as [t' TR'' EQtu]; eauto.
    edestruct F' as (T' & TRT & EQuT); [apply BISt |..]; eauto.
    erewrite γι in TRT; eauto.
    eexists. apply TRT.
    apply bisimilar_bisimilar_inv in EQuU, EQuT.
    eapply cross_model_compose'; eauto.
Qed.

Theorem equiv_bisims : forall t u, ⟦t⟧ ~ ⟦u⟧ <-> Operational.bisim t u.
Proof.
  intros; split; eauto using embed_complete, embed_sound.
Qed.

