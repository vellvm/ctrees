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

(* Notation "t ⊢ l →sem u" := (trans l ⟦t⟧ ⟦u⟧) (at level 10) : ccs_scope. *)

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

Lemma trans_model : forall P l q,
    trans l ⟦P⟧ q ->
    exists Q, q ≅ ⟦Q⟧.
Proof.
  induction P; intros * TR.
  - apply trans_nil_inv in TR; easy.
  - apply trans_TauV_inv in TR as [EQ ->]; eauto.
  - apply trans_prefix_inv in TR as [EQ ->]; eauto.
  - trans_para_invT TR; fold model in *.
    + apply IHP1 in TRp as [Q' ?EQ].
      rewrite EQ0 in EQ.
      exists (Q' ∥ P2); auto.
    + apply IHP2 in TRq as [Q' ?EQ].
      rewrite EQ0 in EQ.
      exists (P1 ∥ Q'); auto.
    + apply IHP1 in TRp as [P' ?EQ].
      apply IHP2 in TRq as [Q' ?EQ].
      rewrite EQ0,EQ1 in EQ.
      exists (P' ∥ Q'); auto.
  - apply trans_plus_inv in TR as [(?&TR&EQ)|(?&TR&EQ)]; fold model in *.
    + apply IHP1 in TR as [? ?].
      rewrite <- EQ in H; eauto.
    + apply IHP2 in TR as [? ?].
      rewrite <- EQ in H; eauto.
  - apply trans_new_inv in TR as (? & ? & TR & EQ); fold model in *.
    apply IHP in TR as [? ?].
    rewrite H0 in EQ.
    exists (x0 ∖ c).
    auto.
  - (* unsolvable, the model steps to a parabang that is not the model of anyone up-to [equ] *)
Abort.

Lemma trans_model : forall P l q,
    trans l ⟦P⟧ q ->
    exists Q, q ~ ⟦Q⟧.
Proof.
  induction P; intros * TR.
  - apply trans_nil_inv in TR; easy.
  - apply trans_TauV_inv in TR as [EQ ->]; fold model in *.
    setoid_rewrite EQ; eauto.
  - apply trans_prefix_inv in TR as [EQ ->]; fold model in *.
    setoid_rewrite EQ; eauto.
  - trans_para_invT TR; fold model in *.
    + apply IHP1 in TRp as [Q' ?EQ].
      apply equ_sbisim_subrelation in EQ.
      rewrite EQ0 in EQ.
      exists (Q' ∥ P2); auto.
    + apply IHP2 in TRq as [Q' ?EQ].
      apply equ_sbisim_subrelation in EQ.
      rewrite EQ0 in EQ.
      exists (P1 ∥ Q'); auto.
    + apply IHP1 in TRp as [P' ?EQ].
      apply IHP2 in TRq as [Q' ?EQ].
      apply equ_sbisim_subrelation in EQ.
      rewrite EQ0,EQ1 in EQ.
      exists (P' ∥ Q'); auto.
  - apply trans_plus_inv in TR as [(?&TR&EQ)|(?&TR&EQ)]; fold model in *.
    + apply IHP1 in TR as [? ?].
      rewrite <- EQ in H; eauto.
    + apply IHP2 in TR as [? ?].
      rewrite <- EQ in H; eauto.
  - apply trans_new_inv in TR as (? & ? & TR & EQ); fold model in *.
    apply IHP in TR as [? ?].
    apply equ_sbisim_subrelation in EQ.
    rewrite H0 in EQ.
    exists (x0 ∖ c).
    auto.
  - trans_parabang_invT TR; fold model in *.
    + apply IHP in TRp' as [Q' ?EQ].
      apply equ_sbisim_subrelation in EQ.
      rewrite EQ0 in EQ.
      rewrite parabang_eq in EQ.
      exists (Q' ∥ !P).
      cbn; auto.
    + apply IHP in TRq' as [Q' ?EQ].
      apply equ_sbisim_subrelation in EQ.
      rewrite EQ0 in EQ.
      rewrite paraC, parabang_aux in EQ.
      rewrite parabang_eq in EQ.
      exists (Q' ∥ !P).
      cbn; auto.
    + apply IHP in TRp' as [Q' ?EQ].
      apply IHP in TRq' as [Q'' ?EQ].
      apply equ_sbisim_subrelation in EQ.
      rewrite EQ0,EQ1 in EQ.
      rewrite parabang_eq in EQ.
      exists ((Q' ∥ Q'') ∥ !P).
      cbn; auto.
    + apply IHP in TRq'  as [Q' ?EQ].
      apply IHP in TRq'' as [Q'' ?EQ].
      apply equ_sbisim_subrelation in EQ.
      rewrite EQ0,EQ1 in EQ.
      rewrite paraC, parabang_aux in EQ.
      rewrite parabang_eq in EQ.
      exists ((Q' ∥ Q'') ∥ !P).
      cbn; auto.
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

Definition bisim_model := fun P q => ⟦P⟧ ~ q.

Lemma complete_func : forward bisim_model.
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
    step in HR; edestruct HR as [[q'' TR'' EQ''] _].
    apply trans_new.
    apply TR'.
    apply use_channel_can_comm; auto.
    eexists; split.
    apply TR''.
    rewrite <- EQ'', <- EQ'; auto.
  - rewrite unfold_bang', paraC in HR.
    exact (IHTR _ HR).
Qed.



Definition forward_func (R : term -> term -> Prop) : Prop :=
  forall P P' Q a,
		R P Q ->
		P ⊢ a →op P' ->
	  exists Q', trans (ι a) ⟦Q⟧ ⟦Q'⟧ /\ R P' Q'.

Definition backward_func (R : term -> term -> Prop) : Prop :=
  forall P Q Q' l,
		R P Q ->
    trans l ⟦Q⟧ ⟦Q'⟧ ->
	  exists P', P ⊢ γ l →op P' /\ R P' Q'.

Definition bisimilar := exists R, forward_func R /\ backward_func R.

(* Need to move toward [bisim] instead of [equ].
   Fixing the proof will require a whole new bunch of inversion lemmas unfortunately

Actually need to change stuff: the semantics does not always reduce to models of terms
 *)
Definition equ_models := fun P Q => ⟦P⟧ ~ ⟦Q⟧.

Lemma complete_func : forward_func equ_models.
Proof.
  unfold equ_models; red.
  induction P; intros * HR TR; cbn in *.
  - inv TR.
  - clear IHP.
    inv TR.
    pose proof @trans_TauV _ _ ⟦ P' ⟧ as TR.
    copy HR; copy TR.
    step in HR; destruct HR as [F _].
    apply F in TR as [? TR' EQ]; clear F.
    pose proof trans_model _ TR' as [Q' ?].
    exists Q'; split.
    apply TR'.
    eexists; split; [| reflexivity].
    rewrite <- HR; apply trans_TauV.
  - inv TR.
    eexists; split; [| reflexivity].
    rewrite <- HR; apply trans_prefix.
  - inv TR.
    + edestruct IHP1 as (? & ? & EQ); eauto.
      rewrite <- EQ in H; clear x EQ.
      setoid_rewrite <- HR.
      exists (P'0 ∥ P2) ; split.
      cbn; apply trans_paraL; eassumption.
      reflexivity.
    + edestruct IHP2 as (? & ? & EQ); eauto.
      rewrite <- EQ in H; clear x EQ.
      setoid_rewrite <- HR.
      exists (P1 ∥ Q'); split.
      apply trans_paraR; eassumption.
      reflexivity.
    + edestruct IHP1 as (? & ? & EQ1); eauto.
      edestruct IHP2 as (? & ? & EQ2); eauto.
      rewrite <- EQ1 in H; rewrite <- EQ2 in H0; clear x x0 EQ1 EQ2.
      exists (P'0 ∥ Q'); split.
      rewrite <- HR; eapply trans_paraSynch; cbn in *; eauto.
      apply are_opposite_op.
      reflexivity.
  - inv TR.
    + edestruct IHP1 as (? & ? & EQ); eauto.
      rewrite <- EQ in H.
      eexists; split; [| reflexivity].
      rewrite <- HR; apply trans_plusL; eassumption.
    + edestruct IHP2 as (? & ? & EQ); eauto.
      rewrite <- EQ in H.
      eexists; split; [| reflexivity].
      rewrite <- HR; apply trans_plusR; eassumption.
  - inv TR.
    edestruct IHP as (? & ? & EQ); eauto.
    rewrite <- EQ in H.
    eexists; split; [| reflexivity].
    rewrite <- HR; apply trans_new; eauto.
    apply use_channel_can_comm; auto.
  - admit.
Admitted.

(* Proof broken due to the weaking in [trans_model].
   Needs to be redone against the bigger bisimulation invariant anyway.
 *)
Lemma correct_func : backward_func equ_models.
Proof.
  (*
  unfold equ_models; red; induction P; intros * HR TR;
    cbn in *; rewrite <- HR in TR.
  - exfalso; eapply trans_nil_inv,TR.
  - apply trans_TauV_inv in TR as [EQ ->].
    eexists; split; [constructor |].
    symmetry; auto.
  - apply trans_prefix_inv in TR as [EQ ->].
    eexists; split; [constructor |].
    symmetry; auto.
  - trans_para_invT TR.
    + edestruct trans_model; eauto.
      rewrite H in TRp.
      apply IHP1 in TRp; auto.
      destruct TRp as (? & ? & ?).
      eexists.
      split.
      apply SParL; eauto.
      cbn; rewrite EQ,H,H1; reflexivity.
    + edestruct trans_model; eauto.
      rewrite H in TRq.
      apply IHP2 in TRq; auto.
      destruct TRq as (? & ? & ?).
      eexists.
      split.
      apply SParR; eauto.
      cbn; rewrite EQ,H,H1; reflexivity.
    + edestruct trans_model; [exact TRp |].
      edestruct trans_model; [exact TRq |].
      rewrite H in TRp.
      rewrite H0 in TRq.
      apply IHP1 in TRp; auto.
      apply IHP2 in TRq; auto.
      destruct TRp as (? & ? & ?).
      destruct TRq as (? & ? & ?).
      cbn in *.
      apply are_opposite_sym in Op.
      apply are_opposite_are_op in Op; subst.
      eexists.
      split.
      eapply SPar; eauto.
      cbn; rewrite EQ,H,H0,H2,H4; reflexivity.
  - apply trans_plus_inv in TR as [(? & TR & EQ) | (? & TR & EQ)].
    + edestruct trans_model; eauto.
      rewrite H in TR.
      apply IHP1 in TR as (P' & ? & ?); auto.
      eexists; split; [apply SSumL; eauto |].
      rewrite H1,EQ,H; reflexivity.
    + edestruct trans_model; eauto.
      rewrite H in TR.
      apply IHP2 in TR as (P' & ? & ?); auto.
      eexists; split; [apply SSumR; eauto |].
      rewrite H1,EQ,H; reflexivity.
  - apply trans_new_inv in TR as (? & ? & TR & EQ).
    edestruct trans_model; eauto.
    rewrite H0 in TR.
    apply IHP in TR as (P' & ? & ?); auto.
    eexists; split.
    constructor; eauto.
    apply use_channel_can_comm; cbn; auto.
    destruct l; try now inv H.
    destruct e; auto.
    cbn; rewrite EQ, H2, H0; auto.
Qed.
   *)
Admitted.

Theorem bisim : bisimilar.
Proof.
  exists equ_models.
  auto using correct_func, complete_func.
Qed.

(* Simpler forward, but not a backward *)
Lemma complete_func_simpler : forward_func eq.
Proof.
  red.
  induction P; intros * HR TR; cbn in *.
  - inv TR.
  - inv TR.
    eexists; split; [| reflexivity].
    apply trans_TauV.
  - inv TR.
    eexists; split; [| reflexivity].
    apply trans_prefix.
  - inv TR.
    + edestruct IHP1 as (? & ? & ?); subst; eauto.
      eexists; split; [| reflexivity].
      apply trans_paraL; eassumption.
    + edestruct IHP2 as (? & ? & ?); subst; eauto.
      eexists; split; [| reflexivity].
      apply trans_paraR; eassumption.
    + edestruct IHP1 as (? & trP & ?); eauto.
      edestruct IHP2 as (? & trQ & ?); eauto.
      subst; eexists; split; [| reflexivity].
      eapply (trans_paraSynch trP trQ).
      apply are_opposite_op.
  - inv TR.
    + edestruct IHP1 as (? & ? & ?); eauto; subst.
      eexists; split; [| reflexivity].
      apply trans_plusL; eassumption.
    + edestruct IHP2 as (? & ? & ?); eauto; subst.
      eexists; split; [| reflexivity].
      apply trans_plusR; eassumption.
  - inv TR.
    edestruct IHP as (? & ? & ?); eauto; subst.
    eexists; split; [| reflexivity].
    apply trans_new; eauto.
    apply use_channel_can_comm; auto.
  - admit.
Admitted.
