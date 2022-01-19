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

Lemma use_channel_can_comm : forall c a,
  use_channel c a = false <->
  can_comm c (ι a) = true.
Proof.
  unfold can_comm, use_channel.
  intros ? [[]|]; cbn; split; auto.
  all:match goal with |- context[if ?b then _ else _] => destruct b; easy end.
Qed.

Definition forward_func (R : term -> term -> Prop) : Prop :=
  forall P P' Q a,
		R P Q ->
		P ⊢ a →op P' ->
	  exists Q', trans (ι a) ⟦Q⟧ ⟦Q'⟧ /\ R P' Q'.

Lemma complete_func : forward_func eq.
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
Qed.

Definition backward_func (R : term -> term -> Prop) : Prop :=
  forall P Q Q' l,
		R P Q ->
    trans l ⟦Q⟧ ⟦Q'⟧ ->
	  exists P', P ⊢ γ l →op P' /\ R P' Q'.

Lemma correct_func : backward_func (fun P Q => ⟦P⟧ ≅ ⟦Q⟧).
Proof.
  red; induction P; intros * HR TR;
    cbn in *; rewrite <- HR in TR.
  - exfalso; eapply trans_nil_inv,TR.
  - apply trans_TauV_inv in TR as [EQ ->].
    eexists; split; [constructor |].
    symmetry; auto.
  - apply trans_prefix_inv in TR as [EQ ->].
    eexists; split; [constructor |].
    symmetry; auto.
  - trans_para_invT TR.
    + (* Need to ensure that trans led to the model of someone? *)
      (* apply IHP1 in TRp. *)
      (* eexists; split. *)
      (* apply SParL; eauto. *)
Admitted.

Definition forward (R : term -> ccs -> Prop) : Prop :=
  forall P P' Q a,
		R P Q ->
		P ⊢ a →op P' ->
	  exists Q', trans (ι a) Q Q' /\ R P' Q'.

Definition bisim_rel := fun P q => q ≅ ⟦P⟧.
Arguments bisim_rel/.

Lemma complete : forward bisim_rel.
Proof.
  red.
  induction P; intros * HR TR; cbn in *.
  - inv TR.
  - inv TR.
    exists ⟦ P' ⟧.
    split; [| reflexivity].
    rewrite HR; apply trans_TauV.
  - inv TR.
    exists ⟦ P' ⟧.
    split; [| reflexivity].
    rewrite HR. apply trans_prefix.
  - inv TR.
    + edestruct IHP1 as (? & ? & EQ); eauto.
      eexists; split.
      rewrite HR; apply trans_paraL; eassumption.
      rewrite EQ; reflexivity.
    + edestruct IHP2 as (? & ? & EQ); eauto.
      eexists; split.
      rewrite HR; apply trans_paraR; eassumption.
      rewrite EQ; reflexivity.
    + edestruct IHP1 as (? & ? & EQ1); eauto.
      edestruct IHP2 as (? & ? & EQ2); eauto.
      eexists; split.
      rewrite HR; eapply trans_paraSynch; cbn in *; eauto.
      apply are_opposite_op.
      rewrite EQ1,EQ2; reflexivity.
  - inv TR.
    + edestruct IHP1 as (? & ? & EQ); eauto.
      eexists; split.
      rewrite HR; apply trans_plusL; eassumption.
      rewrite EQ; reflexivity.
    + edestruct IHP2 as (? & ? & EQ); eauto.
      eexists; split.
      rewrite HR; apply trans_plusR; eassumption.
      rewrite EQ; reflexivity.
  - inv TR.
    edestruct IHP as (? & ? & EQ); eauto.
    eexists.
    split.
    rewrite HR.
    apply trans_new; eauto.
    apply use_channel_can_comm; auto.
    (* Need congruence for restrict *)
    admit.
Admitted.

Definition backward (R : term -> ccs -> Prop) : Prop :=
  forall P Q Q' l,
		R P Q ->
    trans l Q Q' ->
	  exists P', P ⊢ γ l →op P' /\ R P' Q'.

