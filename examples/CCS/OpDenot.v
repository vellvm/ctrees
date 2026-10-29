Unset Universe Checking.

From CTree Require Import
     CTree
     Eq
     Interp.Fold.

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
  intros * abs; eapply trans_stuck_inv; apply abs.
Qed.

(*| As before one CCS action as one tree move using a helper [mstep]. 

[None] is a [τ] step, and [Some a] asks [Act a] and continues after the answer
[tt]. |*)
Variant mstep : option action -> ccs -> ccs -> Prop :=
| mtau (p q : ccs) : trans τ p q -> mstep None p q
| mact a (p : ccs) k : trans (comm a) p (β (Act a) k) -> mstep (Some a) p (k tt).

Lemma mstep_sbisim : forall a (p q p' : ccs),
    p ≃ q -> mstep a p p' -> exists q', mstep a q q' /\ p' ≃ q'.
Proof.
  intros * EQ ST. destruct ST as [p p' TR | a p k TR].
  - destruct (sbisimT_step _ _ _ _ EQ TR) as (s & TR' & HS).
    destruct (trans_τ_inv TR') as (q' & EQq). rewrite EQq in TR', HS.
    exists q'; split; [now constructor | exact HS].
  - destruct (sbisimT_step _ _ _ _ EQ TR) as (s & TR' & HS).
    destruct (trans_ask_inv TR') as (k' & EQk). rewrite EQk in TR', HS.
    exists (k' tt); split; [now constructor | exact (sbisim_sbm_passive _ _ _ HS tt)].
Qed.

Definition ι : option action -> label ccsE void :=
  fun a => match a with
        | None => τ
        | Some a => comm a
        end.

Definition γ : label ccsE void -> option action :=
  fun l => match l with
        | ask e => match e with Act a => Some a end
        | _ => None
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
    exists q', mstep a q q' /\ R P' q'.

Definition backward (R : term -> ccs -> Prop) : Prop :=
  forall P q q' a,
    R P q ->
    mstep a q q' ->
    exists P', P ⊢ a →op P' /\ R P' q'.

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

Definition bisim_model := fun P (q: ccs) => ⟦P⟧ ≃ q.

Lemma model_mstep : forall P a P', P ⊢ a →op P' -> exists p', mstep a ⟦P⟧ p' /\ p' ≃ ⟦P'⟧.
Proof.
  intros * ST. induction ST; cbn.
  - exists ⟦P⟧; split; [| reflexivity].
    exact (@mact a (prefix a ⟦P⟧) (fun _ => ⟦P⟧) (trans_prefix a ⟦P⟧)).
  - exists ⟦P⟧; split; [| reflexivity]. constructor. apply trans_step.
  - destruct IHST as (p' & MS & EQ). exists p'; split; auto.
    destruct MS; constructor; now apply trans_plusL.
  - destruct IHST as (p' & MS & EQ). exists p'; split; auto.
    destruct MS; constructor; now apply trans_plusR.
  - destruct IHST as (p' & MS & EQ). exists (para p' ⟦Q⟧); split; [| now rewrite EQ].
    destruct MS as [p p' TR | a p k TR].
    + constructor. apply (trans_paraL _ _ ⟦Q⟧) in TR. exact TR.
    + apply (trans_paraL _ _ ⟦Q⟧) in TR. exact (@mact a _ (fun i => para (k i) ⟦Q⟧) TR).
  - destruct IHST as (q' & MS & EQ). exists (para ⟦P⟧ q'); split; [| now rewrite EQ].
    destruct MS as [q q' TR | a q k TR].
    + constructor. apply (trans_paraR _ ⟦P⟧) in TR. exact TR.
    + apply (trans_paraR _ ⟦P⟧) in TR. exact (@mact a _ (fun i => para ⟦P⟧ (k i)) TR).
  - destruct IHST1 as (p1 & MS1 & EQ1), IHST2 as (p2 & MS2 & EQ2).
    inv MS1. inv MS2.
    exists (para (k tt) (k0 tt)); split; [| now rewrite EQ1, EQ2].
    constructor. eapply trans_paraSynch; [exact H0 | exact H1 | apply are_opposite_op].
  - destruct IHST as (p' & MS & EQ).
    destruct MS as [p p' TR | a p k TR].
    + destruct (trans_new _ c _ _ TR eq_refl) as (s & TRs & HS).
      destruct (trans_τ_inv TRs) as (q' & EQq). rewrite EQq in TRs, HS.
      exists q'; split; [now constructor |]. cbn in HS. unfold sbisimT. rewrite HS. now rewrite EQ.
    + assert (COMM : can_comm c (comm a) = true) by (destruct a; cbn in *; now rewrite FC).
      destruct (trans_new _ c _ _ TR COMM) as (s & TRs & HS).
      destruct (trans_ask_inv TRs) as (k' & EQk). rewrite EQk in TRs, HS.
      exists (k' tt); split; [now constructor |]. cbn in HS.
      rewrite (sbisim_sbm_passive _ _ _ HS tt). now rewrite EQ.
  - destruct IHST as (p' & MS & EQ). cbn in MS.
    assert (E : para ⟦P⟧ (bang ⟦P⟧) ≃ bang ⟦P⟧) by (rewrite paraC; symmetry; apply unfold_bang').
    destruct (mstep_sbisim E MS) as (q' & MS' & EQ').
    exists q'; split; [exact MS' | now rewrite <- EQ', EQ].
Qed.

Lemma model_mstep_inv : forall P a p', mstep a ⟦P⟧ p' -> exists P', P ⊢ a →op P' /\ ⟦P'⟧ ≃ p'.
Proof.
  induction P; intros oa p' MS; cbn in *; inversion MS as [p p'' TR | b p k TR]; subst.
  all: try now apply trans_stuck_inv in TR.
  - apply trans_step_inv' in TR as (EQ & _). inv EQ.
    exists P; split; [constructor | unfold sbisimT; now rewrite EQ0].
  - apply trans_step_inv' in TR as (_ & abs). discriminate.
  - apply trans_prefix_inv in TR as (_ & abs). discriminate.
  - apply trans_prefix_inv in TR as (EQ & EQl). inv EQl. dependent destruction EQ.
    exists P; split; [constructor | unfold sbisimT; now rewrite (EQ tt)].
  - unfold comm in *. trans_para_invT TR.
    + destruct (trans_τ_inv TRp) as (t & EQt). rewrite EQt in TRp, EQ.
      destruct (IHP1 _ _ (mtau TRp)) as (P' & ST & EQ').
      exists (P' ∥ P2); split; [now constructor |]. cbn. inv EQ. unfold sbisimT. rewrite EQ0. now rewrite EQ'.
    + destruct (trans_τ_inv TRq) as (t & EQt). rewrite EQt in TRq, EQ.
      destruct (IHP2 _ _ (mtau TRq)) as (P' & ST & EQ').
      exists (P1 ∥ P'); split; [now constructor |]. cbn. inv EQ. unfold sbisimT. rewrite EQ0. now rewrite EQ'.
    + destruct (IHP1 _ _ (mact TRp)) as (P1' & ST1 & EQ1).
      destruct (IHP2 _ _ (mact TRq)) as (P2' & ST2 & EQ2).
      exists (P1' ∥ P2'); split.
      * apply SPar with a; [exact ST1 |]. apply are_opposite_sym in Op. rewrite <- (are_opposite_are_op _ Op). exact ST2.
      * cbn. inv EQ. unfold sbisimT. rewrite EQ0. now rewrite EQ1, EQ2.
  - unfold comm in *. trans_para_invT TR; try discriminate.
    + destruct (trans_ask_inv TRp) as (g & EQg). rewrite EQg in TRp, EQ.
      destruct (IHP1 _ _ (mact TRp)) as (P' & ST & EQ').
      exists (P' ∥ P2); split; [now constructor |]. cbn. dependent destruction EQ. unfold sbisimT. rewrite (EQ tt). now rewrite EQ'.
    + destruct (trans_ask_inv TRq) as (g & EQg). rewrite EQg in TRq, EQ.
      destruct (IHP2 _ _ (mact TRq)) as (P' & ST & EQ').
      exists (P1 ∥ P'); split; [now constructor |]. cbn. dependent destruction EQ. unfold sbisimT. rewrite (EQ tt). now rewrite EQ'.
  - apply trans_plus_inv in TR as [(q & TRq & EQ) | (q & TRq & EQ)].
    + destruct (trans_τ_inv TRq) as (t & EQt). rewrite EQt in TRq, EQ.
      destruct (IHP1 _ _ (mtau TRq)) as (P' & ST & EQ').
      exists P'; split; [now constructor |]. inv EQ. unfold sbisimT. rewrite EQ0. exact EQ'.
    + destruct (trans_τ_inv TRq) as (t & EQt). rewrite EQt in TRq, EQ.
      destruct (IHP2 _ _ (mtau TRq)) as (P' & ST & EQ').
      exists P'; split; [now constructor |]. inv EQ. unfold sbisimT. rewrite EQ0. exact EQ'.
  - apply trans_plus_inv in TR as [(q & TRq & EQ) | (q & TRq & EQ)].
    + destruct (trans_ask_inv TRq) as (g & EQg). rewrite EQg in TRq, EQ.
      destruct (IHP1 _ _ (mact TRq)) as (P' & ST & EQ').
      exists P'; split; [now constructor |]. dependent destruction EQ. unfold sbisimT. rewrite (EQ tt). exact EQ'.
    + destruct (trans_ask_inv TRq) as (g & EQg). rewrite EQg in TRq, EQ.
      destruct (IHP2 _ _ (mact TRq)) as (P' & ST & EQ').
      exists P'; split; [now constructor |]. dependent destruction EQ. unfold sbisimT. rewrite (EQ tt). exact EQ'.
  - apply trans_new_inv in TR as (q & COMM & TRq & EQ).
    destruct (trans_τ_inv TRq) as (t & EQt).
    destruct q as [t0 | Y e g0]; [| inv EQt].
    destruct (IHP _ _ (mtau TRq)) as (P' & ST & EQ').
    exists (P' ∖ c); split; [now constructor |]. cbn in EQ |- *. inv EQ.
    unfold sbisimT. rewrite EQ0, sbisim_guard. now rewrite EQ'.
  - apply trans_new_inv in TR as (q & COMM & TRq & EQ).
    destruct (trans_ask_inv TRq) as (g & EQg).
    destruct q as [t0 | Y e g0]; [inv EQg |]. dependent destruction EQg.
    destruct (IHP _ _ (mact TRq)) as (P' & ST & EQ').
    exists (P' ∖ c); split.
    + constructor; [exact ST |]. destruct b; cbn in *; destruct (c =? c0)%string; easy.
    + cbn in EQ |- *. dependent destruction EQ. unfold sbisimT. rewrite (EQ tt), sbisim_guard. now rewrite EQ'.
  - unfold bang, comm in *. trans_parabang_invT TR.
    + destruct p'0 as [t | ]; [| destruct (trans_τ_inv TRp') as (? & abs); inv abs].
      destruct (IHP _ _ (mtau TRp')) as (P1 & ST & EQ'). cbn in EQ. inv EQ.
      exists (P1 ∥ !P); split; [now apply SRep, SParL |].
      cbn. unfold sbisimT. rewrite EQ0, parabang_eq. now rewrite EQ'.
    + destruct q' as [t | ]; [| destruct (trans_τ_inv TRq') as (? & abs); inv abs].
      destruct (IHP _ _ (mtau TRq')) as (P1 & ST & EQ'). cbn in EQ. inv EQ.
      exists (P1 ∥ !P); split; [now apply SRep, SParL |].
      cbn. unfold sbisimT. rewrite EQ0, (paraC ⟦P⟧), parabang_aux, parabang_eq. now rewrite EQ'.
    + destruct (IHP _ _ (mact TRp')) as (P1 & ST1 & EQ1).
      destruct (IHP _ _ (mact TRq')) as (P2 & ST2 & EQ2).
      exists (P1 ∥ (P2 ∥ !P)); split.
      * apply SRep. apply SPar with a; [exact ST1 |].
        apply are_opposite_sym in Op. rewrite <- (are_opposite_are_op _ Op). now apply SRep'.
      * cbn. inv EQ. unfold sbisimT. rewrite EQ0, parabang_eq, paraA. now rewrite EQ1, EQ2.
    + destruct (IHP _ _ (mact TRq')) as (P1 & ST1 & EQ1).
      destruct (IHP _ _ (mact TRq'')) as (P2 & ST2 & EQ2).
      exists (P1 ∥ (P2 ∥ !P)); split.
      * apply SRep. apply SPar with a; [exact ST1 |].
        apply are_opposite_sym in Op. rewrite <- (are_opposite_are_op _ Op). now apply SRep'.
      * cbn. inv EQ. unfold sbisimT. rewrite EQ0, (paraC ⟦P⟧), parabang_aux, parabang_eq, paraA. now rewrite EQ1, EQ2.
  - unfold bang, comm in *. trans_parabang_invT TR; try discriminate.
    + destruct (trans_ask_inv TRp') as (g & EQg).
      destruct p' as [t0 | Y e g0]; [inv EQg |]. dependent destruction EQg.
      destruct (IHP _ _ (mact TRp')) as (P1 & ST & EQ').
      exists (P1 ∥ !P); split; [now apply SRep, SParL |].
      cbn in EQ |- *. dependent destruction EQ. unfold sbisimT. rewrite (EQ tt), parabang_eq. now rewrite EQ'.
    + destruct (trans_ask_inv TRq') as (g & EQg).
      destruct q' as [t0 | Y e g0]; [inv EQg |]. dependent destruction EQg.
      destruct (IHP _ _ (mact TRq')) as (P1 & ST & EQ').
      exists (P1 ∥ !P); split; [now apply SRep, SParL |].
      cbn in EQ |- *. dependent destruction EQ. unfold sbisimT.
      rewrite (EQ tt), (paraC ⟦P⟧), parabang_aux, parabang_eq. now rewrite EQ'.
Qed.

Lemma complete : forward bisim_model.
Proof.
  unfold bisim_model; red. intros * HR ST.
  destruct (model_mstep ST) as (p' & MS & EQ).
  destruct (mstep_sbisim HR MS) as (q' & MS' & EQ').
  exists q'; split; [exact MS' | now rewrite <- EQ].
Qed.

Lemma correct : backward bisim_model.
Proof.
  unfold bisim_model; red. intros * HR MS.
  symmetry in HR. destruct (mstep_sbisim HR MS) as (p' & MS' & EQ).
  destruct (model_mstep_inv MS') as (P' & ST & EQ').
  exists P'; split; [exact ST | now rewrite EQ'].
Qed.

Theorem term_model_bisimilar : forall P, bisimilar P ⟦P⟧.
Proof.
  exists bisim_model; split; red; auto using correct,complete.
Qed.

Lemma ιγ : forall l (t : ccs) u,
    trans l t u ->
    ι (γ l) = l.
Proof.
  intros [| ? [] | ? e y | []] ? ? TR; cbn; auto.
  now apply trans_rcv_active_inv in TR.
Qed.

Lemma γι : forall l,
    γ (ι l) = l.
Proof.
  intros []; auto.
Qed.

(* Naming *)
Lemma cross_model_compose : forall T t u U,
    bisimilar t T ->
    Operational.bisim t u ->
    bisimilar u U ->
    T ≃ U.
Proof.
  intros * EQtT EQtu EQuU. apply sbm_sbisim. revert T t u U EQtT EQtu EQuU. unfold sbmbisim.
  coinduction r cih.
  intros * EQtT EQtu EQuU.
  pose proof bisimilar_bisim as [F B].
  step in EQtu; destruct EQtu as [F' B'].
  split; apply ss_ssm; intros l s TR;
    (destruct l as [| ? e | ? e y | []]; [| | now apply trans_rcv_active_inv in TR]).
  - destruct (trans_τ_inv TR) as (T' & EQ). rewrite EQ in TR.
    edestruct B as (t' & ST & ?); [apply EQtT | exact (mtau TR) |].
    edestruct F' as [u' STu ?]; [exact ST |].
    edestruct F as (U' & MS & ?); [apply EQuU | exact STu |]. inv MS.
    exists (α T'), (α U'); split; [exact EQ | split; [assumption | constructor; eapply cih; eauto]].
  - destruct e as [a]. destruct (trans_ask_inv TR) as (k & EQ). rewrite EQ in TR.
    edestruct B as (t' & ST & ?); [apply EQtT | exact (mact TR) |].
    edestruct F' as [u' STu ?]; [exact ST |].
    edestruct F as (U' & MS & ?); [apply EQuU | exact STu |]. inv MS.
    exists (β (Act a) k), (β (Act a) k0); split; [exact EQ | split; [assumption | constructor; intros []; eapply cih; eauto]].
  - destruct (trans_τ_inv TR) as (U' & EQ). rewrite EQ in TR.
    edestruct B as (u' & ST & ?); [apply EQuU | exact (mtau TR) |].
    edestruct B' as [t' STt ?]; [exact ST |].
    edestruct F as (T' & MS & ?); [apply EQtT | exact STt |]. inv MS.
    exists (α U'), (α T'); split; [exact EQ | split; [assumption | constructor; unfold flip; eapply cih; [exact H1 | exact H0 | exact H]]].
  - destruct e as [a]. destruct (trans_ask_inv TR) as (k & EQ). rewrite EQ in TR.
    edestruct B as (u' & ST & ?); [apply EQuU | exact (mact TR) |].
    edestruct B' as [t' STt ?]; [exact ST |].
    edestruct F as (T' & MS & ?); [apply EQtT | exact STt |]. inv MS.
    exists (β (Act a) k), (β (Act a) k0); split; [exact EQ | split; [assumption | constructor; intros []; unfold flip; eapply cih; [exact H1 | exact H0 | exact H]]].
Qed.

Lemma cross_model_compose' : forall T t u U,
    bisimilar t T ->
    T ≃ U ->
    bisimilar u U ->
    Operational.bisim t u.
Proof.
  unfold Operational.bisim.
  coinduction r cih.
  intros * EQtT EQTU EQuU.
  pose proof bisimilar_bisim as [F B].
  split.
  - intros a t' ST.
    edestruct F as (T' & MS & ?); [apply EQtT | exact ST |].
    destruct (mstep_sbisim EQTU MS) as (U' & MSU & EQU).
    edestruct B as (u' & STu & ?); [apply EQuU | exact MSU |].
    exists u'; [exact STu | eapply cih; eauto].
  - cbn. intros a u' ST.
    edestruct F as (U' & MS & ?); [apply EQuU | exact ST |].
    symmetry in EQTU. destruct (mstep_sbisim EQTU MS) as (T' & MST & EQT).
    edestruct B as (t' & STt & ?); [apply EQtT | exact MST |].
    exists t'; [exact STt | eapply cih; [eassumption | symmetry; exact EQT | eassumption]].
Qed.

Lemma embed_sound : forall t u, Operational.bisim t u -> ⟦t⟧ ≃ ⟦u⟧.
Proof.
  intros * BIS. eapply cross_model_compose; eauto using term_model_bisimilar.
Qed.

Lemma embed_complete : forall t u, ⟦t⟧ ≃ ⟦u⟧ -> Operational.bisim t u.
Proof.
  intros * BIS. eapply cross_model_compose'; eauto using term_model_bisimilar.
Qed.

Theorem equiv_bisims : forall t u, ⟦t⟧ ≃ ⟦u⟧ <-> Operational.bisim t u.
Proof.
  intros; split; eauto using embed_complete, embed_sound.
Qed.
