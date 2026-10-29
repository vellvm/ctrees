(*|
AI: Comparison between the pre-refactor [obs] semantics, where a [Vis] node
asks its question and receives the answer in a single step, and the current
[ask]/[rcv] semantics. The [obs] transition relation below is copied from
[dev] ([theories/Eq/Trans.v]); the only change is that value labels are typed
by the return type. Results: [ask]/[rcv] bisimilarity implies [obs]
bisimilarity ([sbisim_osbisim]), and the converse fails ([P_osbisim_Q],
[P_not_sbisim_Q]); both are packaged in [osbisim_strictly_coarser].
|*)

From Stdlib Require Import Basics Program.Equality.

From Coinduction Require Import all.

From ITree Require Import Core.Subevent.

From CTree Require Import
     CTree
     Eq.Shallow
     Eq.Equ
     Eq.Trans
     Eq.SBisim.

Import CTree CTreeNotations EquNotations SBisimNotations.
Open Scope ctree.

Set Implicit Arguments.

Section ObsTrans.

  Context {E B : Type -> Type} {R : Type}.

  Notation S' := (ctree' E B R).
  Notation S  := (ctree  E B R).

  Variant olabel : Type :=
    | oτ
    | oobs {X : Type} (e : E X) (v : X)
    | oval (v : R).

  Inductive otrans_ : olabel -> S' -> S' -> Prop :=

  | OTransbr {X} (c : B X) x k l t :
    otrans_ l (observe (k x)) t ->
    otrans_ l (BrF c k) t

  | OTransguard t t' l :
    otrans_ l (observe t) t' ->
    otrans_ l (GuardF t) t'

  | OTranstau t u :
    u ≅ t ->
    otrans_ oτ (StepF t) (observe u)

  | OTransobs {X} (e : E X) k x t :
    k x ≅ t ->
    otrans_ (oobs e x) (VisF e k) (observe t)

  | OTransval r :
    otrans_ (oval r) (RetF r) StuckF.
  Hint Constructors otrans_ : core.

  Definition otrans l : S -> S -> Prop :=
    fun u v => otrans_ l (observe u) (observe v).

  Ltac FtoObs :=
    match goal with
      |- otrans_ _ _ ?t =>
        change t with (observe {| _observe := t |})
    end.

  #[local] Instance otrans_equ_aux1 l t :
    Proper (going (equ eq) ==> flip impl) (otrans_ l t).
  Proof.
    intros u u' equ; intros TR.
    inv equ; rename H into equ.
    __step_in_equ equ.
    revert u equ.
    dependent induction TR; intros; subst; eauto.
    + inv equ.
      * rewrite H2; eauto.
      * FtoObs.
        constructor.
        rewrite <- H.
        apply observing_sub_equ; eauto.
      * FtoObs.
        constructor.
        rewrite <- H, REL.
        apply observing_sub_equ; eauto.
      * FtoObs.
        constructor.
        rewrite <- H, REL.
        apply observing_sub_equ; eauto.
      * FtoObs.
        constructor.
        rewrite <- H.
        __step_equ; rewrite <- H2; constructor; intros.
        auto.
      * FtoObs.
        constructor.
        rewrite <- H.
        __step_equ; rewrite <- H2; constructor; intros.
        auto.
    + FtoObs.
      econstructor.
      rewrite H; symmetry; __step_equ; auto.
    + inv equ. eauto.
  Qed.

  #[local] Instance otrans_equ_aux2 l :
    Proper (going (equ eq) ==> going (equ eq) ==> impl) (otrans_ l).
  Proof.
    intros t t' eqt u u' equ TR.
    rewrite <- equ; clear u' equ.
    inv eqt; rename H into eqt.
    revert t' eqt.
    dependent induction TR; intros; auto.
    + __step_in_equ eqt; dependent induction eqt.
      econstructor.
      apply IHTR.
      rewrite REL; reflexivity.
    + __step_in_equ eqt; dependent induction eqt.
      econstructor.
      apply IHTR. rewrite REL; reflexivity.
    + __step_in_equ eqt; dependent induction eqt.
      econstructor. rewrite H,REL; auto.
    + __step_in_equ eqt; dependent induction eqt.
      econstructor.
      rewrite <- REL; eauto.
    + __step_in_equ eqt; dependent induction eqt.
      econstructor.
  Qed.

  #[global] Instance otrans_equ_ l :
    Proper (going (equ eq) ==> going (equ eq) ==> iff) (otrans_ l).
  Proof.
    intros ? ? eqt ? ? equ; split; intros TR.
    - eapply otrans_equ_aux2; eauto.
    - symmetry in equ; symmetry in eqt; eapply otrans_equ_aux2; eauto.
  Qed.

  #[global] Instance otrans_equ l :
    Proper (equ eq ==> equ eq ==> iff) (otrans l).
  Proof.
    intros ? ? eqt ? ? equ; unfold otrans.
    rewrite eqt, equ; reflexivity.
  Qed.

End ObsTrans.

Section Bridge.

  Context {E B : Type -> Type} {R : Type}.

  Notation S := (ctree E B R).

  Lemma otrans_trans_ : forall l (T U : ctree' E B R),
      otrans_ l T U ->
      match l with
      | oτ => trans τ (go T) (go U)
      | oobs e v => exists k, trans (ask e) (go T) (β e k) /\ go U ≅ k v
      | oval r => trans (val r) (go T) (go U)
      end.
  Proof.
    intros * TR. induction TR.
    - destruct l.
      + rewrite <- ctree_eta in IHTR. apply trans_br with (y := x); exact IHTR.
      + destruct IHTR as (k' & TR' & EQ). rewrite <- ctree_eta in TR'.
        exists k'; split; auto. apply trans_br with (y := x); exact TR'.
      + rewrite <- ctree_eta in IHTR. apply trans_br with (y := x); exact IHTR.
    - destruct l.
      + rewrite <- ctree_eta in IHTR. now apply trans_guard.
      + destruct IHTR as (k' & TR' & EQ). rewrite <- ctree_eta in TR'.
        exists k'; split; auto.
      + rewrite <- ctree_eta in IHTR. now apply trans_guard.
    - rewrite <- ctree_eta, H. apply trans_step.
    - exists k; split; [apply trans_ask |]. now rewrite <- ctree_eta, H.
    - apply trans_ret.
  Qed.

  Lemma otrans_τ (t u : S) : otrans oτ t u -> trans τ t u.
  Proof. intros TR. apply otrans_trans_ in TR. now rewrite <- !ctree_eta in TR. Qed.

  Lemma otrans_val r (t u : S) : otrans (oval r) t u -> trans (val r) t u.
  Proof. intros TR. apply otrans_trans_ in TR. now rewrite <- !ctree_eta in TR. Qed.

  Lemma otrans_obs {X} (e : E X) v (t u : S) :
    otrans (oobs e v) t u -> exists k, trans (ask e) t (β e k) /\ u ≅ k v.
  Proof.
    intros TR. apply otrans_trans_ in TR as (k & TR & EQ).
    rewrite <- ctree_eta in TR, EQ. eauto.
  Qed.

  Lemma otrans_br {X} l (c : B X) (k : X -> S) x u : otrans l (k x) u -> otrans l (Br c k) u.
  Proof. intros TR; red; cbn; econstructor; exact TR. Qed.

  Lemma otrans_guard l (t u : S) : otrans l t u -> otrans l (Guard t) u.
  Proof. intros TR; red; cbn; econstructor; exact TR. Qed.

  Lemma trans_otrans : forall l (t : S) s,
      trans l t s ->
      match l with
      | τ => forall u, s ⩸ (α u) -> otrans oτ t u
      | ask e => forall k, s ⩸ (β e k) -> forall v, otrans (oobs e v) t (k v)
      | rcv _ _ => False
      | val r => otrans (oval r) t Stuck
      end.
  Proof.
    intros l t s TR.
    enough (G : forall st, trans l st s -> forall (T : S), st = Active T -> match l with
      | τ => forall u, s ⩸ (α u) -> otrans oτ T u
      | ask e => forall k, s ⩸ (β e k) -> forall v, otrans (oobs e v) T (k v)
      | rcv _ _ => False
      | val r => otrans (oval r) T Stuck
      end) by (eapply G; eauto).
    clear t TR. intros st TR. hnf in TR. induction TR; intros T Hs; inv Hs.
    - specialize (IHTR _ eq_refl). destruct l; auto.
      + intros u0 EQ. rewrite H. apply otrans_br with (x := x). rewrite <- H0. now apply IHTR.
      + intros k0 EQ v. rewrite H. apply otrans_br with (x := x). rewrite <- H0. now apply IHTR.
      + rewrite H. apply otrans_br with (x := x). rewrite <- H0. exact IHTR.
    - specialize (IHTR _ eq_refl). destruct l; auto.
      + intros u0 EQ. rewrite H. apply otrans_guard. now apply IHTR.
      + intros k0 EQ v. rewrite H. apply otrans_guard. now apply IHTR.
      + rewrite H. apply otrans_guard. exact IHTR.
    - intros u0 EQ. inv EQ. rewrite H. red; cbn. econstructor. now rewrite <- EQ0, H0.
    - intros k0 EQ v. dependent destruction EQ. rewrite H. red; cbn. econstructor. now rewrite EQ.
    - rewrite H. red; cbn. econstructor.
  Qed.

End Bridge.

(*| AI: Strong bisimilarity for [obs] steps, with equal labels on both sides. |*)
Section ObsBisim.

  Context {E B : Type -> Type} {R : Type}.

  Program Definition osb : mon (rel (ctree E B R) (ctree E B R)) :=
    {| body Rl t u :=
        (forall l t', otrans l t t' -> exists u', otrans l u u' /\ Rl t' u') /\
        (forall l u', otrans l u u' -> exists t', otrans l t t' /\ Rl t' u') |}.
  Next Obligation.
    split; intros l t' TR;
      [destruct (H0 _ _ TR) as (u' & ? & ?) | destruct (H1 _ _ TR) as (u' & ? & ?)]; eauto.
  Qed.

  Definition osbisim := gfp osb.

  Lemma osbisim_refl : forall t, osbisim t t.
  Proof.
    unfold osbisim. coinduction Rl CIH. intros t; split; intros l t' TR; eauto.
  Qed.

End ObsBisim.

Lemma sbisim_passive_inv {E C X Y} (e : E Y) (k k' : Y -> ctree E C X) :
  sbisimeq (β e k) (β e k') -> forall y, k y ≃ k' y.
Proof.
  intros HR y. step in HR. destruct HR as [F _].
  destruct (F _ _ (trans_rcv e k y)) as (l' & s' & TR & HR' & HL).
  apply Leq_eq in HL; subst l'. apply trans_passive_inv' in TR as (y' & EQ & EQl). dependent destruction EQl.
  unfold sbisimT. now rewrite EQ in HR'.
Qed.

Theorem sbisim_osbisim {E B R} : forall (t u : ctree E B R), t ≃ u -> osbisim t u.
Proof.
  unfold osbisim. coinduction Rl CIH. intros t u H. step in H. destruct H as [F B'].
  split.
  - intros [| ? e v | r] t' TR.
    + apply otrans_τ in TR. apply F in TR as (l' & s & TR' & HR & HL). apply Leq_eq in HL; subst l'.
      destruct (trans_τ_inv TR') as (u' & EQ). rewrite EQ in TR', HR.
      exists u'; split; [exact (trans_otrans TR' _ (reflexivity _)) | apply CIH; exact HR].
    + apply otrans_obs in TR as (k & TRk & EQ).
      apply F in TRk as (l' & s & TR' & HR & HL). apply Leq_eq in HL; subst l'.
      destruct (trans_ask_inv TR') as (k' & EQ'). rewrite EQ' in TR', HR.
      exists (k' v); split; [exact (trans_otrans TR' _ (reflexivity _) v) |].
      apply CIH. rewrite EQ. exact (sbisim_passive_inv HR v).
    + apply otrans_val in TR. apply F in TR as TR'. destruct TR' as (l' & s & TR' & HR & HL).
      apply Leq_eq in HL; subst l'.
      exists t'; split; [| apply CIH; reflexivity].
      pose proof (trans_otrans TR') as T. cbn in T. rewrite (trans_val_inv TR). exact T.
  - intros [| ? e v | r] u' TR.
    + apply otrans_τ in TR. apply B' in TR as (l' & s & TR' & HR & HL).
      rewrite flipL_Leq in HL. apply Leq_eq in HL; subst l'.
      destruct (trans_τ_inv TR') as (t' & EQ). rewrite EQ in TR', HR.
      exists t'; split; [exact (trans_otrans TR' _ (reflexivity _)) | apply CIH; exact HR].
    + apply otrans_obs in TR as (k & TRk & EQ).
      apply B' in TRk as (l' & s & TR' & HR & HL). rewrite flipL_Leq in HL. apply Leq_eq in HL; subst l'.
      destruct (trans_ask_inv TR') as (k' & EQ'). rewrite EQ' in TR', HR.
      exists (k' v); split; [exact (trans_otrans TR' _ (reflexivity _) v) |].
      apply CIH. rewrite EQ. exact (sbisim_passive_inv HR v).
    + apply otrans_val in TR. apply B' in TR as TR'. destruct TR' as (l' & s & TR' & HR & HL).
      rewrite flipL_Leq in HL. apply Leq_eq in HL; subst l'.
      exists u'; split; [| apply CIH; reflexivity].
      pose proof (trans_otrans TR') as T. cbn in T. rewrite (trans_val_inv TR). exact T.
Qed.

Lemma otrans_vis {E B R X} (e : E X) (k : X -> ctree E B R) x : otrans (oobs e x) (Vis e k) (k x).
Proof. red; cbn; econstructor; reflexivity. Qed.

Lemma otrans_br_inv {E B R X} l (c : B X) (k : X -> ctree E B R) u :
  otrans l (Br c k) u -> exists x, otrans l (k x) u.
Proof. intros TR; red in TR; cbn in TR; dependent destruction TR; eauto. Qed.

Lemma otrans_vis_inv {E B R X} l (e : E X) (k : X -> ctree E B R) u :
  otrans l (Vis e k) u -> exists x, l = oobs e x /\ u ≅ k x.
Proof.
  intros TR. red in TR; cbn in TR. remember (observe u) as ou eqn:Hu. dependent destruction TR.
  exists x; split; auto. rewrite (ctree_eta u), <- Hu, <- ctree_eta. now symmetry.
Qed.

Module Example.

  Variant QE : Type -> Type := Qb : QE bool.

  Definition P : ctree QE B2 nat :=
    br2 (Vis Qb (fun b : bool => if b then Ret 1 else Ret 2))
        (Vis Qb (fun b : bool => if b then Ret 3 else Ret 4)).

  Definition Q : ctree QE B2 nat :=
    br2 (Vis Qb (fun b : bool => if b then Ret 3 else Ret 2))
        (Vis Qb (fun b : bool => if b then Ret 1 else Ret 4)).

  Lemma P_osbisim_Q : osbisim P Q.
  Proof.
    unfold osbisim. step. split.
    - intros l t' TR. unfold P, br2 in TR. apply otrans_br_inv in TR as ([] & TR); cbn in TR;
        apply otrans_vis_inv in TR as ([] & -> & EQ); cbn in EQ; exists t'; (split; [| apply osbisim_refl]);
        unfold Q, br2; rewrite EQ.
      + apply otrans_br with (x := false). exact (otrans_vis Qb _ true).
      + apply otrans_br with (x := true). exact (otrans_vis Qb _ false).
      + apply otrans_br with (x := true). exact (otrans_vis Qb _ true).
      + apply otrans_br with (x := false). exact (otrans_vis Qb _ false).
    - intros l u' TR. unfold Q, br2 in TR. apply otrans_br_inv in TR as ([] & TR); cbn in TR;
        apply otrans_vis_inv in TR as ([] & -> & EQ); cbn in EQ; exists u'; (split; [| apply osbisim_refl]);
        unfold P, br2; rewrite EQ.
      + apply otrans_br with (x := false). exact (otrans_vis Qb _ true).
      + apply otrans_br with (x := true). exact (otrans_vis Qb _ false).
      + apply otrans_br with (x := true). exact (otrans_vis Qb _ true).
      + apply otrans_br with (x := false). exact (otrans_vis Qb _ false).
  Qed.

  Lemma P_not_sbisim_Q : ~ P ≃ Q.
  Proof.
    intros H. step in H. destruct H as [F _].
    assert (TR : trans (ask Qb) P (β Qb (fun b : bool => if b then Ret 1 else Ret 2)))
      by (unfold P; apply trans_br21, trans_ask).
    apply F in TR as (l' & s & TR' & HR & HL). apply Leq_eq in HL; subst l'.
    unfold Q, br2 in TR'. apply trans_br_inv in TR' as ([] & TR'); cbn in TR';
      apply trans_vis_inv' in TR' as (EQ & _); rewrite EQ in HR.
    - pose proof (sbisim_passive_inv HR true) as H; cbn in H. apply sbisim_ret_inv in H. discriminate.
    - pose proof (sbisim_passive_inv HR false) as H; cbn in H. apply sbisim_ret_inv in H. discriminate.
  Qed.

End Example.

Corollary osbisim_strictly_coarser :
  (forall E B R (t u : ctree E B R), t ≃ u -> osbisim t u) /\
  exists t u : ctree Example.QE B2 nat, osbisim t u /\ ~ t ≃ u.
Proof.
  split; [intros; now apply sbisim_osbisim |].
  exists Example.P, Example.Q; split; [apply Example.P_osbisim_Q | apply Example.P_not_sbisim_Q].
Qed.
