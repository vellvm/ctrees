From Stdlib Require Import Fin Program.Equality.

From Coinduction Require Import all.

From ITree Require Import
     Core.Subevent
     Indexed.Sum.

From CTree Require Import
     CTree Eq Eq.Equ.

From CTree Require Eq.Trans Eq.SSim Eq.SBisim.

From CTree Require Import Eq.TransAlt Eq.EpsilonAlt Eq.SSimAlt Eq.SBisimAlt Eq.OldAltEquiv.TransEquiv Eq.OldAltEquiv.EpsilonEquiv Eq.OldAltEquiv.SSimEquiv.

From RelationAlgebra Require Import
     monoid kat kat_tac prop rel srel comparisons rewriting normalisation.

Import CTree.
Import CTreeNotations.
Import EquNotations.
Import CoindNotations.
Open Scope ctree.

Set Implicit Arguments.

(* 
Equivalence of old and new bisimilarities
*)
Section sbisim_sbisim'. 

Lemma o_ss_br_step {E F C D X Y} (L : Trans.lrel E F X Y)
  (Rel : rel (Trans.S E C X) (Trans.S F D Y))
  Z (c : C Z) (k : Z -> ctree E C X) (t u : ctree E C X) (b : Trans.S F D Y) x :
  SSim.ss L Rel (Trans.Active t) b -> t ≅ Br c k -> u ≅ k x ->
  SSim.ss L Rel (Trans.Active u) b.
Proof.
  intros H Hbr Hu; cbn in H |- *; intros l t' TR.
  apply (H l t').
  eapply Trans.Transbr; [apply Hbr | apply Hu | apply TR].
Qed.

Lemma o_ss_guard_step {E F C D X Y} (L : Trans.lrel E F X Y)
  (Rel : rel (Trans.S E C X) (Trans.S F D Y))
  (t tg u : ctree E C X) (b : Trans.S F D Y) :
  SSim.ss L Rel (Trans.Active t) b -> t ≅ Guard tg -> u ≅ tg ->
  SSim.ss L Rel (Trans.Active u) b.
Proof.
  intros H Hg Hu; cbn in H |- *; intros l t' TR.
  apply (H l t').
  assert (Htu : t ≅ Guard u) by (rewrite Hu; apply Hg).
  eapply Trans.Transguard; [apply Htu | apply TR].
Qed.

Theorem gfp_sb'_ss_sbisim {E F C D X Y} (L : Trans.lrel E F X Y) :
  forall (a : Trans.S E C X) (b : Trans.S F D Y),
  (SSim.ss L (SBisim.sbisim L) a b ->
     gfp (@sb' E F C D) true X Y (lift_L L) (o2n_S a) (o2n_S b)) /\
  (SSim.ss (Trans.flipL L) (flip (SBisim.sbisim L)) b a ->
     gfp (@sb' E F C D) false X Y (lift_L L) (o2n_S a) (o2n_S b)).
Proof.
  coinduction R CH. intros a b.
  split; intro H.
  - split; intro; [| easy].
    split.
    + intros x l Hne TR.
      apply label_non_eps_image in Hne as [lo ->].
      assert (oTR : Trans.transR lo a (n2o_S x)).
      { rewrite <- (n2o_o2n_S a). apply transR_n2o. apply trans_star_l. apply TR. }
      cbn in H.
      destruct (H lo (n2o_S x) oTR) as (lo' & bo' & TRb & Hrel & HL).
      exists (o2n_label lo'), (o2n_S bo'); ssplit.
      * apply transR_o2n; exact TRb.
      * apply (gfp_pfp (@SBisim.sb E F C D X Y L)) in Hrel.
        destruct Hrel as [Hf Hb].
        pose proof (CH (n2o_S x) bo') as CHx.
        rewrite o2n_n2o_S in CHx.
        intro side; destruct side; [apply CHx | apply CHx]; assumption.
      * apply lift_L_o2n; exact HL.
    + intros x TR.
      exists (o2n_S b); split; [apply trans_star_self |].
      apply trans_alt_eps_inv in TR as
        [ (Z & c & k & t & u & x0 & Ha & Hx & Hbr & Hu)
        | (t & tg & u & Ha & Hx & Hg & Hu) ].
      * subst x; destruct a as [ta | ? e0 k0]; cbn in Ha; [| easy].
        inv Ha; apply (CH (Trans.Active u) b).
        eapply o_ss_br_step; eauto.
      * subst x; destruct a as [ta | ? e0 k0]; cbn in Ha; [| easy].
        inv Ha; apply (CH (Trans.Active u) b).
        eapply o_ss_guard_step; eauto.
  - split; intro; [easy |].
    split.
    + intros x l Hne TR.
      apply label_non_eps_image in Hne as [lo ->].
      assert (oTR : Trans.transR lo b (n2o_S x)).
      { rewrite <- (n2o_o2n_S b). apply transR_n2o. apply trans_star_l. apply TR. }
      cbn in H.
      destruct (H lo (n2o_S x) oTR) as (lo' & ao' & TRa & Hrel & HL).
      exists (o2n_label lo'), (o2n_S ao'); ssplit.
      * apply transR_o2n; exact TRa.
      * unfold flip in Hrel.
        apply (gfp_pfp (@SBisim.sb E F C D X Y L)) in Hrel.
        destruct Hrel as [Hf Hb].
        pose proof (CH ao' (n2o_S x)) as CHx.
        rewrite o2n_n2o_S in CHx.
        intro side; destruct side; [apply CHx | apply CHx]; assumption.
      * rewrite <- lift_L_flipL. apply lift_L_o2n; exact HL.
    + intros x TR.
      exists (o2n_S a); split; [apply trans_star_self |].
      apply trans_alt_eps_inv in TR as
        [ (Z & c & k & t & u & x0 & Hb & Hx & Hbr & Hu)
        | (t & tg & u & Hb & Hx & Hg & Hu) ].
      * subst x; destruct b as [tb | ? e0 k0]; cbn in Hb; [| easy].
        inv Hb; apply (CH a (Trans.Active u)).
        eapply o_ss_br_step; eauto.
      * subst x; destruct b as [tb | ? e0 k0]; cbn in Hb; [| easy].
        inv Hb; apply (CH a (Trans.Active u)).
        eapply o_ss_guard_step; eauto.
Qed.

Lemma gfp_sb'_true_ss_sbisim {E F C D X Y} (L : Trans.lrel E F X Y) :
  forall (a : Trans.S E C X) (b : Trans.S F D Y),
  SSim.ss L (SBisim.sbisim L) a b ->
  gfp (@sb' E F C D) true X Y (lift_L L) (o2n_S a) (o2n_S b).
Proof.
  intros a b; apply (gfp_sb'_ss_sbisim L a b).
Qed.

Theorem sbisim_sbisim' {E F C D X Y} (L : Trans.lrel E F X Y) :
  forall (a : Trans.S E C X) (b : Trans.S F D Y),
    SBisim.sbisim L a b <-> sbisim' (lift_L L) (o2n_S a) (o2n_S b).
Proof.
  intros a b; split; intro H.
  (* from previous lemmas *)
  - intro side.
    step in H. 
    destruct H as [Hf Hb]; destruct side;
      apply (gfp_sb'_ss_sbisim L a b); assumption.
  (* here we do a manual argument by coinduction.
     in each case we can use the sbisim' argument with 
     a different boolean flag to match the argument we wish to 
     follow. 
  *)
  - revert a b H. unfold SBisim.sbisim. coinduction R CH. intros a b H.
    split.
    + intros lo x oTR.
      apply transR_o2n in oTR; destruct oTR as [m STAR STEP].
      pose proof (HT := H true).
      eapply sbisim'_epsilon_l in HT; [| exact STAR].
      step in HT. 
      destruct HT as [HT _]; specialize (HT eq_refl); destruct HT as [HTA _].
      assert (Hne : o2n_label lo <> ε) by (destruct lo; cbn [o2n_label]; easy).
      destruct (HTA _ _ Hne STEP) as (l' & u' & RESP & Hall & HL).
      apply lift_L_o2n_inv in HL as (la & lb & Hla & Hlb & HLab).
      apply o2n_label_inj in Hla; subst la; subst l'.
      exists lb, (n2o_S u'); ssplit.
      (* trick is to lift through n2o_S *)
      * rewrite <- (n2o_o2n_S b). apply transR_n2o; exact RESP.
      * apply CH. rewrite o2n_n2o_S. exact Hall.
      * exact HLab.
    + intros lo x oTR.
      apply transR_o2n in oTR; destruct oTR as [m STAR STEP].
      pose proof (HF := H false).
      eapply sbisim'_epsilon_r in HF; [| exact STAR].
      step in HF. 
      destruct HF as [_ HF]; specialize (HF eq_refl); destruct HF as [HFA _].
      assert (Hne : o2n_label lo <> ε) by (destruct lo; cbn [o2n_label]; easy).
      destruct (HFA _ _ Hne STEP) as (l' & t'' & RESP & Hall & HL).
      apply flipL_flip in HL.
      apply lift_L_o2n_inv in HL as (la & lb & Hla & Hlb & HLab).
      apply o2n_label_inj in Hlb; subst.
      exists la, (n2o_S t''); ssplit.
      * rewrite <- (n2o_o2n_S a). apply transR_n2o; exact RESP.
      * unfold flip. apply CH. rewrite o2n_n2o_S. exact Hall.
      * apply Trans.flipL_flip; exact HLab.
Qed.

Corollary sbisim_gfp_sb' {E F C D X Y} (L : Trans.lrel E F X Y) :
  forall side (a : Trans.S E C X) (b : Trans.S F D Y),
    SBisim.sbisim L a b ->
    gfp (@sb' E F C D) side X Y (lift_L L) (o2n_S a) (o2n_S b).
Proof.
  intros. apply sbisim_sbisim' in H. apply H.
Qed.

Theorem ss_sbisim_gfp_sb' {E F C D X Y} (L : Trans.lrel E F X Y) :
  forall (a : Trans.S E C X) (b : Trans.S F D Y),
  (gfp (@sb' E F C D) true X Y (lift_L L) (o2n_S a) (o2n_S b) ->
     SSim.ss L (SBisim.sbisim L) a b) /\
  (gfp (@sb' E F C D) false X Y (lift_L L) (o2n_S a) (o2n_S b) ->
     SSim.ss (Trans.flipL L) (flip (SBisim.sbisim L)) b a).
Proof.
  intros a b; split; intro H.
  - intros lo x oTR.
    apply transR_o2n in oTR; destruct oTR as [m STAR STEP].
    eapply sbisim'_epsilon_l in H; [| exact STAR].
    apply (gfp_pfp (@sb' E F C D)) in H.
    destruct H as [H _]; specialize (H eq_refl); destruct H as [HA _].
    assert (Hne : o2n_label lo <> ε) by (destruct lo; cbn [o2n_label]; easy).
    destruct (HA _ _ Hne STEP) as (l' & u' & RESP & Hall & HL).
    apply lift_L_o2n_inv in HL as (la & lb & Hla & Hlb & HLab).
    apply o2n_label_inj in Hla; subst la; subst l'.
    exists lb, (n2o_S u'); ssplit.
    + rewrite <- (n2o_o2n_S b). apply transR_n2o; exact RESP.
    + apply sbisim_sbisim'. rewrite o2n_n2o_S. exact Hall.
    + exact HLab.
  - intros lo x oTR.
    apply transR_o2n in oTR; destruct oTR as [m STAR STEP].
    eapply sbisim'_epsilon_r in H; [| exact STAR].
    apply (gfp_pfp (@sb' E F C D)) in H.
    destruct H as [_ H]; specialize (H eq_refl); destruct H as [HA _].
    assert (Hne : o2n_label lo <> ε) by (destruct lo; cbn [o2n_label]; easy).
    destruct (HA _ _ Hne STEP) as (l' & t'' & RESP & Hall & HL).
    apply flipL_flip in HL.
    apply lift_L_o2n_inv in HL as (la & lb & Hla & Hlb & HLab).
    apply o2n_label_inj in Hlb; subst lb; subst l'.
    exists la, (n2o_S t''); ssplit.
    + rewrite <- (n2o_o2n_S a). apply transR_n2o; exact RESP.
    + unfold flip. apply sbisim_sbisim'. rewrite o2n_n2o_S. exact Hall.
    + apply Trans.flipL_flip; exact HLab.
Qed.

Lemma sb'_clo_bind_lift_eq {E B X X'} {R : Chain (@sb' E E B B)} side
  (t t' : ctree E B X) (k k' : X -> ctree E B X') :
  SBisim.sbisim (@Trans.Leq E X) (Trans.Active t) (Trans.Active t') ->
  (forall side x, elem R side X' X' (lift_L (@Trans.Leq E X'))
                    (TransAlt.Active (k x)) (TransAlt.Active (k' x))) ->
  elem R side X' X' (lift_L (@Trans.Leq E X'))
    (TransAlt.Active (x <- t;; k x)) (TransAlt.Active (x <- t';; k' x)).
Proof.
  intros tt kk.
  eapply bind_chain_gen with (SS := @eq X).
  - apply (gfp_chain R).
    change (gfp (@sb' E E B B) side X X (lift_L (@Trans.Leq E X))
              (o2n_S (Trans.Active t)) (o2n_S (Trans.Active t'))).
    now apply sbisim_gfp_sb'.
  - intros ? x ? <-; apply kk.
Qed.

End sbisim_sbisim'.
