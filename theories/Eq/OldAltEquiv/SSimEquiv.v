From Stdlib Require Import Fin Program.Equality.

From Coinduction Require Import all.

From ITree Require Import
     Core.Subevent
     Indexed.Sum.

From CTree Require Import
     CTree Eq Eq.Equ.

From CTree Require Eq.Trans Eq.SSim.

From CTree Require Import Eq.TransAlt Eq.EpsilonAlt Eq.SSimAlt Eq.OldAltEquiv.TransEquiv Eq.OldAltEquiv.EpsilonEquiv.

From RelationAlgebra Require Import
     monoid kat kat_tac prop rel srel comparisons rewriting normalisation.

Import CTree.
Import CTreeNotations.
Import EquNotations.
Import CoindNotations.
Open Scope ctree.

Set Implicit Arguments.

Lemma o_ssim_br_step {E F C D X Y} (L : Trans.lrel E F X Y)
  Z (c : C Z) (k : Z -> ctree E C X) (t u : ctree E C X) (b : Trans.S F D Y) x :
  SSim.ssim L (Trans.Active t) b -> t ≅ Br c k -> u ≅ k x ->
  SSim.ssim L (Trans.Active u) b.
Proof.
  intros H Hbr Hu.
  unfold SSim.ssim in H |- *.
  apply (gfp_pfp (SSim.ss L)) in H.
  apply (b_chain (chain_gfp (SSim.ss L))).
  intros l t' TR.
  apply (H l t').
  eapply Trans.Transbr.
  - apply Hbr.
  - apply Hu.
  - apply TR.
Qed.

Lemma o_ssim_guard_step {E F C D X Y} (L : Trans.lrel E F X Y)
  (t tg u : ctree E C X) (b : Trans.S F D Y) :
  SSim.ssim L (Trans.Active t) b -> t ≅ Guard tg -> u ≅ tg ->
  SSim.ssim L (Trans.Active u) b.
Proof.
  intros H Hg Hu.
  unfold SSim.ssim in H |- *.
  apply (gfp_pfp (SSim.ss L)) in H.
  apply (b_chain (chain_gfp (SSim.ss L))).
  intros l t' TR.
  apply (H l t').
  assert (Htu : t ≅ Guard u) by (rewrite Hu; apply Hg).
  eapply Trans.Transguard; [ apply Htu | apply TR ].
Qed.

(* main result *)
Lemma o_ssim_to_ssim' {E F C D X Y} (L : Trans.lrel E F X Y) :
  forall (a : Trans.S E C X) (b : Trans.S F D Y),
    SSim.ssim L a b -> SSimAlt.ssim' (lift_L L) (o2n_S a) (o2n_S b).
Proof.
  unfold SSimAlt.ssim'.
  coinduction c cih.
  intros a b H.
  split.
  - intros x l Hne TR.
    apply label_non_eps_image in Hne as [lo ->].
    step in H.
    assert (oTR : Trans.transR lo a (n2o_S x)).
    { rewrite <- (n2o_o2n_S a). apply transR_n2o. apply trans_star_l. apply TR. }
    repeat red in H.
    destruct (H lo (n2o_S x) oTR) as (lo' & bo' & TRb & Hrel & HL).
    exists (o2n_label lo'), (o2n_S bo').
    split; [| split].
    + apply transR_o2n. apply TRb.
    + specialize (cih (n2o_S x) bo' Hrel).
      rewrite o2n_n2o_S in cih. apply cih.
    + apply lift_L_o2n; exact HL.
  - intros x TR.
    exists (o2n_S b). split.
    + apply trans_star_self.
    + apply trans_alt_eps_inv in TR as
        [ (Z & c' & k & t & u & x0 & Ha & Hx & Hbr & Hu)
        | (t & tg & u & Ha & Hx & Hg & Hu) ].
      (* t is a branch,  *)
        * subst x. destruct a as [ta | YY e0 k0]; cbn in Ha; [| easy].
          inv Ha.
          apply (cih (Trans.Active u) b).
          eapply o_ssim_br_step; eauto.
      (* t is a guard, one epsilon step and coinduction *)
        * subst x. destruct a as [ta | YY e0 k0]; cbn in Ha; [| easy].
          inv Ha.
          apply (cih (Trans.Active u) b).
          eapply o_ssim_guard_step; eauto.
Qed.

Lemma ssim'_to_o_ssim {E F C D X Y} (L : Trans.lrel E F X Y) :
  forall (a : Trans.S E C X) (b : Trans.S F D Y),
    SSimAlt.ssim' (lift_L L) (o2n_S a) (o2n_S b) -> SSim.ssim L a b.
Proof.
  unfold SSim.ssim.
  coinduction R cih.
  intros a b H.
  intros l ao' oTR.
  apply transR_o2n in oTR.
  destruct oTR as [m STAR STEP].
  eapply SSimAlt.ssim'_epsilon_l in H. 2: apply STAR.
  apply (gfp_pfp (@SSimAlt.ss' E F C D) X Y (lift_L L)) in H.
  destruct H as (Hchal & _).
  destruct (Hchal (o2n_S ao') (o2n_label l)) as (nl' & u' & RESP & Hgfp & HL).
  { destruct l; cbn [o2n_label]; easy. }
  { apply STEP. }
  apply lift_L_o2n_inv in HL as (la & lb & Hla & Hlb & HLab).
  apply o2n_label_inj in Hla; subst la.
  subst nl'.
  exists lb, (n2o_S u').
  split; [| split].
  - rewrite <- (n2o_o2n_S b). apply transR_n2o. apply RESP.
  - apply cih. rewrite o2n_n2o_S. apply Hgfp.
  - apply HLab.
Qed.

Theorem ssim_ssim' {E F C D X Y} (L : Trans.lrel E F X Y)
  (t : ctree E C X) (t' : ctree F D Y) :
  SSim.ssim L (Trans.Active t) (Trans.Active t') <->
  SSimAlt.ssim' (lift_L L) (TransAlt.Active t) (TransAlt.Active t').
Proof.
  split; intro H.
  - apply o_ssim_to_ssim' in H. apply H.
  - apply ssim'_to_o_ssim. apply H.
Qed.

Lemma ss'_clo_bind_eq {E B X X'}
  (t t' : ctree E B X) (k k' : X -> ctree E B X') :
  SSim.ssim (@Trans.Leq E X) (Trans.Active t) (Trans.Active t') ->
  (forall x, SSimAlt.ssim' (lift_L (@Trans.Leq E X'))
               (TransAlt.Active (k x)) (TransAlt.Active (k' x))) ->
  SSimAlt.ssim' (lift_L (@Trans.Leq E X'))
    (TransAlt.Active (x <- t;; k x)) (TransAlt.Active (x <- t';; k' x)).
Proof.
  intros tt kk.
  apply ssim_ssim' in tt.
  eapply SSimAlt.ssim'_clo_bind with (SS := @eq X).
  - exact tt.
  - intros x x' ->; apply kk.
Qed.
