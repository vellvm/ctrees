From Stdlib Require Import Fin Program.Equality.

From Coinduction Require Import all.

From ITree Require Import
     Core.Subevent
     Indexed.Sum.

From CTree Require Import
     CTree Eq.Equ.

From CTree Require Eq.Trans.

From CTree Require Import Eq.TransAlt Eq.EpsilonAlt Eq.OldAltEquiv.TransEquiv.

From RelationAlgebra Require Import
     monoid kat kat_tac prop rel srel comparisons rewriting normalisation.

Import CTree.
Import CTreeNotations.
Import EquNotations.
Import CoindNotations.
Open Scope ctree.

Set Implicit Arguments.

Lemma transR_o2n {E C X} (l : Trans.label E X) (a a' : Trans.S E C X) :
  Trans.transR l a a' ->
  ((trans_alt ε)^* ⋅ trans_alt (o2n_label l)) (o2n_S a) (o2n_S a').
Proof.
  intros TR; induction TR.
  - destruct IHTR as [m STAR STEP].
    exists m; [| apply STEP].
    eapply EpsilonAlt.estar_cons_epsilon; [ | apply STAR ].
    eapply TransAlt.Transbr; [ apply H | apply H0 ].
  - destruct IHTR as [m STAR STEP].
    exists m; [| apply STEP].
    eapply EpsilonAlt.estar_cons_epsilon; [ | apply STAR ].
    eapply TransAlt.Transguard; [ apply H | reflexivity ].
  - apply trans_star_l. eapply TransAlt.Transstep; [ apply H | apply H0 ].
  - apply trans_star_l. eapply TransAlt.Transask; apply H.
  - apply trans_star_l. eapply TransAlt.Transrcv; apply H.
  - apply trans_star_l. eapply TransAlt.Transval; [ apply H | apply H0 ].
Qed.

Lemma eps_absorb1 {E C X} (l : Trans.label E X) (a mid c : TransAlt.S E C X) :
  trans_alt ε a mid ->
  Trans.transR l (n2o_S mid) (n2o_S c) ->
  Trans.transR l (n2o_S a) (n2o_S c).
Proof.
  intros TR Hold.
  apply trans_alt_eps_inv in TR as
    [ (Z & cc & k & t & u & x & -> & -> & Hbr & Hu)
    | (t & t' & u & -> & -> & Hg & Hu) ];
    cbn [n2o_S] in *.
  - assert (S1 : Trans.Seq (Trans.Active t) (Trans.Active (Br cc k)))
      by (constructor; apply Hbr).
    rewrite S1.
    eapply Trans.trans_br with (y := x).
    assert (S2 : Trans.Seq (Trans.Active (k x)) (Trans.Active u))
      by (constructor; symmetry; apply Hu).
    rewrite S2. apply Hold.
  - assert (S1 : Trans.Seq (Trans.Active t) (Trans.Active (Guard t')))
      by (constructor; apply Hg).
    rewrite S1.
    eapply Trans.trans_guard.
    assert (S2 : Trans.Seq (Trans.Active t') (Trans.Active u))
      by (constructor; symmetry; apply Hu).
    rewrite S2. apply Hold.
Qed.

Lemma estar_absorb {E C X} (l : Trans.label E X) (a m : TransAlt.S E C X) :
  (trans_alt ε)^* a m ->
  forall c, Trans.transR l (n2o_S m) (n2o_S c) -> Trans.transR l (n2o_S a) (n2o_S c).
Proof.
  intros [n STAR]. revert a m STAR.
  induction n; intros a m STAR c Hold.
  - cbn in STAR. apply n2o_S_Seq in STAR. rewrite STAR. apply Hold.
  - destruct STAR as [mid STEP REST].
    eapply eps_absorb1; [ apply STEP | ].
    eapply IHn; [ apply REST | apply Hold ].
Qed.

Lemma transR_n2o {E C X} (l : Trans.label E X) (a b : TransAlt.S E C X) :
  ((trans_alt ε)^* ⋅ trans_alt (o2n_label l)) a b ->
  Trans.transR l (n2o_S a) (n2o_S b).
Proof.
  intros [m STAR STEP].
  eapply estar_absorb; [ apply STAR | ].
  apply transR_label_base; apply STEP.
Qed.
