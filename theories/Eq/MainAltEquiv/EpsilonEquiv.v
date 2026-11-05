From Stdlib Require Import Fin Program.Equality.

From Coinduction Require Import all.

From ITree Require Import
     Core.Subevent
     Indexed.Sum.

From CTree Require Import
     CTree Eq.Equ.

From CTree Require Eq.Main.Trans.

From CTree Require Import Eq.Alt.Trans Eq.Alt.Epsilon Eq.MainAltEquiv.TransEquiv.

From RelationAlgebra Require Import
     monoid kat kat_tac prop rel srel comparisons rewriting normalisation.

Import CTree.
Import CTreeNotations.
Import EquNotations.
Import CoindNotations.
Open Scope ctree.

Set Implicit Arguments.

Lemma transR_o2n {E C X} (l : Main.Trans.label E X) (a a' : Main.Trans.S E C X) :
  Main.Trans.transR l a a' ->
  ((trans_alt ε)^* ⋅ trans_alt (o2n_label l)) (o2n_S a) (o2n_S a').
Proof.
  intros TR; induction TR.
  - destruct IHTR as [m STAR STEP].
    exists m; [| apply STEP].
    eapply Alt.Epsilon.estar_cons_epsilon; [ | apply STAR ].
    eapply Alt.Trans.Transbr; [ apply H | apply H0 ].
  - destruct IHTR as [m STAR STEP].
    exists m; [| apply STEP].
    eapply Alt.Epsilon.estar_cons_epsilon; [ | apply STAR ].
    eapply Alt.Trans.Transguard; [ apply H | reflexivity ].
  - apply trans_star_l. eapply Alt.Trans.Transstep; [ apply H | apply H0 ].
  - apply trans_star_l. eapply Alt.Trans.Transask; apply H.
  - apply trans_star_l. eapply Alt.Trans.Transrcv; apply H.
  - apply trans_star_l. eapply Alt.Trans.Transval; [ apply H | apply H0 ].
Qed.

Lemma eps_absorb1 {E C X} (l : Main.Trans.label E X) (a mid c : Alt.Trans.S E C X) :
  trans_alt ε a mid ->
  Main.Trans.transR l (n2o_S mid) (n2o_S c) ->
  Main.Trans.transR l (n2o_S a) (n2o_S c).
Proof.
  intros TR Hold.
  apply trans_alt_eps_inv in TR as
    [ (Z & cc & k & t & u & x & -> & -> & Hbr & Hu)
    | (t & t' & u & -> & -> & Hg & Hu) ];
    cbn [n2o_S] in *.
  - assert (S1 : Main.Trans.Seq (Main.Trans.Active t) (Main.Trans.Active (Br cc k)))
      by (constructor; apply Hbr).
    rewrite S1.
    eapply Main.Trans.trans_br with (y := x).
    assert (S2 : Main.Trans.Seq (Main.Trans.Active (k x)) (Main.Trans.Active u))
      by (constructor; symmetry; apply Hu).
    rewrite S2. apply Hold.
  - assert (S1 : Main.Trans.Seq (Main.Trans.Active t) (Main.Trans.Active (Guard t')))
      by (constructor; apply Hg).
    rewrite S1.
    eapply Main.Trans.trans_guard.
    assert (S2 : Main.Trans.Seq (Main.Trans.Active t') (Main.Trans.Active u))
      by (constructor; symmetry; apply Hu).
    rewrite S2. apply Hold.
Qed.

Lemma estar_absorb {E C X} (l : Main.Trans.label E X) (a m : Alt.Trans.S E C X) :
  (trans_alt ε)^* a m ->
  forall c, Main.Trans.transR l (n2o_S m) (n2o_S c) -> Main.Trans.transR l (n2o_S a) (n2o_S c).
Proof.
  intros [n STAR]. revert a m STAR.
  induction n; intros a m STAR c Hold.
  - cbn in STAR. apply n2o_S_Seq in STAR. rewrite STAR. apply Hold.
  - destruct STAR as [mid STEP REST].
    eapply eps_absorb1; [ apply STEP | ].
    eapply IHn; [ apply REST | apply Hold ].
Qed.

Lemma transR_n2o {E C X} (l : Main.Trans.label E X) (a b : Alt.Trans.S E C X) :
  ((trans_alt ε)^* ⋅ trans_alt (o2n_label l)) a b ->
  Main.Trans.transR l (n2o_S a) (n2o_S b).
Proof.
  intros [m STAR STEP].
  eapply estar_absorb; [ apply STAR | ].
  apply transR_label_base; apply STEP.
Qed.
