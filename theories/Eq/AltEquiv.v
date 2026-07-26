From Stdlib Require Import Fin Program.Equality.

From Coinduction Require Import all.

From ITree Require Import
     Core.Subevent
     Indexed.Sum.

From CTree Require Import
     CTree Eq.Shallow Eq.Equ Eq.Epsilon.

From CTree Require Eq.Trans Eq.SSim Eq.EstarTheory.

From CTree Require Import Eq.TransAlt Eq.SSimAlt.

From RelationAlgebra Require Import
     monoid kat kat_tac prop rel srel comparisons rewriting normalisation.

Import CTree.
Import CTreeNotations.
Import EquNotations.
Import CoindNotations.
Open Scope ctree.

Set Implicit Arguments.

(* label and S conversion *)
(* convention: "o" is old, "n" is new. *)

Definition o2n_S {E B X} (s : Trans.S E B X) : TransAlt.S E B X :=
  match s with
  | Trans.Active t => TransAlt.Active t
  | Trans.Passive e k => TransAlt.Passive e k
  end.

Definition n2o_S {E B X} (s : TransAlt.S E B X) : Trans.S E B X :=
  match s with
  | TransAlt.Active t => Trans.Active t
  | TransAlt.Passive e k => Trans.Passive e k
  end.

Definition o2n_label {E X} (l : Trans.label E X) : TransAlt.label E X :=
  match l with
  | Trans.τ => TransAlt.τ
  | Trans.ask e => TransAlt.ask e
  | Trans.rcv e v => TransAlt.rcv e v
  | Trans.val v => TransAlt.val v
  end.

Lemma n2o_o2n_S {E B X} (s : Trans.S E B X) : n2o_S (o2n_S s) = s.
Proof. now destruct s. Qed.

Lemma o2n_n2o_S {E B X} (s : TransAlt.S E B X) : o2n_S (n2o_S s) = s.
Proof. now destruct s. Qed.

Lemma transR_o2n {E B X} (l : Trans.label E X) (a a' : Trans.S E B X) :
  Trans.transR l a a' ->
  ((trans_alt ε)^* ⋅ trans_alt (o2n_label l)) (o2n_S a) (o2n_S a').
Proof.
  intros TR; induction TR.
  - destruct IHTR as [m STAR STEP].
    exists m; [| apply STEP].
    eapply EstarTheory.estar_cons_epsilon; [ | apply STAR ].
    eapply TransAlt.Transbr; [ apply H | apply H0 ].
  - destruct IHTR as [m STAR STEP].
    exists m; [| apply STEP].
    eapply EstarTheory.estar_cons_epsilon; [ | apply STAR ].
    eapply TransAlt.Transguard; [ apply H | reflexivity ].
  - apply trans_star_l. eapply TransAlt.Transstep; [ apply H | apply H0 ].
  - apply trans_star_l. eapply TransAlt.Transask; apply H.
  - apply trans_star_l. eapply TransAlt.Transrcv; apply H.
  - apply trans_star_l. eapply TransAlt.Transval; [ apply H | apply H0 ].
Qed.

Lemma n2o_S_Seq {E B X} (a b : TransAlt.S E B X) :
  TransAlt.Seq a b -> Trans.Seq (n2o_S a) (n2o_S b).
Proof. intros H; inv H; cbn [n2o_S]; constructor; assumption. Qed.

Lemma trans_alt_eps_inv {E B X} (a mid : TransAlt.S E B X) :
  trans_alt ε a mid ->
  (exists Z (c : B Z) (k : Z -> ctree E B X) t u x,
      a = TransAlt.Active t /\ mid = TransAlt.Active u /\ t ≅ Br c k /\ u ≅ k x)
  \/ (exists t t' u,
      a = TransAlt.Active t /\ mid = TransAlt.Active u /\ t ≅ Guard t' /\ u ≅ t').
Proof.
  intros TR; unfold trans_alt in TR; cbn in TR.
  inversion TR; subst.
  - left. eauto 12.
  - right. eauto 12.
Qed.

Lemma eps_absorb1 {E B X} (l : Trans.label E X) (a mid c : TransAlt.S E B X) :
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

Lemma estar_absorb {E B X} (l : Trans.label E X) (a m : TransAlt.S E B X) :
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

Lemma transR_label_base {E B X} (l : Trans.label E X) (m b : TransAlt.S E B X) :
  trans_alt (o2n_label l) m b -> Trans.transR l (n2o_S m) (n2o_S b).
Proof.
  destruct l; cbn [o2n_label]; intros TR; unfold trans_alt in TR; cbn in TR.
  - dependent destruction TR; cbn [n2o_S]. eapply Trans.Transstep; eassumption.
  - dependent destruction TR; cbn [n2o_S]. eapply Trans.Transask; eassumption.
  - dependent destruction TR; cbn [n2o_S]. eapply Trans.Transrcv; eassumption.
  - dependent destruction TR; cbn [n2o_S]. eapply Trans.Transval; eassumption.
Qed.

Lemma transR_n2o {E B X} (l : Trans.label E X) (a b : TransAlt.S E B X) :
  ((trans_alt ε)^* ⋅ trans_alt (o2n_label l)) a b ->
  Trans.transR l (n2o_S a) (n2o_S b).
Proof.
  intros [m STAR STEP].
  eapply estar_absorb; [ apply STAR | ].
  apply transR_label_base; apply STEP.
Qed.

Definition lift_L {E F X} (L : Trans.lrel E F X X) : TransAlt.lrel E F X X :=
  {| TransAlt.RR   := Trans.RR L ;
     TransAlt.Rask := Trans.Rask L ;
     TransAlt.Rrcv := Trans.Rrcv L |}.

(* old to new through lifting *)
Lemma lift_L_o2n {E F X} (L : Trans.lrel E F X X)
  (la : Trans.label E X) (lb : Trans.label F X) :
  Trans.build_rel L la lb ->
  TransAlt.build_rel (lift_L L) (o2n_label la) (o2n_label lb).
Proof.
  intros H; destruct H; cbn [o2n_label]; now constructor.
Qed.

Lemma lift_L_o2n_inv {E F X} (L : Trans.lrel E F X X)
  (a : TransAlt.label E X) (b : TransAlt.label F X) :
  TransAlt.build_rel (lift_L L) a b ->
  exists la lb, a = o2n_label la /\ b = o2n_label lb /\ Trans.build_rel L la lb.
Proof.
  intros H; destruct H.
  - exists Trans.τ, Trans.τ; cbn [o2n_label]; repeat split; constructor.
  - exists (Trans.ask e), (Trans.ask f); cbn [o2n_label]; repeat split; now constructor.
  - exists (Trans.rcv e x), (Trans.rcv f y); cbn [o2n_label]; repeat split; now constructor.
  - exists (Trans.val x), (Trans.val y); cbn [o2n_label]; repeat split; now constructor.
Qed.

Lemma label_non_eps_image {E X} (l : TransAlt.label E X) :
  l <> ε -> exists lo, l = o2n_label lo.
Proof.
  destruct l; intro Hne.
  - exists Trans.τ; reflexivity.
  - easy.
  - exists (Trans.ask e); reflexivity.
  - exists (Trans.rcv e v); reflexivity.
  - exists (Trans.val v); reflexivity.
Qed.

Lemma o2n_label_inj {E X} (l l' : Trans.label E X) :
  o2n_label l = o2n_label l' -> l = l'.
Proof.
  destruct l, l'; cbn; intro H; try easy;
    dependent destruction H; reflexivity.
Qed.

Lemma o_ssim_br_step {E F B X} (L : Trans.lrel E F X X)
  Z (c : B Z) (k : Z -> ctree E B X) (t u : ctree E B X) (b : Trans.S F B X) x :
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

Lemma o_ssim_guard_step {E F B X} (L : Trans.lrel E F X X)
  (t tg u : ctree E B X) (b : Trans.S F B X) :
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
Lemma o_ssim_to_ssim' {E F B X} (L : Trans.lrel E F X X) :
  forall (a : Trans.S E B X) (b : Trans.S F B X),
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

Lemma ssim'_to_o_ssim {E F B X} (L : Trans.lrel E F X X) :
  forall (a : Trans.S E B X) (b : Trans.S F B X),
    SSimAlt.ssim' (lift_L L) (o2n_S a) (o2n_S b) -> SSim.ssim L a b.
Proof.
  unfold SSim.ssim.
  coinduction R cih.
  intros a b H.
  intros l ao' oTR.
  apply transR_o2n in oTR.
  destruct oTR as [m STAR STEP].
  eapply SSimAlt.ssim'_epsilon_l in H. 2: apply STAR.
  apply (gfp_pfp (@SSimAlt.ss' E F B B) X X (lift_L L)) in H.
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

Theorem ssim_ssim' {E F B X} (L : Trans.lrel E F X X)
  (t : ctree E B X) (t' : ctree F B X) :
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
