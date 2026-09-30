From Stdlib Require Import Fin Program.Equality.

From Coinduction Require Import all.

From ITree Require Import
     Core.Subevent
     Indexed.Sum.

From CTree Require Import
     CTree Eq Eq.Equ.

From CTree Require Eq.Trans.

From CTree Require Import Eq.TransAlt.

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

Definition o2n_S {E C X} (s : Trans.S E C X) : TransAlt.S E C X :=
  match s with
  | Trans.Active t => TransAlt.Active t
  | Trans.Passive e k => TransAlt.Passive e k
  end.

Definition n2o_S {E C X} (s : TransAlt.S E C X) : Trans.S E C X :=
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

Lemma n2o_o2n_S {E C X} (s : Trans.S E C X) : n2o_S (o2n_S s) = s.
Proof. now destruct s. Qed.

Lemma o2n_n2o_S {E C X} (s : TransAlt.S E C X) : o2n_S (n2o_S s) = s.
Proof. now destruct s. Qed.

Lemma n2o_S_Seq {E C X} (a b : TransAlt.S E C X) :
  TransAlt.Seq a b -> Trans.Seq (n2o_S a) (n2o_S b).
Proof. intros H; inv H; cbn [n2o_S]; constructor; assumption. Qed.

Lemma trans_alt_eps_inv {E C X} (a mid : TransAlt.S E C X) :
  trans_alt ε a mid ->
  (exists Z (c : C Z) (k : Z -> ctree E C X) t u x,
      a = TransAlt.Active t /\ mid = TransAlt.Active u /\ t ≅ Br c k /\ u ≅ k x)
  \/ (exists t t' u,
      a = TransAlt.Active t /\ mid = TransAlt.Active u /\ t ≅ Guard t' /\ u ≅ t').
Proof.
  intros TR; unfold trans_alt in TR; cbn in TR.
  inversion TR; subst.
  - left. eauto 12.
  - right. eauto 12.
Qed.

Lemma transR_label_base {E C X} (l : Trans.label E X) (m b : TransAlt.S E C X) :
  trans_alt (o2n_label l) m b -> Trans.transR l (n2o_S m) (n2o_S b).
Proof.
  destruct l; cbn [o2n_label]; intros TR; unfold trans_alt in TR; cbn in TR.
  - dependent destruction TR; cbn [n2o_S]. eapply Trans.Transstep; eassumption.
  - dependent destruction TR; cbn [n2o_S]. eapply Trans.Transask; eassumption.
  - dependent destruction TR; cbn [n2o_S]. eapply Trans.Transrcv; eassumption.
  - dependent destruction TR; cbn [n2o_S]. eapply Trans.Transval; eassumption.
Qed.

Definition lift_L {E F X Y} (L : Trans.lrel E F X Y) : TransAlt.lrel E F X Y :=
  {| TransAlt.RR   := Trans.RR L ;
     TransAlt.Rask := Trans.Rask L ;
     TransAlt.Rrcv := Trans.Rrcv L |}.

(* old to new through lifting *)
Lemma lift_L_o2n {E F X Y} (L : Trans.lrel E F X Y)
  (la : Trans.label E X) (lb : Trans.label F Y) :
  Trans.build_rel L la lb ->
  TransAlt.build_rel (lift_L L) (o2n_label la) (o2n_label lb).
Proof.
  intros H; destruct H; cbn [o2n_label]; now constructor.
Qed.

Lemma lift_L_o2n_inv {E F X Y} (L : Trans.lrel E F X Y)
  (a : TransAlt.label E X) (b : TransAlt.label F Y) :
  TransAlt.build_rel (lift_L L) a b ->
  exists la lb, a = o2n_label la /\ b = o2n_label lb /\ Trans.build_rel L la lb.
Proof.
  intros H; destruct H.
  - exists Trans.τ, Trans.τ; cbn [o2n_label]; repeat split; constructor.
  - exists (Trans.ask e), (Trans.ask f); cbn [o2n_label]; repeat split; now constructor.
  - exists (Trans.rcv e x), (Trans.rcv f y); cbn [o2n_label]; repeat split; now constructor.
  - exists (Trans.val x), (Trans.val y); cbn [o2n_label]; repeat split; now constructor.
Qed.

#[global] Instance lift_L_Leq_reflexiveL {E X} : ReflexiveL (lift_L (@Trans.Leq E X)).
Proof.
  intros [] Hne; try easy; constructor; cbn; first [reflexivity | constructor].
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

Lemma lift_L_flipL {E F X Y} (L : Trans.lrel E F X Y) :
  lift_L (Trans.flipL L) = TransAlt.flipL (lift_L L).
Proof.
  now destruct L.
Qed.
