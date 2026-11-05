From Stdlib Require Import Fin Program.Equality.

From Coinduction Require Import all.

From ITree Require Import
     Core.Subevent
     Indexed.Sum.

From CTree Require Import
     CTree Eq.Equ.

From CTree Require Eq.Main.Trans.

From CTree Require Import Eq.Alt.Trans.

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

Definition o2n_S {E C X} (s : Main.Trans.S E C X) : Alt.Trans.S E C X :=
  match s with
  | Main.Trans.Active t => Alt.Trans.Active t
  | Main.Trans.Passive e k => Alt.Trans.Passive e k
  end.

Definition n2o_S {E C X} (s : Alt.Trans.S E C X) : Main.Trans.S E C X :=
  match s with
  | Alt.Trans.Active t => Main.Trans.Active t
  | Alt.Trans.Passive e k => Main.Trans.Passive e k
  end.

Definition o2n_label {E X} (l : Main.Trans.label E X) : Alt.Trans.label E X :=
  match l with
  | Main.Trans.τ => Alt.Trans.τ
  | Main.Trans.ask e => Alt.Trans.ask e
  | Main.Trans.rcv e v => Alt.Trans.rcv e v
  | Main.Trans.val v => Alt.Trans.val v
  end.

Lemma n2o_o2n_S {E C X} (s : Main.Trans.S E C X) : n2o_S (o2n_S s) = s.
Proof. now destruct s. Qed.

Lemma o2n_n2o_S {E C X} (s : Alt.Trans.S E C X) : o2n_S (n2o_S s) = s.
Proof. now destruct s. Qed.

Lemma n2o_S_Seq {E C X} (a b : Alt.Trans.S E C X) :
  Alt.Trans.Seq a b -> Main.Trans.Seq (n2o_S a) (n2o_S b).
Proof. intros H; inv H; cbn [n2o_S]; constructor; assumption. Qed.

Lemma trans_alt_eps_inv {E C X} (a mid : Alt.Trans.S E C X) :
  trans_alt ε a mid ->
  (exists Z (c : C Z) (k : Z -> ctree E C X) t u x,
      a = Alt.Trans.Active t /\ mid = Alt.Trans.Active u /\ t ≅ Br c k /\ u ≅ k x)
  \/ (exists t t' u,
      a = Alt.Trans.Active t /\ mid = Alt.Trans.Active u /\ t ≅ Guard t' /\ u ≅ t').
Proof.
  intros TR; unfold trans_alt in TR; cbn in TR.
  inversion TR; subst.
  - left. eauto 12.
  - right. eauto 12.
Qed.

Lemma transR_label_base {E C X} (l : Main.Trans.label E X) (m b : Alt.Trans.S E C X) :
  trans_alt (o2n_label l) m b -> Main.Trans.transR l (n2o_S m) (n2o_S b).
Proof.
  destruct l; cbn [o2n_label]; intros TR; unfold trans_alt in TR; cbn in TR.
  - dependent destruction TR; cbn [n2o_S]. eapply Main.Trans.Transstep; eassumption.
  - dependent destruction TR; cbn [n2o_S]. eapply Main.Trans.Transask; eassumption.
  - dependent destruction TR; cbn [n2o_S]. eapply Main.Trans.Transrcv; eassumption.
  - dependent destruction TR; cbn [n2o_S]. eapply Main.Trans.Transval; eassumption.
Qed.

Definition lift_L {E F X Y} (L : Main.Trans.lrel E F X Y) : Alt.Trans.lrel E F X Y :=
  {| Alt.Trans.RR   := Main.Trans.RR L ;
     Alt.Trans.Rask := Main.Trans.Rask L ;
     Alt.Trans.Rrcv := Main.Trans.Rrcv L |}.

(* old to new through lifting *)
Lemma lift_L_o2n {E F X Y} (L : Main.Trans.lrel E F X Y)
  (la : Main.Trans.label E X) (lb : Main.Trans.label F Y) :
  Main.Trans.build_rel L la lb ->
  Alt.Trans.build_rel (lift_L L) (o2n_label la) (o2n_label lb).
Proof.
  intros H; destruct H; cbn [o2n_label]; now constructor.
Qed.

Lemma lift_L_o2n_inv {E F X Y} (L : Main.Trans.lrel E F X Y)
  (a : Alt.Trans.label E X) (b : Alt.Trans.label F Y) :
  Alt.Trans.build_rel (lift_L L) a b ->
  exists la lb, a = o2n_label la /\ b = o2n_label lb /\ Main.Trans.build_rel L la lb.
Proof.
  intros H; destruct H.
  - exists Main.Trans.τ, Main.Trans.τ; cbn [o2n_label]; repeat split; constructor.
  - exists (Main.Trans.ask e), (Main.Trans.ask f); cbn [o2n_label]; repeat split; now constructor.
  - exists (Main.Trans.rcv e x), (Main.Trans.rcv f y); cbn [o2n_label]; repeat split; now constructor.
  - exists (Main.Trans.val x), (Main.Trans.val y); cbn [o2n_label]; repeat split; now constructor.
Qed.

#[global] Instance lift_L_Leq_reflexiveL {E X} : ReflexiveL (lift_L (@Main.Trans.Leq E X)).
Proof.
  intros [] Hne; try easy; constructor; cbn; first [reflexivity | constructor].
Qed.

Lemma label_non_eps_image {E X} (l : Alt.Trans.label E X) :
  l <> ε -> exists lo, l = o2n_label lo.
Proof.
  destruct l; intro Hne.
  - exists Main.Trans.τ; reflexivity.
  - easy.
  - exists (Main.Trans.ask e); reflexivity.
  - exists (Main.Trans.rcv e v); reflexivity.
  - exists (Main.Trans.val v); reflexivity.
Qed.

Lemma o2n_label_inj {E X} (l l' : Main.Trans.label E X) :
  o2n_label l = o2n_label l' -> l = l'.
Proof.
  destruct l, l'; cbn; intro H; try easy;
    dependent destruction H; reflexivity.
Qed.

Lemma lift_L_flipL {E F X Y} (L : Main.Trans.lrel E F X Y) :
  lift_L (Main.Trans.flipL L) = Alt.Trans.flipL (lift_L L).
Proof.
  now destruct L.
Qed.

(* Reversing a lifted value relation is the same as lifting the reversed relation. *)
Lemma flipL_lift_L_Lvrel {E X Y} (RS : rel X Y) :
  Alt.Trans.lequiv (Alt.Trans.flipL (lift_L (@Main.Trans.Lvrel E X Y RS))) (lift_L (Main.Trans.Lvrel (flip RS))).
Proof.
  split3; cbn; intros;
    [reflexivity | split; intros H; destruct H; constructor | split; intros H; destruct H; constructor].
Qed.
