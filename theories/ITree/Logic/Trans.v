From ExtLib Require Import
     Structures.Monads
     Structures.MonadState
     Data.Monads.StateMonad.

From Coq Require Import
  List
  Basics
  Classes.SetoidClass
  Classes.RelationPairs.

From Coinduction Require Import lattice.

From CTree Require Import
  Logic.Kripke
  Events.Writer
  ITree.Equ
  ITree.Interp
  ITree.Core.

Set Implicit Arguments.
Generalizable All Variables.

Import Itree ITreeNotations.
Local Open Scope itree_scope.
Local Open Scope ctl_scope.

(*| Kripke transition system |*)
Section KripkeTrans.
  Context {W: Type}.
  Notation itreeW X := (itree (writerE W) X).
  Notation itreeW' X := (itree' (writerE W) X).

  (*| Kripke transition system |*)
  Inductive trans_{X}: rel (itreeW' X * W) (itreeW' X * W) :=
  | kTau t t' w w':
    trans_ (observe t, w) (observe t', w') ->
    trans_ (TauF t, w) (observe t', w')
  | kVis t w w' w'' (k: encode (Log w') -> itreeW X):
    t ≅ k tt ->
    w' = w'' ->
    trans_ (VisF (Log w') k, w) (observe t, w'').
  Hint Constructors trans_ : core.

  Definition trans{X}: rel (itreeW X * W) (itreeW X * W) :=
    fun '(t,w) '(t',w') => trans_ (X:=X) (observe t, w) (observe t', w').

  Ltac FtoObs :=
    match goal with
      |- trans_ _ (?t,_) =>
        change t with (observe {| _observe := t |})
    end.

  #[global] Instance trans_equ_aux1 {X} (t: itreeW' X) (w: W):
    Proper (going (equ eq) * eq ==> flip impl) (trans_ (t,w)).
  Proof.
    unfold Proper, respectful, iff, fst, snd; cbn; unfold fst, snd;
      cbn; unfold RelCompFun; cbn.
    intros (u & su) (u' & su') (equ & <-) TR.
    inv equ; rename H into equ; cbn in *.
    step in equ.
    revert u equ.
    dependent induction TR; intros; subst; eauto.
    + FtoObs.
      eapply kTau.
      eapply IHTR; auto.
    + FtoObs.
      eapply kVis; auto.
      * rewrite <- H.
        cbn.
        step.
        assumption.
  Qed.

  #[global] Instance trans_equ_aux2{X}:
    Proper (going (equ eq) * eq ==> going (equ eq) * eq ==> impl) (trans_ (X:=X)).
  Proof.
    intros (t & s) (t' & s') (eqt & eqs) (u & su) (u' & su') (equ & eqsu) TR; cbn in *;
      unfold RelCompFun in *; cbn in *; subst.
    rewrite <- equ; clear u' equ.
    inv eqt; rename H into eqt.
    revert t' eqt.
    dependent induction TR; intros; auto.
    + step in eqt; inv eqt; dependent induction H1.
      cbn in x; rewrite <- x.
      eapply kTau.
      eapply IHTR; auto.
      rewrite <- !itree_eta.
      assumption.
    + step in eqt; inv eqt; dependent induction H1.
      cbn in x; rewrite <- x.
      eapply kVis; eauto.
      now rewrite <- H3.
  Qed.

  #[local] Instance trans_equ_proper{X}:
    Proper (equ eq * eq ==> equ eq * eq ==> iff) (trans (X:=X)).
  Proof.
    unfold Proper, respectful, RelCompFun, fst, snd; cbn; intros.
    destruct2 H0; destruct2 H; destruct x, y, x0, y0; subst.
    split; intros TR; unfold trans.
    - now rewrite <- Heqt0, <- Heqt.
    - now rewrite Heqt0, Heqt.
  Qed.

  Definition EquF (X: Type) := @equ (writerE W) (@encode_writerE W) X X eq.
  Arguments EquF /.

  (*| CTree is a kripke automaton |*)
  #[global] Program Instance itree_kripke : Kripke (itree (writerE W)) W :=
    {|
      mequ X := @equ (writerE W) (@encode_writerE W) X X eq;
      ktrans X := trans (X:=X)
    |}.
  Next Obligation.
    exists s'; split; auto.
    now rewrite <- H.
  Qed.

  Context {X: Type}.
  Lemma trans_ret: forall x (t': itreeW X) s s',
      ~ ((Ret x, s) ↦ (t', s')).
  Proof. intros * Hcontra. inv Hcontra. Qed.

  Lemma trans_tau: forall (t t': itreeW X) s s',
      (Tau t, s) ↦ (t', s') <-> ktrans (t, s) (t', s').
  Proof.
    intros; split; intro H.
    - inv H; cbn; now rewrite H3 in H1.
    - cbn; apply kTau. now cbn in H.
  Qed.

  Lemma trans_vis {t': itreeW X} s s' s'' (k: unit -> itreeW X):
    (Vis (Log s'') k, s) ↦ (t', s') <->
      t' ≅ k tt /\ s'' = s'.
  Proof.
    intros; split; intro TR.
    - unfold ktrans in TR; cbn in TR.
      dependent destruction TR; observe_equ x.
      split.
      + now rewrite <- H.
      + reflexivity.
    - destruct TR as (Eqt & ->).
      unfold ktrans; cbn.
      now apply kVis.
  Qed.

  (*| Deterministic [trans] |*)
  Lemma trans_det:
    Deterministic trans (eqY:=(equ eq (X2:=X)*eq)%signature).
  Proof.
    intros [tx sx] [ty sy] [tz sz]; cbn.
    intros Hx Hy.
    dependent induction Hx; rewrite <- x0 in Hy; inv Hy.
    - eapply IHHx; auto.
      + now rewrite x.
      + now rewrite <- H2.
    - invert.
      rewrite <- H in H2.
      observe_equ H4.
      observe_equ x.
      rewrite <- Eqt0, <- Eqt, H2.
      unfold RelCompFun, fst, snd.
      split; reflexivity.
  Qed.

  Lemma trans_bind_inv_aux {Y} (s s': W)(T U: itreeW' Y) :
    trans_ (T, s) (U, s') ->
  forall (t: itreeW X) (k: X -> itreeW Y) (u: itreeW Y),
    go T ≅ t >>= k ->
    go U ≅ u ->
    (exists t', (t, s) ↦ (t', s') /\ u ≅ x <- t' ;; k x) \/
      (exists x, is_ret x t /\ (k x, s) ↦ (u, s')).
  Proof.
    intros TR.
    dependent induction TR; intros.
    - rewrite unfold_bind in H.
      unfold ktrans, trans; cbn.
      desobs t0; observe_equ Heqt.
      + right.
        exists x; split.
        * unfold is_ret; rewrite Heqt; apply RetRet.
        * rewrite <- H, <- H0.
          cbn; now apply kTau.
      + pose proof (equ_tau_invE H).
        setoid_rewrite trans_tau.
        specialize (IHTR _ _ _ _ eq_refl eq_refl t1 k u).
        rewrite <- itree_eta in IHTR.
        edestruct (IHTR H1 H0)  as [(t2 & TR2 & Eq2) | (x' & Hr & TRr)].
        * left.
          exists t2.
          split; eauto.
        * right.
          exists x'; split; auto.
          unfold is_ret.
          eapply RetTau; eauto.
      + step in H; inv H.
    - rewrite unfold_bind in H0.
      desobs t0; observe_equ Heqt.
      + right.
        exists x; split.
        * unfold is_ret; rewrite Heqt; apply RetRet.
        * rewrite <- H0.
          cbn; apply kVis; [|reflexivity].
          now rewrite <- H, <- H1, <- itree_eta.
      + step in H0; inv H0.
      + pose proof (equ_vis_invT H0) as (_ & <-).
        apply equ_vis_invE with tt in H0.
        left.
        exists (k1 tt); rewrite Eqt; split.
        * now cbn; apply kVis.
        * now rewrite <- H1, <- itree_eta, <- H0.
  Qed.

  Lemma trans_bind_inv: forall {Y} (s s': W)
                          (t: itreeW X) (u: itreeW Y) (k: X -> itreeW Y),
      (x <- t ;; k x, s) ↦ (u, s') ->
      (exists t', (t, s) ↦ (t', s') /\ u ≅ x <- t' ;; k x) \/
        (exists x, is_ret x t /\ (k x, s) ↦ (u, s')).
  Proof.
    intros * TR.
    eapply trans_bind_inv_aux.
    apply TR.
    rewrite <- itree_eta; reflexivity.
    rewrite <- itree_eta; reflexivity.
  Qed.

  Lemma trans_bind_inv_l: forall {Y} (s s': W)
                            (t: itreeW X) (u: itreeW Y) (k: X -> itreeW Y),
      (x <- t ;; k x, s) ↦ (u, s') ->
      ~ (exists x, is_ret x t) ->
      (exists t', (t, s) ↦ (t', s') /\ u ≅ x <- t' ;; k x).
  Proof.
    intros.
    apply trans_bind_inv in H.
    destruct H as [(? & ?) | (x0 & Hret & Hcont)]; eauto.
    exfalso.
    apply H0.
    now exists x0.
  Qed.

  (*| Computational version of [transR]

      Here I am embracing determinism to get reflection
      of finite [n-step] itree evaluations. We also prove
      an the equivalence [transF_trans_iff] between
      [transF] and [trans^*].

      The number of steps between [transF] and [trans^*] should
      be the same.
  |*)
  Fixpoint transF_ (n: nat) (t: itreeW' X) (s: W): itreeW X * W :=
    match t, n with
    | RetF x, _ => (Ret x, s)
    | VisF (Log s') k, S m =>
        transF_ m (observe (k tt)) s'
    | TauF t, S m => transF_ m (observe t) s
    | VisF e k, 0 => (Vis e k, s)
    | TauF t, 0 => (Tau t, s)
    end.

  Definition transF(n: nat)(p: itreeW X * W) :=
    let '(t,s) := p in transF_ n (observe t) s.

  #[global] Instance transF_proper_equ n:
    Proper (equ eq * eq ==> equ eq * eq) (transF n).
  Proof.
    repeat red; cbn.
    unfold fst, snd, RelCompFun.
    intros (t & s) (t' & s') (Ht & ->).
    destruct (transF n (t, s')) as (tn, sn') eqn:Htn.
    destruct (transF n (t', s')) as (tn', sn'') eqn:Htn'.
    revert Htn'  Htn.
    revert sn'' tn' sn' tn Ht s'.
    revert t t'.
    induction n; cbn; intros; step in Ht; cbn in Ht.
    - desobs t; desobs t'; cbn in Ht;
        dependent destruction Ht; inv Htn'; inv Htn.
      + split; reflexivity.
      + split; [red; step; cbn; rewrite H |]; reflexivity.
      + destruct e0.
        dependent destruction H1.
        dependent destruction H2.
        split; [|reflexivity].
        red; step; cbn; now constructor.
    - desobs t; desobs t'; cbn in Ht;
        dependent destruction Ht; inv Htn'; inv Htn.
      + split; reflexivity.
      + apply IHn with (t:=t0) (t':=t1) (s':=s'); auto.
      + destruct e0.
        eapply IHn with (t:=k tt) (t':=k0 tt); eauto.
  Qed.

  Infix "≅2" := ((equ eq * eq)%signature) (at level 42, left associativity).
  Ltac split2 := unfold RelCompFun, fst, snd; cbn; split.

  Lemma transF_ret: forall n x t s s',
      (Ret x ≅ t /\ s = s') <->
      transF n (Ret x, s) ≅2 (t, s').
  Proof. induction n; split; cbn; auto. Qed.

  Lemma transF_tau: forall x t t' x',
      (t' ≅ t /\ x = x') <->
      transF 1 (Tau t, x) ≅2 (t', x').
  Proof.
    split; intros (eqt & ?); subst.
    - desobs t; observe_equ Heqt; rewrite eqt, Eqt; try reflexivity.
      destruct e; reflexivity.
    - unfold fst, snd, RelCompFun in *.
      cbn in H, eqt; desobs t; subst; observe_equ_all; rewrite <- eqt, Eqt; auto.
      + now destruct e.
  Qed.

  Lemma transF_vis: forall x k x' t' s,
      (t' ≅ k tt /\ x' = s) <->
      transF 1 (Vis (Log s) k, x) ≅2 (t', x').
  Proof.
    split; intros * (eqt & ?); subst.
    - cbn; rewrite eqt.
      desobs (k tt); observe_equ Heqt; rewrite Eqt; auto.
      split2; destruct e; reflexivity.
    - unfold fst, snd, RelCompFun in *.
      cbn in H, eqt.
      desobs (k tt); subst; observe_equ_all; rewrite <- eqt, Eqt; auto.
      + now destruct e.
  Qed.

  Lemma transF_0: forall x y,
      transF 0 x ≅2 y <-> x ≅2 y.
  Proof.
    intros [tx sx] [ty sy]; split; intros.
    - cbn in H; desobs tx; destruct2 H; observe_equ_all;
        subst; rewrite <- Heqt0, Eqt; auto.
      now destruct e.
    - destruct2 H; cbn; desobs tx;
        observe_equ_all; subst.
      + rewrite <- Heqt, <- Eqt; split2; reflexivity.
      + rewrite <- Heqt, <- Eqt; split2; reflexivity.
      + destruct e; rewrite <- Eqt; split; auto.
  Qed.

  (*| Deterministic [transF] |*)
  Lemma transF_det: forall n x y z,
      transF n x ≅2 y ->
      transF n x ≅2 z ->
      y ≅2 z.
  Proof.
    induction n; intros [tx sx] [ty sy] [tz sz]; cbn; desobs tx;
      intros Hx Hy; split2; destruct2 Hx; destruct2 Hy; subst; try reflexivity;
      rewrite <- Heqt0, <- Heqt1; reflexivity.
  Qed.

  Lemma transF_Sn_left: forall n x z,
      transF (S n) x ≅2 z <->
        (exists y, transF 1 x ≅2 y /\ transF n y ≅2 z).
  Proof.
    induction n; intros [tx sx] [tz sz]; split; intro TR.
    - exists (tz, sz); split; auto.
      now apply transF_0.
    - destruct TR as [[ty sy] [TR1 TR0]].
      rewrite transF_0 in TR0.
      now rewrite TR1.
    - remember (S n) as p.
      cbn in TR.
      desobs tx.
      + exists (tz, sz); split.
        cbn; rewrite Heqt; auto.
  Admitted.

  Lemma transF_Sn_right: forall n x z,
      transF (S n) x ≅2 z <->
        (exists y, transF n x ≅2 y /\ transF 1 y ≅2 z).
  Proof.
    induction n; intros [tx sx] [tz sz]; split; intro TR.
    - exists (tx, sx); split; auto.
      apply transF_0; reflexivity.
    - destruct TR as [[ty sy] [TR0 TR1]].
      rewrite transF_0 in TR0.
      now rewrite TR0.
    - admit. (* <- *)
    - admit.
  Admitted.

  Lemma transF_transitive: forall x y z n m,
      transF n x ≅2 y -> transF m y ≅2 z -> transF (n+m) x ≅2 z.
  Proof.
    intros.
    revert H H0.
    revert m x y z.
    induction n; intros.
    - rewrite transF_0 in H; intros.
      rewrite plus_O_n.
      now rewrite H.
    - apply transF_Sn_right in H as (x' & TR1 & TRn).
      rewrite PeanoNat.Nat.add_succ_comm.
      eapply IHn with x'; auto.
      apply transF_Sn_left.
      exists y; auto.
  Qed.

End KripkeTrans.
