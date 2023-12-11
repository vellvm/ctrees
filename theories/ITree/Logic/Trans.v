From ExtLib Require Import
     Structures.Monads
     Structures.MonadState
     Data.Monads.StateMonad.


From Coq Require Import
  Relations.Relation_Definitions
  Basics
  Classes.SetoidClass
  Classes.RelationPairs.

From CTree Require Import
  Logic.Kripke
  Events.Core
  ITree.Events.Writer
  ITree.Equ
  ITree.Interp
  ITree.Core.

Generalizable All Variables.

Import Itree ITreeNotations.
Local Open Scope itree_scope.
Local Open Scope ctl_scope.

Notation itreeW W := (itree (writerE W)).
Notation itreeEW E := (itree (writerE (Bar E))).
Notation itreeW' W X := (itree' (writerE W) X).
Notation itreeEW' E X := (itree' (writerE (Bar E)) X).

(*| Kripke transition system |*)
Section KripkeTrans.
  Context {E: Type} `{HE: Encode E} {X: Type}.
  Notation opt E := (option (Bar E)).

  (*| Kripke transition system |*)
  Inductive trans_: relation (itree' E X * opt E) :=
  | kTau t t' w w':
    trans_ (observe t, w) (observe t', w') ->
    trans_ (TauF t, w) (observe t', w')
  | kVis t w e (k: encode e -> itree E X) x:
    t ≅ k x ->
    trans_ (VisF e k, w) (observe t, Some (Obs e x)).
  Hint Constructors trans_ : core.

  Definition trans: relation (itree E X * opt E) :=
    fun '(t,w) '(t',w') =>
      trans_ (observe t, w) (observe t', w').

  Ltac FtoObs :=
    match goal with
      |- trans_ _ (?t,_) =>
        change t with (observe {| _observe := t |})
    end.

  Global Instance trans_equ_aux1 (t: itree' E X) (w: opt E):
    Proper (going (equ eq) * eq ==> flip impl) (trans_ (t,w)).
  Proof.
    unfold Proper, respectful, iff, fst, snd; cbn; unfold fst, snd;
      cbn; unfold RelCompFun; cbn.
    intros (u & su) (u' & su') (equ & <-) TR.
    inv equ; rename H into equ; cbn in *.
    step in equ.
    revert u equ.
    dependent induction TR; intros; subst; eauto; FtoObs.
    + eapply kTau.
      eapply IHTR; auto.
    + eapply kVis; auto.
      * rewrite <- H.
        cbn.
        step.
        assumption.
  Qed.

  Global Instance trans_equ_aux2:
    Proper (going (equ eq) * eq ==> going (equ eq) * eq ==> impl) trans_.
  Proof.
    intros (t & s) (t' & s') (eqt & eqs) (u & su)
      (u' & su') (equ & eqsu) TR; cbn in *;
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

  Global Instance trans_equ_proper:
    Proper (equ eq * eq ==> equ eq * eq ==> iff) trans.
  Proof.
    unfold Proper, respectful, RelCompFun, fst, snd; cbn; intros.
    destruct2 H0; destruct2 H; destruct x, y, x0, y0; subst.
    split; intros TR; unfold trans.
    - now rewrite <- Heqt0, <- Heqt.
    - now rewrite Heqt0, Heqt.
  Qed.

  Global Instance iter_trans_proper n:
    Proper (equ eq * eq ==> equ eq * eq ==> iff)
      (rel_iter (equ eq * eq)%signature n trans).
  Proof.
  induction n; unfold Proper, respectful, RelProd, RelCompFun, fst, snd; cbn;
    intros [t s] [u w] [Ht ->] [t' s'] [u' w'] [Ht' ->]; split2; intros; subst.
  - destruct H as (? & ->).
    split2; [|reflexivity].
    symmetry in Ht.
    transitivity t; auto.
    transitivity t'; auto.
  - destruct H as (? & ->).
    split2; [|reflexivity].
    transitivity u; auto.
    transitivity u'; auto.
    now symmetry.
  - destruct H as ([t_ w_] & TR & TRi).
    exists (t_, w_).
    rewrite <- Ht; split; [assumption|].
    eapply IHn with (x:=(t_, w_)) in TRi; eauto.
    split2; red; cbn; [symmetry|]; auto.
  - destruct H as ([t_ w_] & TR & TRi).
    exists (t_, w_).
    rewrite Ht; split; [assumption|].
    eapply IHn with (x:=(t_, w_)) in TRi; eauto.
  Qed.
End KripkeTrans.

Ltac ktrans_inv H :=
  simpl ktrans in H;
  simpl trans in H;
  dependent destruction H.

Section KripkeLemmas.
  Context {E: Type} {HE: Encode E}.
  Notation equ := (fun (X: Type) => @equ E HE X X eq).

  (*| ITree is a kripke automaton |*)
  #[refine] Global Instance itree_kripke: Kripke (itree E) equ (Bar E) :=
    {| ktrans X := trans (X:=X) |}.
  Proof.
    - intros.
      exists s'; split; auto.
      now rewrite <- H.
    - intros.
      unfold trans in H.
      remember (observe t, Some w).
      remember (observe t', w').
      generalize dependent t.
      generalize dependent t'.
      revert w'.
      induction H; intros; subst; inv Heqp.
      + now eapply IHtrans_ with (t:=t) (t':=t'0).
      + inv Heqp0; eexists; reflexivity.
  Qed.
  Arguments ktrans /.
  Typeclasses eauto := 1.
  Lemma ktrans_ret{X}: forall (x: X) (t': itree E X) (s s': option (Bar E)),
      (Ret x, s) ↦ (t', s') -> False.
  Proof.
    intros * Hcontra.


    dependent destruction Hcontra.
    ktrans_inv Hcontra.
  Qed.

  Lemma ktrans_tau{X}: forall (t t': itree E X) s s',
      (Tau t, s) ↦ (t', s') <-> ktrans (t, s) (t', s').
  Proof.
    intros; split; intro H.
    - ktrans_inv H; cbn; now rewrite x in H.
    - cbn; apply kTau; now cbn in H.
  Qed.

  Lemma ktrans_vis {X} {t': itree E X} s s' e (k: encode e -> itree E X):
    (Vis e k, s) ↦ (t', s') <->
      (exists (x: encode e), t' ≅ k x /\ s' = Some (Obs e x)).
  Proof.
    intros; split; intro TR; ktrans_inv TR.
    - observe_equ x; exists x0.
      split.
      + now rewrite <- H.
      + reflexivity.
    - unfold ktrans; cbn.
      destruct H as (Heq & ->).
      now apply kVis.
  Qed.

  Lemma ktrans_bind_inv_aux {X Y} (s s': option (Bar E))(T U: itree' E Y) :
    trans_ (T, s) (U, s') ->
    forall (t: itree E X) (k: X -> itree E Y) (u: itree E Y),
      go T ≅ t >>= k ->
      go U ≅ u ->
      (exists t', (t, s) ↦ (t', s') /\ u ≅ x <- t' ;; k x) \/
        (exists x, may_ret x t /\ (k x, s) ↦ (u, s')).
  Proof.
    intros TR.
    dependent induction TR; intros.
    - rewrite unfold_bind in H.
      unfold ktrans, trans; cbn.
      desobs t0; observe_equ Heqt.
      + right.
        exists x; split.
        * unfold may_ret; rewrite Heqt; apply RetRet.
        * rewrite <- H, <- H0.
          cbn; now apply kTau.
      + pose proof (equ_tau_invE H).
        setoid_rewrite ktrans_tau.
        specialize (IHTR _ _ _ _ eq_refl eq_refl t1 k u).
        rewrite <- itree_eta in IHTR.
        edestruct (IHTR H1 H0)  as [(t2 & TR2 & Eq2) | (x' & Hr & TRr)].
        * left.
          exists t2.
          split; eauto.
        * right.
          exists x'; split; auto.
          unfold may_ret.
          eapply RetTau; eauto.
      + step in H; inv H.
    - rewrite unfold_bind in H0.
      desobs t0; observe_equ Heqt.
      + right.
        exists x0; split.
        * unfold may_ret; rewrite Heqt; apply RetRet.
        * rewrite <- H0.
          apply ktrans_vis; exists x.
          split; [|reflexivity].
          now rewrite <- H, <- H1, <- itree_eta.
      + step in H0; inv H0.
      + pose proof (equ_vis_invT H0) as (_ & <-).
        apply equ_vis_invE with x in H0.
        left.
        exists (k1 x); rewrite Eqt; split.
        * now cbn; apply kVis.
        * now rewrite <- H1, <- itree_eta, <- H0.
  Qed.

  Lemma ktrans_bind_inv: forall {X Y} (s s': option (Bar E))
                           (t: itree E X) (u: itree E Y) (k: X -> itree E Y),
      (x <- t ;; k x, s) ↦ (u, s') ->
      (exists t', (t, s) ↦ (t', s') /\ u ≅ x <- t' ;; k x) \/
        (exists x, may_ret x t /\ (k x, s) ↦ (u, s')).
  Proof.
    intros * TR.
    eapply ktrans_bind_inv_aux.
    apply TR.
    rewrite <- itree_eta; reflexivity.
    rewrite <- itree_eta; reflexivity.
  Qed.

  Lemma ktrans_bind_inv_l: forall {X Y} (s s': option (Bar E))
                             (t: itree E X) (u: itree E Y) (k: X -> itree E Y),
      (x <- t ;; k x, s) ↦ (u, s') ->
      ~ (exists x, may_ret x t) ->
      (exists t', (t, s) ↦ (t', s') /\ u ≅ x <- t' ;; k x).
  Proof.
    intros.
    apply ktrans_bind_inv in H.
    destruct H as [(? & ?) | (x0 & Hret & Hcont)]; eauto.
    exfalso.
    apply H0.
    now exists x0.
  Qed.
End KripkeLemmas.

Section FixpointTransW.
  Context {W X: Type}.

  (*| The base instance is [ctree_kripke] but depending on what we observe,
    some more convenient thin wrappers work better |*)
  #[refine] Global Instance itreeW_kripke{W}: Kripke (itreeW W) (option W) | 80 :=
    {|
      MM := Monad_itree;
      ktrans X '(t, w) '(t', w') :=
        let opt_proj := option_map (fun w => Obs (Log w) tt) in  
        itree_kripke.(ktrans) (X:=X) (t, opt_proj w) (t', opt_proj w');
      mequ X := @equ (writerE W) _ _ X eq
    |}.
  Proof.
    intros; now apply itree_kripke.(ktrans_semiproper) with (t:=t) (s:=s).
  Defined.
  
  (*| Computational version of [ktrans] for |*)
  Fixpoint transW_ {W X}(n: nat) (t: itreeW' W X) (s: W): itreeW W X * W :=
    match t, n with
    | RetF x, _ => (Ret x, s)
    | VisF (Log s') k, S m =>
        transW_ m (observe (k tt)) s'
    | TauF t, S m => transW_ m (observe t) s
    | VisF e k, 0 => (Vis e k, s)
    | TauF t, 0 => (Tau t, s)
    end.

  Definition transW{W X}(n: nat)(p: itreeW W X * W) :=
    let '(t,s) := p in transW_ n (observe t) s.

  Global Instance transW_proper_equ:
    Proper (eq ==> equ eq * eq ==> equ eq * eq) (@transW W X).
  Proof.
    repeat red; cbn.
    intros ? n ->.
    unfold fst, snd, RelCompFun.
    intros (t & s) (t' & s') (Ht & ->).
    destruct (transW n (t, s')) as (tn, sn') eqn:Htn.
    destruct (transW n (t', s')) as (tn', sn'') eqn:Htn'.
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

  Infix "≅2" := ((@equ (writerE W) (encode_writerE (S:=W)) X X eq * eq)%signature)
                  (at level 42, left associativity).

  Lemma transW_ret: forall n x t s s',
      (Ret x ≅ t /\ s = s') <->
        transW n (Ret x, s) ≅2 (t, s').
  Proof. induction n; split; cbn; auto. Qed.

  Lemma transW_tau: forall x t t' x',
      (t' ≅ t /\ x = x') <->
        transW 1 (Tau t, x) ≅2 (t', x').
  Proof.
    split; intros (eqt & ?); subst.
    - desobs t; observe_equ Heqt; rewrite eqt, Eqt; try reflexivity.
      destruct e; reflexivity.
    - unfold fst, snd, RelCompFun in *.
      cbn in H, eqt; desobs t; subst; observe_equ_all; rewrite <- eqt, Eqt; auto.
      + now destruct e.
  Qed.

  Lemma transW_vis: forall x k x' t' s,
      (t' ≅ k tt /\ x' = s) <->
        transW 1 (Vis (Log s) k, x) ≅2 (t', x').
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

  Lemma transW_0: forall x y,
      transW 0 x ≅2 y <-> x ≅2 y.
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

  (*| Deterministic [transW] |*)
  Lemma transW_det: forall n x y z,
      transW n x ≅2 y ->
      transW n x ≅2 z ->
      y ≅2 z.
  Proof.
    induction n; intros [tx sx] [ty sy] [tz sz]; cbn; desobs tx;
      intros Hx Hy; split2; destruct2 Hx; destruct2 Hy; subst; try reflexivity;
      rewrite <- Heqt0, <- Heqt1; reflexivity.
  Qed.

  (*| Deterministic [ktrans] |*)
  Lemma ktransW_det: forall (t t' t'': itreeW W X) s s' s'',
      (t, s) ↦ (t', s') ->
      (t, s) ↦ (t'', s'') ->
      t' ≅ t'' /\ s' = s''.
  Proof.
    cbn; intros * Hx Hy.
    dependent induction Hx. 
    - rewrite <- x0 in Hy; inv Hy.
      eapply IHHx; auto.
      + now rewrite x.
      + now rewrite <- H2.
    - unfold encode, encode_writerE in x0, k.
      destruct x0.
      rewrite <- x1 in Hy.
      apply ktrans_vis in Hy as ([] & ? & ->).
      observe_equ x.
      rewrite <- Eqt, H0, H; split; reflexivity.
  Qed.

  Lemma transW_Sn_left: forall n x z,
      transW (S n) x ≅2 z <->
        (exists y, transW 1 x ≅2 y /\ transW n y ≅2 z).
  Proof.
    induction n; intros [tx sx] [tz sz]; split; intro TR.
    - exists (tz, sz); split; auto.
      now apply transW_0.
    - destruct TR as [[ty sy] [TR1 TR0]].
      rewrite transW_0 in TR0.
      now rewrite TR1.
    - remember (S n) as p.
      desobs tx.
      + exists (tz, sz); split.
        * cbn; destruct2 TR; rewrite Heqt in *; auto.
        * cbn in TR; rewrite Heqt in TR; destruct2 TR; subst; rewrite <- Heqt0.
          cbn; split2; reflexivity.
      + exists (t, sx); split.
        * admit.
  Admitted.

  Lemma transW_Sn_right: forall n x z,
      transW (S n) x ≅2 z <->
        (exists y, transW n x ≅2 y /\ transW 1 y ≅2 z).
  Proof.
    induction n; intros [tx sx] [tz sz]; split; intro TR.
    - exists (tx, sx); split; auto.
      apply transW_0; reflexivity.
    - destruct TR as [[ty sy] [TR0 TR1]].
      rewrite transW_0 in TR0.
      now rewrite TR0.
    - admit. (* <- *)
    - admit.
  Admitted.

  Lemma transF_transitive: forall x y z n m,
      transW n x ≅2 y -> transW m y ≅2 z -> transW (n+m) x ≅2 z.
  Proof.
    intros.
    revert H H0.
    revert m x y z.
    induction n; intros.
    - rewrite transW_0 in H; intros.
      rewrite plus_O_n.
      now rewrite H.
    - apply transW_Sn_right in H as (x' & TR1 & TRn).
      rewrite PeanoNat.Nat.add_succ_comm.
      eapply IHn with x'; auto.
      apply transW_Sn_left.
      exists y; auto.
  Qed.

End FixpointTransW.
