(* begin hide *)
From Coinduction Require Import
     coinduction rel tactics.

From CTree Require Import
     Utils CTrees Equ Shallow Trans.

From RelationAlgebra Require Import
     monoid
     kat      (* kat == Kleene Algebra with Test, we don't use the tests part *)
     kat_tac
     prop
     rel
     srel
     comparisons
     rewriting
     normalisation.

Section Bisim.

  Context {E : Type -> Type} {X : Type}.
  Notation S := (ctree E X).

  Section Strong.

    (** The function defining strong simulations *)
    Program Definition ss : mon (S -> S -> Prop) :=
      {| body R t u :=
        forall l t', trans l t t' -> exists2 u', trans l u u' & R t' u'
      |}.
    Next Obligation.
      edestruct H0; eauto.
    Qed.

    (* Symmetrized version: the other direction of the simulation is obtained as
     fun R t u => ss (fun x y => R y x) u t
    i.e. fun R t u => ss (converse R) u t
    i.e. fun R => converse (ss (converse R))
    i.e. comp converse (comp ss converse)
     *)
    Notation sb := (Coinduction.lattice.cap ss (comp converse (comp ss converse))).

    Notation sbisim := (gfp sb : hrel _ _).
    Notation "t ~ u" := (gfp sb t u) (at level 70).
    Notation st := (t sb).
    Notation sbt := (bt sb).
    (** notations  for easing readability in proofs by enhanced coinduction *)
    Notation "t [~] u" := (st  _ t u) (at level 79).
    Notation "t {~} u" := (sbt _ t u) (at level 79).

    Definition seq: relation (ctree E X) := eq.
    Arguments seq/.

    (** [eq] is a post-fixpoint, thus [const eq] is below [t] *)
    Lemma refl_st: const seq <= st.
    Proof.
      apply leq_t.
      split; intros; cbn in *; subst; eauto.
    Qed.

    (** converse is compatible *)
    Lemma converse_st: converse <= st.
    Proof.
      apply invol_t.
    Qed.

    (** so is squaring *)
    Lemma square_st: square <= st.
    Proof.
      apply Coinduction, by_Symmetry.
      (* We can use a symmetry argument:
       - we have defined [sb] as [sb = ss /\ i ss i]
       - so if f (square here) is symmetric in the sense that
         f i <= i f
       - then it suffices to prove that [square sb <= ss square]
         instead of [square sb <= sb square]
       *)
      - intros R x z [y xy yz].
        now exists y.
      - rewrite cap_l at 1.
        intros R x z [y xy yz] l x' xx'.
        destruct (xy _ _ xx') as [y' yy' x'y'].
        destruct (yz _ _ yy') as [z' zz' y'z'].
        exists z'. assumption.
        apply (f_Tf sb).  (* TODO: set of tactics for the companion *)
        eexists; eauto.
    Qed.

    (** thus bisimilarity and [t R] are always equivalence relations. *)
    Global Instance Equivalence_st R: Equivalence (st R).
    Proof. apply Equivalence_t. apply refl_st. apply square_st. apply converse_st. Qed.

    Corollary Equivalence_bisim: Equivalence sbisim.
    Proof. apply Equivalence_st. Qed.

  End Strong.

  Notation sb := (Coinduction.lattice.cap ss (comp converse (comp ss converse))).
  Notation sbisim := (gfp sb : hrel _ _).
  Notation "t ~ u" := (gfp sb t u) (at level 70).
  Notation st := (t sb).
  Notation sbt := (bt sb).
  (** notations  for easing readability in proofs by enhanced coinduction *)
  Notation "t [~] u" := (st  _ t u) (at level 79).
  Notation "t {~} u" := (sbt _ t u) (at level 79).

  Section Weak.

    (** the function defining weak simulations and similarity *)
    Program Definition ws: mon (rel S S) :=
      {| body R p q :=
        forall l p', trans l p p' -> exists2 q', wtrans l q q' & R p' q' |}.
    Next Obligation. destruct (H0 _ _ H1). eauto. Qed.

    (** the symmetrised version, defining weak bisimulations and bisimilarity *)
    Notation wb := (Coinduction.lattice.cap ws (comp converse (comp ws converse))).

    Notation wbisim := (gfp wb: hrel _ _).
    Notation "p ≈ q" := (gfp wb p q) (at level 70).
    Notation wt := (coinduction.t wb).
    Notation wT := (coinduction.T wb).
    Notation wbt := (coinduction.bt wb).
    Notation wbT := (coinduction.bT wb).
    (** notations  for easing readability in proofs by enhanced coinduction *)
    Notation "x [≈] y" := (wt _ x y) (at level 80).
    Notation "x {≈} y" := (wbt _ x y) (at level 80).

    (** the function defining one-sided expansion (only used later) *)
    Program Definition es: mon (rel S S) :=
      {| body R p q :=
        forall l p', trans l p p' -> exists2 q', etrans l q q' & R p' q' |}.
    Next Obligation. destruct (H0 _ _ H1). eauto. Qed.

    Lemma s_e: ss <= es.
    Proof. intros R p q H l p' pp'. destruct (H _ _ pp'). eauto using trans_etrans_. Qed.
    Lemma e_w: es <= ws.
    Proof. intros R p q H l p' pp'. destruct (H _ _ pp'). eauto using etrans_wtrans_. Qed.
    Lemma s_w: ss <= ws.
    Proof. rewrite s_e. apply e_w. Qed.

    Corollary sbisim_wbisim: sbisim <= wbisim.
    Proof.
      apply gfp_leq.
      apply Coinduction.lattice.cap_leq. apply s_w.
      intros R p q. apply (@s_w (R°) q p).
    Qed.

    (* Instance sbisim_wbisim_subrelation : subrelation sbisim wbisim.
  apply sbisim_wbisim.
  Qed. *)

    (** [wt R] is always reflexive: it contains ~ *)
    #[global] Instance Reflexive_wt R: Reflexive (wt R).
    Proof. intro. apply (gfp_t wb). now apply sbisim_wbisim. Qed.

    (** converse is compatible *)
    Lemma converse_wt: converse <= wt.
    Proof. apply invol_t. Qed.

    (** thus [wt R] is always symmetric *)
    #[global] Instance Symmetric_wt R: Symmetric (wt R).
    Proof. intros ??. apply (ft_t converse_wt). Qed.

    Lemma TauI_wb : forall t,
        TauI t ≈ t.
    Proof.
      intros t; step; split.
      - intros l t' H.
        apply trans_TauI in H.
        exists t'.
        apply trans_wtrans; auto.
        reflexivity.
      - intros l t' H. exists t'.
        apply trans_wtrans.
        apply TauI_trans; auto.
        cbn; reflexivity.
    Qed.

    Lemma TauV_wb : forall t,
        TauV t ≈ t.
    Proof.
      intros t; step; split.
      - intros l t' H.
        apply TauV_trans in H as [EQ ->].
        exists t'.
        rewrite EQ. apply wnil.
        reflexivity.
      - intros l t' H. exists t'.
        apply wtrans_TauV.
        apply trans_wtrans; auto.
        cbn; reflexivity.
    Qed.

    (* This proof should be shorter if actually using some braincells I think *)
    #[global] Instance equ_sbisim_compat : Proper (equ eq ==> equ eq ==> iff) sbisim.
    Proof.
      intros t t' tt' u u' uu'; split.
      - revert t t' u u' tt' uu'.
        coinduction ? CIH.
        intros * eqt equ eqtu.
        step in eqtu.
        destruct eqtu as [ftu btu].
        split.
        + cbn; intros.
          rewrite <- eqt in H.
          apply ftu in H as [?u' T eq].
          eexists. rewrite <- equ. apply T.
          eapply CIH; try reflexivity; auto.
        + cbn; intros.
          rewrite <- equ in H.
          apply btu in H as [?t' T eq].
          eexists. rewrite <- eqt. apply T.
          eapply CIH; try reflexivity; auto.
      - revert t t' u u' tt' uu'.
        coinduction ? CIH.
        intros * eqt equ eqtu.
        step in eqtu.
        destruct eqtu as [ftu btu].
        split.
        + cbn; intros.
          rewrite eqt in H.
          apply ftu in H as [?u' T eq].
          eexists. rewrite equ. apply T.
          eapply CIH; try reflexivity; auto.
        + cbn; intros.
          rewrite equ in H.
          apply btu in H as [?t' T eq].
          eexists. rewrite eqt. apply T.
          eapply CIH; try reflexivity; auto.
    Qed.

    #[global] Instance equ_wbisim_compat : Proper (equ eq ==> equ eq ==> iff) wbisim.
    Proof.
      intros t t' eqt u u' equ; split.
      - revert t t' u u' eqt equ.
        coinduction ? CIH.
        intros * eqt equ eqtu.
        step in eqtu.
        destruct eqtu as [ftu btu].
        split.
        + intros ? ? ?.
          rewrite <- eqt in H.
          apply ftu in H as [?u' T eq].
          eexists. rewrite <- equ. apply T.
          eapply CIH; try reflexivity; auto.
        + intros ? ? ?.
          rewrite <- equ in H.
          apply btu in H as [?t' T eq].
          eexists. rewrite <- eqt. apply T.
          eapply CIH; try reflexivity; auto.
      - revert t t' u u' eqt equ.
        coinduction ? CIH.
        intros * eqt equ eqtu.
        step in eqtu.
        destruct eqtu as [ftu btu].
        split.
        + intros ? ? ?.
          rewrite eqt in H.
          apply ftu in H as [?u' T eq].
          eexists. rewrite equ. apply T.
          eapply CIH; try reflexivity; auto.
        + intros ? ? ?.
          rewrite equ in H.
          apply btu in H as [?t' T eq].
          eexists. rewrite eqt. apply T.
          eapply CIH; try reflexivity; auto.
    Qed.

    #[global] Instance equ_wbisim_subrelation : subrelation (equ eq) wbisim.
    intros t u EQ. rewrite EQ. reflexivity.
    Qed.

    (** but squaring is not compatible and [t R] is not always transitive *)
    Lemma not_Transitive_wt Z: X -> Z -> E Z -> ~ forall R, Transitive (wt R).
    Proof.
      intros x z e H.
      cut (Vis e (fun _ => Ret x) ≈ Ret x).
      - intros abs. step in abs; destruct abs as [abs _].
        destruct (abs (obs e z) (Ret x)) as [? step EQ].
        constructor; reflexivity.
        apply wtrans_ret in step as [absurd _]; inv absurd.
      - rewrite <- TauV_wb.
        coinduction ? CIH.
        split.
        + intros l t' tt'.
          apply TauV_trans in tt' as [EQ ->].
          exists (Ret x); auto.
          apply equ_wbisim_subrelation in EQ.
          rewrite (subrelation_gfp_t _ EQ).
          rewrite <- (subrelation_gfp_t _ (TauV_wb _)).
          assumption.  (* Here clearly some instances are missing, the rewrite do not work in the other order, and should not require such an explicit low level call *)
        + intros ? ? ?.
          inv H0.
    Qed.

    Lemma not_square_wt Z: X -> Z -> E Z -> ~ square <= wt.
    Proof.
      intros x z e H. elim (not_Transitive_wt _ x z e). intro R.
      intros ? y ???. apply (ft_t H). now exists y.
    Qed.

    Definition wbisimT : srel SS SS :=
      {| hrel_of := wbisim : hrel SS SS |}.

    (** weak bisimilarity is nevertheless transitive, which we prove below *)

    (** algebraic refomulation of the right-to-left part of the game *)
    (* We get to express it in the setoid world or not, not yet sure what's best *)
    Lemma wbisim_trans_back l: wbisimT ⋅ trans l ≦ wtrans l ⋅ wbisimT.
    Proof.
      intros p q' [q pq qq']. apply (gfp_pfp wb) in pq as [_ pq]. now apply pq.
    Qed.
    Lemma wbisim_trans_back' l: wbisim ⋅ transR l ≦ (wtrans l : hrel _ _) ⋅ wbisim.
    Proof.
      intros p q' [q pq qq']. apply (gfp_pfp wb) in pq as [_ pq]. now apply pq.
    Qed.
    (* Lemma wbisim_etrans_back l: wbisim ⋅ etrans l ≦ (wtrans l : hrel _ _) ⋅ wbisim.
 Proof.
   unfold etrans; destruct l. 2: apply @wbisim_trans_back.
   ra_normalise. rewrite wbisim_trans_back.
   unfold wtrans, etrans. ka.
 Qed. *)
    Lemma wbisim_etrans_back' l: wbisimT ⋅ etrans l ≦ wtrans l ⋅ wbisimT.
    Proof.
      unfold etrans; destruct l. 2: apply @wbisim_trans_back'.
      ra_normalise. rewrite wbisim_trans_back.
      unfold wtrans, etrans. ka.
    Qed.
    Lemma wbisim_taus_back': wbisimT ⋅ (trans tau)^* ≦ (trans tau)^* ⋅ wbisimT.
    Proof.
      rewrite <-str_invol at 2.
      apply str_move_l. rewrite wbisim_trans_back. unfold wtrans, etrans. ka.
    Qed.
    Lemma wbisim_wtrans_back' l: wbisimT ⋅ wtrans l ≦ wtrans l ⋅ wbisimT.
    Proof.
      unfold wtrans.
      mrewrite wbisim_taus_back'.
      mrewrite wbisim_etrans_back'.
      mrewrite wbisim_taus_back'.
      unfold wtrans, etrans. ka.
    Qed.

    Lemma cnv_wt R: (wt R: hrel _ _)° ≡ wt R.
    Proof. apply RelationAlgebra.lattice.antisym; intros ???; now apply Symmetric_wt. Qed.
    Lemma cnv_wbisim: wbisim° ≡ wbisim.
    Proof. apply cnv_wt. Qed.
    Lemma cnv_wbisim': wbisimT° ≡ wbisimT.
    Proof. apply cnv_wt. Qed.

    (** by symmetry, similar results for left-to-right game *)
    Lemma wbisim_trans_front l: (trans l)° ⋅ wbisimT ≦ wbisimT ⋅ (wtrans l)°.
    Proof. cnv_switch. rewrite 2cnvdot, cnv_invol, cnv_wbisim'. apply wbisim_trans_back'. Qed.
    Lemma wbisim_etrans_front l: (etrans l)° ⋅ wbisimT ≦ wbisimT ⋅ (wtrans l)°.
    Proof. cnv_switch. rewrite 2cnvdot, cnv_invol, cnv_wbisim'. apply wbisim_etrans_back'. Qed.
    Lemma wbisim_wtrans_front l: (wtrans l)° ⋅ wbisimT ≦ wbisimT ⋅ (wtrans l)°.
    Proof. cnv_switch. rewrite 2cnvdot, cnv_invol, cnv_wbisim'. apply wbisim_wtrans_back'. Qed.

    (** explicit, non-algebraic version *)
    Lemma wbisim_wtrans_front_ p q l p': wtrans l p p' -> p ≈ q -> exists2 q', p' ≈ q' & wtrans l q q'.
    Proof. intros pp' pq. apply wbisim_wtrans_front. now exists p. Qed.

    Global Instance Equivalence_wbisim: Equivalence wbisim.
    Proof.
      split. apply Reflexive_wt. apply Symmetric_wt.
      assert (square wbisim <= wbisim) as H.
      apply leq_gfp. apply symmetric_pfp.
      now rewrite converse_square, cnv_wbisim.
      intros x z [y xy yz] l x' xx'.
      apply (gfp_pfp wb) in xy as [xy _].
      destruct (xy _ _ xx') as [y' yy' x'y'].
      destruct (wbisim_wtrans_front_ _ _ _ _ yy' yz) as [z' y'z' zz'].
      exists z'. assumption. now exists y'.
                                        intros x y z xy yz. apply H. now exists y.
    Qed.


  (* Strong bisimulation played over the weak game, to fix

  (** The function defining weak bisimulations *)
  Program Definition wb' : mon (rel S S) :=
    {| body R t u :=
        (forall l t', wtrans l t t' -> exists2 u', wtrans l u u' & R t' u') /\
        (forall l u', wtrans l u u' -> exists2 t', wtrans l t t' & R t' u')
    |}.
  Next Obligation.
    intros R1 R2 INCL t u [F B]; split; [intros l t' STEP | intros l u' STEP].
    - edestruct F; eauto.
      eexists; eauto; apply INCL; auto.
    - edestruct B; eauto.
      eexists; eauto; apply INCL; auto.
  Qed.

  Notation wbisim' := (gfp wb').
  Notation "t ≈' u" := (gfp wb' t u) (at level 70).
  Notation wt' := (t wb').
  Notation wbt' := (bt wb').
  (** notations  for easing readability in proofs by enhanced coinduction *)
  Notation "t [≈'] u" := (wt'  _ t u) (at level 79).
  Notation "t {≈'} u" := (wbt' _ t u) (at level 79).

  Lemma trans_transs : forall l (t u : S),
    trans  l t u ->
    transs l t u.
  Proof.
  Admitted.
  Hint Resolve trans_transs : core.

 (** [eq] is a post-fixpoint, thus [const eq] is below [t] *)
  Lemma refl_wt': const eq <= wt'.
  Proof.
   apply leq_t.
   split; intros; cbn in *; subst; eauto.
  Qed.

  (** converse is compatible *)
  Lemma converse_wt': converse <= wt'.
  Proof.
    apply leq_t.
    intros R p q [F B]; split; intros * STEP.
    edestruct B; eauto.
    edestruct F; eauto.
  Qed.

(*
 Lemma cnv_wt R: (wt R: hrel _ _)° ≡ wt R.
 Proof. apply RelationAlgebra.lattice.antisym; intros ???; now apply Symmetric_wt. Qed.
 Lemma cnv_wbisim: wbisim° ≡ wbisim.
 Proof. apply cnv_wt. Qed.

 (** by symmetry, similar results for left-to-right game *)
 Lemma wbisim_trans_front l: (trans l)° ⋅ wbisim ≦ wbisim ⋅ (wtrans l)°.
 Proof. cnv_switch. rewrite 2cnvdot, cnv_invol, cnv_wbisim. apply wbisim_trans_back. Qed.
 Lemma wbisim_etrans_front l: (etrans l)° ⋅ wbisim ≦ wbisim ⋅ (wtrans l)°.
 Proof. cnv_switch. rewrite 2cnvdot, cnv_invol, cnv_wbisim. apply wbisim_etrans_back. Qed.
 Lemma wbisim_wtrans_front l: (wtrans l)° ⋅ wbisim ≦ wbisim ⋅ (wtrans l)°.
 Proof. cnv_switch. rewrite 2cnvdot, cnv_invol, cnv_wbisim. apply wbisim_wtrans_back. Qed.

 (** explicit, non-algebraic version *)
 Lemma wbisim_wtrans_front_ p q l p': wtrans l p p' -> p ≈ q -> exists2 q', p' ≈ q' & wtrans l q q'.
 Proof. intros pp' pq. apply wbisim_wtrans_front. now exists p. Qed. *)


  Lemma wbisim_wtrans_front_ :
  forall [t u : S] [l : label] [t' : S],
  transs l t t' ->
  t ≈' u ->
  exists2 u' : S, t' ≈' u' & transs l u u'.
  Proof.
    intros * STEP eq.
    trans in eq; destruct eq as [F B].
    destruct STEP as (v2 & (v1 & s & s') & s'').



  Lemma wbisim'_trans : forall (u v w : S),
    u ≈' v ->
    v ≈' w ->
    u ≈' w.
  Proof.
    coinduction R CIH; intros * eq1 eq2.
    split.
    - intros l u' STEP.
      trans in eq1; destruct eq1 as [F1 B1].
      apply F1 in STEP as [v' STEP equv].
      destruct (wbisim_wtrans_front_ STEP eq2); eauto.

  Lemma square_wt': square <= wt'.
  Proof.
    apply leq_t.
    intros R x z [y [F B] [F' B']].
    split.
    - cbn; intros.
      edestruct F; eauto.
      edestruct F'; eauto.
    - cbn; intros.
      edestruct B'; eauto.
      edestruct B; eauto.
  Qed.
   *)
  End Weak.
End Bisim.

Notation sb := (Coinduction.lattice.cap ss (comp converse (comp ss converse))).

Notation sbisim := (gfp sb : hrel _ _).
Notation "t ~ u" := (gfp sb t u) (at level 70).
Notation st := (t sb).
Notation sbt := (bt sb).
(** notations  for easing readability in proofs by enhanced coinduction *)
Notation "t [~] u" := (st  _ t u) (at level 79).
Notation "t {~} u" := (sbt _ t u) (at level 79).

(** the symmetrised version, defining weak bisimulations and bisimilarity *)
Notation wb := (Coinduction.lattice.cap ws (comp converse (comp ws converse))).

Notation wbisim := (gfp wb: hrel _ _).
Notation "p ≈ q" := (gfp wb p q) (at level 70).
Notation wt := (coinduction.t wb).
Notation wT := (coinduction.T wb).
Notation wbt := (coinduction.bt wb).
Notation wbT := (coinduction.bT wb).
(** notations  for easing readability in proofs by enhanced coinduction *)
Notation "x [≈] y" := (wt _ x y) (at level 80).
Notation "x {≈} y" := (wbt _ x y) (at level 80).
