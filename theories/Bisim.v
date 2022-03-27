(*|
=========================================
Strong and Weak Bisimulations over ctrees
=========================================
The [equ] relation provides [ctree]s with a suitable notion of equality.
It is however much too fine to properly capture any notion of behavioral
equivalence that we could want to capture over computations modelled as
[ctree]s.
If we draw a parallel with [itree]s, [equ] maps directly to [eq_itree],
while [eutt] was introduced to characterize computations that exhibit the
same external observations, but may disagree finitely on the amount of
internal steps occuring between any two observations.
While the only consideration over [itree]s was to be insensitive to the
amount of fuel needed to run, things are richer over [ctree]s.
We essentially want to capture three intuitive things:
- to be insensitive to the particular branches chosen at non-deterministic
nodes -- in particular, we want [choice t u ~~ choice u t];
- to always be insensitive to how many _invisible_ choice nodes are crawled
through -- they really are a generalization of [Tau] in [itree]s;
- to have the flexibility to be sensible or not to the amount of _visible_
choice nodes encountered -- they really are a generalization of CCS's tau
steps. This last fact, whether we observe or not these nodes, will constrain
the distinction between the weak and strong bisimulations we define.

In contrast with [equ], as well as the relations in [itree]s, we do not
define the functions generating the relations directly structurally on
the trees. Instead, we follow a definition closely following the style
developed for process calculi, essentially stating that diagrams of this
shape can be closed.
t  R  u
|     |
l     l
v     v
t' R  u'
The transition relations that we use to this end are defined in the [Trans]
module:
- strong bisimulation is defined as a symmetric games over [trans];
- weak bisimulation is defined as an asymmetric game in which [trans] get
answered by [wtrans].

.. coq::none
|*)
From Coinduction Require Import
     coinduction rel tactics.

From CTree Require Import
     Utils CTrees Equ Shallow Trans.

From RelationAlgebra Require Import
     monoid
     kat
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

(*|
Strong Bisimulation
-------------------
Relation relaxing [equ] to become insensitive to:
- the amount of _invisible_ choices taken;
- the particular branches taken during (any kind of) choices.
|*)
  Section Strong.

(*|
The function defining strong simulations: [trans] plays must be answered
using [trans].
The [ss] definition stands for [strong simulation]. The bisimulation [sb]
is obtained by expliciting the symmetric aspect of the definition following
Pous'16 in order to be able to exploit symmetry arguments in proofs
(see [square_st] for an illustration).
|*)
    Program Definition ss : mon (S -> S -> Prop) :=
      {| body R t u :=
        forall l t', trans l t t' -> exists2 u', trans l u u' & R t' u'
      |}.
    Next Obligation.
      edestruct H0; eauto.
    Qed.

(*|
Symmetrized version: the other direction of the simulation is obtained as
fun R t u => ss (fun x y => R y x) u t
i.e. fun R t u => ss (converse R) u t
i.e. fun R => converse (ss (converse R))
i.e. comp converse (comp ss converse)
The bisimulation is then obtained by intersecting both relations.
|*)
    Definition sb := (Coinduction.lattice.cap ss (comp converse (comp ss converse))).

    Definition sbisim := (gfp sb : hrel _ _).
    Notation "t ~ u" := (sbisim t u) (at level 70).
    Notation st := (t sb).
    Notation sbt := (bt sb).
(*|
Notations for easing readability in proofs by enhanced coinduction
|*)
    Notation "t [~] u" := (st  _ t u) (at level 79).
    Notation "t {~} u" := (sbt _ t u) (at level 79).

(*|
This is just a hack suggested by Damien Pous to avoid a
universe inconsistency when using both the relational algebra
and coinduction libraries (we fix the type at which we'll use [eq]).
|*)
    Definition seq: relation (ctree E X) := eq.
    Arguments seq/.

(*|
[eq] is a post-fixpoint, thus [const eq] is below [t]
i.e. validity of up-to reflexivity
|*)
    Lemma refl_st: const seq <= st.
    Proof.
      apply leq_t.
      split; intros; cbn in *; subst; eauto.
    Qed.

(*|
[converse] is compatible
i.e. validity of up-to symmetry
|*)
    Lemma converse_st: converse <= st.
    Proof.
      apply invol_t.
    Qed.

(*|
[square] is compatible
 i.e. validity of up-to transivitiy
|*)
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
      - unfold sb; rewrite cap_l at 1.
        intros R x z [y xy yz] l x' xx'.
        destruct (xy _ _ xx') as [y' yy' x'y'].
        destruct (yz _ _ yy') as [z' zz' y'z'].
        exists z'. assumption.
        apply (f_Tf sb).  (* TODO: set of tactics for the companion *)
        eexists; eauto.
    Qed.

(*|
Thus bisimilarity and [t R] are always equivalence relations.
|*)
    #[global] Instance Equivalence_st R: Equivalence (st R).
    Proof. apply Equivalence_t. apply refl_st. apply square_st. apply converse_st. Qed.

    Corollary Equivalence_bisim: Equivalence sbisim.
    Proof. apply Equivalence_st. Qed.

	  #[global] Instance Equivalence_sbt R: Equivalence (sbt R).
	  Proof. apply rel.Equivalence_bt. apply refl_st. apply square_st. apply converse_st. Qed.

    #[global] Instance Equivalence_sT f R: Equivalence ((T sb) f R).
    Proof. apply rel.Equivalence_T. apply refl_st. apply square_st. apply converse_st. Qed.

    #[global] Instance equ_ss_closed_goal {r} : Proper (equ eq ==> equ eq ==> flip impl) (ss r).
    Proof.
      intros t t' tt' u u' uu'; cbn; intros.
      rewrite tt' in H0. apply H in H0 as [? ? ?].
      eexists; eauto. rewrite uu'. eauto.
    Qed.

    #[global] Instance equ_ss_closed_ctx {r} : Proper (equ eq ==> equ eq ==> impl) (ss r).
    Proof.
      intros t t' tt' u u' uu'; cbn; intros.
      rewrite <- tt' in H0. apply H in H0 as [? ? ?].
      eexists; eauto. rewrite <- uu'. eauto.
    Qed.

(*|
[sbism] is closed under [equ]
This proof should be shorter if actually using some braincells I think.
|*)
    #[global] Instance equ_sbisim_closed_goal : Proper (equ eq ==> equ eq ==> flip impl) sbisim.
    Proof.
      intros t t' tt' u u' uu'; cbn.
      revert t t' u u' tt' uu'.
      unfold sbisim; coinduction ? CIH; fold sbisim in *.
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

    #[global] Instance equ_sbisim_closed_ctx : Proper (equ eq ==> equ eq ==> impl) sbisim.
    Proof.
      intros t t' tt' u u' uu'; cbn.
      revert t t' u u' tt' uu'.
      unfold sbisim; coinduction ? CIH; fold sbisim in *.
      intros * eqt equ eqtu.
      step in eqtu.
      split.
      + cbn; intros.
        rewrite <- eqt in H.
        apply eqtu in H as [?u' T eq].
        eexists. rewrite <- equ. apply T.
        eapply CIH; try reflexivity. auto.
      + cbn; intros.
        rewrite <- equ in H.
        apply eqtu in H as [?t' T eq].
        eexists. rewrite <- eqt. apply T.
        eapply CIH; try reflexivity; auto.
    Qed.

    #[global] Instance equ_sbt_closed {r} :
      Proper (equ eq ==> equ eq ==> flip impl)
             (sbt r).
    Proof.
      repeat intro. pose proof (gfp_bt sb r).
      etransitivity; [| etransitivity]; [ | apply H1 | ]; apply H2.
      rewrite H; auto. rewrite H0; auto.
    Qed.

(*|
Hence [equ eq] is a included in [sbisim]
|*)
    #[global] Instance equ_sbisim_subrelation : subrelation (equ eq) sbisim.
    Proof.
      red; intros.
      rewrite H; reflexivity.
    Qed.

    #[global] Instance sbisim_sbisim_closed_goal : Proper (sbisim ==> sbisim ==> flip impl) sbisim.
    Proof.
      repeat intro.
      etransitivity; [etransitivity; eauto | symmetry; eassumption].
    Qed.

    #[global] Instance sbisim_sbisim_closed_ctx : Proper (sbisim ==> sbisim ==> impl) sbisim.
    Proof.
      repeat intro.
      etransitivity; [symmetry; eassumption | etransitivity; eauto].
    Qed.

  End Strong.

  (* Notation sb := (Coinduction.lattice.cap ss (comp converse (comp ss converse))). *)
  (* Notation sbisim := (gfp sb : hrel _ _). *)
  Notation "t ~ u" := (sbisim t u) (at level 70).
  Notation st := (t sb).
  Notation sbt := (bt sb).
  (** notations  for easing readability in proofs by enhanced coinduction *)
  Notation "t [~] u" := (st  _ t u) (at level 79).
  Notation "t {~} u" := (sbt _ t u) (at level 79).

(*|
Weak Bisimulation
-------------------
Relation relaxing [equ] to become insensible to:
- the amount of (any kind of) choices taken;
- the particular branches taken during (any kind of) choices.
|*)

  Section Weak.

(*|
The function defining weak simulations: [trans] plays must be answered
using [wtrans].
The [ws] definition stands for [weak simulation]. The bisimulation [wb]
is once again obtained by expliciting the symmetric aspect of the definition.
|*)
    Program Definition ws: mon (rel S S) :=
      {| body R p q :=
        forall l p', trans l p p' -> exists2 q', wtrans l q q' & R p' q' |}.
    Next Obligation. destruct (H0 _ _ H1). eauto. Qed.


(*|
The bisimulation is obtained by intersecting [ws] with its symmetrized version.
|*)
    Definition wb := (Coinduction.lattice.cap ws (comp converse (comp ws converse))).

    Definition wbisim := (gfp wb: hrel _ _).
    Notation "p ≈ q" := (wbisim p q) (at level 70).
    Notation wt := (coinduction.t wb).
    Notation wT := (coinduction.T wb).
    Notation wbt := (coinduction.bt wb).
    Notation wbT := (coinduction.bT wb).
(*|
Notations  for easing readability in proofs by enhanced coinduction
|*)
    Notation "x [≈] y" := (wt _ x y) (at level 80).
    Notation "x {≈} y" := (wbt _ x y) (at level 80).

(*|
The function defining one-sided expansion (standard notion in process algebra).
This relation echoes [euttge] over [itrees]: the amount of fuel required on either
side of the computation can only decrease from left to right, not the other way around.
We are not interested in this relation by itself, but it is an important proof intermediate.
|*)
    Program Definition es: mon (rel S S) :=
      {| body R p q :=
        forall l p', trans l p p' -> exists2 q', etrans l q q' & R p' q' |}.
    Next Obligation. destruct (H0 _ _ H1). eauto. Qed.

(*|
Elementary properties of [wbisim]
----------------------------------------------
We have in short:
- [ss ≤ es ≤ ws] (direct consequence of transition relations' properties)
- [sbisim] ⊆ [wbisim]
- [equ] ⊆ [wbisim]
- [wbisim] is closed under [equ]
- [wbisim] is closed under [bisim]
- up-to reflexivity
- up-to symmetry
- transitivity (but NOT up-to transitivity)

We naturally also have [equ] ⊆ [sbisim], and hence [equ] ⊆  [wbisim], but we need
to work a bit more to establish it.
It is a consequence more generally of [sbisim] and [wbisim] being closed under [equ]
on both arguments.
We also get [wbisim] closed under [sbism] on both arguments, but need first to
establish [wbisim]'s transitivity for that.
|*)
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

    #[global] Instance sbisim_wbisim_subrelation : subrelation sbisim wbisim.
    Proof.
      apply sbisim_wbisim.
    Qed.

(*|
Since [wt R] contains [wbisim] that contains [sbisim] which is known to be reflexive,
it is reflexive as well
|*)
    #[global] Instance Reflexive_wt R: Reflexive (wt R).
    Proof. intro. apply (gfp_t wb). now apply sbisim_wbisim. Qed.

(*|
[converse] is compatible
|*)
    Lemma converse_wt: converse <= wt.
    Proof. apply invol_t. Qed.

(*|
Hence [wt R] is always symmetric
|*)
    #[global] Instance Symmetric_wt R: Symmetric (wt R).
    Proof. intros ??. apply (ft_t converse_wt). Qed.

(*|
[wbism] is closed under [equ]
|*)
    #[global] Instance equ_wbisim_compat_goal : Proper (equ eq ==> equ eq ==> flip impl) wbisim.
    Proof.
      intros t t' eqt u u' equ; cbn.
      revert t t' u u' eqt equ.
      unfold wbisim; coinduction ? CIH; fold wbisim in *.
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

    #[global] Instance equ_wbisim_compat_ctx : Proper (equ eq ==> equ eq ==> impl) wbisim.
    Proof.
      intros t t' eqt u u' equ; cbn.
      revert t t' u u' eqt equ.
      unfold wbisim; coinduction ? CIH; fold wbisim in *.
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
    Qed.

(*|
Hence [equ eq] is a included in [wbisim]
|*)
    #[global] Instance equ_wbisim_subrelation : subrelation (equ eq) wbisim.
    Proof.
      red; intros.
      rewrite H; reflexivity.
    Qed.

(*|
Transitivity
~~~~~~~~~~~~
As for weak bisimulation on process algebra, [square] is not a valid
enhancing function (an explicit counter example is provided below,
see [not_square_wt]).
Weak bisimilariy is however transitive nonetheless. We can actually
reproduce directly Pous' proof for CCS, the relation between [trans] and [wtrans]
being exactly the same in both cases, even if the underlying objects
and transitions are completely different.
|*)

(*|
Moving to the [srel] world once again to establish algebaric laws based
on operators from the relation algebra library.
|*)
    #[local] Instance equ_wbisim_compat : Proper (equ eq ==> equ eq ==> iff) wbisim.
    Proof.
      split; intros.
      now rewrite <- H, <- H0.
      now rewrite H, H0.
    Qed.

    Definition wbisimT : srel SS SS :=
      {| hrel_of := wbisim : hrel SS SS |}.

(*|
Algebraic reformulation of the right-to-left part of the game

Note: We can express these laws in the setoid world or not.
Unclear if there's a benefit to either at this point, we do everything
on the setoid side.
|*)
    Lemma wbisim_trans_back l: wbisimT ⋅ trans l ≦ wtrans l ⋅ wbisimT.
    Proof.
      intros p q' [q pq qq']. apply (gfp_pfp wb) in pq as [_ pq]. now apply pq.
    Qed.
    Lemma wbisim_trans_back' l: wbisim ⋅ transR l ≦ (wtrans l : hrel _ _) ⋅ wbisim.
    Proof.
      intros p q' [q pq qq']. apply (gfp_pfp wb) in pq as [_ pq]. now apply pq.
    Qed.
    Lemma wbisim_etrans_back l: wbisimT ⋅ etrans l ≦ wtrans l ⋅ wbisimT.
    Proof.
      unfold etrans; destruct l.
      2,3: apply @wbisim_trans_back.
      ra_normalise. rewrite wbisim_trans_back.
      unfold wtrans, etrans. ka.
    Qed.
    Lemma wbisim_taus_back: wbisimT ⋅ (trans tau)^* ≦ (trans tau)^* ⋅ wbisimT.
    Proof.
      rewrite <-str_invol at 2.
      apply str_move_l. rewrite wbisim_trans_back. unfold wtrans, etrans. ka.
    Qed.
    Lemma wbisim_wtrans_back l: wbisimT ⋅ wtrans l ≦ wtrans l ⋅ wbisimT.
    Proof.
      unfold wtrans.
      mrewrite wbisim_taus_back.
      mrewrite wbisim_etrans_back.
      mrewrite wbisim_taus_back.
      unfold wtrans, etrans. ka.
    Qed.

    Lemma cnv_wt R: (wt R: hrel _ _)° ≡ wt R.
    Proof. apply RelationAlgebra.lattice.antisym; intros ???; now apply Symmetric_wt. Qed.
    Lemma cnv_gfp: RelationAlgebra.lattice.weq ((gfp wb: hrel _ _)°) (gfp wb).
    Proof. apply cnv_wt. Qed.
    Lemma cnv_wbisim: wbisimT° ≡ wbisimT.
    Proof. apply cnv_wt. Qed.
    Lemma cnv_wbisim': wbisim° ≡ wbisim.
    Proof. apply cnv_wt. Qed.


(*|
By symmetry, similar results for left-to-right game
|*)
    Lemma wbisim_trans_front l: (trans l)° ⋅ wbisimT ≦ wbisimT ⋅ (wtrans l)°.
    Proof. cnv_switch. rewrite 2cnvdot, cnv_invol, cnv_wbisim. apply wbisim_trans_back. Qed.
    Lemma wbisim_etrans_front l: (etrans l)° ⋅ wbisimT ≦ wbisimT ⋅ (wtrans l)°.
    Proof. cnv_switch. rewrite 2cnvdot, cnv_invol, cnv_wbisim. apply wbisim_etrans_back. Qed.
    Lemma wbisim_wtrans_front l: (wtrans l)° ⋅ wbisimT ≦ wbisimT ⋅ (wtrans l)°.
    Proof. cnv_switch. rewrite 2cnvdot, cnv_invol, cnv_wbisim. apply wbisim_wtrans_back. Qed.

(*|
Explicit, non-algebraic version
|*)
    Lemma wbisim_wtrans_front_ p q l p': wtrans l p p' -> p ≈ q -> exists2 q', p' ≈ q' & wtrans l q q'.
    Proof. intros pp' pq. apply wbisim_wtrans_front. now exists p. Qed.

(*|
Finally, the proof of transitivity
|*)
    #[global] Instance Transitive_wbisim: Transitive wbisim.
    Proof.
      assert (square wbisim <= wbisim) as H.
      apply leq_gfp. apply symmetric_pfp.
      rewrite converse_square.
      apply square. simpl. apply cnv_gfp.
      intros x z [y xy yz] l x' xx'.
      apply (gfp_pfp wb) in xy as [xy _].
      destruct (xy _ _ xx') as [y' yy' x'y'].
      destruct (wbisim_wtrans_front_ _ _ _ _ yy' yz) as [z' y'z' zz'].
      exists z'. assumption. now exists y'.
      intros x y z xy yz. apply H. now exists y.
    Qed.

    #[global] Instance Equivalence_wbisim: Equivalence wbisim.
    Proof.
      split; typeclasses eauto.
    Qed.

(*|
We can now easily derive that [wbisim] is closed under [sbisim]
|*)
    #[global] Instance sbisim_wbisim_closed_goal : Proper (sbisim ==> sbisim ==> flip impl) wbisim.
    Proof.
      repeat intro.
      now rewrite H, H0.
    Qed.

    #[global] Instance sbisim_wbisim_closed_ctx : Proper (sbisim ==> sbisim ==> impl) wbisim.
    Proof.
      repeat intro.
      now rewrite <- H, <- H0.
    Qed.

    #[global] Instance sbisim_st_goal {R} : Proper (sbisim ==> sbisim ==> flip impl) (st R).
    Proof.
      repeat intro.
      now rewrite H, H0. (* This instance is meant to precisely speed up this kind of subsequent rewrites *)
    Qed.

    #[global] Instance sbisim_st_ctx {R} : Proper (sbisim ==> sbisim ==> impl) (st R).
    Proof.
      repeat intro.
      now rewrite <- H, <- H0.
    Qed.

(*|
Visible vs. Invisible Taus
~~~~~~~~~~~~~~~~~~~~~~~~~~
The following two lemmas quickly illustrate how weak and strong
bisimulations relate to visible and invisible choices
|*)

    Lemma TauI_sb : forall t,
        TauI t ~ t.
    Proof.
      intros t; step; split.
      - intros l t' H.
        apply trans_TauI_inv in H.
        eauto.
      - intros l t' H. exists t'.
        apply trans_TauI; auto.
        cbn; reflexivity.
    Qed.

    Lemma TauI_wb : forall t,
        TauI t ≈ t.
    Proof.
      intros. now rewrite TauI_sb.
    Qed.

    Lemma TauV_wb : forall t,
        TauV t ≈ t.
    Proof.
      intros t; step; split.
      - intros l t' H.
        apply trans_TauV_inv in H as [EQ ->].
        exists t'.
        rewrite EQ. apply wnil.
        reflexivity.
      - intros l t' H. exists t'.
        apply wtrans_TauV.
        apply trans_wtrans; auto.
        cbn; reflexivity.
    Qed.

(*|
Disproving the transitivity of [wt R]
-------------------------------------
|*)

    Lemma not_Transitive_wt Z: X -> Z -> E Z -> ~ forall R, Transitive (wt R).
    Proof.
      intros x z e H.
      cut (Vis e (fun _ => Ret x) ≈ Ret x).
      - intros abs. step in abs; destruct abs as [abs _].
        destruct (abs (obs e z) (Ret x)) as [? step EQ].
        constructor; reflexivity.
        apply wtrans_ret_inv in step as [[abs' ?] | [abs' ?]]; inv abs'.
      - rewrite <- TauV_wb.
        rewrite <- (TauV_wb (Ret x)).
        unfold wbisim; coinduction ? CIH; fold wbisim in *.
        split.
        + intros l t' tt'.
          apply trans_TauV_inv in tt' as [EQ ->].
          exists (Ret x); auto.
          apply trans_wtrans; constructor; [exact Fin.F1 | reflexivity].
          apply equ_wbisim_subrelation in EQ.
          rewrite EQ.
          rewrite <- (subrelation_gfp_t _ (TauV_wb _)).
          rewrite <- (subrelation_gfp_t _ (TauV_wb (Ret x))).
          assumption.  (* Here clearly some instances are missing, the rewrite do not work in the other order, and should not require such an explicit low level call *)
        + intros ? ? ?.
          apply trans_TauV_inv in H0 as [EQ ->].
          eexists.
          apply trans_wtrans; constructor; [exact Fin.F1 | reflexivity].
          cbn.
          apply equ_wbisim_subrelation in EQ.
          rewrite <- (subrelation_gfp_t _ (TauV_wb _)).
          symmetry.
          rewrite EQ.
          rewrite <- (subrelation_gfp_t _ (TauV_wb _)).
          symmetry.
          assumption.
    Qed.

    Lemma not_square_wt Z: X -> Z -> E Z -> ~ square <= wt.
    Proof.
      intros x z e H. elim (not_Transitive_wt _ x z e). intro R.
      intros ? y ???. apply (ft_t H). now exists y.
    Qed.

(*|
Remarks and TODOs:
------------------
- Strong and weak bisimulations are only defined as relations enforcing
  equality of returned values. We should generalize this when needed.
- Weak bisimulation can also be defined as the strong game over [wtrans].
  Are we interested in doing so?

|*)

  End Weak.

End Bisim.

(* Notation sb := (Coinduction.lattice.cap ss (comp converse (comp ss converse))). *)

(* Notation sbisim := (gfp sb : hrel _ _). *)
Notation "t ~ u" := (sbisim t u) (at level 70).
Notation st := (t sb).
Notation sT := (T sb).
Notation sbt := (bt sb).
Notation sbT := (bT sb).
(** notations  for easing readability in proofs by enhanced coinduction *)
Notation "t [~] u" := (st  _ t u) (at level 79).
Notation "t {~} u" := (sbt _ t u) (at level 79).

(** the symmetrised version, defining weak bisimulations and bisimilarity *)
(* Notation wb := (Coinduction.lattice.cap ws (comp converse (comp ws converse))). *)

(* Notation wbisim := (gfp wb: hrel _ _). *)
Notation "p ≈ q" := (wbisim p q) (at level 70).
Notation wt := (coinduction.t wb).
Notation wT := (coinduction.T wb).
Notation wbt := (coinduction.bt wb).
Notation wbT := (coinduction.bT wb).
(** notations  for easing readability in proofs by enhanced coinduction *)
Notation "x [≈] y" := (wt _ x y) (at level 80).
Notation "x {≈} y" := (wbt _ x y) (at level 80).

Tactic Notation "coinduction" simple_intropattern(R) simple_intropattern(H) :=
  match goal with
  | |- context [@equ ?E ?R1 ?R2 ?RR _ _] =>
      unfold equ;
      apply_coinduction;
      fold (@equ E R1 R2 RR);
      intros R H
  | |- context [@sbisim ?E ?X _ _] =>
      unfold sbisim;
      apply_coinduction;
      fold (@sbisim E X);
      intros R H
  | |- context [@wbisim ?E ?X _ _] =>
      unfold wbisim;
      apply_coinduction;
      fold (@wbisim E X);
      intros R H
  | |- _ =>
      apply_coinduction;
      intros R H
  end.

#[global] Opaque wtrans.

