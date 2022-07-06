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
nodes -- in particular, we want [br t u ~~ br u t];
- to always be insensitive to how many _invisible_ br nodes are crawled
through -- they really are a generalization of [Tau] in [itree]s;
- to have the flexibility to be sensible or not to the amount of _visible_
br nodes encountered -- they really are a generalization of CCS's tau
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
     CTree
     Eq.Equ
     Eq.Shallow
     Eq.Trans
     Eq.SBisim.

From RelationAlgebra Require Export
     rel srel monoid kat kat_tac rewriting normalisation.

Import CTree.
Import CTreeNotations.
Import EquNotations.
Import SBisimNotations.

(*|
Weak Bisimulation
-------------------
Relation relaxing [equ] to become insensible to:
- the amount of (any kind of) brs taken;
- the particular branches taken during (any kind of) brs.
|*)

Section WeakBisim.

  Context {E : Type -> Type} {X : Type}.
  Notation S := (ctree E X).

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

End WeakBisim.

(*|
The relation itself
|*)
Definition wbisim {E X} := (gfp (@wb E X): hrel _ _).

Module WBisimNotations.

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
  Notation "t {{≈}} u" := (wb _ t u) (at level 79).

End WBisimNotations.

Import WBisimNotations.

Ltac fold_wbisim :=
  repeat
    match goal with
    | h: context[@wb ?E ?X] |- _ => fold (@wbisim E X) in h
    | |- context[@wb ?E ?X]      => fold (@wbisim E X)
    end.

Ltac __coinduction_wbisim R H :=
  unfold wbisim; apply_coinduction; fold_wbisim; intros R H.

Tactic Notation "__step_wbisim" :=
  match goal with
  | |- context[@wbisim ?E ?X] =>
      unfold wbisim;
      step;
      fold (@wbisim E X)
  | |- _ => step
  end.

#[local] Tactic Notation "step" := __step_wbisim.

#[local] Tactic Notation "coinduction" simple_intropattern(R) simple_intropattern(H) :=
  __coinduction_wbisim R H.

Ltac __step_in_wbisim H :=
  match type of H with
  | context [@wbisim ?E ?X] =>
      unfold wbisim in H;
      step in H;
      fold (@wbisim E X) in H
  end.

#[local] Tactic Notation "step" "in" ident(H) := __step_in_wbisim H.

Ltac twplayL_ tac :=
  match goal with
  | h : @wbisim ?E ?X _ _ |- _ =>
      step in h;
      let Hf := fresh "Hf" in
      destruct h as [Hf _];
      cbn in Hf; edestruct Hf as [? ?TR ?EQ];
      [tac | clear Hf]
  end.

Tactic Notation "twplayL" tactic(t) := twplayL_ t.
Ltac wplayL H := twplayL ltac:(apply @H).
Ltac ewplayL := twplayL etrans.

Ltac twplayR_ tac :=
  match goal with
  | h : @wbisim ?E ?X _ _ |- _ =>
      step in h;
      let Hb := fresh "Hb" in
      destruct h as [_ Hb];
      cbn in Hb; edestruct Hb as [? ?TR ?EQ];
      [tac | clear Hb]
  end.

Tactic Notation "twplayR" tactic(t) := twplayR_ t.
Ltac wplayR H := twplayR ltac:(apply @H).
Ltac ewplayR := twplayR etrans.

Section wbisim_theory.

	Context {E : Type -> Type} {X : Type}.
  Notation ws := (@ws E X).
  Notation wb := (@wb E X).
  Notation wbisim  := (@wbisim E X).
  Notation wt  := (coinduction.t wb).
  Notation wbt := (coinduction.bt wb).
  Notation wT  := (coinduction.T wb).

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
    Lemma s_e: @ss E X <= es.
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
    Lemma wbisim_wtrans_front_ p q l p': wtrans l p p' -> p ≈ q -> exists2 q', p' ≈ q' & @wtrans E X l q q'.
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

#[global] Opaque wtrans.

(*|
Weak bisimulation up-to [equ] is valid
|*)
    Lemma equ_clos_wt : @equ_clos E X X <= wt.
    Proof.
      apply Coinduction, by_Symmetry; [apply equ_clos_sym |].
      intros R t u EQ l t1 TR; inv EQ.
      destruct HR as [F _]; cbn in *.
      rewrite Equt in TR.
      apply F in TR.
      destruct TR as [? ? ?].
      eexists.
      rewrite <- Equu; eauto.
      apply (f_Tf wb).
      econstructor; intuition.
      auto.
    Qed.

(*|
We can therefore rewrite [equ] in the middle of bisimulation proofs
|*)
    #[global] Instance equ_clos_wt_proper_goal RR :
      Proper (equ eq ==> equ eq ==> flip impl) (wt RR).
    Proof.
      cbn; unfold Proper, respectful; intros.
      apply (ft_t equ_clos_wt).
      econstructor; [eauto | | symmetry; eauto]; auto.
    Qed.

    #[global] Instance equ_clos_wt_proper_ctx RR :
      Proper (equ eq ==> equ eq ==> impl) (wt RR).
    Proof.
      cbn; unfold Proper, respectful; intros.
      apply (ft_t equ_clos_wt).
      econstructor; [symmetry; eauto | | eauto]; auto.
    Qed.

(*|
Contrary to what happens with [sbisim], weak bisimulation ignores both kinds of taus
|*)

    Lemma guard_wb : forall (t : ctree E X),
        Guard t ≈ t.
    Proof.
      intros. now rewrite sb_guard.
    Qed.

    Lemma step_wb : forall (t : ctree E X),
        Step t ≈ t.
    Proof.
      intros t; step; split.
      - intros l t' H.
        apply trans_step_inv in H as [EQ ->].
        exists t'.
        rewrite EQ. apply wnil.
        reflexivity.
      - intros l t' H. exists t'.
        apply wtrans_step.
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
      - rewrite <- step_wb.
        rewrite <- (step_wb (Ret x)).
        unfold wbisim; coinduction ? CIH; fold wbisim in *.
        split.
        + intros l t' tt'.
          apply trans_step_inv in tt' as [EQ ->].
          exists (Ret x); auto.
          apply trans_wtrans; constructor; [exact Fin.F1 | reflexivity].
          apply equ_wbisim_subrelation in EQ.
          rewrite EQ.
          rewrite <- (subrelation_gfp_t _ (step_wb _)).
          rewrite <- (subrelation_gfp_t _ (step_wb (Ret x))).
          assumption.  (* Here clearly some instances are missing, the rewrite do not work in the other order, and should not require such an explicit low level call *)
        + intros ? ? ?.
          apply trans_step_inv in H0 as [EQ ->].
          eexists.
          apply trans_wtrans; constructor; [exact Fin.F1 | reflexivity].
          cbn.
          apply equ_wbisim_subrelation in EQ.
          rewrite <- (subrelation_gfp_t _ (step_wb _)).
          symmetry.
          rewrite EQ.
          rewrite <- (subrelation_gfp_t _ (step_wb _)).
          symmetry.
          assumption.
    Qed.

    Lemma not_square_wt Z: X -> Z -> E Z -> ~ square <= wt.
    Proof.
      intros x z e H. elim (not_Transitive_wt _ x z e). intro R.
      intros ? y ???. apply (ft_t H). now exists y.
    Qed.

End wbisim_theory.

Lemma wbisim_ret_inv {E R} : forall (x y : R),
    Ret x ≈ (Ret y : ctree E R) ->
    x = y.
Proof.
  intros * EQ.
  ewplayL.
  apply wtrans_case' in TR as [(?v & TR & WTR)|(?v & TR & WTR)].
  inv_trans; auto.
  inv_trans; auto.
Qed.

(*|
Note: with brD2, these relations hold up-to strong bisimulation.
With brS2 however they don't even hold up-to weak bisimulation.
|*)
Lemma spinS_nary_0 : forall {E R}, @spinS_nary E R 0 ≈ spinS_nary 0.
Proof.
  intros E R.
  reflexivity.
Qed.

Ltac wcase :=
  match goal with
    [ h   : hrel_of (wtrans ?l) _ _,
      bis : wbisim _ _
      |- _] =>
      let EQ := fresh "EQ" in
      match l with
      | tau => apply wtrans_case' in h as [EQ|(? & ?TR & ?WTR)];
              [rewrite <- EQ in bis; clear EQ |]
      | _   => apply wtrans_case' in h as [(? & ?TR & ?WTR)|(? & ?TR & ?WTR)]
      end
  end.

#[local] Arguments trans_brS21 [_ _].
#[local] Arguments trans_brS22 [_ _].
#[local] Arguments trans_ret [_ _] _.

(*|
With brS2 however they don't even hold up-to weak bisimulation.
The proof is not interesting, but it would be good to have a
light way to automate it, so it's a decent case study.
|*)
Lemma brS2_not_assoc :
	~ (brS2 (brS2 (Ret 0 : ctree Sum.void1 nat) (Ret 1)) (Ret 2) ≈ brS2 (Ret 0) (brS2 (Ret 1) (Ret 2)))%nat.
Proof.
  intros abs.

  (* init: 012 || 012 *)
  wplayL trans_brS21.

  (* PL  : 01  || 012 *)
  wcase.
  - (* AR:  01  || 012 *)
    wplayR trans_brS22.
    (* PR:  01  ||  12 *)
    wcase.
    + (* AL:  01  ||  12 *)
      wplayR trans_brS22.
      (* PR:  01  ||   2 *)
      wcase.
      * (* AL: 01  ||   2 *)
        wplayR trans_ret.
        (* PR: 01  |2?|   ∅ *)
        wcase.
        (* AL: steps with 2, abs *)
        inv_trans.
        inv_trans.
        (* PR: 0   ||   ∅ *)
        wcase; inv_trans.
        (* PR: 1   ||   ∅ *)
        wcase; inv_trans.
      * inv_trans.
        (* AL: 0  ||   2 *)
        wcase.
        apply wbisim_ret_inv in EQ; inv EQ.
        inv_trans.
        (* AL: 1  ||   2 *)
        wcase.
        apply wbisim_ret_inv in EQ; inv EQ.
        inv_trans.
    + inv_trans.
      * (* AL:  0  ||  12 *)
        wcase.
        wplayL trans_ret.
        wcase; inv_trans.
        wcase; inv_trans.
        wcase; inv_trans.
        inv_trans.
      * (* AL:  1  ||  12 *)
        wcase.
        wplayR trans_brS22.
        wcase.
        apply wbisim_ret_inv in EQ; inv EQ.
        inv_trans.
        inv_trans.
  - inv_trans.
    + wcase.
      * wplayL trans_brS22.
        wcase.
        apply wbisim_ret_inv in EQ; inv EQ.
        inv_trans.
      * inv_trans.
    + wcase.
      wplayL trans_brS21.
      wcase.
      wplayL trans_ret.
      wcase.
      inv_trans.
      inv_trans.
      wcase; inv_trans.
      wcase; inv_trans.
      inv_trans.
      wcase.
      apply wbisim_ret_inv in EQ; inv EQ.
      inv_trans.
      wcase.
      apply wbisim_ret_inv in EQ; inv EQ.
      inv_trans.
      inv_trans.
      wcase.
      wplayL trans_brS21.
      wcase.
      apply wbisim_ret_inv in EQ; inv EQ.
      inv_trans.
      inv_trans.
      wcase.
      wplayL trans_brS21.
      wcase.
      apply wbisim_ret_inv in EQ; inv EQ.
      inv_trans.
      inv_trans.
Qed.
