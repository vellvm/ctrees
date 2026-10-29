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
From Coinduction Require Import all.

From ITree Require Import Core.Subevent.

From CTree Require Import
     CTree
     Eq.Equ
     Eq.Shallow
     Eq.Trans
     Eq.SSim
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

  Context {E C : Type -> Type} {X : Type}.
  Notation S := (Trans.S E C X).

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
Definition wbisim {E C X} := (gfp (@wb E C X): hrel _ _).

Module WBisimNotations.

  Notation "p ≈ q" := (wbisim p q) (at level 70).
  (*|
    Notations  for easing readability in proofs by enhanced coinduction
    |*)
  Notation "t {{≈}} u" := (wb _ t u) (at level 79).

End WBisimNotations.

Import WBisimNotations.

Ltac fold_wbisim :=
  repeat
    match goal with
    | h: context[@wb ?E ?C ?X] |- _ => fold (@wbisim E C X) in h
    | |- context[@wb ?E ?C ?X]      => fold (@wbisim E C X)
    end.

Tactic Notation "__coinduction_wbisim" simple_intropattern(r) simple_intropattern(cih) :=
  first [unfold wbisim at 4 | unfold wbisim at 3 | unfold wbisim at 2 | unfold wbisim at 1]; coinduction r cih.
#[local] Tactic Notation "coinduction" simple_intropattern(r) simple_intropattern(cih) :=
  __coinduction_wbisim r cih.

Tactic Notation "__step_wbisim" :=
  match goal with
  | |- context[@wbisim ?E ?C ?X ] =>
      unfold wbisim;
      step;
      fold (@wbisim E C X)
  | |- _ => step
  end.

#[local] Tactic Notation "step" := __step_wbisim.

#[local] Tactic Notation "coinduction" simple_intropattern(R) simple_intropattern(H) :=
  __coinduction_wbisim R H.

Ltac __step_in_wbisim H :=
  match type of H with
  | context [@wbisim ?E ?C ?X ] =>
      unfold wbisim in H;
      step in H;
      fold (@wbisim E C X) in H
  end.

#[local] Tactic Notation "step" "in" ident(H) := __step_in_wbisim H.

Ltac twplayL_ tac :=
  match goal with
  | h : @wbisim ?E ?C ?X _ _ |- _ =>
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
  | h : @wbisim ?E ?F ?C ?D ?X ?Y _ ?L |- _ =>
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

  Context {E C : Type -> Type} {X : Type}.
  Notation ws := (@ws E C X).
  Notation wb := (@wb E C X).
  Notation wbisim  := (@wbisim E C X).

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
  Lemma s_e: @ss E E C C X X Leq <= es.
  Proof.
    intros R p q H l p' pp'. destruct (H _ _ pp') as (l' & q' & TR & HR & HL).
    apply Leq_eq in HL. subst l'.
    exists q'; eauto using trans_etrans_.
  Qed.

  Lemma e_w: es <= ws.
  Proof. intros R p q H l p' pp'. destruct (H _ _ pp'). eauto using etrans_wtrans_. Qed.

  Lemma s_w: ss Leq <= ws.
  Proof. rewrite s_e. apply e_w. Qed.

  Corollary sbisim_wbisim: sbisim Leq <= wbisim.
  Proof.
    apply gfp_leq.
    intros r x y [F B].
    split.
    - intros l x' TR.
      apply F in TR as (l' & y' & TR & HR & HL). simpL.
      econstructor; eauto.
      now apply trans_wtrans.
    - intros l x' TR.
      apply B in TR as (l' & y' & TR & HR & HL). simpL.
      econstructor; eauto.
      now apply trans_wtrans.
  Qed.

  #[global] Instance sbisim_wbisim_subrelation : subrelation (sbisim Leq) wbisim.
  Proof.
    apply sbisim_wbisim.
  Qed.

(*|
Since [wt R] contains [wbisim] that contains [sbisim] which is known to be reflexive,
it is reflexive as well
|*)
  #[global] Instance refl_t {c: Chain wb}: Reflexive (elem c).
  Proof.
    intro. apply (gfp_chain c). now apply sbisim_wbisim.
  Qed.

(*|
[converse] is compatible
|*)
  #[global] Instance sym_t {c: Chain wb}: Symmetric (elem c).
  Proof. apply Symmetric_symchain. Qed.

(*|
[wbism] is closed under [equ]
|*)
    #[global] Instance equ_wbisim_compat_goal : Proper (Seq ==> Seq ==> flip impl) wbisim.
    Proof.
      intros t t' eqt u u' equ; cbn.
      revert t t' u u' eqt equ.
      coinduction r CIH; fold wbisim in *.
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

    #[global] Instance equ_wbisim_compat_ctx : Proper (Seq ==> Seq ==> impl) wbisim.
    Proof.
      intros t t' eqt u u' equ; cbn.
      revert t t' u u' eqt equ.
      coinduction r CIH; fold wbisim in *.
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
    #[global] Instance equ_wbisim_subrelation : subrelation Seq wbisim.
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
    #[local] Instance equ_wbisim_compat : Proper (Seq ==> Seq ==> iff) wbisim.
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
      intros p q' [q pq qq'].
      apply (gfp_pfp wb) in pq as [_ pq].
      now apply pq.
    Qed.
    Lemma wbisim_etrans_back l: wbisimT ⋅ etrans l ≦ wtrans l ⋅ wbisimT.
    Proof.
      unfold etrans; destruct l.
      2,3,4: apply @wbisim_trans_back.
      ra_normalise. rewrite wbisim_trans_back.
      unfold wtrans, etrans. ka.
    Qed.
    Lemma wbisim_τs_back: wbisimT ⋅ (trans τ)^* ≦ (trans τ)^* ⋅ wbisimT.
    Proof.
      rewrite <-str_invol at 2.
      apply str_move_l. rewrite wbisim_trans_back. unfold wtrans, etrans. ka.
    Qed.
    Lemma wbisim_wtrans_back l: wbisimT ⋅ wtrans l ≦ wtrans l ⋅ wbisimT.
    Proof.
      unfold wtrans.
      mrewrite wbisim_τs_back.
      mrewrite wbisim_etrans_back.
      mrewrite wbisim_τs_back.
      unfold wtrans, etrans. ka.
    Qed.

    Lemma cnv_wt (R : Chain wb) : (elem R: hrel _ _)° ≡ elem R.
    Proof. apply RelationAlgebra.lattice.antisym; intros ???; apply sym_t,H. Qed.
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
    Lemma wbisim_wtrans_front_ p q l p': wtrans l p p' -> p ≈ q -> exists2 q', p' ≈ q' & @wtrans E C X l q q'.
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
    #[global] Instance sbisim_wbisim_closed_goal :
      Proper (sbisim Leq ==> sbisim Leq ==> flip impl) wbisim.
    Proof.
      repeat intro.
      now rewrite H, H0.
    Qed.

    #[global] Instance sbisim_wbisim_closed_ctx :
      Proper (sbisim Leq ==> sbisim Leq ==> impl) wbisim.
    Proof.
      repeat intro.
      now rewrite <- H, <- H0.
    Qed.

#[global] Opaque wtrans.

#[global] Instance seq_clos_wt_proper_goal (r : Chain wb) :
      Proper (Seq ==> Seq ==> flip impl) (elem r).
    Proof.
      apply tower.
      - intros ? INC t t' HP1 ? ? HP2 ?? HP3.
        red. eapply INC; eauto.
        apply leq_infx in HP3. now apply HP3.
      - intros ? INC t t' EQt u u' EQu [HF HB]; split.
        + intros l v TR. rewrite EQt in TR. apply HF in TR as [w TR HR].
          exists w; [now rewrite EQu | exact HR].
        + intros l v TR. rewrite EQu in TR. apply HB in TR as [w TR HR].
          exists w; [now rewrite EQt | exact HR].
    Qed.

    #[global] Instance seq_clos_wt_proper_ctx (r : Chain wb) :
      Proper (Seq ==> Seq ==> impl) (elem r).
    Proof.
      intros t t' EQt u u' EQu H. eapply seq_clos_wt_proper_goal; [symmetry; exact EQt | symmetry; exact EQu | exact H].
    Qed.

(*|
Contrary to what happens with [sbisim], weak bisimulation ignores both kinds of τs
|*)
    Lemma guard_wb : forall (t : ctree E C X),
        Guard t ≈ t.
    Proof.
      intros. apply sbisim_wbisim. apply sbisim_guard.
    Qed.

    Lemma step_wb : forall (t : ctree E C X),
        Step t ≈ t.
    Proof.
      intros t; step; split.
      - intros l t' H.
        apply trans_step_inv' in H as [EQ ->].
        exists t'; [| reflexivity].
        rewrite EQ. apply wnil.
      - intros l t' H. exists t'; [| cbn; reflexivity].
        eapply wcons; [apply trans_step | apply trans_wtrans; exact H].
    Qed.

(*|
Disproving the transitivity of [wt R]
-------------------------------------
|*)

    Lemma not_Transitive_wt Z: X -> Z -> E Z -> ~ forall (R : Chain wb), Transitive (elem R).
    Proof.
      intros x z e H.
      cut (Vis e (fun _ => Ret x) ≈ (Ret x : ctree E C X)).
      - intros abs. step in abs; destruct abs as [abs _].
        destruct (abs (ask e) (β e (fun _ => Ret x))) as [? step EQ].
        econstructor; reflexivity.
        destruct step as [? [? s1 s2] s3].
        apply trans_τ_str_ret_inv' in s1. rewrite s1 in s2. unfold etrans in s2. now apply trans_ret_inv' in s2 as [_ ?].
      - coinduction r CIH; fold wbisim in *.
        rewrite <- step_wb.
        symmetry; rewrite <- step_wb; symmetry.
        split.
        + intros l t' tt'.
          apply trans_step_inv' in tt' as [EQ ->].
          exists (α Ret x).
          apply trans_wtrans; apply trans_step.
          now rewrite EQ.
        + intros l t' tt'.
          apply trans_step_inv' in tt' as [EQ ->].
          exists (α Vis e (fun _ => Ret x)).
          apply trans_wtrans; apply trans_step.
          cbn. now rewrite EQ.
    Qed.

End wbisim_theory.

Import CoindNotations.

Lemma step_wb_brS {E B X Y} {R : Chain (@wb E B X)} :
  forall (b c : B Y) (k k' : Y -> ctree E B X),
  (forall x, ` R (k x) (k' x)) ->
  wb `R (BrS b k) (BrS c k').
Proof.
  symmetric using idtac.
  { intros. apply H. intros. symmetry. apply H0. }
  intros ** ???. inv_trans.
  exists (α k' n).
  - apply trans_wtrans. apply trans_brS.
  - rewrite EQ. apply H.
Qed.

Lemma wb_step_inv {E C X}
  {R : Chain (@wb E C X)} :
  forall (t u : ctree E C X),
    wb `R (Step t) (Step u) ->
    `R t u.
Proof.
  intros ?? STEP. destruct STEP as [STEP STEPb].
  specialize (STEP τ t ltac:(etrans)). destruct STEP as [u' STEP EQ].
  apply wtrans_τ in STEP. destruct STEP as (n & STEP).
Abort.

Lemma bind_chain_gen {E C X X'}
  {R : Chain (@wb E C X')} :
  forall (t u : ctree E C X) (k k' : X -> ctree E C X'),
    wbisim t u ->
    (forall x, ` R (k x) (k' x)) ->
    ` R (bind t (fun x => Step (k x))) (bind u (fun x => Step (k' x))).
Proof.
Admitted.

Lemma wbisim_ret_inv {E C R} `{B0 -< C} : forall (x y : R),
    Ret x ≈ (Ret y : ctree E C R) ->
    x = y.
Proof.
  intros * EQ.
  ewplayL.
  destruct TR as [? [? s1 s2] s3].
  apply trans_τ_str_ret_inv' in s1. rewrite s1 in s2. unfold etrans in s2.
  apply trans_ret_inv' in s2 as [_ HL]. now apply val_eq_inv in HL.
Qed.

(*|
Note: with brD2, these relations hold up-to strong bisimulation.
With brS2 however they don't even hold up-to weak bisimulation.
|*)
(*
Lemma spinS_nary_0 : forall {E R}, @spinS_nary E R 0 ≈ spinS_nary 0.
Proof.
  intros E R.
  reflexivity.
Qed.*)

#[local] Arguments trans_brS21 [_ _].
#[local] Arguments trans_brS22 [_ _].
#[local] Arguments trans_ret [_ _] _.


(*|
With brS2 however they don't even hold up-to weak bisimulation.
The proof is not interesting, but it would be good to have a
light way to automate it, so it's a decent case study.
|*)
(*
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
Qed.*)
