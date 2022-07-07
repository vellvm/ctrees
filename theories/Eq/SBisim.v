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
From Coq Require Import Lia Basics Fin.

From Coinduction Require Import
     coinduction rel tactics.

From CTree Require Import
     CTree
     Utils
     Eq.Equ
     Eq.Shallow
     Eq.Trans.

From RelationAlgebra Require Export
     rel srel.

Set Implicit Arguments.

Arguments trans : simpl never.

Section StrongBisim.

  Context {E : Type -> Type} {X : Type}.
  Notation S := (ctree E X).

(*|
Strong Bisimulation
-------------------
Relation relaxing [equ] to become insensitive to:
- the amount of _invisible_ brs taken;
- the particular branches taken during (any kind of) brs.
|*)

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

End StrongBisim.

(*|
The relations themselves
|*)
Definition ssim {E X} := (gfp (@ss E X) : hrel _ _).
Definition sbisim {E X} := (gfp (@sb E X) : hrel _ _).

Module SBisimNotations.

  Notation "t ≲ u" := (ssim t u) (at level 70).
  Notation "t ~ u" := (sbisim t u) (at level 70).

  Notation sst := (t ss).
  Notation ssbt := (bt ss).
  Notation ssT := (T ss).
  Notation ssbT := (bT ss).

  Notation st := (t sb).
  Notation sT := (T sb).
  Notation sbt := (bt sb).
  Notation sbT := (bT sb).

  (** notations  for easing readability in proofs by enhanced coinduction *)
  Notation "t [≲] u" := (ss _ t u) (at level 79).
  Notation "t {≲} u" := (sst _ t u) (at level 79).
  Notation "t {{≲}} u" := (ssbt _ t u) (at level 79).

  Notation "t [~] u" := (st  _ t u) (at level 79).
  Notation "t {~} u" := (sbt _ t u) (at level 79).
  Notation "t {{~}} u" := (sb _ t u) (at level 79).

End SBisimNotations.

Import SBisimNotations.

Ltac fold_sbisim :=
  repeat
    match goal with
    | h: context[gfp (@sb ?E ?X)] |- _ => fold (@sbisim E X) in h
    | |- context[gfp (@sb ?E ?X)]      => fold (@sbisim E X)
    | h: context[gfp (@ss ?E ?X)] |- _ => fold (@ssim E X) in h
    | |- context[gfp (@ss ?E ?X)]      => fold (@ssim E X)
    end.

Ltac __coinduction_sbisim R H :=
  (try unfold sbisim);
  (try unfold ssim);
  apply_coinduction; fold_sbisim; intros R H.

Tactic Notation "__step_sbisim" :=
  match goal with
  | |- context[@ssim ?E ?X] =>
      unfold ssim;
      step;
      fold (@ssim E X)
  | |- context[@sbisim ?E ?X] =>
      unfold sbisim;
      step;
      fold (@sbisim E X)
  end.

#[local] Tactic Notation "step" := __step_sbisim || step.

#[local] Tactic Notation "coinduction" simple_intropattern(R) simple_intropattern(H) :=
  __coinduction_sbisim R H.

Ltac __step_in_sbisim H :=
  match type of H with
  | context [@ssim ?E ?X] =>
      unfold ssim in H;
      step in H;
      fold (@ssim E X) in H
  | context [@sbisim ?E ?X] =>
      unfold sbisim in H;
      step in H;
      fold (@sbisim E X) in H
  end.

#[local] Tactic Notation "step" "in" ident(H) := __step_in_sbisim H || step in H.

(*|
A bisimulation trivially gives a simulation.
|*)
Lemma sb_ss : forall {E X} RR (t t' : ctree E X),
  sb RR t t' -> ss RR t t'.
Proof.
  intros. apply H.
Qed.

Lemma sbisim_ssim : forall {E X} (t t' : ctree E X),
  sbisim t t' -> ssim t t'.
Proof.
  intros ? ?.
  coinduction R CH. simpl. intros.
  step in H.
  apply H in H0 as [].
  exists x; auto.
Qed.

Section sbisim_theory.

	Context {E : Type -> Type} {X : Type}.
  Notation ss := (@ss E X).
  Notation sb := (@sb E X).
  Notation sbisim  := (@sbisim E X).
  Notation st  := (coinduction.t sb).
  Notation sbt := (coinduction.bt sb).
  Notation sT  := (coinduction.T sb).
(*|
This is just a hack to avoid a universe inconsistency when
using both the relational algebra and coinduction libraries
(we fix the type at which we'll use [eq]).
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
      apply (f_Tf sb).
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

(*|
Aggressively providing instances for rewriting hopefully faster
[sbisim] under all [sb]-related contexts (consequence of the transitivity
of the companion).
|*)

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

  #[global] Instance sbisim_clos_st_goal RR :
    Proper (sbisim ==> sbisim ==> flip impl) (st RR).
  Proof.
    cbn; intros ? ? eq1 ? ? eq2 H.
    rewrite eq1, eq2.
    auto.
  Qed.

  #[global] Instance sbisim_clos_st_ctx RR :
    Proper (sbisim ==> sbisim ==> impl) (st RR).
  Proof.
    cbn; intros ? ? eq1 ? ? eq2 H.
    rewrite <- eq1, <- eq2.
    auto.
  Qed.

  #[global] Instance sbisim_clos_sT_goal RR f :
    Proper (sbisim ==> sbisim ==> flip impl) (sT f RR).
  Proof.
    cbn; intros ? ? eq1 ? ? eq2 H.
    rewrite eq1, eq2.
    auto.
  Qed.

  #[global] Instance sbisim_clos_sT_ctx RR f :
    Proper (sbisim ==> sbisim ==> impl) (sT f RR).
  Proof.
    cbn; intros ? ? eq1 ? ? eq2 H.
    rewrite <- eq1, <- eq2.
    auto.
  Qed.

(*|
Strong bisimulation up-to [equ] is valid
----------------------------------------
|*)
  Lemma equ_clos_st : equ_clos <= st.
  Proof.
    apply Coinduction, by_Symmetry; [apply equ_clos_sym |].
    intros R t u EQ l t1 TR; inv EQ.
    destruct HR as [F _]; cbn in *.
    rewrite Equt in TR.
    apply F in TR.
    destruct TR as [? ? ?].
    eexists.
    rewrite <- Equu; eauto.
    apply (f_Tf sb).
    econstructor; intuition.
    auto.
  Qed.

(*|
Aggressively providing instances for rewriting [equ] under all [sb]-related
contexts.
|*)
  #[global] Instance equ_clos_st_goal RR :
    Proper (equ eq ==> equ eq ==> flip impl) (st RR).
  Proof.
    cbn; intros ? ? eq1 ? ? eq2 H.
    apply (ft_t equ_clos_st); econstructor; [eauto | | symmetry; eauto]; assumption.
  Qed.

  #[global] Instance equ_clos_st_ctx RR :
    Proper (equ eq ==> equ eq ==> impl) (st RR).
  Proof.
    cbn; intros ? ? eq1 ? ? eq2 H.
    apply (ft_t equ_clos_st); econstructor; [symmetry; eauto | | eauto]; assumption.
  Qed.

  #[global] Instance equ_sbt_closed_goal {r} :
    Proper (equ eq ==> equ eq ==> flip impl) (sbt r).
  Proof.
    repeat intro. pose proof (gfp_bt sb r).
    etransitivity; [| etransitivity]; [ | apply H1 | ]; apply H2.
    rewrite H; auto. rewrite H0; auto.
  Qed.

  #[global] Instance equ_sbt_closed_ctx {r} :
    Proper (equ eq ==> equ eq ==> impl) (sbt r).
  Proof.
    repeat intro. pose proof (gfp_bt sb r).
    etransitivity; [| etransitivity]; [ | apply H1 | ]; apply H2.
    rewrite H; auto. rewrite H0; auto.
  Qed.

  #[global] Instance equ_clos_sT_goal RR f :
    Proper (equ eq ==> equ eq ==> flip impl) (sT f RR).
  Proof.
    cbn; intros ? ? eq1 ? ? eq2 H.
    apply (fT_T equ_clos_st); econstructor; [eauto | | symmetry; eauto]; assumption.
  Qed.

  #[global] Instance equ_clos_sT_ctx RR f :
    Proper (equ eq ==> equ eq ==> impl) (sT f RR).
  Proof.
    cbn; intros ? ? eq1 ? ? eq2 H.
    apply (fT_T equ_clos_st); econstructor; [symmetry; eauto | | eauto]; assumption.
  Qed.

  #[global] Instance equ_clos_sbisim_goal :
    Proper (equ eq ==> equ eq ==> flip impl) sbisim.
  Proof.
    cbn; intros ? ? eq1 ? ? eq2 H.
    apply (ft_t equ_clos_st); econstructor; [eauto | | symmetry; eauto]; assumption.
  Qed.

  #[global] Instance equ_clos_sbisim_ctx :
    Proper (equ eq ==> equ eq ==> impl) sbisim.
  Proof.
    cbn; intros ? ? eq1 ? ? eq2 H.
    apply (ft_t equ_clos_st); econstructor; [symmetry; eauto | | eauto]; assumption.
  Qed.

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
Hence [equ eq] is included in [sbisim]
|*)
  #[global] Instance equ_sbisim_subrelation : subrelation (equ eq) sbisim.
  Proof.
    red; intros.
    rewrite H; reflexivity.
  Qed.

End sbisim_theory.


(*|
Up-to [bind] context bisimulations
----------------------------------
We have proved in the module [Equ] that up-to bind context is
a valid enhancement to prove [equ].
We now prove the same result, but for strong and weak bisimulation.
|*)

Section bind.
  Obligation Tactic := idtac.

  Context {E: Type -> Type} {X Y: Type}.

(*|
Specialization of [bind_ctx] to a function acting with [sbisim] on the bound value,
and with the argument (pointwise) on the continuation.
|*)
  Program Definition bind_ctx_sbisim : mon (rel (ctree E Y) (ctree E Y)) :=
    {|body := fun R => @bind_ctx E X X Y Y sbisim (pointwise eq R) |}.
  Next Obligation.
    intros ?? H. apply leq_bind_ctx. intros ?? H' ?? H''.
    apply in_bind_ctx. apply H'. intros t t' HS. apply H, H'', HS.
  Qed.

(*|
Sufficient condition to exploit symmetry
|*)
  Lemma bind_ctx_sbisim_sym: compat converse bind_ctx_sbisim.
  Proof.
    intro R. simpl. apply leq_bind_ctx. intros. apply in_bind_ctx.
    symmetry; auto.
    intros ? ? ->.
    apply H0; auto.
  Qed.

(*|
The resulting enhancing function gives a valid up-to technique
|*)
  Lemma bind_ctx_sbisim_t : bind_ctx_sbisim <= st.
  Proof.
    apply Coinduction, by_Symmetry.
    apply bind_ctx_sbisim_sym.
    intros R. apply (leq_bind_ctx _).
    intros t1 t2 tt k1 k2 kk.
    step in tt; destruct tt as (F & B); cbn in *.
    cbn in *; intros l u STEP.
    apply trans_bind_inv in STEP as [(H & t' & STEP & EQ) | (v & STEPres & STEP)]; cbn in *.
    - apply F in STEP as [u' STEP EQ'].
      eexists.
      apply trans_bind_l; eauto.
      apply (fT_T equ_clos_st).
      econstructor; [exact EQ | | reflexivity].
      apply (fTf_Tf sb).
      apply in_bind_ctx; auto.
      intros ? ? ->.
      apply (b_T sb).
      apply kk; auto.
    - apply F in STEPres as [u' STEPres EQ'].
      pose proof (trans_val_inv STEPres) as EQ.
      rewrite EQ in STEPres.
      specialize (kk v v eq_refl) as [Fk Bk].
      apply Fk in STEP as [u'' STEP EQ'']; cbn in *.
      eexists.
      eapply trans_bind_r; cbn in *; eauto.
      eapply (id_T sb); cbn; auto.
  Qed.

End bind.

Import CTree.
Import CTreeNotations.

(*|
Expliciting the reasoning rule provided by the up-to principles.
|*)
Lemma st_clo_bind (E: Type -> Type) (X Y : Type) :
	forall (t1 t2 : ctree E X) (k1 k2 : X -> ctree E Y) RR,
		t1 ~ t2 ->
    (forall x, (st RR) (k1 x) (k2 x)) ->
    st RR (t1 >>= k1) (t2 >>= k2)
.
Proof.
  intros.
  apply (ft_t (@bind_ctx_sbisim_t E X Y)).
  apply in_bind_ctx; auto.
  intros ? ? <-; auto.
Qed.

(*|
Specializing the congruence principle for [~]
|*)
Lemma sbisim_clo_bind (E: Type -> Type) (X Y : Type) :
	forall (t1 t2 : ctree E X) (k1 k2 : X -> ctree E Y),
		t1 ~ t2 ->
    (forall x, k1 x ~ k2 x) ->
    t1 >>= k1 ~ t2 >>= k2
.
Proof.
  intros * EQ EQs.
  apply (ft_t (@bind_ctx_sbisim_t E X Y)).
  apply in_bind_ctx; auto.
  intros ? ? <-; auto.
  apply EQs.
Qed.

(*|
And in particular, we get the proper instance justifying rewriting [~] to the left of a [bind].
|*)
#[global] Instance bind_sbisim_cong_gen :
 forall (E : Type -> Type) (X Y : Type) RR,
   Proper (sbisim ==> pointwise_relation X (st RR) ==> st RR) (@bind E X Y).
Proof.
  repeat red; intros; eapply st_clo_bind; eauto.
Qed.

Ltac __upto_bind_sbisim :=
  match goal with
    |- @sbisim _ ?X (CTree.bind (T := ?T) _ _) (CTree.bind (T := ?T) _ _) =>
      apply sbisim_clo_bind
  | |- body (t (@sb ?E ?X)) ?R (CTree.bind (T := ?T) _ _) (CTree.bind (T := ?T) _ _) =>
      apply (ft_t (@bind_ctx_sbisim_t E T X)), in_bind_ctx
  | |- body (bt (@sb ?E ?X)) ?R (CTree.bind (T := ?T) _ _) (CTree.bind (T := ?T) _ _) =>
      apply (fbt_bt (@bind_ctx_sbisim_t E T X)), in_bind_ctx
  end.

Ltac __upto_bind_eq_sbisim :=
  match goal with
  | |- @sbisim _ ?X (CTree.bind (T := ?T) _ _) (CTree.bind (T := ?T) _ _) =>
      __upto_bind_sbisim; [reflexivity | intros ?]
  | _ =>
      __upto_bind_sbisim; [reflexivity | intros ? ? <-]
  end.

Section Ctx.

  Context {E: Type -> Type} {X Y Y': Type}.

  Definition vis_ctx (e : E X)
             (R: rel (X -> ctree E Y) (X -> ctree E Y')):
    rel (ctree E Y) (ctree E Y') :=
    sup_all (fun k => sup (R k) (fun k' => pairH (Vis e k) (vis e k'))).

  Lemma leq_vis_ctx e:
    forall R R', vis_ctx e R <= R' <->
              (forall k k', R k k' -> R' (vis e k) (vis e k')).
  Proof.
    intros.
    unfold vis_ctx.
    setoid_rewrite sup_all_spec.
    setoid_rewrite sup_spec.
    setoid_rewrite <-leq_pairH.
    firstorder.
  Qed.

  Lemma in_vis_ctx e (R :rel _ _) x x' :
    R x x' -> vis_ctx e R (vis e x) (vis e x').
  Proof. intros. now apply ->leq_vis_ctx. Qed.
  #[global] Opaque vis_ctx.

End Ctx.

Section sb_vis_ctx.
  Obligation Tactic := idtac.

  Context {E: Type -> Type} {X Y: Type}.

  Program Definition vis_ctx_sbisim (e : E X): mon (rel (ctree E Y) (ctree E Y)) :=
    {|body := fun R => @vis_ctx E X Y Y e (pointwise eq R) |}.
  Next Obligation.
    intros ??? H. apply leq_vis_ctx. intros ?? H'.
    apply in_vis_ctx. intros ? ? <-. now apply H, H'.
  Qed.

(*|
The resulting enhancing function gives a valid up-to technique
|*)
  Lemma vis_ctx_sbisim_t (e : E X) : vis_ctx_sbisim e <= st.
  Proof.
    apply Coinduction.
    intros R.
    apply leq_vis_ctx.
    intros k k' kk'.
    cbn.
    split; intros ? ? TR; inv_trans; subst.
    all: cbn; eexists; eauto with trans.
    all: rewrite EQ.
    all: specialize (kk' x x eq_refl).
    all: now eapply (b_T sb).
  Qed.

End sb_vis_ctx.
Arguments vis_ctx_sbisim_t {_ _ _} e.

Ltac __upto_vis_sbisim :=
  match goal with
    |- @sbisim _ ?X (Vis ?e _) (Vis ?e _) => apply (ft_t (vis_ctx_sbisim_t (Y := X) e)), in_vis_ctx; intros ? ? <-
  | |- body (t (@sb ?E ?R)) ?RR (Vis ?e _) (Vis ?e _) =>
      apply (ft_t (vis_ctx_sbisim_t e)), in_vis_ctx; intros ? ? <-
  | |- body (bt (@sb ?E ?R)) ?RR (Vis ?e _) (Vis ?e _) =>
      apply (fbt_bt (vis_ctx_sbisim_t e)), in_vis_ctx; intros ? ? <-
  end.

#[local] Tactic Notation "upto_vis" := __upto_vis_sbisim.

Ltac __play_sbisim := step; split; cbn; intros ? ? ?TR.

Ltac __playL_sbisim H :=
  step in H;
  let Hf := fresh "Hf" in
  destruct H as [Hf _];
  cbn in Hf; edestruct Hf as [? ?TR ?EQ];
  clear Hf; [etrans |].

Ltac __eplayL_sbisim :=
  match goal with
  | h : @sbisim ?E ?X _ _ |- _ =>
      __playL_sbisim h
  end.

Ltac __playR_sbisim H :=
  step in H;
  let Hb := fresh "Hb" in
  destruct H as [_ Hb];
  cbn in Hb; edestruct Hb;
  clear Hb; [etrans |].

Ltac __eplayR_sbisim :=
  match goal with
  | h : @sbisim ?E ?X _ _ |- _ =>
      __playR_sbisim h
  end.

#[local] Tactic Notation "play" := __play_sbisim.
#[local] Tactic Notation "playL" "in" ident(H) := __playL_sbisim H.
#[local] Tactic Notation "playR" "in" ident(H) := __playR_sbisim H.
#[local] Tactic Notation "eplayL" := __eplayL_sbisim.
#[local] Tactic Notation "eplayR" := __eplayR_sbisim.

(*|
Proof rules for [~]
-------------------
Naive bisimulations proofs naturally degenerate into exponential proofs,
splitting into two goals at each step.
The following proof rules avoid this issue in particular cases.

Be sure to notice that contrary to equations such that [sb_tauI] or
up-to principles such that [upto_vis], (most of) these rules consume a [sb].
|*)

Section Proof_Rules.

  Lemma step_sb_ret_gen E X (x y : X) (R : rel _ _) :
    R stuckD stuckD ->
    (Proper (equ eq ==> equ eq ==> impl) R) ->
    x = y ->
    sb R (Ret x) (Ret y : ctree E X).
  Proof.
    intros Rstuck PROP <-.
    split; cbn; intros ? ? TR; inv_trans; subst.
    all: cbn; eexists; etrans.
    all: now rewrite EQ.
  Qed.

  Lemma step_sb_ret E X (x y : X) (R : rel _ _) :
    x = y ->
    sbt R (Ret x) (Ret y : ctree E X).
  Proof.
    apply step_sb_ret_gen.
    reflexivity.
    typeclasses eauto.
  Qed.

(*|
The vis nodes are deterministic from the perspective of the labeled transition system,
stepping is hence symmetric and we can just recover the itree-style rule.
|*)
  Lemma step_sb_vis_gen E X Y (e : E X) (k k' : X -> ctree E Y) (R : rel _ _) :
    (Proper (equ eq ==> equ eq ==> impl) R) ->
    (forall x, R (k x) (k' x)) ->
    sb R (Vis e k) (Vis e k').
  Proof.
    intros PR EQs.
    split; intros ? ? TR; inv_trans; subst.
    all: cbn; eexists; etrans; rewrite EQ; auto.
  Qed.

  Lemma step_sb_vis E X Y (e : E X) (k k' : X -> ctree E Y) (R : rel _ _) :
    (forall x, (st R) (k x) (k' x)) ->
    sbt R (Vis e k) (Vis e k').
  Proof.
    intros * EQ.
    apply step_sb_vis_gen; auto.
    typeclasses eauto.
  Qed.

(*|
Same goes for visible tau nodes.
|*)
   Lemma step_sb_step_gen E X (t t' : ctree E X) (R : rel _ _) :
    (Proper (equ eq ==> equ eq ==> impl) R) ->
    (R t t') ->
    sb R (Step t) (Step t').
  Proof.
    intros PR EQs.
    split; intros ? ? TR; inv_trans; subst.
    all: cbn; eexists; etrans; rewrite EQ; auto.
  Qed.

  Lemma step_sb_step E X (t t' : ctree E X) (R : rel _ _) :
    (st R t t') ->
    sbt R (Step t) (Step t').
  Proof.
    apply step_sb_step_gen.
    typeclasses eauto.
  Qed.

(*|
When matching visible brs one against another, in general we need to explain how
we map the branches from the left to the branches to the right, and reciprocally.
A useful special case is the one where the arity coincide and we simply use the identity
in both directions. We can in this case have [n] rather than [2n] obligations.
|*)

  Lemma step_sb_brS_gen E X n m (k : fin n -> ctree E X) (k' : fin m -> ctree E X) (R : rel _ _) :
    (Proper (equ eq ==> equ eq ==> impl) R) ->
    (forall x, exists y, R (k x) (k' y)) ->
    (forall y, exists x, R (k x) (k' y)) ->
    sb R (BrS n k) (BrS m k').
  Proof.
    intros PROP EQs1 EQs2.
    split; intros ? ? TR; inv_trans; subst.
    - destruct (EQs1 n0) as [x HR].
      eexists.
      etrans.
      rewrite EQ; eauto.
    - destruct (EQs2 m0) as [x HR].
      eexists.
      etrans.
      cbn; rewrite EQ; eauto.
  Qed.

  Lemma step_sb_brS E X n m (k : fin n -> ctree E X) (k' : fin m -> ctree E X) (R : rel _ _) :
    (forall x, exists y, st R (k x) (k' y)) ->
    (forall y, exists x, st R (k x) (k' y)) ->
    sbt R (BrS n k) (BrS m k').
  Proof.
    intros EQs1 EQs2.
    apply step_sb_brS_gen; auto.
    typeclasses eauto.
  Qed.

  Lemma step_sb_brS_id_gen E X n (k k' : fin n -> ctree E X) (R : rel _ _) :
    (Proper (equ eq ==> equ eq ==> impl) R) ->
    (forall x, R (k x) (k' x)) ->
    sb R (BrS n k) (BrS n k').
  Proof.
    intros PROP EQs.
    apply step_sb_brS_gen; auto.
    all: intros x; exists x; auto.
  Qed.

  Lemma step_sb_brS_id E X n (k k' : fin n -> ctree E X) (R : rel _ _) :
    (forall x, st R (k x) (k' x)) ->
    sbt R (BrS n k) (BrS n k').
  Proof.
    apply step_sb_brS_id_gen.
    typeclasses eauto.
  Qed.

(*|
For invisible nodes, the situation is different: we may kill them, but that execution
cannot act as going under the guard.
|*)
  Lemma step_sb_guard_gen E X (t t' : ctree E X) (R : rel _ _) :
    sb R t t' ->
    sb R (Guard t) (Guard t').
  Proof.
    intros EQ.
    split; intros ? ? TR; inv_trans; subst.
    all: apply EQ in TR as [? ? ?].
    all: eexists; [apply trans_guard; eauto | eauto].
  Qed.

  Lemma step_sb_guard E X (t t' : ctree E X) (R : rel _ _) :
    sbt R t t' ->
    sbt R (Guard t) (Guard t').
  Proof.
    apply step_sb_guard_gen.
  Qed.

  Lemma step_sb_brD_gen E X n m (k : fin n -> ctree E X) (k' : fin m -> ctree E X) (R : rel _ _) :
    (forall x, exists y, sb R (k x) (k' y)) ->
    (forall y, exists x, sb R (k x) (k' y)) ->
    sb R (BrD n k) (BrD m k').
  Proof.
    intros EQs1 EQs2.
    split; intros ? ? TR; inv_trans; subst.
    - destruct (EQs1 n0) as [x [F _]]; cbn in F.
      apply F in TR; destruct TR as [u' TR' EQ'].
      eexists.
      eapply trans_brD with (x := x); [|reflexivity].
      eauto.
      eauto.
    - destruct (EQs2 m0) as [x [_ B]]; cbn in B.
      apply B in TR; destruct TR as [u' TR' EQ'].
      eexists.
      eapply trans_brD with (x := x); [|reflexivity].
      eauto.
      eauto.
  Qed.

  Lemma step_sb_brD E X n m (k : fin n -> ctree E X) (k' : fin m -> ctree E X) (R : rel _ _) :
    (forall x, exists y, sbt R (k x) (k' y)) ->
    (forall y, exists x, sbt R (k x) (k' y)) ->
    sbt R (BrD n k) (BrD m k').
  Proof.
    apply step_sb_brD_gen.
  Qed.

  Lemma step_sb_brD_id_gen {E X} n (k k' : fin n -> ctree E X) (R : rel _ _) :
    (forall x, sb R (k x) (k' x)) ->
    sb R (BrD n k) (BrD n k').
  Proof.
    intros; apply step_sb_brD_gen.
    intros x; exists x; apply H.
    intros x; exists x; apply H.
  Qed.

  Lemma step_sb_brD_id {E X} n (k k' : fin n -> ctree E X) (R : rel _ _) :
    (forall x, sbt R (k x) (k' x)) ->
    sbt R (BrD n k) (BrD n k').
  Proof.
    apply step_sb_brD_id_gen.
  Qed.

End Proof_Rules.

(*|
Proof system for [~]
--------------------

While the proof rules from the previous section are useful for performing full on
coinductive proofs, lifting these at the level of [sbisim] can allow for completely
avoiding any coinduction when combined with a pre-established equational theory.
|*)
Section Sb_Proof_System.

  Lemma sb_ret E X : forall x y,
      x = y ->
      Ret x ~ (Ret y : ctree E X).
  Proof.
    intros * <-.
    now step.
  Qed.

  Lemma sb_vis E X e Y : forall (k k' : X -> ctree E Y),
      (forall x, k x ~ k' x) ->
      Vis e k ~ Vis e k'.
  Proof.
    intros * EQ.
    upto_vis.
    apply EQ.
  Qed.

(*|
Visible vs. Invisible Taus
~~~~~~~~~~~~~~~~~~~~~~~~~~
Invisible taus can be stripped-out w.r.t. to [sbisim], but not visible ones
|*)
  Lemma sb_guard E X : forall (t : ctree E X),
      Guard t ~ t.
  Proof.
    intros t; play.
    - inv_trans.
      etrans.
    - etrans.
  Qed.

 Lemma sb_guard_l E X : forall (t u : ctree E X),
      t ~ u ->
      Guard t ~ u.
  Proof.
    intros * EQ; now rewrite sb_guard.
  Qed.

  Lemma sb_guard_r E X : forall (t u : ctree E X),
      t ~ u ->
      t ~ Guard u.
  Proof.
    intros * EQ; now rewrite sb_guard.
  Qed.

  Lemma sb_guard_lr E X : forall (t u : ctree E X),
      t ~ u ->
      Guard t ~ Guard u.
  Proof.
    intros * EQ; now rewrite !sb_guard.
  Qed.

  Lemma sb_step E X : forall (t u : ctree E X),
      t ~ u ->
      Step t ~ Step u.
  Proof.
    intros * EQ; step.
    apply step_sb_step; auto.
  Qed.

(*|
Br
|*)
  Lemma sb_brD1 E X : forall (k : fin 1 -> ctree E X),
      BrD 1 k ~ k F1.
  Proof.
    intros; step; econstructor.
    - intros ? ? ?. inv H.
      apply Eqdep.EqdepTheory.inj_pair2 in H3; subst.
      dependent destruction x; exists t'; etrans; auto.
      inversion x.
    - intros ? ? ?; cbn.
      etrans.
  Qed.

  Lemma sb_brS E X n m (k : fin n -> ctree E X) (k' : fin m -> ctree E X) :
    (forall x, exists y, k x ~ k' y) ->
    (forall y, exists x, k x ~ k' y) ->
    BrS n k ~ BrS m k'.
  Proof.
    intros * EQs1 EQs2; step.
    apply step_sb_brS; auto.
  Qed.

  Lemma sb_brS_id E X n (k k' : fin n -> ctree E X) :
    (forall x, k x ~ k' x) ->
    BrS n k ~ BrS n k'.
  Proof.
    intros * EQs; step.
    apply step_sb_brS_id; auto.
  Qed.

  Lemma sb_brD E X n m (k : fin n -> ctree E X) (k' : fin m -> ctree E X) :
    (forall x, exists y, k x ~ k' y) ->
    (forall y, exists x, k x ~ k' y) ->
    BrD n k ~ BrD m k'.
  Proof.
    intros; step.
    eapply step_sb_brD; auto.
    intros x; destruct (H x) as (y & EQ).
    exists y; now step in EQ.
    intros y; destruct (H0 y) as (x & EQ).
    exists x; now step in EQ.
  Qed.

  Lemma sb_brD_id {E X} n (k k' : fin n -> ctree E X)  :
    (forall x, k x ~ k' x) ->
    BrD n k ~ BrD n k'.
  Proof.
    intros; step.
    apply @step_sb_brD_id; intros x.
    specialize (H x).
    now step in H.
  Qed.

  Lemma sb_brD_idempotent E X n: forall (k: fin (S n) -> ctree E X) t,
      (forall x, k x ~ t) ->
      BrD (S n) k ~ t.
  Proof.
    intros * EQ.
    rewrite <- sb_guard with (t:=t).
    apply sb_brD; intros; exists F1; apply EQ.
  Qed.

End Sb_Proof_System.

(*|
Sanity checks
=============
- invisible n-ary spins are strongly bisimilar
- non-empty visible n-ary spins are strongly bisimilar
- Binary invisible br is:
  + associative
  + commutative
  + merges into a ternary invisible br
  + admits any stuckD computation as a unit

Note: binary visible br are not associative up-to [sbisim].
They aren't even up-to [wbisim].
|*)

(*|
Note that with visible schedules, nary-spins are equivalent only
if neither are empty, or if both are empty: they match each other's
tau challenge infinitely often.
With invisible schedules, they are always equivalent: neither of them
produce any challenge for the other.
|*)
Lemma spinS_nary_n_m : forall {E R} n m,
    n>0 ->
    m>0 ->
    @spinS_nary E R n ~ spinS_nary m.
Proof.
  intros E R.
  coinduction S CIH; symmetric.
  intros * ? ? l p' TR.
  destruct m as [|m]; [lia |].
  rewrite ctree_eta in TR; cbn in TR.
  inv_trans.
  subst.
  eexists.
  rewrite ctree_eta; cbn.
  econstructor. exact Fin.F1.
  reflexivity.
  rewrite EQ; eauto.
Qed.

Lemma spinD_nary_n_m : forall {E R} n m,
    @spinD_nary E R n ~ spinD_nary m.
Proof.
  intros E R.
  coinduction S _; symmetric.
  cbn; intros * TR.
  exfalso; eapply spinD_nary_is_stuck, TR.
Qed.

(*|
BrD2 is associative, commutative, idempotent, merges into BrD3, and admits _a lot_ of units.
|*)
Lemma brD2_assoc {E X} : forall (t u v : ctree E X),
	  brD2 (brD2 t u) v ~ brD2 t (brD2 u v).
Proof.
  intros.
  play; inv_trans; etrans.
Qed.

Lemma brD2_commut {E X} : forall (t u : ctree E X),
	  brD2 t u ~ brD2 u t.
Proof.
(*|
Note: could use a symmetry argument here as follows to only play one direction of the game.
[coinduction ? _; symmetric.]
but automation just handles it...
|*)
  intros.
  play; inv_trans; etrans.
Qed.

Lemma brD2_idem {E X} : forall (t : ctree E X),
	  brD2 t t ~ t.
Proof.
  intros.
  play; inv_trans; etrans.
Qed.

Lemma brD2_merge {E X} : forall (t u v : ctree E X),
	  brD2 (brD2 t u) v ~ brD3 t u v.
Proof.
  intros.
  play; inv_trans; etrans.
Qed.

Lemma brD2_is_stuck {E X} : forall (u v : ctree E X),
    is_stuck u ->
	  brD2 u v ~ v.
Proof.
  intros * ST.
  play.
  - inv_trans.
    exfalso; eapply ST, TR.
    exists t'; auto.
  - etrans.
Qed.

Lemma brD2_stuckS_l {E X} : forall (t : ctree E X),
	  brD2 stuckS t ~ t.
Proof.
  intros; apply brD2_is_stuck, stuckS_is_stuck.
Qed.

Lemma brD2_stuckD_l {E X} : forall (t : ctree E X),
	  brD2 stuckD t ~ t.
Proof.
  intros; apply brD2_is_stuck, stuckD_is_stuck.
Qed.

Lemma brD2_stuckS_r {E X} : forall (t : ctree E X),
	  brD2 t stuckS ~ t.
Proof.
  intros; rewrite brD2_commut; apply brD2_stuckS_l.
Qed.

Lemma brD2_stuckD_r {E X} : forall (t : ctree E X),
	  brD2 t stuckD ~ t.
Proof.
  intros; rewrite brD2_commut; apply brD2_stuckD_l.
Qed.

Lemma brD2_spinD_l {E X} : forall (t : ctree E X),
	  brD2 spinD t ~ t.
Proof.
  intros; apply brD2_is_stuck, spinD_is_stuck.
Qed.

Lemma brD2_spinD_r {E X} : forall (t : ctree E X),
	  brD2 t spinD ~ t.
Proof.
  intros; rewrite brD2_commut; apply brD2_is_stuck, spinD_is_stuck.
Qed.

(*|
BrS2 is commutative and "almost" idempotent
|*)
Lemma brS2_commut {E X} : forall (t u : ctree E X),
	  brS2 t u ~ brS2 u t.
Proof.
  intros.
  play; inv_trans; subst.
  all:eexists; [| rewrite EQ; reflexivity]; etrans.
Qed.

Lemma brS2_idem {E X} : forall (t : ctree E X),
	  brS2 t t ~ Step t.
Proof.
  intros.
  play; inv_trans; subst.
  all:eexists; [| rewrite EQ; reflexivity]; etrans.
Qed.

(*|
Inversion principles
--------------------
|*)
Lemma sbisim_ret_inv {E R} (r1 r2 : R) :
  (Ret r1 : ctree E R) ~ Ret r2 ->
  r1 = r2.
Proof.
  intro.
  eplayL.
  now inv_trans.
Qed.

(*|
For the next few lemmas, we need to know that [X] is inhabited in order to
take a step
|*)
Lemma sbisim_vis_invT {E R X1 X2}
      (e1 : E X1) (e2 : E X2) (k1 : X1 -> ctree E R) (k2 : X2 -> ctree E R) (x : X1):
  Vis e1 k1 ~ Vis e2 k2 ->
  X1 = X2.
Proof.
  intros.
  eplayL.
  inv TR; auto.
  Unshelve. auto.
Qed.

Lemma sbisim_vis_invE {E R X} (e1 e2 : E X) (k1 k2 : X -> ctree E R) (x : X) :
  Vis e1 k1 ~ Vis e2 k2 ->
  e1 = e2 /\ forall x, k1 x ~ k2 x.
Proof.
  intros.
  split.
  - eplayL.
    etrans.
    inv_trans; eauto.
  - intros.
    clear x.
    eplayL.
    inv_trans.
    subst. eauto.
    Unshelve. auto.
Qed.

Lemma sbisim_BrS_inv {E R}
      n1 n2 (k1 : fin n1 -> ctree E R) (k2 : fin n2 -> ctree E R) :
  BrS n1 k1 ~ BrS n2 k2 ->
  (forall i1, exists i2, k1 i1 ~ k2 i2) /\ (forall i2, exists i1, k1 i1 ~ k2 i2).
Proof.
  intros EQ; split.
  - intros i1.
    eplayL.
    inv_trans.
    eexists; eauto.
  - intros i2.
    eplayR.
    inv_trans.
    eexists; eauto.
Qed.

(*|
Annoying case: [Vis e k ~ BrS n k'] is true if [e : E void] and [n = 0].
We rule out [n = 0] in this definition.
|*)
Definition are_bisim_incompat {E R} (t u : ctree E R) :=
  match observe t, observe u with
  | RetF _, RetF _
  | VisF _ _, VisF _ _
  | BrSF _ _, BrSF _ _
  | BrDF _ _, _
  | _, BrDF _ _ => false
  | BrSF n _, RetF _ => true
  | RetF _,  BrSF n _ => true
  | BrSF n _, VisF _ _ => negb (Nat.eqb n O)
  | VisF _ _, BrSF n _ => negb (Nat.eqb n O)
  | _, _ => true
  end.

Lemma sbisim_absurd {E R} (t u : ctree E R) :
  are_bisim_incompat t u = true ->
  t ~ u ->
  False.
Proof.
  intros * IC EQ.
  unfold are_bisim_incompat in IC.
  step in EQ; destruct EQ as [Hf Hb]; cbn in Hf,Hb.
  unfold trans, transR in Hf,Hb; cbn in Hf,Hb.
  desobs t; desobs u; try now inv IC.
  edestruct Hf; [apply trans_ret | inv H].
  destruct vis; try now inv IC.
  edestruct Hf; [apply trans_ret | inv H].
  edestruct Hb; [apply trans_ret | inv H].
  destruct vis; try now inv IC.
  edestruct Hb; [apply trans_brS | inv H; inv IC].
  destruct vis; try now inv IC.
  edestruct Hb; [apply trans_ret | inv H].
  destruct vis; try now inv IC.
  edestruct Hf; [apply trans_brS | inv H; inv IC].
  destruct vis; try now inv IC.
  destruct vis0; try now inv IC.
  Unshelve.
  all:destruct n; [inv IC | exact Fin.F1].
Qed.

Ltac sb_abs h :=
  exfalso; eapply sbisim_absurd; [| eassumption]; cbn; try reflexivity.

Lemma sbisim_ret_vis_inv {E R X} (r : R) (e : E X) k :
  Ret r ~ Vis e k -> False.
Proof.
  intros * abs; sb_abs abs.
Qed.

Lemma sbisim_ret_BrS_inv {E R} (r : R) n (k : fin n -> ctree E R) :
  Ret r ~ BrS n k -> False.
Proof.
  intros * abs; sb_abs abs.
Qed.

(*|
For this to be absurd, we need one of the return types to be inhabited.
|*)
Lemma sbisim_vis_BrS_inv {E R X}
      (e : E X) (k1 : X -> ctree E R) n (k2 : fin n -> ctree E R) :
  n > 0 ->
  Vis e k1 ~ BrS n k2 -> False.
Proof.
  intros * INEQ abs.
  sb_abs abs.
  rewrite Bool.negb_true_iff, PeanoNat.Nat.eqb_neq.
  lia.
Qed.

Lemma sbisim_vis_BrS_inv' {E R X}
      (e : E X) (k1 : X -> ctree E R) n (k2 : fin n -> ctree E R) (x : X) :
  Vis e k1 ~ BrS n k2 -> False.
Proof.
  intro. step in H. destruct H as [Hf Hb]. cbn in *.
  edestruct Hf as [x' Ht Hs]; [apply (@trans_vis _ _ _ _ x _) |]. inv_trans.
Qed.

Lemma sbisim_ret_BrD_inv {E R} (r : R) n (k : fin n -> ctree E R) :
  Ret r ~ BrD n k ->
  exists i, Ret r ~ k i.
Proof.
  intro. step in H. destruct H as [Hf Hb]. cbn in *.
  edestruct Hf as [x Ht Hs]; [apply trans_ret |].
  apply trans_brD_inv in Ht.
  destruct Ht as [i Ht]. exists i.
  step. split.
  - repeat intro. inv H. exists x; auto. rewrite <- Hs.
    rewrite ctree_eta. rewrite <- H3. rewrite brD0_always_stuck. auto.
  - repeat intro. eapply trans_brD in H; eauto. specialize (Hb _ _ H).
    destruct Hb. inv H0. exists stuckD. constructor.
    cbn. rewrite <- H1. symmetry. rewrite ctree_eta .
    rewrite <- H5. rewrite brD0_always_stuck. auto.
Qed.

Lemma sbisim_BrD_1_inv {E R} (k : fin 1 -> ctree E R) t x :
  BrD 1 k ~ t ->
  k x ~ t.
Proof.
  intro. step in H. step. destruct H. cbn in *. split; repeat intro.
  - apply H. econstructor; apply H1.
  - edestruct H0. apply H1. exists x0; auto.
    inv H2. apply Eqdep.EqdepTheory.inj_pair2 in H7. subst.
    assert (x = x1).
    {
      clear H H0 H1 H3 H8 l t' x0 t k E R.
      remember 1%nat.
      destruct x.
      - dependent destruction x1; auto.
        inv Heqn. inv x1.
      - inv Heqn. inv x.
    }
    subst. auto.
Qed.
