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

(* TODO: Decide where to set this *)
Arguments trans : simpl never.

Section StrongBisim.

  Context {E : Type -> Type} {X : Type}.
  Notation S := (ctree E X).

(*|
Strong Bisimulation
-------------------
Relation relaxing [equ] to become insensitive to:
- the amount of _invisible_ choices taken;
- the particular branches taken during (any kind of) choices.
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
The relation itself
|*)
Definition sbisim {E X} := (gfp (@sb E X) : hrel _ _).

Module SBisimNotations.

  Notation "t ~ u" := (sbisim t u) (at level 70).
  Notation st := (t sb).
  Notation sT := (T sb).
  Notation sbt := (bt sb).
  Notation sbT := (bT sb).
  (** notations  for easing readability in proofs by enhanced coinduction *)
  Notation "t [~] u" := (st  _ t u) (at level 79).
  Notation "t {~} u" := (sbt _ t u) (at level 79).
  Notation "t {{~}} u" := (sb _ t u) (at level 79).

End SBisimNotations.

Import SBisimNotations.

Ltac fold_sbisim :=
  repeat
    match goal with
    | h: context[@sb ?E ?X] |- _ => fold (@sbisim E X) in h
    | |- context[@sb ?E ?X]      => fold (@sbisim E X)
    end.

Ltac __coinduction_sbisim R H :=
  unfold sbisim; apply_coinduction; fold_sbisim; intros R H.

Tactic Notation "__step_sbisim" :=
  match goal with
  | |- context[@sbisim ?E ?X] =>
      unfold sbisim;
      step;
      fold (@sbisim E X)
  | |- _ => step
  end.

#[local] Tactic Notation "step" := __step_sbisim.

#[local] Tactic Notation "coinduction" simple_intropattern(R) simple_intropattern(H) :=
  __coinduction_sbisim R H.

Ltac __step_in_sbisim H :=
  match type of H with
  | context [@sbisim ?E ?X] =>
      unfold sbisim in H;
      step in H;
      fold (@sbisim E X) in H
  end.

#[local] Tactic Notation "step" "in" ident(H) := __step_in_sbisim H.

Section sbisim_theory.

	Context {E : Type -> Type} {X : Type}.
  Notation ss := (@ss E X).
  Notation sb := (@sb E X).
  Notation sbisim  := (@sbisim E X).
  Notation st  := (coinduction.t sb).
  Notation sbt := (coinduction.bt sb).
  Notation sT  := (coinduction.T sb).
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
Hence [equ eq] is a included in [sbisim]
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

Ltac __upto_bind_sbisim :=
  match goal with
    |- body (t (@sb ?E ?X)) ?R (CTree.bind (T := ?T) _ _) (CTree.bind (T := ?T) _ _) =>
      apply (ft_t (@bind_ctx_sbisim_t E T X)), in_bind_ctx
  | |- body (bt (@sb ?E ?X)) ?R (CTree.bind (T := ?T) _ _) (CTree.bind (T := ?T) _ _) =>
      apply (fbt_bt (@bind_ctx_sbisim_t E T X)), in_bind_ctx
  end.
Ltac __upto_bind_eq_sbisim :=
  __upto_bind_sbisim; [reflexivity | intros ? ? <-].

Import CTree.
Import CTreeNotations.

(*|
Expliciting the reasoning rule provided by the up-to principles.
|*)
Lemma sbisim_clo_bind (E: Type -> Type) (X Y : Type) :
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
And in particular, we get the proper instance justifying rewriting [~] to the left of a [bind].
|*)
#[global] Instance bind_sbisim_cong :
 forall (E : Type -> Type) (X Y : Type) RR,
   Proper (sbisim ==> pointwise_relation X (st RR) ==> st RR) (@bind E X Y).
Proof.
  repeat red; intros; eapply sbisim_clo_bind; eauto.
Qed.

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
  [etrans |].

Ltac __eplayL_sbisim :=
  match goal with
  | h : @sbisim ?E ?X _ _ |- _ =>
      step in h;
      let Hf := fresh "Hf" in
      destruct h as [Hf _];
      cbn in Hf; edestruct Hf as [? ?TR ?EQ];
      [etrans |]
  end.

Ltac __playR_sbisim H :=
  step in H;
  let Hb := fresh "Hb" in
  destruct H as [_ Hb];
  cbn in Hb; edestruct Hb;
  [etrans |].

Ltac __eplayR_sbisim :=
  match goal with
  | h : @sbisim ?E ?X _ _ |- _ =>
      step in h;
      let Hb := fresh "Hb" in
      destruct h as [Hb _];
      cbn in Hb; edestruct Hb as [? ?TR ?EQ];
      [etrans |]
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

TODO: need to think more about this --- do we want more proof rules?
Do we actually need them on [sb (st R)], or something else?
|*)

Section Proof_Rules.

  Lemma step_sb_ret_gen E X (x y : X) (R : rel _ _) :
    R stuckI stuckI ->
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
   Lemma step_sb_tauV_gen E X (t t' : ctree E X) (R : rel _ _) :
    (Proper (equ eq ==> equ eq ==> impl) R) ->
    (R t t') ->
    sb R (TauV t) (TauV t').
  Proof.
    intros PR EQs.
    split; intros ? ? TR; inv_trans; subst.
    all: cbn; eexists; etrans; rewrite EQ; auto.
  Qed.

  Lemma step_sb_tauV E X (t t' : ctree E X) (R : rel _ _) :
    (st R t t') ->
    sbt R (TauV t) (TauV t').
  Proof.
    apply step_sb_tauV_gen.
    typeclasses eauto.
  Qed.

(*|
When matching visible choices one against another, in general we need to explain how
we map the branches from the left to the branches to the right, and reciprocally.
A useful special case is the one where the arity coincide and we simply use the identity
in both directions. We can in this case have [n] rather than [2n] obligations.
|*)

  Lemma step_sb_choiceV_gen E X n m (k : fin n -> ctree E X) (k' : fin m -> ctree E X) (R : rel _ _) :
    (Proper (equ eq ==> equ eq ==> impl) R) ->
    (forall x, exists y, R (k x) (k' y)) ->
    (forall y, exists x, R (k x) (k' y)) ->
    sb R (ChoiceV n k) (ChoiceV m k').
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

  Lemma step_sb_choiceV E X n m (k : fin n -> ctree E X) (k' : fin m -> ctree E X) (R : rel _ _) :
    (forall x, exists y, st R (k x) (k' y)) ->
    (forall y, exists x, st R (k x) (k' y)) ->
    sbt R (ChoiceV n k) (ChoiceV m k').
  Proof.
    intros EQs1 EQs2.
    apply step_sb_choiceV_gen; auto.
    typeclasses eauto.
  Qed.

  Lemma step_sb_choiceV_id_gen E X n (k k' : fin n -> ctree E X) (R : rel _ _) :
    (Proper (equ eq ==> equ eq ==> impl) R) ->
    (forall x, R (k x) (k' x)) ->
    sb R (ChoiceV n k) (ChoiceV n k').
  Proof.
    intros PROP EQs.
    apply step_sb_choiceV_gen; auto.
    all: intros x; exists x; auto.
  Qed.

  Lemma step_sb_choiceV_id E X n (k k' : fin n -> ctree E X) (R : rel _ _) :
    (forall x, st R (k x) (k' x)) ->
    sbt R (ChoiceV n k) (ChoiceV n k').
  Proof.
    apply step_sb_choiceV_id_gen.
    typeclasses eauto.
  Qed.

(*|
For invisible nodes, the situation is different: we may kill them, but that execution
cannot act as going under the guard.
|*)
  Lemma step_sb_tauI_gen E X (t t' : ctree E X) (R : rel _ _) :
    sb R t t' ->
    sb R (TauI t) (TauI t').
  Proof.
    intros EQ.
    split; intros ? ? TR; inv_trans; subst.
    all: apply EQ in TR as [? ? ?].
    all: eexists; [apply trans_tauI; eauto | eauto].
  Qed.

  Lemma step_sb_tauI E X (t t' : ctree E X) (R : rel _ _) :
    sbt R t t' ->
    sbt R (TauI t) (TauI t').
  Proof.
    apply step_sb_tauI_gen.
  Qed.

  Lemma step_sb_choiceI_gen E X n m (k : fin n -> ctree E X) (k' : fin m -> ctree E X) (R : rel _ _) :
    (forall x, exists y, sb R (k x) (k' y)) ->
    (forall y, exists x, sb R (k x) (k' y)) ->
    sb R (ChoiceI n k) (ChoiceI m k').
  Proof.
    intros EQs1 EQs2.
    split; intros ? ? TR; inv_trans; subst.
    - destruct (EQs1 n0) as [x [F _]]; cbn in F.
      apply F in TR; destruct TR as [u' TR' EQ'].
      eexists.
      eapply trans_choiceI with (x := x); [|reflexivity].
      eauto.
      eauto.
    - destruct (EQs2 m0) as [x [_ B]]; cbn in B.
      apply B in TR; destruct TR as [u' TR' EQ'].
      eexists.
      eapply trans_choiceI with (x := x); [|reflexivity].
      eauto.
      eauto.
  Qed.

  Lemma step_sb_choiceI E X n m (k : fin n -> ctree E X) (k' : fin m -> ctree E X) (R : rel _ _) :
    (forall x, exists y, sbt R (k x) (k' y)) ->
    (forall y, exists x, sbt R (k x) (k' y)) ->
    sbt R (ChoiceI n k) (ChoiceI m k').
  Proof.
    apply step_sb_choiceI_gen.
  Qed.

  Lemma step_sb_choiceI_id_gen {E X} n (k k' : fin n -> ctree E X) (R : rel _ _) :
    (forall x, sb R (k x) (k' x)) ->
    sb R (ChoiceI n k) (ChoiceI n k').
  Proof.
    intros; apply step_sb_choiceI_gen.
    intros x; exists x; apply H.
    intros x; exists x; apply H.
  Qed.

  Lemma step_sb_choiceI_id {E X} n (k k' : fin n -> ctree E X) (R : rel _ _) :
    (forall x, sbt R (k x) (k' x)) ->
    sbt R (ChoiceI n k) (ChoiceI n k').
  Proof.
    apply step_sb_choiceI_id_gen.
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
  Lemma sb_tauI E X : forall (t : ctree E X),
      TauI t ~ t.
  Proof.
    intros t; play.
    - inv_trans.
      etrans.
    - etrans.
  Qed.

 Lemma sb_tauI_l E X : forall (t u : ctree E X),
      t ~ u ->
      TauI t ~ u.
  Proof.
    intros * EQ; now rewrite sb_tauI.
  Qed.

  Lemma sb_tauI_r E X : forall (t u : ctree E X),
      t ~ u ->
      t ~ TauI u.
  Proof.
    intros * EQ; now rewrite sb_tauI.
  Qed.

  Lemma sb_tauI_lr E X : forall (t u : ctree E X),
      t ~ u ->
      TauI t ~ TauI u.
  Proof.
    intros * EQ; now rewrite !sb_tauI.
  Qed.

  Lemma sb_tauV E X : forall (t u : ctree E X),
      t ~ u ->
      TauV t ~ TauV u.
  Proof.
    intros * EQ; step.
    apply step_sb_tauV; auto.
  Qed.

(*|
Choice
|*)
  (* TODO: Double check that this is needed, it should be taus in all contexts I can think of *)
  Lemma sb_choiceI1 E X : forall (k : fin 1 -> ctree E X),
      ChoiceI 1 k ~ k F1.
  Proof.
    intros; step; econstructor.
    - intros ? ? ?. inv H.
      apply Eqdep.EqdepTheory.inj_pair2 in H3; subst.
      dependent destruction x; exists t'; etrans; auto.
      inversion x.
    - intros ? ? ?; cbn.
      etrans.
  Qed.

  Lemma sb_choiceV E X n m (k : fin n -> ctree E X) (k' : fin m -> ctree E X) :
    (forall x, exists y, k x ~ k' y) ->
    (forall y, exists x, k x ~ k' y) ->
    ChoiceV n k ~ ChoiceV m k'.
  Proof.
    intros * EQs1 EQs2; step.
    apply step_sb_choiceV; auto.
  Qed.

  Lemma sb_choiceV_id E X n (k k' : fin n -> ctree E X) :
    (forall x, k x ~ k' x) ->
    ChoiceV n k ~ ChoiceV n k'.
  Proof.
    intros * EQs; step.
    apply step_sb_choiceV_id; auto.
  Qed.

  Lemma sb_choiceI E X n m (k : fin n -> ctree E X) (k' : fin m -> ctree E X) :
    (forall x, exists y, k x ~ k' y) ->
    (forall y, exists x, k x ~ k' y) ->
    ChoiceI n k ~ ChoiceI m k'.
  Proof.
    intros; step.
    eapply step_sb_choiceI; auto.
    intros x; destruct (H x) as (y & EQ).
    exists y; now step in EQ.
    intros y; destruct (H0 y) as (x & EQ).
    exists x; now step in EQ.
  Qed.

  Lemma sb_choiceI_id {E X} n (k k' : fin n -> ctree E X)  :
    (forall x, k x ~ k' x) ->
    ChoiceI n k ~ ChoiceI n k'.
  Proof.
    intros; step.
    apply @step_sb_choiceI_id; intros x.
    specialize (H x).
    now step in H.
  Qed.

  Lemma sb_choiceI_idempotent E X n: forall (k: fin (S n) -> ctree E X) t,
      (forall x, k x ~ t) ->
      ChoiceI (S n) k ~ t.
  Proof.
    intros * EQ.
    rewrite <- sb_tauI with (t:=t).
    apply sb_choiceI; intros; exists F1; apply EQ.
  Qed.

End Sb_Proof_System.

(* TODO: tactics!
   Should it be the same to step at both levels or two different sets?

Ltac bsret  := apply step_sb_ret.
Ltac bsvis  := apply step_sb_vis.
Ltac bstauv := apply step_sb_tauV.
Ltac bsstep := bsret || bsvis || bstauv.

Ltac sret  := apply sb_ret.
Ltac svis  := apply sb_vis.
Ltac stauv := apply sb_tauV.
Ltac sstep := sret || svis || stauv.


 *)

(*|
Sanity checks
=============
- invisible n-ary spins are strongly bisimilar
- non-empty visible n-ary spins are strongly bisimilar
- Binary invisible choice is:
  + associative
  + commutative
  + merges into a ternary invisible choice
  + admits any stuckI computation as a unit

Note: binary visible choice are not associative up-to [sbisim].
They aren't even up-to [wbisim].
|*)

(*|
Note that with visible schedules, nary-spins are equivalent only
if neither are empty, or if both are empty: they match each other's
tau challenge infinitely often.
With invisible schedules, they are always equivalent: neither of them
produce any challenge for the other.
|*)
Lemma spinV_nary_n_m : forall {E R} n m,
    n>0 ->
    m>0 ->
    @spinV_nary E R n ~ spinV_nary m.
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

Lemma spinI_nary_n_m : forall {E R} n m,
    @spinI_nary E R n ~ spinI_nary m.
Proof.
  intros E R.
  coinduction S _; symmetric.
  cbn; intros * TR.
  exfalso; eapply spinI_nary_is_stuck, TR.
Qed.

(*|
ChoiceI2 is associative, commutative, idempotent, merges into ChoiceI3, and admits _a lot_ of units.
|*)
Lemma choiceI2_assoc {E X} : forall (t u v : ctree E X),
	  choiceI2 (choiceI2 t u) v ~ choiceI2 t (choiceI2 u v).
Proof.
  intros.
  play; inv_trans; etrans.
Qed.

Lemma choiceI2_commut {E X} : forall (t u : ctree E X),
	  choiceI2 t u ~ choiceI2 u t.
Proof.
(*|
Note: could use a symmetry argument here as follows to only play one direction of the game.
[coinduction ? _; symmetric.]
but automation just handles it...
|*)
  intros.
  play; inv_trans; etrans.
Qed.

Lemma choiceI2_idem {E X} : forall (t : ctree E X),
	  choiceI2 t t ~ t.
Proof.
  intros.
  play; inv_trans; etrans.
Qed.

Lemma choiceI2_merge {E X} : forall (t u v : ctree E X),
	  choiceI2 (choiceI2 t u) v ~ choiceI3 t u v.
Proof.
  intros.
  play; inv_trans; etrans.
Qed.

Lemma choiceI2_is_stuck {E X} : forall (u v : ctree E X),
    is_stuck u ->
	  choiceI2 u v ~ v.
Proof.
  intros * ST.
  play.
  - inv_trans.
    exfalso; eapply ST, TR. (* automate stuck transition trying to step? *)
    exists t'; auto.             (* automate trivial case *)
  - etrans.
Qed.

Lemma choiceI2_stuckV_l {E X} : forall (t : ctree E X),
	  choiceI2 stuckV t ~ t.
Proof.
  intros; apply choiceI2_is_stuck, stuckV_is_stuck.
Qed.

Lemma choiceI2_stuckI_l {E X} : forall (t : ctree E X),
	  choiceI2 stuckI t ~ t.
Proof.
  intros; apply choiceI2_is_stuck, stuckI_is_stuck.
Qed.

Lemma choiceI2_stuckV_r {E X} : forall (t : ctree E X),
	  choiceI2 t stuckV ~ t.
Proof.
  intros; rewrite choiceI2_commut; apply choiceI2_stuckV_l.
Qed.

Lemma choiceI2_stuckI_r {E X} : forall (t : ctree E X),
	  choiceI2 t stuckI ~ t.
Proof.
  intros; rewrite choiceI2_commut; apply choiceI2_stuckI_l.
Qed.

Lemma choiceI2_spinI_l {E X} : forall (t : ctree E X),
	  choiceI2 spinI t ~ t.
Proof.
  intros; apply choiceI2_is_stuck, spinI_is_stuck.
Qed.

Lemma choiceI2_spinI_r {E X} : forall (t : ctree E X),
	  choiceI2 t spinI ~ t.
Proof.
  intros; rewrite choiceI2_commut; apply choiceI2_is_stuck, spinI_is_stuck.
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

(** For the next few lemmas, we need to know that [X] is inhabited in order to
    take a step *)
Lemma sbisim_vis_inv_type {E R X1 X2}
      (e1 : E X1) (e2 : E X2) (k1 : X1 -> ctree E R) (k2 : X2 -> ctree E R) (x : X1):
  Vis e1 k1 ~ Vis e2 k2 ->
  X1 = X2.
Proof.
  intros.
  eplayL.
  inv TR; auto.
  Unshelve. auto.
Qed.

Lemma sbisim_vis_inv {E R X} (e1 e2 : E X) (k1 k2 : X -> ctree E R) (x : X) :
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

Lemma sbisim_ChoiceV_inv {E R}
      n1 n2 (k1 : fin n1 -> ctree E R) (k2 : fin n2 -> ctree E R) :
  ChoiceV n1 k1 ~ ChoiceV n2 k2 ->
  (forall i1, exists i2, k1 i1 ~ k2 i2).
Proof.
  intros EQ i1.
  eplayL.
  inv_trans.
  eexists; eauto.
Qed.

(*|
Annoying case: [Vis e k ~ ChoiceV n k'] is true if [e : E void] and [n = 0].
We rule out [n = 0] in this definition.
|*)
Definition are_bisim_incompat {E R} (t u : ctree E R) :=
  match observe t, observe u with
  | RetF _, RetF _
  | VisF _ _, VisF _ _
  | ChoiceVF _ _, ChoiceVF _ _
  | ChoiceIF _ _, _
  | _, ChoiceIF _ _ => false
  | ChoiceVF n _, RetF _ => true
  | RetF _,  ChoiceVF n _ => true
  | ChoiceVF n _, VisF _ _ => negb (Nat.eqb n O)
  | VisF _ _, ChoiceVF n _ => negb (Nat.eqb n O)
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
  edestruct Hb; [apply trans_choiceV | inv H; inv IC].
  destruct vis; try now inv IC.
  edestruct Hb; [apply trans_ret | inv H].
  destruct vis; try now inv IC.
  edestruct Hf; [apply trans_choiceV | inv H; inv IC].
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

Lemma sbisim_ret_ChoiceV_inv {E R} (r : R) n (k : fin n -> ctree E R) :
  Ret r ~ ChoiceV n k -> False.
Proof.
  intros * abs; sb_abs abs.
Qed.

(*|
For this to be absurd, we need one of the return types to be inhabited.
|*)
Lemma sbisim_vis_ChoiceV_inv {E R X}
      (e : E X) (k1 : X -> ctree E R) n (k2 : fin n -> ctree E R) :
  n > 0 ->
  Vis e k1 ~ ChoiceV n k2 -> False.
Proof.
  intros * INEQ abs.
  sb_abs abs.
  rewrite Bool.negb_true_iff, PeanoNat.Nat.eqb_neq.
  lia.
Qed.

Lemma sbisim_vis_ChoiceV_inv' {E R X}
      (e : E X) (k1 : X -> ctree E R) n (k2 : fin n -> ctree E R) (x : X) :
  Vis e k1 ~ ChoiceV n k2 -> False.
Proof.
  intro. step in H. destruct H as [Hf Hb]. cbn in *.
  edestruct Hf as [x' Ht Hs]; [apply (@trans_vis _ _ _ _ x _) |]. inv_trans.
Qed.

(*|
Not fond of these two, need to give some thoughts about them
|*)
Lemma sbisim_ret_ChoiceI_inv {E R} (r : R) n (k : fin n -> ctree E R) :
  Ret r ~ ChoiceI n k ->
  exists i, Ret r ~ k i.
Proof.
  intro. step in H. destruct H as [Hf Hb]. cbn in *.
  edestruct Hf as [x Ht Hs]; [apply trans_ret |].
  apply trans_choiceI_inv in Ht.
  destruct Ht as [i Ht]. exists i.
  step. split.
  - repeat intro. inv H. exists x; auto. rewrite <- Hs.
    rewrite ctree_eta. rewrite <- H3. rewrite choiceI0_always_stuck. auto.
  - repeat intro. eapply trans_choiceI in H; eauto. specialize (Hb _ _ H).
    destruct Hb. inv H0. exists stuckI. constructor.
    cbn. rewrite <- H1. symmetry. rewrite ctree_eta .
    rewrite <- H5. rewrite choiceI0_always_stuck. auto.
Qed.

Lemma sbisim_ChoiceI_1_inv {E R} (k : fin 1 -> ctree E R) t x :
  ChoiceI 1 k ~ t ->
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
