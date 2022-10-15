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
From Coq Require Import
     Lia
     Basics
     Fin
     RelationClasses
     Program.Equality
     Logic.Eqdep.

From Coinduction Require Import
     coinduction rel tactics.

From ITree Require Import Core.Subevent.

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

(*|
Strong Bisimulation
-------------------
Relation relaxing [equ] to become insensitive to:
- the amount of _invisible_ brs taken;
- the particular branches taken during (any kind of) brs.
|*)

Section StrongSim.
(*|
The function defining strong simulations: [trans] plays must be answered
using [trans].
The [ss0] definition stands for [strong simulation]. The bisimulation [sb]
is obtained by expliciting the symmetric aspect of the definition following
Pous'16 in order to be able to exploit symmetry arguments in proofs
(see [square_st] for an illustration).
|*)
  Program Definition ss0 {E F C D : Type -> Type} {X Y : Type}
    `{HasStuck : B0 -< C} `{HasStuck' : B0 -< D}
    (L : rel (@label E) (@label F)) :
    mon (ctree E C X -> ctree F D Y -> Prop) :=
    {| body R t u :=
      forall l t', trans l t t' -> exists l' u', trans l' u u' /\ R t' u' /\ L l l'
    |}.
  Next Obligation.
    edestruct H0 as (u' & l' & ?); eauto.
    eexists; eexists; intuition; eauto.
  Qed.

(*|
Complete strong simulation [ss].
|*)
  Program Definition ss {E F C D : Type -> Type} {X Y : Type}
    `{HasStuck : B0 -< C} `{HasStuck' : B0 -< D}
    (L : rel (@label E) (@label F)) : mon (ctree E C X -> ctree F D Y -> Prop) :=
    {| body R t u :=
        ss0 L R t u /\
          forall l u', trans l u u' -> exists l' t', L l' l /\ trans l' t t'
    |}.
  Next Obligation.
    split; eauto. intros.
    edestruct H0 as (? & ? & ? & ? & ?); repeat econstructor; eauto.
  Qed.

End StrongSim.

Section StrongSBisim.
  Context {E F C D : Type -> Type} {X Y : Type} `{HasStuck : B0 -< C} `{HasStuck' : B0 -< D}.
  Notation S := (ctree E C X).
  Notation S' := (ctree F D Y).

(*|
In the heterogeneous case, the relation is not symmetric.
|*)
  Program Definition sb L : mon (S -> S' -> Prop) :=
    {| body R t u := ss0 L R t u /\ ss0 (flip L) (flip R) u t |}.
  Next Obligation.
    split; intros; [edestruct H0 as (? & ? & ?) | edestruct H1 as (? & ? & ?)]; eauto; eexists; eexists; intuition; eauto.
  Qed.

End StrongSBisim.

(*|
The relations themselves
|*)

Definition ssim0 {E F C D X Y} `{HasStuck : B0 -< C} `{HasStuck' : B0 -< D} L :=
  (gfp (@ss0 E F C D X Y _ _ L): hrel _ _).

Definition ssim {E F C D X Y} `{HasStuck : B0 -< C} `{HasStuck' : B0 -< D} L :=
  (gfp (@ss E F C D X Y _ _ L) : hrel _ _).

Definition sbisim {E F C D X Y} `{HasStuck : B0 -< C} `{HasStuck': B0 -< D} L :=
  (gfp (@sb E F C D X Y _ _ L) : hrel _ _).

Module SBisimNotations.

  Notation sst0 L := (t (ss0 L)).
  Notation ssbt0 L := (bt (ss0 L)).
  Notation ssT0 L := (T (ss0 L)).
  Notation ssbT0 L := (bT (ss0 L)).
  
  Notation sst L := (t (ss L)).
  Notation ssbt L := (bt (ss L)).
  Notation ssT L := (T (ss L)).
  Notation ssbT L := (bT (ss L)).

  Notation "t (≲ L ) u" := (ssim L t u) (at level 70).
  Notation "t ≲ u" := (ssim eq t u) (at level 70). (* FIXME we should ensure that return types are the same. *)
  Notation "t (~ L ) u" := (sbisim L t u) (at level 70).
  Notation "t ~ u" := (sbisim eq t u) (at level 70).

  Notation st L := (t (sb L)).
  Notation sT L := (T (sb L)).
  Notation sbt L := (bt (sb L)).
  Notation sbT L := (bT (sb L)).

  (** notations for easing readability in proofs by enhanced coinduction *)
  Notation "t [≲ L ] u" := (ss L _ t u) (at level 79).
  Notation "t [≲] u" := (ss eq _ t u) (at level 79).

  Notation "t {≲ L } u" := (sst L _ t u) (at level 79).
  Notation "t {≲} u" := (sst eq _ t u) (at level 79).

  Notation "t {{≲ L }} u" := (ssbt L _ t u) (at level 79).
  Notation "t {{≲}} u" := (ssbt eq _ t u) (at level 79).

  Notation "t [~ L] u" := (st L _ t u) (at level 79).
  Notation "t [~] u" := (st eq _ t u) (at level 79).

  Notation "t {~ L } u" := (sbt L _ t u) (at level 79).
  Notation "t {~} u" := (sbt eq _ t u) (at level 79).

  Notation "t {{ ~ L }} u" := (sb L _ t u) (at level 79).
  Notation "t {{~}} u" := (sb eq _ t u) (at level 79).

End SBisimNotations.

Import SBisimNotations.

Ltac fold_sbisim :=
  repeat
    match goal with
    | h: context[gfp (@sb ?E ?C ?X _)] |- _ => fold (@sbisim E C X _) in h
    | |- context[gfp (@sb ?E ?C ?X _)]      => fold (@sbisim E C X _)
    | h: context[gfp (@ss ?E ?F ?C ?D ?X ?Y _ _ ?L)] |- _ => fold (@ssim E F C D X Y _ _ L) in h
    | |- context[gfp (@ss ?E ?F ?C ?D ?X ?Y _ _ ?L)]      => fold (@ssim E F C D X Y _ _ L)
    | h: context[gfp (@ss0 ?E ?F ?C ?D ?X ?Y _ _ ?L)] |- _ => fold (@ssim0 E F C D X Y _ _ L) in h
    | |- context[gfp (@ss0 ?E ?F ?C ?D ?X ?Y _ _ ?L)]      => fold (@ssim0 E F C D X Y _ _ L)
    end.

Ltac __coinduction_sbisim R H :=
  (try unfold sbisim);
  (try unfold ssim0);
  (try unfold ssim);
  apply_coinduction; fold_sbisim; intros R H.

Tactic Notation "__step_sbisim" :=
  match goal with
  | |- context[@ssim0 ?E ?F ?C ?D ?X ?Y _ _ ?LR] =>
      unfold ssim0;
      step;
      fold (@ssim0 E F C D X Y _ _ LR)
  | |- context[@ssim ?E ?F ?C ?D ?X ?Y _ _ ?LR] =>
      unfold ssim;
      step;
      fold (@ssim E F C D X Y _ _ LR)
  | |- context[t (@ss ?E ?F ?C ?D ?X ?Y _ _ ?LR)] =>
      unfold ss;
      step;
      fold (@ss E F C D X Y _ _ LR)
  | |- context[@sbisim ?E ?C ?X _] =>
      unfold sbisim;
      step;
      fold (@sbisim E C X _)
  | |- context[@sb ?E ?C ?X _] =>
      unfold sb;
      step;
      fold (@sb E C X _)
  end.

#[local] Tactic Notation "step" := __step_sbisim || step.

#[local] Tactic Notation "coinduction" simple_intropattern(R) simple_intropattern(H) :=
  __coinduction_sbisim R H || coinduction R H.

Ltac __step_in_sbisim H :=
  match type of H with  
  | context[@ssim0 ?E ?F ?C ?D ?X ?Y _ _ ?LR] =>
      unfold ssim0 in H;
      step in H;
      fold (@ssim0 E F C D X Y _ _ LR) in H
  | context[@ssim ?E ?F ?C ?D ?X ?Y _ _ ?LR] =>
      unfold ssim in H;
      step in H;
      fold (@ssim E F C D X Y _ _ LR) in H
  | context [@sbisim ?E ?C ?X _] =>
      unfold sbisim in H;
      step in H;
      fold (@sbisim E C X _) in H
  end.

#[local] Tactic Notation "step" "in" ident(H) := __step_in_sbisim H || step in H.

(*|
A bisimulation trivially gives a simulation.
|*)
Lemma sb_ss : forall {E F C D X Y} `{B0 -< C} `{B0 -< D} L RR
  (t : ctree E C X) (t' : ctree F D Y),
  sb L RR t t' -> ss L RR t t'.
Proof.
  intros; split.
  - apply H1.
  - intros. apply H1 in H2 as (? & ? & ? & ? & ?). eauto.
Qed.

Lemma sbisim_ssim : forall {E F C D X Y} `{B0 -< C} `{B0 -< D} L
  (t : ctree E C X) (t' : ctree F D Y),
  sbisim L t t' -> ssim L t t'.
Proof.
  intros until L.
  coinduction R CH. simpl. intros.
  split; step in H1; intros;
    apply H1 in H2 as (? & ? & ? & ? & ?);
    exists x, x0; auto.
Qed.

Lemma ssim_ssim0 : forall {E C X} `{B0 -< C} L (t t' : ctree E C X),
  ssim L t t' -> ssim0 L t t'.
Proof.
  intros ? ? ? ? L.
  coinduction R CH. simpl. intros.
  step in H0.
  apply H0 in H1 as (? & ? & ? & ? & ?).
  apply CH in H2.
  exists x, x0; eauto.
Qed.

Lemma sbisim_ssim0 : forall {E C X} `{B0 -< C} L (t t' : ctree E C X),
  sbisim L t t' -> ssim0 L t t'.
Proof.
  intros. apply ssim_ssim0. now apply sbisim_ssim.
Qed.



Section sbisim_homogenous_theory.
  Context {E C: Type -> Type} {X: Type} `{HasStuck: B0 -< C}
          (L: relation (@label E)).
  
  Notation ss := (@ss E E C C X X _ _ L).
  Notation sb  := (@sb E E C C X X _ _ L).
  Notation sbisim := (@sbisim E E C C X X _ _ L).

  Notation st := (coinduction.t sb).
  Notation sbt := (coinduction.bt sb).
  Notation sT  := (coinduction.T sb).

  (*|
    This is just a hack suggested by Damien Pous to avoid a
    universe inconsistency when using both the relational algebra
    and coinduction libraries (we fix the type at which we'll use [eq]).
    |*)
  Definition seq: relation (ctree E C X) := eq.
  Arguments seq/.

  Lemma refl_st {RL: Reflexive L} : const seq <= st.
  Proof.
    apply leq_t.
    split; intros; cbn*; intros; inv H; subst;
      exists l, t'; split; eauto.
  Qed.

  (*|
    [converse] is compatible
    i.e. validity of up-to symmetry
    |*)
  Lemma converse_st {SL: Symmetric L}: converse <= st.
  Proof.
    apply leq_t; cbn.
    intros R ? ? [H1 H2]; split; intros.
    - destruct (H2 _ _ H) as (? & ? & ? & ? & ?); subst; symmetry in H4; eauto.
    - destruct (H1 _ _ H) as (? & ? & ? & ? & ?); subst; symmetry in H4; eauto.
  Qed.

  (*|
    [square] is compatible
    i.e. validity of up-to transivitiy
    |*)
  Lemma square_st {TR: Transitive L}: square <= st.
  Proof.
    apply Coinduction; cbn.    
    intros R x z [y [xy yx] [yz zy]].
    split.
     - intros ?l x' xx'.
      destruct (xy _ _ xx') as (?l & y' & yy' & ? & EQ).
      destruct (yz _ _ yy') as (?l & z' & zz' & ? & EQ').
      do 2 eexists; repeat split.
      eauto.
      apply (f_Tf sb).
      eexists; eauto.
      transitivity l0; assumption.
    - intros ?l z' zz'.
      destruct (zy _ _ zz') as (?l & y' & yy' & ? & EQ).
      destruct (yx _ _ yy') as (?l & x' & xx' & ? & EQ').
      do 2 eexists; repeat split.
      eauto.
      apply (f_Tf sb).
      eexists; eauto.
      transitivity l0; assumption.
  Qed.

  (*|
    Thus bisimilarity and [t R] are always equivalence relations.
    |*)
  #[global] Instance Equivalence_st `{Equivalence _ L} R: Equivalence (st R).
  Proof. apply Equivalence_t. apply refl_st. apply square_st. apply converse_st. Qed.

  Corollary Equivalence_bisim `{Equivalence _ L}: Equivalence sbisim.
  Proof. apply Equivalence_st. Qed.

  #[global] Instance Equivalence_sbt `{Equivalence _ L} R: Equivalence (sbt R).
  Proof. apply rel.Equivalence_bt. apply refl_st. apply square_st. apply converse_st. Qed.

  #[global] Instance Equivalence_sT `{Equivalence _ L} f R: Equivalence ((T sb) f R).
  Proof. apply rel.Equivalence_T. apply refl_st. apply square_st. apply converse_st. Qed.

  (*|
Aggressively providing instances for rewriting hopefully faster
[sbisim] under all [sb]-related contexts (consequence of the transitivity
of the companion).
|*)

  #[global] Instance sbisim_sbisim_closed_goal `{Equivalence _ L} : Proper (sbisim ==> sbisim ==> flip impl) sbisim.
  Proof.
    repeat intro.
    etransitivity; [etransitivity; eauto | symmetry; eassumption].
  Qed.

  #[global] Instance sbisim_sbisim_closed_ctx `{Equivalence _ L} : Proper (sbisim ==> sbisim ==> impl) sbisim.
  Proof.
    repeat intro.
    etransitivity; [symmetry; eassumption | etransitivity; eauto].
  Qed.

  #[global] Instance sbisim_clos_st_goal `{Equivalence _ L} R :
    Proper (sbisim ==> sbisim ==> flip impl) (st R).
  Proof.
    cbn; intros ? ? eq1 ? ? eq2 ?.
    rewrite eq1, eq2.
    auto.
  Qed.

  #[global] Instance sbisim_clos_st_ctx `{Equivalence _ L} R :
    Proper (sbisim ==> sbisim ==> impl) (st R).
  Proof.
    cbn; intros ? ? eq1 ? ? eq2 ?.
    rewrite <- eq1, <- eq2.
    auto.
  Qed.

  #[global] Instance sbisim_clos_sT_goal `{Equivalence _ L} R f :
    Proper (sbisim ==> sbisim ==> flip impl) (sT f R).
  Proof.
    cbn; intros ? ? eq1 ? ? eq2 ?.
    rewrite eq1, eq2.
    auto.
  Qed.

  #[global] Instance sbisim_clos_sT_ctx `{Equivalence _ L} R f :
    Proper (sbisim ==> sbisim ==> impl) (sT f R).
  Proof.
    cbn; intros ? ? eq1 ? ? eq2 ?.
    rewrite <- eq1, <- eq2.
    auto.
  Qed.

  (*|
    Strong bisimulation up-to [equ] is valid
    ----------------------------------------
    |*)
  Lemma equ_clos_st : equ_clos <= st.
  Proof.
    apply Coinduction; cbn.
    intros R x y [x' y' x'' y'' EQ' [F B] EQ'']; split.
    - intros l z x'z.
      rewrite EQ' in x'z.
      apply F in x'z.
      destruct x'z as (? & ? & ? & ? & ?).
      do 2 eexists; intuition.
      rewrite <- EQ''. eauto.
      eapply (f_Tf sb).
      econstructor; eauto.
      eauto.
    - intros l z y'z.
      rewrite <- EQ'' in y'z.
      apply B in y'z.
      destruct y'z as (? & ? & ? & ? & ?).
      do 2 eexists; intuition.
      rewrite EQ'; eauto.
      eapply (f_Tf sb).
      econstructor; eauto.
      eauto.
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

  #[global] Instance equ_sbt_closed_goal `{EqL: Equivalence _ L} R:
    Proper (equ eq ==> equ eq ==> flip impl) (sbt R).
  Proof.
    repeat intro. pose proof (gfp_bt sb R).
    etransitivity; [| etransitivity]; [ | apply H1 | ]; apply H2.
    rewrite H; auto. rewrite H0; auto.
  Qed.

  #[global] Instance equ_sbt_closed_ctx `{EqL: Equivalence _ L} {R} :
    Proper (equ eq ==> equ eq ==> impl) (sbt R).
  Proof.
    repeat intro. pose proof (gfp_bt sb R).
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

  #[global] Instance equ_ss0_closed_goal {r} : Proper (equ eq ==> equ eq ==> flip impl) (@ss0 E E C C X X _ _ L r).
  Proof.
    intros t t' tt' u u' uu'; cbn; intros.
    rewrite tt' in H0. apply H in H0 as (? & ? & ? & ? & ?).
    eexists; eexists; eauto. rewrite uu'. eauto.
  Qed.

  #[global] Instance equ_ss0_closed_ctx {r} : Proper (equ eq ==> equ eq ==> impl) (@ss0 E E C C X X _ _ L r).
  Proof.
    intros t t' tt' u u' uu'; intros.
    rewrite tt', uu'. reflexivity.
  Qed.

  #[global] Instance equ_ss_closed_goal `{EqL: Equivalence _ L} {r} : Proper (equ eq ==> equ eq ==> flip impl) (ss r).
  Proof.
    intros t t' tt' u u' uu'; split; intros.
    - rewrite tt', uu'. apply H.
    - rewrite uu' in H0. apply H in H0. setoid_rewrite tt'. apply H0.
  Qed.

  #[global] Instance equ_ss_closed_ctx `{EqL: Equivalence _ L} {r} : Proper (equ eq ==> equ eq ==> impl) (ss r).
  Proof.
    intros t t' tt' u u' uu'; intros.
    rewrite tt', uu'. reflexivity.
  Qed.

  (*|
Hence [equ eq] is a included in [sbisim]
|*)
  #[global] Instance equ_sbisim_subrelation `{EqL: Equivalence _ L} : subrelation (equ eq) sbisim.
  Proof.
    red; intros.
    rewrite H; reflexivity.
  Qed.
End sbisim_homogenous_theory.

(*|
Up-to [bind] context bisimulations
----------------------------------
We have proved in the module [Equ] that up-to bind context is
a valid enhancement to prove [equ].
We now prove the same result, but for strong and weak bisimulation.
|*)

Section bind_homogenous.
  Obligation Tactic := trivial.
  Context {E C: Type -> Type} {X Y: Type} `{HasStuck: B0 -< C}.
   
  (*|
    Specialization of [bind_ctx] to a function acting with [hsisim] on the bound value,
    and with the argument (pointwise) on the continuation.
    |*)
  Program Definition bind_ctx_sbisim : mon (rel (ctree E C Y) (ctree E C Y)) :=
    {|body := fun R => @bind_ctx E E C C X X Y Y (sbisim eq) (pointwise eq R) |}.
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

  (** Lef: When I change eq to L here, I need the following lemma
      {HPval: Proper (L ==> flip impl) is_val}
      so I can make [L a b -> is_val a -> is_val b], it doesn't work for any [L] *)
  (*|
    The resulting enhancing function gives a valid up-to technique
        |*)
  Lemma bind_ctx_sbisim_t: bind_ctx_sbisim <= (st eq).
  Proof.
    apply Coinduction; cbn.
    
    intros R x y [z _ [t zt [k1 _ [k2 EQ H]]]]; inv H; split; intros.
    - edestruct EQ; trivial.
      red in EQ; simpl in *.
      step in zt; destruct zt as (Fzt & Btz); cbn in *.
      apply trans_bind_inv in H as
          [(H & t'' & STEP & EQ') | (v & STEPres & STEP)]; cbn in *.
      + apply Fzt in STEP as (u' & ? & STEP & EQ'' & ?); subst.
        exists u'; eexists; split; subst.
        * eapply trans_bind_l; eauto with trans.
        * split; eauto.
          apply (fT_T (equ_clos_st eq)).
          econstructor; [exact EQ' | | reflexivity].
          apply (fTf_Tf (sb eq)).
          apply in_bind_ctx; auto.
          intros ? ? ->.
          apply (b_T (sb eq)).
          apply EQ; reflexivity.
      + apply Fzt in STEPres as (u' & ? & STEPres & EQ' & ?); subst.
        pose proof (trans_val_inv STEPres) as EQ''.
        rewrite EQ'' in STEPres.
        specialize (EQ v v eq_refl) as [Fk Bk].
        apply Fk in STEP as (u'' & ? & STEP & EQu & ?); cbn in *.
        eexists. eexists. split.
        eapply trans_bind_r; cbn in *; eauto.
        apply STEP.
        split.
        -- eapply (id_T (sb eq)); cbn; auto.
        -- assumption.
    - edestruct EQ; trivial.
      red in EQ; simpl in *.
      step in zt; destruct zt as (Fzt & Btz); cbn in *.
      apply trans_bind_inv in H as
          [(H & t'' & STEP & EQ') | (v & STEPres & STEP)]; cbn in *.
      + apply Btz in STEP as (u' & ? & STEP & EQ'' & ?); subst.
        exists l; eexists; split; subst.
        * eapply trans_bind_l; eauto with trans.
        * split; eauto.
          apply (fT_T (equ_clos_st eq)).
          econstructor.
          -- (* Not the equality I want here *)
            admit.
          -- apply (fTf_Tf (sb eq)).
             apply in_bind_ctx; auto.
             intros ? ? ->.
             apply (b_T (sb eq)).
             apply EQ; reflexivity.
          -- admit.
      + apply Btz in STEPres as (u' & ? & STEPres & EQ' & ?); subst.
        pose proof (trans_val_inv STEPres) as EQ''.
        rewrite EQ'' in STEPres.
        specialize (EQ v v eq_refl) as [Fk Bk].
        apply Bk in STEP as (u'' & ? & STEP & EQu & ?); cbn in *.
        eexists. eexists. split.
        eapply trans_bind_r; cbn in *; eauto.
        apply STEP.
        split.
        -- eapply (id_T (sb eq)); cbn; auto.
        -- assumption.
Admitted.
          
End bind_homogenous.

Import CTree.
Import CTreeNotations.

(*|
Expliciting the reasoning rule provided by the up-to principles.
|*)
Lemma st_clo_bind (E C: Type -> Type) `{B0 -< C} (X Y : Type) :
	forall (t1 t2 : ctree E C X) (k1 k2 : X -> ctree E C Y) RR,
		t1 ~ t2 ->
    (forall x, (st eq RR) (k1 x) (k2 x)) ->
    st eq RR (t1 >>= k1) (t2 >>= k2)
.
Proof.
  intros.
  apply (ft_t (@bind_ctx_sbisim_t E C X Y _)).
  apply in_bind_ctx; auto.
  intros ? ? <-; auto.
Qed.

(*|
Specializing the congruence principle for [~]
|*)
Lemma sbisim_clo_bind (E C: Type -> Type) `{B0 -< C} (X Y : Type) :
	forall (t1 t2 : ctree E C X) (k1 k2 : X -> ctree E C Y),
		t1 ~ t2 ->
    (forall x, k1 x ~ k2 x) ->
    t1 >>= k1 ~ t2 >>= k2
.
Proof.
  intros * EQ EQs.
  apply (ft_t (@bind_ctx_sbisim_t E C X Y _)).
  apply in_bind_ctx; auto.
  intros ? ? <-; auto.
  apply EQs.
Qed.

(*|
And in particular, we get the proper instance justifying rewriting [~] to the left of a [bind].
|*)
#[global] Instance bind_sbisim_cong_gen :
 forall (E C : Type -> Type) `{B0 -< C} (X Y : Type) RR,
   Proper (sbisim eq ==> pointwise_relation X (st eq RR) ==> st eq RR) (@bind E C X Y).
Proof.
  repeat red; intros; eapply st_clo_bind; eauto.
Qed.

Ltac __upto_bind_sbisim :=
  match goal with
    |- @sbisim _ _ ?X _ (CTree.bind (T := ?T) _ _) (CTree.bind (T := ?T) _ _) =>
      apply sbisim_clo_bind
  | |- body (t (@sb ?E ?C ?X _)) ?R (CTree.bind (T := ?T) _ _) (CTree.bind (T := ?T) _ _) =>
      apply (ft_t (@bind_ctx_sbisim_t E C T X _)), in_bind_ctx
  | |- body (bt (@sb ?E ?C ?X _)) ?R (CTree.bind (T := ?T) _ _) (CTree.bind (T := ?T) _ _) =>
      apply (fbt_bt (@bind_ctx_sbisim_t E C T X _)), in_bind_ctx
  end.

Ltac __upto_bind_eq_sbisim :=
  match goal with
  | |- @sbisim _ ?X (CTree.bind (T := ?T) _ _) (CTree.bind (T := ?T) _ _) =>
      __upto_bind_sbisim; [reflexivity | intros ?]
  | _ =>
      __upto_bind_sbisim; [reflexivity | intros ? ? <-]
  end.

Section Ctx.

  Context {E C: Type -> Type} {X Y Y': Type}.

  Definition vis_ctx (e : E X)
             (R: rel (X -> ctree E C Y) (X -> ctree E C Y')):
    rel (ctree E C Y) (ctree E C Y') :=
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

  Context {E C: Type -> Type} {X Y: Type}.

  Program Definition vis_ctx_sbisim (e : E X): mon (rel (ctree E C Y) (ctree E C Y)) :=
    {|body := fun R => @vis_ctx E C X Y Y e (pointwise eq R) |}.
  Next Obligation.
    intros ??? H. apply leq_vis_ctx. intros ?? H'.
    apply in_vis_ctx. intros ? ? <-. now apply H, H'.
  Qed.

(*|
The resulting enhancing function gives a valid up-to technique
|*)
  Lemma vis_ctx_sbisim_t `{B0 -< C} (e : E X) : vis_ctx_sbisim e <= (st eq).
  Proof.
    apply Coinduction.
    intros R.
    apply leq_vis_ctx.
    intros k k' kk'.
    cbn.
    split; intros ? ? TR; inv_trans; subst.
    all: cbn; eexists; eexists.
    all: split; eauto with trans.
    all: split; auto.
    all: rewrite EQ.
    all: specialize (kk' x x eq_refl).
    all: now eapply (b_T (sb eq)).
  Qed.

End sb_vis_ctx.
Arguments vis_ctx_sbisim_t {_ _ _ _ _} e.

Ltac __upto_vis_sbisim :=
  match goal with
    |- @sbisim ?E _ ?C _ ?X _ _ _ ?RR (Vis ?e _) (Vis ?e _) =>
      apply (ft_t (vis_ctx_sbisim_t (Y := X) e)), in_vis_ctx; intros ? ? <-
  | |- body (t (@sb ?E _ ?C _ ?X _ _ ?R _)) ?RR (Vis ?e _) (Vis ?e _) =>
      apply (ft_t (vis_ctx_sbisim_t e)), in_vis_ctx; intros ? ? <-
  | |- body (bt (@sb ?E _ ?C _ ?X _ _ ?R _)) ?RR (Vis ?e _) (Vis ?e _) =>
      apply (fbt_bt (vis_ctx_sbisim_t e)), in_vis_ctx; intros ? ? <-
  end.

#[local] Tactic Notation "upto_vis" := __upto_vis_sbisim.

Ltac __play_sbisim := step; split; cbn; intros ? ? ?TR.

Ltac __playL_sbisim H :=
  step in H;
  let Hf := fresh "Hf" in
  destruct H as [Hf _];
  cbn in Hf; edestruct Hf as (? & ? & ?TR & ?EQ & ?);
  clear Hf; subst; [etrans |].

Ltac __eplayL_sbisim :=
  match goal with
  | h : @sbisim ?E _ ?C _ ?X _ _ _ ?RR _ _ |- _ =>
      __playL_sbisim h
  end.

Ltac __playR_sbisim H :=
  step in H;
  let Hb := fresh "Hb" in
  destruct H as [_ Hb];
  cbn in Hb; edestruct Hb as (? & ? & ?TR & ?EQ & ?);
  clear Hb; subst; [etrans |].

Ltac __eplayR_sbisim :=
  match goal with
  | h : @sbisim ?E ?C ?X _ _ _ |- _ =>
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

Be sure to notice that contrary to equations such that [sb_guard] or
up-to principles such that [upto_vis], (most of) these rules consume a [sb].

TODO: need to think more about this --- do we want more proof rules?
Do we actually need them on [sb (st R)], or something else?
|*)

Section Proof_Rules.

  Context {E C : Type -> Type}.
  Context {HasStuck : B0 -< C}.
  Context {HasTau : B1 -< C}.
  Context {X Y : Type}.
  Context {L: relation (@label E)}.

  Lemma step_sb_ret_gen (x y : X) (R : rel _ _) :
    R stuckD stuckD ->
    (Proper (equ eq ==> equ eq ==> impl) R) ->
    x = y ->
    sb eq R (Ret x) (Ret y : ctree E C X).
  Proof.
    intros Rstuck PROP <-.
    split; cbn; intros ? ? TR; inv_trans; subst.
    all: cbn; exists (val x), stuckD; eexists; intuition; etrans.
    all: now rewrite EQ.
  Qed.

  Lemma step_sb_ret (x y : X) (R : rel _ _) :
    x = y ->
    sbt eq R (Ret x) (Ret y : ctree E C X).
  Proof.
    apply step_sb_ret_gen.
    reflexivity.
    typeclasses eauto.
  Qed.

(*|
The vis nodes are deterministic from the perspective of the labeled transition system,
stepping is hence symmetric and we can just recover the itree-style rule.
|*)
  Lemma step_sb_vis_gen (e : E X) (k k' : X -> ctree E C Y) (R : rel _ _) :
    (Proper (equ eq ==> equ eq ==> impl) R) ->
    (forall x, R (k x) (k' x)) ->
    sb eq R (Vis e k) (Vis e k').
  Proof.
    intros PR EQs.
    split; intros ? ? TR; inv_trans; subst.
    all: cbn; eexists; eexists; intuition; etrans; rewrite EQ; auto.
  Qed.

  Lemma step_sb_vis (e : E X) (k k' : X -> ctree E C Y) (R : rel _ _) :
    (forall x, (st eq R) (k x) (k' x)) ->
    sbt eq R (Vis e k) (Vis e k').
  Proof.
    intros * EQ.
    apply step_sb_vis_gen; auto.
    typeclasses eauto.
  Qed.

  (*|
    Same goes for visible tau nodes.
    |*)
  Lemma step_sb_step_gen (t t' : ctree E C X) (R : rel _ _) :
    (Proper (equ eq ==> equ eq ==> impl) R) ->
    (R t t') ->
    sb eq R (Step t) (Step t').
  Proof.
    intros PR EQs.
    split; intros ? ? TR; inv_trans; subst.
    all: cbn; eexists; eexists; intuition; etrans; rewrite EQ; auto.
  Qed.

  Lemma step_sb_step (t t' : ctree E C X) (R : rel _ _) :
    (st eq R t t') ->
    sbt eq R (Step t) (Step t').
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
  Lemma step_sb_brS_gen Z (c : C Y) (c' : C Z) (k : Y -> ctree E C X) (k' : Z -> ctree E C X) (R : rel _ _) :
    (Proper (equ eq ==> equ eq ==> impl) R) ->
    (forall x, exists y, R (k x) (k' y)) ->
    (forall y, exists x, R (k x) (k' y)) ->
    sb eq R (BrS c k) (BrS c' k').
  Proof.
    intros PROP EQs1 EQs2.
    split; intros ? ? TR; inv_trans; subst.
    - destruct (EQs1 x) as [y HR].
      eexists. eexists. intuition.
      etrans.
      rewrite EQ; eauto.
    - destruct (EQs2 x) as [y HR].
      eexists. eexists. intuition.
      etrans.
      cbn; rewrite EQ; eauto.
  Qed.

  Lemma step_sb_brS Z (c : C Y) (c' : C Z) (k : Y -> ctree E C X) (k' : Z -> ctree E C X) (R : rel _ _) :
    (forall x, exists y, st eq R (k x) (k' y)) ->
    (forall y, exists x, st eq R (k x) (k' y)) ->
    sbt eq R (BrS c k) (BrS c' k').
  Proof.
    intros EQs1 EQs2.
    apply step_sb_brS_gen; auto.
    typeclasses eauto.
  Qed.

  Lemma step_sb_brS_id_gen (c : C Y) (k k' : Y -> ctree E C X) (R : rel _ _) :
    (Proper (equ eq ==> equ eq ==> impl) R) ->
    (forall x, R (k x) (k' x)) ->
    sb eq R (BrS c k) (BrS c k').
  Proof.
    intros PROP EQs.
    apply step_sb_brS_gen; auto.
    all: intros x; exists x; auto.
  Qed.

  Lemma step_sb_brS_id (c : C Y) (k k' : Y -> ctree E C X) (R : rel _ _) :
    (forall x, st eq R (k x) (k' x)) ->
    sbt eq R (BrS c k) (BrS c k').
  Proof.
    apply step_sb_brS_id_gen.
    typeclasses eauto.
  Qed.

  (*|
  For invisible nodes, the situation is different: we may kill them, but that execution
  cannot act as going under the guard.
  |*)
  Lemma step_sb_guard_gen (t t' : ctree E C X) (R : rel _ _) :
    sb eq R t t' ->
    sb eq R (Guard t) (Guard t').
  Proof.
    intros EQ.
    split; intros ? ? TR; inv_trans; subst.
    all: apply EQ in TR as (? & ? & ? & ? & ?); subst.
    all: do 2 eexists; intuition.
    - apply trans_guard; eauto.
    - assumption.
    - apply trans_guard; cbn in *; subst; eauto.
    - assumption. 
  Qed.

  Lemma step_sb_guard (t t' : ctree E C X) (R : rel _ _) :
    sbt eq R t t' ->
    sbt eq R (Guard t) (Guard t').
  Proof.
    apply step_sb_guard_gen.
  Qed.

  Lemma step_sb_brD_gen Z (c : C Y) (c' : C Z) (k : Y -> ctree E C X) (k' : Z -> ctree E C X) (R : rel _ _) :
    (forall x, exists y, sb eq R (k x) (k' y)) ->
    (forall y, exists x, sb eq R (k x) (k' y)) ->
    sb eq R (BrD c k) (BrD c' k').
  Proof.
    intros EQs1 EQs2.
    split; intros ? ? TR; inv_trans; subst.
    - destruct (EQs1 x) as [z [F _]]; cbn in F.
      apply F in TR; destruct TR as (u' & ? & TR' & EQ' & ?).
      eexists. eexists. subst. intuition.
      eapply trans_brD with (x := z); [|reflexivity].
      eauto.
      eauto.
    - destruct (EQs2 x) as [y [_ B]]; cbn in B.
      apply B in TR; destruct TR as (u' & ? & TR' & EQ' & ?).
      eexists. eexists. subst. intuition.
      eapply trans_brD with (x := y); [|reflexivity].
      eauto.
      eauto.
  Qed.

  Lemma step_sb_brD Z (c : C Y) (c' : C Z) (k : Y -> ctree E C X) (k' : Z -> ctree E C X) (R : rel _ _) :
    (forall x, exists y, sbt eq R (k x) (k' y)) ->
    (forall y, exists x, sbt eq R (k x) (k' y)) ->
    sbt eq R (BrD c k) (BrD c' k').
  Proof.
    apply step_sb_brD_gen.
  Qed.

  Lemma step_sb_brD_id_gen (c : C Y) (k k' : Y -> ctree E C X) (R : rel _ _) :
    (forall x, sb eq R (k x) (k' x)) ->
    sb eq R (BrD c k) (BrD c k').
  Proof.
    intros; apply step_sb_brD_gen.
    intros x; exists x; apply H.
    intros x; exists x; apply H.
  Qed.

  Lemma step_sb_brD_id (c : C Y) (k k' : Y -> ctree E C X) (R : rel _ _) :
    (forall x, sbt eq R (k x) (k' x)) ->
    sbt eq R (BrD c k) (BrD c k').
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

  Context {E C : Type -> Type}.
  Context {HasStuck : B0 -< C}.
  Context {HasTau : B1 -< C}.
  Context {X Y : Type}.

  Lemma sb_ret : forall x y,
      x = y ->
      Ret x ~ (Ret y : ctree E C X).
  Proof.
    intros * <-.
    now step.
  Qed.

  (** LEF: TODO: make sure all the ltac patterns have the right arguments for sb, sbisim, st etc. *)
  Lemma sb_vis e : forall (k k' : X -> ctree E C Y),
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
  Lemma sb_guard : forall (t : ctree E C X),
      Guard t ~ t.
  Proof.
    intros t; play.
    - inv_trans.
      etrans.
    - eauto 6 with trans.
  Qed.

 Lemma sb_guard_l : forall (t u : ctree E C X),
      t ~ u ->
      Guard t ~ u.
  Proof.
    intros * EQ; now rewrite sb_guard.
  Qed.

  Lemma sb_guard_r : forall (t u : ctree E C X),
      t ~ u ->
      t ~ Guard u.
  Proof.
    intros * EQ; now rewrite sb_guard.
  Qed.

  Lemma sb_guard_lr : forall (t u : ctree E C X),
      t ~ u ->
      Guard t ~ Guard u.
  Proof.
    intros * EQ; now rewrite !sb_guard.
  Qed.

  Lemma sb_step : forall (t u : ctree E C X),
      t ~ u ->
      Step t ~ Step u.
  Proof.
    intros * EQ; step.
    apply step_sb_step; auto.
  Qed.

  (* TODO: Double check that this is needed, it should be taus in all contexts I can think of *)
  Lemma sb_brD1 (c1: C (fin 1)): forall (k : fin 1 -> ctree E C X),
      BrD c1 k ~ k F1.
  Proof.
    intros; step; econstructor.
    - intros ? ? ?. inv H.
      apply Eqdep.EqdepTheory.inj_pair2 in H4, H3; subst.
      dependent destruction x; exists l, t'; etrans; auto.
      inversion x.
    - intros ? ? ?; cbn.
      eauto 6 with trans.
  Qed.

  Lemma sb_brS I J (ci : C I) (cj : C J)
        (k : I -> ctree E C X) (k' : J -> ctree E C X) :
    (forall x, exists y, k x ~ k' y) ->
    (forall y, exists x, k x ~ k' y) ->
    BrS ci k ~ BrS cj k'.
  Proof.
    intros * EQs1 EQs2; step.
    apply @step_sb_brS; auto.
  Qed.

  Lemma sb_brS_id I (c : C I)
        (k k' : I -> ctree E C X) :
    (forall x, k x ~ k' x) ->
    BrS c k ~ BrS c k'.
  Proof.
    intros * EQs; step.
    apply @step_sb_brS_id; auto.
  Qed.

  Lemma sb_brD I J (ci : C I) (cj : C J)
        (k : I -> ctree E C X) (k' : J -> ctree E C X) :
    (forall x, exists y, k x ~ k' y) ->
    (forall y, exists x, k x ~ k' y) ->
    BrD ci k ~ BrD cj k'.
  Proof.
    intros; step.
    eapply @step_sb_brD; auto.
    intros x; destruct (H x) as (y & EQ).
    exists y; now step in EQ.
    intros y; destruct (H0 y) as (x & EQ).
    exists x; now step in EQ.
  Qed.

  Lemma sb_brD_id I (c : C I)
        (k k' : I -> ctree E C X) :
    (forall x, k x ~ k' x) ->
    BrD c k ~ BrD c k'.
  Proof.
    intros; step.
    apply @step_sb_brD_id; intros x.
    specialize (H x).
    now step in H.
  Qed.

  Lemma sb_brD_idempotent {HasFin : Bn -< C} n (k: fin (S n) -> ctree E C X) (t: ctree E C X):
      (forall x, k x ~ t) ->
      brDn k ~ t.
  Proof.
    intros * EQ.
    rewrite <- sb_guard with (t:=t).
    apply sb_brD; intros.
    exists tt; apply EQ.
    exists F1; apply EQ.
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
Section WithParams.

  Context {E C : Type -> Type}.
  Context {HasStuck : B0 -< C}.
  Context {HasTau : B1 -< C}.
  Context {HasC2 : B2 -< C}.
  Context {HasC3 : B3 -< C}.


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

  Lemma spinS_gen_nonempty : forall {Z X Y} (c: C X) (c': C Y) (x: X) (y: Y),
      @spinS_gen E C Z X c ~ @spinS_gen E C Z Y c'.
  Proof.
    intros R.
    coinduction S CIH; split; cbn; intros L t' TR;
      rewrite ctree_eta in TR; cbn in TR;
      apply trans_brS_inv in TR as (_ & EQ & ->);
      eexists; eexists;
      rewrite ctree_eta; cbn.
    - split; [econstructor|].
      + exact y.
      + reflexivity.
      + rewrite EQ; eauto.
    - split; [econstructor|].
      + exact x.
      + reflexivity.
      + rewrite EQ; eauto.
  Qed.

  Lemma spinD_gen_bisim : forall {Z X Y} (c: C X) (c': C Y),
      @spinD_gen E C Z X c ~ @spinD_gen E C Z Y c'.
  Proof.
    intros R.
    coinduction S _; split; cbn;
      intros * TR; exfalso; eapply spinD_gen_is_stuck, TR.
  Qed.

  (*|
    BrD2 is associative, commutative, idempotent, merges into BrD3, and admits _a lot_ of units.
    |*)
  Lemma brD2_assoc X : forall (t u v : ctree E C X),
	    brD2 (brD2 t u) v ~ brD2 t (brD2 u v).
  Proof.
    intros.
    play; inv_trans; eauto 7 with trans.
  Qed.

  Lemma brD2_commut {X} : forall (t u : ctree E C X),
	    brD2 t u ~ brD2 u t.
  Proof.
    intros.
    play; inv_trans; eauto 6 with trans.
  Qed.

  Lemma brD2_idem {X} : forall (t : ctree E C X),
	    brD2 t t ~ t.
  Proof.
    intros.
    play; inv_trans; eauto 6 with trans.
  Qed.

  Lemma brD2_merge {X} : forall (t u v : ctree E C X),
	    brD2 (brD2 t u) v ~ brD3 t u v.
  Proof.
    intros.
    play; inv_trans; eauto 7 with trans.
  Qed.

  Lemma brD2_is_stuck {X} : forall (u v : ctree E C X),
      is_stuck u ->
	    brD2 u v ~ v.
  Proof.
    intros * ST.
    play.
    - inv_trans.
      exfalso; eapply ST, TR. (* automate stuck transition trying to step? *)
      exists l, t'; eauto.             (* automate trivial case *)
    - eauto 6 with trans.
  Qed.

  Lemma brD2_stuckS_l {X} : forall (t : ctree E C X),
	    brD2 stuckS t ~ t.
  Proof.
    intros; apply brD2_is_stuck, stuckS_is_stuck.
  Qed.

  Lemma brD2_stuckD_l {X} : forall (t : ctree E C X),
	    brD2 stuckD t ~ t.
  Proof.
    intros; apply brD2_is_stuck, stuckD_is_stuck.
  Qed.

  Lemma brD2_stuckS_r {X} : forall (t : ctree E C X),
	    brD2 t stuckS ~ t.
  Proof.
    intros; rewrite brD2_commut; apply brD2_stuckS_l.
  Qed.

  Lemma brD2_stuckD_r {X} : forall (t : ctree E C X),
	    brD2 t stuckD ~ t.
  Proof.
    intros; rewrite brD2_commut; apply brD2_stuckD_l.
  Qed.

  Lemma brD2_spinD_l {X} : forall (t : ctree E C X),
	    brD2 spinD t ~ t.
  Proof.
    intros; apply brD2_is_stuck, spinD_is_stuck.
  Qed.

  Lemma brD2_spinD_r {X} : forall (t : ctree E C X),
	    brD2 t spinD ~ t.
  Proof.
    intros; rewrite brD2_commut; apply brD2_is_stuck, spinD_is_stuck.
  Qed.

(*|
BrS2 is commutative and "almost" idempotent
|*)
Lemma brS2_commut : forall X (t u : ctree E C X),
	  brS2 t u ~ brS2 u t.
Proof.
  intros.
  play; inv_trans; subst.
  (* all:eexists; [| rewrite EQ; reflexivity]; etrans. *)
Admitted.

Lemma brS2_idem : forall X (t : ctree E C X),
	  brS2 t t ~ Step t.
Proof.
  intros.
  play; inv_trans; subst.
  (* all:eexists; [| rewrite EQ; reflexivity]; etrans. *)
Admitted.

(*|
Inversion principles
--------------------
|*)
  Lemma sbisim_ret_inv X (r1 r2 : X) :
    (Ret r1 : ctree E C X) ~ Ret r2 -> r1 = r2.
  Proof.
    intro.
    eplayL.
    now inv_trans.
  Qed.

(*|
 For the next few lemmas, we need to know that [X] is inhabited in order to
 take a step
|*)
  Lemma sbisim_vis_invT {X X1 X2}
        (e1 : E X1) (e2 : E X2) (k1 : X1 -> ctree E C X) (k2 : X2 -> ctree E C X) (x : X1):
    Vis e1 k1 ~ Vis e2 k2 ->
    X1 = X2.
  Proof.
    intros.
    eplayL.
    inv TR; auto.
    Unshelve. auto.
  Qed.

  Lemma sbisim_vis_inv {X Y} (e1 e2 : E Y) (k1 k2 : Y -> ctree E C X) (x : Y) :
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

  Lemma sbisim_BrS_inv {X Y Z}
        c1 c2 (k1 : X -> ctree E C Z) (k2 : Y -> ctree E C Z) :
    BrS c1 k1 ~ BrS c2 k2 ->
    (forall i1, exists i2, k1 i1 ~ k2 i2).
  Proof.
    intros EQ i1.
    eplayL.
    inv_trans.
    eexists; eauto.
  Qed.

  Notation inhabited X := (exists x: X, True).

  (*|
    Annoying case: [Vis e k ~ BrS c k'] is true if [e : E void] and [c : C void].
    We rule out this case in this definition.
    |*)
  Definition are_bisim_incompat {X} (t u : ctree E C X) : Type :=
    match observe t, observe u with
    | RetF _, RetF _
    | VisF _ _, VisF _ _
    | BrF true _ _, BrF true _ _
    | BrF false _ _, _
    | _, BrF false _ _ => False
    | BrF true n _, RetF _ => True
    | RetF _,  BrF true n _ => True
    | @BrF _ _ _ _ true X _ _, @VisF _ _ _ _ Y _ _ =>
        inhabited X \/ inhabited Y
    | @VisF _ _ _ _ Y _ _, @BrF _ _ _ _ true X _ _ =>
        inhabited X \/ inhabited Y
    | _, _ => True
    end.

  Lemma sbisim_absurd {X} (t u : ctree E C X) :
    are_bisim_incompat t u ->
    t ~ u ->
    False.
  Proof.
    intros * IC EQ.
    unfold are_bisim_incompat in IC.
    setoid_rewrite ctree_eta in EQ.
    genobs t ot. genobs u ou.
    destruct ot, ou;
      (try now inv IC); (try destruct vis); (try destruct vis0);
      try now inv IC.
    - playL in EQ. inv_trans.
    - playL in EQ. inv_trans.
    - playR in EQ. inv_trans.
    - destruct IC as [[] | []]; [ playR in EQ | playL in EQ ]; inv_trans.
    - playR in EQ. inv_trans.
    - destruct IC as [[] | []]; [ playL in EQ | playR in EQ ]; inv_trans.
    Unshelve. all: auto.
  Qed.

  Ltac sb_abs h :=
    eapply sbisim_absurd; [| eassumption]; cbn; try reflexivity.

  Lemma sbisim_ret_vis_inv {X Y}(r : Y) (e : E X) (k : X -> ctree E C Y) :
    Ret r ~ Vis e k -> False.
  Proof.
    intros * abs. sb_abs abs.
  Qed.

  Lemma sbisim_ret_BrS_inv {X Y} (r : Y) (c : C X) (k : X -> ctree E C Y) :
    Ret r ~ BrS c k -> False.
  Proof.
    intros * abs; sb_abs abs.
  Qed.

  (*|
    For this to be absurd, we need one of the return types to be inhabited.
    |*)
  Lemma sbisim_vis_BrS_inv {X Y Z}
        (e : E X) (k1 : X -> ctree E C Z) (c : C Y) (k2: Y -> ctree E C Z) (y : Y) :
    Vis e k1 ~ BrS c k2 -> False.
  Proof.
    intros * abs.
    sb_abs abs. eauto.
  Qed.

  Lemma sbisim_vis_BrS_inv' {X Y Z}
        (e : E X) (k1 : X -> ctree E C Z) (c : C Y) (k2: Y -> ctree E C Z) (x : X) :
    Vis e k1 ~ BrS c k2 -> False.
  Proof.
    intros * abs.
    sb_abs abs. eauto.
  Qed.

  (*|
    Not fond of these two, need to give some thoughts about them
    |*)
  Lemma sbisim_ret_BrD_inv {X Y} (r : Y) (c : C X) (k : X -> ctree E C Y) :
    Ret r ~ BrD c k ->
    exists x, Ret r ~ k x.
  Proof.
    intro. step in H. destruct H as [Hf Hb]. cbn in *.
    edestruct Hf as (x & ? & Ht & Hs & ?); [apply trans_ret |].
    apply trans_brD_inv in Ht.
    destruct Ht as [i Ht]. exists i.
    step. split.
    - repeat intro. inv H0. exists (val r), x0. split; intuition. rewrite <- Hs.
      rewrite ctree_eta. rewrite <- H4. rewrite br0_always_stuck. reflexivity.
    - repeat intro. eapply trans_brD in H0; eauto. 
  Qed.

  Lemma sbisim_BrD_1_inv X (c1: C (fin 1)) (k : fin 1 -> ctree E C X) (t: ctree E C X) i :
    BrD c1 k ~ t ->
    k i ~ t.
  Proof.
    intro. step in H. step. destruct H. cbn in *. split; repeat intro.
    - apply H. econstructor; apply H1.
    - edestruct H0. apply H1. exists x; auto.
      destruct H2 as (? & ? & ? & ?); subst.
      destruct (trans_brD_inv H2) as (j & ?).
      assert (i = j).
      {
        remember 1%nat.
        destruct i.
        - dependent destruction j; auto.
          inv Heqn. inv j.
        - inv Heqn. inv i.
      }
      subst. eauto.
  Qed.
End WithParams.

(*|
  This section should describe lemmas proved for the
  heterogenous version of `ss`, parametric on
  - Return types X, Y
  - Label types E, F
  - Branch effects C, D
|*)
Section sbisim_heterogenous_theory.

  Arguments label: clear implicits.
  Context {E F C D : Type -> Type} {X Y : Type}
          {L: rel (@label E) (@label F)}
          {HasStuck1: B0 -< C} {HasStuck2: B0 -< D}.
  
  Notation hss := (@ss E F C D X Y _ _ L).
  Notation hsb := (@sb E F C D X Y _ _ L).
  Notation hsbisim := (@sbisim E F C D X Y _ _ L).

  Notation hst  E C X := (coinduction.t (hsb E C X)).
  Notation hsbt E C X := (coinduction.bt (hsb E C X)).
  Notation hsT  E C X := (coinduction.T (hsb E C X)).


  (*| Up-to-bisimulation enhancing function |*)
  Variant sbisim_clos_body {LE LF}
          (R : rel (ctree E C X) (ctree F D Y)) : (rel (ctree E C X) (ctree F D Y)) :=
    | Sbisim_clos : forall t t' u' u
                      (Sbisimt : t (~ LE) t')
                      (HR : R t' u')
                      (Sbisimu : u' (~ LF) u),
        @sbisim_clos_body LE LF R t u.

  Program Definition sbisim_clos {LE LF} : mon (rel (ctree E C X) (ctree F D Y)) :=
    {| body := @sbisim_clos_body LE LF |}.
  Next Obligation.
    destruct H0.
    econstructor; eauto.
  Qed.

  (* LEF: What is L here? *)
  Theorem sbisim_clos_upto {LE LF} R: @sbisim_clos LE LF R <= st L R.
    Proof. Admitted.

  #[global] Instance sbisim_hsbisim_hclosed_goal {LE: rel (label E) (label E)} {LF: rel (label F) (label F)}:
    
    Proper (sbisim LE ==> sbisim LF ==> flip impl) hsbisim.
  Admitted.

  #[global] Instance sbisim_hsbisim_hclosed_ctx {LE: rel (label E) (label E)} {LF: rel (label F) (label F)}:
    
    Proper (sbisim LE ==> sbisim LF ==> impl) hsbisim.
  Admitted.

  #[global] Instance equ_hsbisim_hclosed_goal:
    
    Proper (equ eq ==> equ eq ==> flip impl) hsbisim.
  Admitted.

  #[global] Instance equ_hsbisim_hclosed_ctx:
    
    Proper (equ eq ==> equ eq ==> impl) hsbisim.
  Admitted.
  
End sbisim_heterogenous_theory.
