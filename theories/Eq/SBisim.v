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

Section StrongHBisim.
  Context {E F C D : Type -> Type} {X Y : Type} `{HasStuck : B0 -< C} `{HasStuck' : B0 -< D}.
  Notation S := (ctree E C X).
  Notation S' := (ctree F D Y).

(*|
In the heterogeneous case, the relation is not symmetric.
|*)
  Program Definition hsb L : mon (S -> S' -> Prop) :=
    {| body R t u := ss0 L R t u /\ ss0 (flip L) (flip R) u t |}.
  Next Obligation.
    split; intros; [edestruct H0 as (? & ? & ?) | edestruct H1 as (? & ? & ?)]; eauto; eexists; eexists; intuition; eauto.
  Qed.

End StrongHBisim.

(*|
Define `sb` in terms of `hsb`
|*)
Section StrongBisim.
  Context {E C : Type -> Type} {X : Type} `{HasStuck' : B0 -< C}.
  Notation S := (ctree E C X).

  Definition sb L : mon (S -> S -> Prop) := hsb L.
End StrongBisim.

(*|
The relations themselves
|*)

Definition ssim0 {E F C D X Y} `{HasStuck : B0 -< C} `{HasStuck' : B0 -< D} L :=
  (gfp (@ss0 E F C D X Y _ _ L): hrel _ _).

Definition ssim {E F C D X Y} `{HasStuck : B0 -< C} `{HasStuck' : B0 -< D} L :=
  (gfp (@ss E F C D X Y _ _ L) : hrel _ _).

Definition sbisim {E C X} `{HasStuck : B0 -< C} L := (gfp (@sb E C X _ L) : hrel _ _).

Definition hsbisim {E F C D X Y} `{HasStuck : B0 -< C} `{HasStuck' : B0 -< D} L :=
  (gfp (@hsb E F C D X Y _ _ L) : hrel _ _).

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

  Notation "t [~ L] u" := (st L t u) (at level 79).
  Notation "t [~] u" := (st eq t u) (at level 79).

  Notation "t {~ L } u" := (sbt L t u) (at level 79).
  Notation "t {~} u" := (sbt eq t u) (at level 79).

  Notation "t {{ ~ L }} u" := (sb L t u) (at level 79).
  Notation "t {{~}} u" := (sb eq t u) (at level 79).

End SBisimNotations.

Import SBisimNotations.

Ltac fold_sbisim :=
  repeat
    match goal with
    | h: context[gfp (@hsb ?E ?F ?C ?D ?X ?Y _ _ ?L)] |- _ => fold (@hsbisim E F C D X Y _ _ L) in h
    | |- context[gfp (@hsb ?E ?F ?C ?D ?X ?Y _ _ ?L)]      => fold (@hsbisim E F C D X Y _ _ L)
    | h: context[gfp (@sb ?E ?C ?X _)] |- _ => fold (@sbisim E C X _) in h
    | |- context[gfp (@sb ?E ?C ?X _)]      => fold (@sbisim E C X _)
    | h: context[gfp (@ss ?E ?F ?C ?D ?X ?Y _ _ ?L)] |- _ => fold (@ssim E F C D X Y _ _ L) in h
    | |- context[gfp (@ss ?E ?F ?C ?D ?X ?Y _ _ ?L)]      => fold (@ssim E F C D X Y _ _ L)
    | h: context[gfp (@ss0 ?E ?F ?C ?D ?X ?Y _ _ ?L)] |- _ => fold (@ssim0 E F C D X Y _ _ L) in h
    | |- context[gfp (@ss0 ?E ?F ?C ?D ?X ?Y _ _ ?L)]      => fold (@ssim0 E F C D X Y _ _ L)
    end.

Ltac __coinduction_sbisim R H :=
  (try unfold sbisim);
  (try unfold hsbisim);
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
  | |- context[@hsbisim ?E ?F ?C ?D ?X ?Y _ _ ?LR] =>
      unfold hsbisim;
      step;
      fold (@hsbisim E F C D X Y _ _ LR)
  | |- context[@hsb ?E ?F ?C ?D ?X ?Y _ _ ?LR] =>
      unfold hsb;
      step;
      fold (@hsb E F C D X Y _ _ LR)
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
  | context[@hsbisim ?E ?F ?C ?D ?X ?Y _ _ ?LR] =>
      unfold hsbisim in H;
      step in H;
      fold (@hsbisim E F C D X Y _ _ LR) in H
  | context [@sbisim ?E ?C ?X _] =>
      unfold sbisim in H;
      step in H;
      fold (@sbisim E C X _) in H
  end.

#[local] Tactic Notation "step" "in" ident(H) := __step_in_sbisim H || step in H.

(*|
The two definitions of homogeneous bisimulation are equivalent.
|*)
Lemma hsbisim_eq_sbisim : forall {E C X} `{B0 -< C} L (t t' : ctree E C X),
  hsbisim L t t' <-> sbisim L t t'.
Proof.
  split; intros; revert t t' H0;
    coinduction R CH; intros; step in H0; cbn in H0;
    split; cbn; intros; apply H0 in H1 as (? & ? & ? & ? & ?); subst;
    exists x, x0; split; auto.
Qed.

(*|
A bisimulation trivially gives a simulation.
|*)
Lemma hsb_ss : forall {E F C D X Y} `{B0 -< C} `{B0 -< D} L RR
  (t : ctree E C X) (t' : ctree F D Y),
  hsb L RR t t' -> ss L RR t t'.
Proof.
  intros; split.
  - apply H1.
  - intros. apply H1 in H2 as (? & ? & ? & ? & ?). eauto.
Qed.

Lemma hsbisim_ssim : forall {E F C D X Y} `{B0 -< C} `{B0 -< D} L
  (t : ctree E C X) (t' : ctree F D Y),
  hsbisim L t t' -> ssim L t t'.
Proof.
  intros until L.
  coinduction R CH. simpl. intros.
  split; step in H1; intros;
    apply H1 in H2 as (? & ? & ? & ? & ?);
    exists x, x0; auto.
Qed.

Lemma sbisim_ssim_eq : forall {E C X} `{B0 -< C} (t t' : ctree E C X) L,
  sbisim L t t' -> ssim L t t'.
Proof.
  intros. apply hsbisim_eq_sbisim in H0.
  now apply hsbisim_ssim in H0 as H1.
Qed.

Lemma sb_ss : forall {E C X} `{B0 -< C} RR L (t t' : ctree E C X),
  sb L RR t t' -> ss L RR t t'.
Proof.
  intros. split.
  - apply H0.
  - intros; apply H0 in H1 as (? & ? & ? & ? & ?); eauto.
Qed.

Lemma sbisim_ssim : forall
    {E C X} `{B0 -< C} L (t t' : ctree E C X),
  sbisim L t t' -> ssim L t t'.
Proof.
  intros until L.
  coinduction R CH; simpl; intros.
  step in H0; split; intros;
    apply H0 in H1 as (? & ? & ? & ? & ?);
    exists x, x0; split; try assumption;
    apply H0 in H1 as (? & ? & ? & ? & ?); split; eauto.
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

Section sbisim_theory.

  Context {E C : Type -> Type} {X : Type} `{HasStuck : B0 -< C}.
  Notation ss := (@ss E E C C X X _ _ eq).
  Notation sb := (@sb E C X _ eq).
  Notation sbisim := (@sbisim E C X _ eq).
  Notation st := (coinduction.t sb).
  Notation sbt := (coinduction.bt sb).
  Notation sT := (coinduction.T sb).
(*|
This is just a hack suggested by Damien Pous to avoid a
universe inconsistency when using both the relational algebra
and coinduction libraries (we fix the type at which we'll use [eq]).
|*)
    Definition seq: relation (ctree E C X) := eq.
    Arguments seq/.

(*|
[eq] is a post-fixpoint, thus [const eq] is below [t]
i.e. validity of up-to reflexivity
|*)
  Lemma refl_st : const seq <= st.
  Proof.
    apply leq_t.
    split; intros; cbn*; intros; inv H; subst; exists l, t'; split; eauto.
  Qed.

(*|
[converse] is compatible
i.e. validity of up-to symmetry
|*)
  Lemma converse_st: converse <= st.
  Proof.
    apply leq_t; cbn.
    intros R ? ? [H1 H2]; split; intros.
    - destruct (H2 _ _ H) as (? & ? & ? & ? & ?); subst; eauto.
    - destruct (H1 _ _ H) as (? & ? & ? & ? & ?); subst; eauto.
  Qed.

(*|
[square] is compatible
 i.e. validity of up-to transivitiy
|*)
  Lemma square_st: square <= st.
  Proof.
    apply Coinduction; cbn.    
    intros R x z [y [xy yx] [yz zy]].
    split.
    - intros ? x' xx'.
      destruct (xy _ _ xx') as (? & y' & yy' & ? & <-). 
      destruct (yz _ _ yy') as (? & z' & zz' & ? & <-).
      exists l, z'; split; intuition.
      apply (f_Tf sb).
      eexists; eauto.
    - intros ? z' zz'.      
      destruct (zy _ _ zz') as (? & y' & yy' & ? & <-).
      destruct (yx _ _ yy') as (l & x' & xx' & ? & <-).
      exists l, x'; split; intuition.
      apply (f_Tf sb).      
      eexists; eauto.
  Qed.

(*|
Thus bisimilarity and [t R] are always equivalence relations.
|*)
  #[global] Instance Equivalence_st R: Equivalence (st R).
  Proof. apply Equivalence_t. apply refl_st. apply square_st. apply converse_st. Qed.

  Corollary Equivalence_bisim : Equivalence sbisim.
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
    apply Coinduction; cbn.
    intros R x y [x' y' x'' y'' EQ' [? ?] EQ'']; split.
    - intros l z x'z.
  Admitted.
  (*
    apply equ_clos_sym.
    intros R t u EQ l t1 TR. cbn in EQ. inv EQ.
    destruct HR as [F _]; cbn in *.
    rewrite Equt in TR.
    apply F in TR.
    destruct TR as (? & ? & ? & ? & ?). subst.
    exists x. exists x0. intuition.
    rewrite <- Equu; eauto.
    eapply (f_Tf sb).
    econstructor; intuition.
    auto.
  Qed.
*)

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

  Check sbisim.
  Check ss0.
  #[global] Instance equ_ss0_closed_goal {r} : Proper (equ eq ==> equ eq ==> flip impl) (@ss0 E E C C X X _ _ eq r).
  Proof.
    intros t t' tt' u u' uu'; cbn; intros.
    rewrite tt' in H0. apply H in H0 as (? & ? & ? & ? & ?).
    eexists; eexists; eauto. rewrite uu'. eauto.
  Qed.

  #[global] Instance equ_ss0_closed_ctx {r} : Proper (equ eq ==> equ eq ==> impl) (@ss0 E E C C X X _ _ eq r).
  Proof.
    intros t t' tt' u u' uu'; intros.
    rewrite tt', uu'. reflexivity.
  Qed.

  #[global] Instance equ_ss_closed_goal {r} : Proper (equ eq ==> equ eq ==> flip impl) (ss r).
  Proof.
    intros t t' tt' u u' uu'; split; intros.
    - rewrite tt', uu'. apply H.
    - rewrite uu' in H0. apply H in H0. setoid_rewrite tt'. apply H0.
  Qed.

  #[global] Instance equ_ss_closed_ctx {r} : Proper (equ eq ==> equ eq ==> impl) (ss r).
  Proof.
    intros t t' tt' u u' uu'; intros.
    rewrite tt', uu'. reflexivity.
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


(* Up-to-bisimulation enhancing function *)
Variant sbisim_clos_body {E F C D X1 X2} `{B0 -< C} `{B0 -< D} (R : rel (ctree E C X1) (ctree F D X2)) : (rel (ctree E C X1) (ctree F D X2)) :=
  | Sbisim_clos : forall t t' u' u
                 (Sbisimt : t ~ t')
                 (HR : R t' u')
                 (Sbisimu : u' ~ u),
      sbisim_clos_body R t u.

Program Definition sbisim_clos {E F C D X1 X2} `{B0 -< C} `{B0 -< D} : mon (rel (ctree E C X1) (ctree F D X2)) :=
  {| body := @sbisim_clos_body E F C D X1 X2 _ _ |}.
Next Obligation.
  destruct H2.
  econstructor; eauto.
Qed.

(*|
Up-to [bind] context bisimulations
----------------------------------
We have proved in the module [Equ] that up-to bind context is
a valid enhancement to prove [equ].
We now prove the same result, but for strong and weak bisimulation.
|*)

Section bind.
  Obligation Tactic := idtac.

 Context {E C: Type -> Type} {X Y: Type} `{HasStuck : B0 -< C}.

(*|
Specialization of [bind_ctx] to a function acting with [sisim] on the bound value,
and with the argument (pointwise) on the continuation.
|*)
 (* LEF: TODO heterogeneous? *)
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

  (* LEF: Up to here *)
(*|
The resulting enhancing function gives a valid up-to technique
|*)
  Lemma bind_ctx_sbisim_t : bind_ctx_sbisim <= (st eq).
  Proof.
    apply Coinduction, by_Symmetry.
    apply bind_ctx_sbisim_sym.
    intros R. apply (leq_bind_ctx _).
    intros t1 t2 tt k1 k2 kk.
    step in tt; destruct tt as (F & B); cbn in *.
    cbn in *; intros l u STEP.
    apply trans_bind_inv in STEP as [(H & t' & STEP & EQ) | (v & STEPres & STEP)]; cbn in *.
    - apply F in STEP as (u' & ? & STEP & EQ' & ?).
      eexists. exists l. subst. split.
      apply trans_bind_l; eauto. split; auto.
      apply (fT_T equ_clos_st).
      econstructor; [exact EQ | | reflexivity].
      apply (fTf_Tf sb).
      apply in_bind_ctx; auto.
      intros ? ? ->.
      apply (b_T sb).
      apply kk; auto.
    - apply F in STEPres as (u' & ? & STEPres & EQ' & ?). subst.
      pose proof (trans_val_inv STEPres) as EQ.
      rewrite EQ in STEPres.
      specialize (kk v v eq_refl) as [Fk Bk].
      apply Fk in STEP as (u'' & ? & STEP & EQ'' & ?); cbn in *.
      eexists. eexists. split.
      eapply trans_bind_r; cbn in *; eauto.
      split; auto.
      eapply (id_T sb); cbn; auto.
  Qed.

End bind.

Import CTree.
Import CTreeNotations.

(*|
Expliciting the reasoning rule provided by the up-to principles.
|*)
Lemma st_clo_bind (E C: Type -> Type) `{B0 -< C} (X Y : Type) :
	forall (t1 t2 : ctree E C X) (k1 k2 : X -> ctree E C Y) RR,
		t1 ~ t2 ->
    (forall x, (st RR) (k1 x) (k2 x)) ->
    st RR (t1 >>= k1) (t2 >>= k2)
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
   Proper (sbisim ==> pointwise_relation X (st RR) ==> st RR) (@bind E C X Y).
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
  Lemma vis_ctx_sbisim_t `{B0 -< C} (e : E X) : vis_ctx_sbisim e <= st.
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
    all: now eapply (b_T sb).
  Qed.

End sb_vis_ctx.
Arguments vis_ctx_sbisim_t {_ _ _ _ _} e.

Ltac __upto_vis_sbisim :=
  match goal with
    |- @sbisim _ _ ?X _ (Vis ?e _) (Vis ?e _) => apply (ft_t (vis_ctx_sbisim_t (Y := X) e)), in_vis_ctx; intros ? ? <-
  | |- body (t (@sb ?E ?C ?R _)) ?RR (Vis ?e _) (Vis ?e _) =>
      apply (ft_t (vis_ctx_sbisim_t e)), in_vis_ctx; intros ? ? <-
  | |- body (bt (@sb ?E ?C ?R _)) ?RR (Vis ?e _) (Vis ?e _) =>
      apply (fbt_bt (vis_ctx_sbisim_t e)), in_vis_ctx; intros ? ? <-
  end.

#[local] Tactic Notation "upto_vis" := __upto_vis_sbisim.

Ltac __play_sbisim := step; split; cbn; intros ? ? ?TR.

Ltac __playL_sbisim H :=
  step in H;
  let Hf := fresh "Hf" in
  destruct H as [Hf _];
<<<<<<< HEAD
  cbn in Hf; edestruct Hf as (? & ? & ?TR & ?EQ & ?);
  clear Hf; subst; [etrans |].

Ltac __eplayL_sbisim :=
  match goal with
  | h : @sbisim ?E ?C ?X _ _ _ |- _ =>
=======
  cbn in Hf; edestruct Hf as [? ?TR ?EQ];
  clear Hf; [etrans |].

Ltac __eplayL_sbisim :=
  match goal with
  | h : @sbisim ?E ?X _ _ |- _ =>
>>>>>>> master
      __playL_sbisim h
  end.

Ltac __playR_sbisim H :=
  step in H;
  let Hb := fresh "Hb" in
  destruct H as [_ Hb];
<<<<<<< HEAD
  cbn in Hb; edestruct Hb as (? & ? & ?TR & ?EQ & ?);
  clear Hb; subst; [etrans |].

Ltac __eplayR_sbisim :=
  match goal with
  | h : @sbisim ?E ?C ?X _ _ _ |- _ =>
=======
  cbn in Hb; edestruct Hb;
  clear Hb; [etrans |].

Ltac __eplayR_sbisim :=
  match goal with
  | h : @sbisim ?E ?X _ _ |- _ =>
>>>>>>> master
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

TODO: need to think more about this --- do we want more proof rules?
Do we actually need them on [sb (st R)], or something else?
|*)

Section Proof_Rules.

<<<<<<< HEAD
  Context {E C : Type -> Type}.
  Context {HasStuck : B0 -< C}.
  Context {HasTau : C1 -< C}.
  Context {X Y : Type}.

  Lemma step_sb_ret_gen (x y : X) (R : rel _ _) :
    R stuckI stuckI ->
=======
  Lemma step_sb_ret_gen E X (x y : X) (R : rel _ _) :
    R stuckD stuckD ->
>>>>>>> master
    (Proper (equ eq ==> equ eq ==> impl) R) ->
    x = y ->
    sb R (Ret x) (Ret y : ctree E C X).
  Proof.
    intros Rstuck PROP <-.
    split; cbn; intros ? ? TR; inv_trans; subst.
    all: cbn; exists stuckI; eexists; intuition; etrans.
    all: now rewrite EQ.
  Qed.

  Lemma step_sb_ret (x y : X) (R : rel _ _) :
    x = y ->
    sbt R (Ret x) (Ret y : ctree E C X).
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
    sb R (Vis e k) (Vis e k').
  Proof.
    intros PR EQs.
    split; intros ? ? TR; inv_trans; subst.
    all: cbn; eexists; eexists; intuition; etrans; rewrite EQ; auto.
  Qed.

  Lemma step_sb_vis (e : E X) (k k' : X -> ctree E C Y) (R : rel _ _) :
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
<<<<<<< HEAD
   Lemma step_sb_tauV_gen (t t' : ctree E C X) (R : rel _ _) :
    (Proper (equ eq ==> equ eq ==> impl) R) ->
    (R t t') ->
    sb R (tauV t) (tauV t').
=======
   Lemma step_sb_step_gen E X (t t' : ctree E X) (R : rel _ _) :
    (Proper (equ eq ==> equ eq ==> impl) R) ->
    (R t t') ->
    sb R (Step t) (Step t').
>>>>>>> master
  Proof.
    intros PR EQs.
    split; intros ? ? TR; inv_trans; subst.
    all: cbn; eexists; eexists; intuition; etrans; rewrite EQ; auto.
  Qed.

<<<<<<< HEAD
  Lemma step_sb_tauV (t t' : ctree E C X) (R : rel _ _) :
    (st R t t') ->
    sbt R (tauV t) (tauV t').
=======
  Lemma step_sb_step E X (t t' : ctree E X) (R : rel _ _) :
    (st R t t') ->
    sbt R (Step t) (Step t').
>>>>>>> master
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

<<<<<<< HEAD
  Lemma step_sb_choiceV_gen Z (c : C Y) (c' : C Z) (k : Y -> ctree E C X) (k' : Z -> ctree E C X) (R : rel _ _) :
    (Proper (equ eq ==> equ eq ==> impl) R) ->
    (forall x, exists y, R (k x) (k' y)) ->
    (forall y, exists x, R (k x) (k' y)) ->
    sb R (ChoiceV c k) (ChoiceV c' k').
  Proof.
    intros PROP EQs1 EQs2.
    split; intros ? ? TR; inv_trans; subst.
    - destruct (EQs1 x) as [z HR].
      eexists. eexists. intuition.
      etrans.
      rewrite EQ; eauto.
    - destruct (EQs2 x) as [y HR].
      eexists. eexists. intuition.
=======
  Lemma step_sb_brS_gen E X n m (k : fin n -> ctree E X) (k' : fin m -> ctree E X) (R : rel _ _) :
    (Proper (equ eq ==> equ eq ==> impl) R) ->
    (forall x, exists y, R (k x) (k' y)) ->
    (forall y, exists x, R (k x) (k' y)) ->
    sb R (BrS n k) (BrS m k').
  Proof.
    intros PROP EQs1 EQs2.
    split; intros ? ? TR; inv_trans; subst.
    - destruct (EQs1 x) as [y HR].
      eexists.
      etrans.
      rewrite EQ; eauto.
    - destruct (EQs2 x) as [y HR].
      eexists.
>>>>>>> master
      etrans.
      cbn; rewrite EQ; eauto.
  Qed.

<<<<<<< HEAD
  Lemma step_sb_choiceV Z (c : C Y) (c' : C Z) (k : Y -> ctree E C X) (k' : Z -> ctree E C X) (R : rel _ _) :
    (forall x, exists y, st R (k x) (k' y)) ->
    (forall y, exists x, st R (k x) (k' y)) ->
    sbt R (ChoiceV c k) (ChoiceV c' k').
=======
  Lemma step_sb_brS E X n m (k : fin n -> ctree E X) (k' : fin m -> ctree E X) (R : rel _ _) :
    (forall x, exists y, st R (k x) (k' y)) ->
    (forall y, exists x, st R (k x) (k' y)) ->
    sbt R (BrS n k) (BrS m k').
>>>>>>> master
  Proof.
    intros EQs1 EQs2.
    apply step_sb_brS_gen; auto.
    typeclasses eauto.
  Qed.

<<<<<<< HEAD
  Lemma step_sb_choiceV_id_gen (c : C Y) (k k' : Y -> ctree E C X) (R : rel _ _) :
    (Proper (equ eq ==> equ eq ==> impl) R) ->
    (forall x, R (k x) (k' x)) ->
    sb R (ChoiceV c k) (ChoiceV c k').
=======
  Lemma step_sb_brS_id_gen E X n (k k' : fin n -> ctree E X) (R : rel _ _) :
    (Proper (equ eq ==> equ eq ==> impl) R) ->
    (forall x, R (k x) (k' x)) ->
    sb R (BrS n k) (BrS n k').
>>>>>>> master
  Proof.
    intros PROP EQs.
    apply step_sb_brS_gen; auto.
    all: intros x; exists x; auto.
  Qed.

<<<<<<< HEAD
  Lemma step_sb_choiceV_id (c : C Y) (k k' : Y -> ctree E C X) (R : rel _ _) :
    (forall x, st R (k x) (k' x)) ->
    sbt R (ChoiceV c k) (ChoiceV c k').
=======
  Lemma step_sb_brS_id E X n (k k' : fin n -> ctree E X) (R : rel _ _) :
    (forall x, st R (k x) (k' x)) ->
    sbt R (BrS n k) (BrS n k').
>>>>>>> master
  Proof.
    apply step_sb_brS_id_gen.
    typeclasses eauto.
  Qed.

(*|
For invisible nodes, the situation is different: we may kill them, but that execution
cannot act as going under the guard.
|*)
<<<<<<< HEAD
  Lemma step_sb_tauI_gen (t t' : ctree E C X) (R : rel _ _) :
    sb R t t' ->
    sb R (tauI t) (tauI t').
  Proof.
    intros EQ.
    split; intros ? ? TR; inv_trans; subst.
    all: apply EQ in TR as (? & ? & ? & ? & ?).
    all: eexists; eexists; intuition; subst; [apply trans_tauI; eauto | eauto].
  Qed.

  Lemma step_sb_tauI (t t' : ctree E C X) (R : rel _ _) :
    sbt R t t' ->
    sbt R (tauI t) (tauI t').
=======
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
>>>>>>> master
  Proof.
    apply step_sb_guard_gen.
  Qed.

<<<<<<< HEAD
  Lemma step_sb_choiceI_gen Z (c : C Y) (c' : C Z) (k : Y -> ctree E C X) (k' : Z -> ctree E C X) (R : rel _ _) :
    (forall x, exists y, sb R (k x) (k' y)) ->
    (forall y, exists x, sb R (k x) (k' y)) ->
    sb R (ChoiceI c k) (ChoiceI c' k').
  Proof.
    intros EQs1 EQs2.
    split; intros ? ? TR; inv_trans; subst.
    - destruct (EQs1 x) as [z [F _]]; cbn in F.
      apply F in TR; destruct TR as (u' & ? & TR' & EQ' & ?).
      eexists. eexists. subst. intuition.
      eapply trans_choiceI with (x := z); [|reflexivity].
      eauto.
      eauto.
    - destruct (EQs2 x) as [y [_ B]]; cbn in B.
      apply B in TR; destruct TR as (u' & ? & TR' & EQ' & ?).
      eexists. eexists. subst. intuition.
      eapply trans_choiceI with (x := y); [|reflexivity].
=======
  Lemma step_sb_brD_gen E X n m (k : fin n -> ctree E X) (k' : fin m -> ctree E X) (R : rel _ _) :
    (forall x, exists y, sb R (k x) (k' y)) ->
    (forall y, exists x, sb R (k x) (k' y)) ->
    sb R (BrD n k) (BrD m k').
  Proof.
    intros EQs1 EQs2.
    split; intros ? ? TR; inv_trans; subst.
    - destruct (EQs1 x) as [y [F _]]; cbn in F.
      apply F in TR; destruct TR as [u' TR' EQ'].
      eexists.
      eapply trans_brD with (x := y); [|reflexivity].
      eauto.
      eauto.
    - destruct (EQs2 x) as [y [_ B]]; cbn in B.
      apply B in TR; destruct TR as [u' TR' EQ'].
      eexists.
      eapply trans_brD with (x := y); [|reflexivity].
>>>>>>> master
      eauto.
      eauto.
  Qed.

<<<<<<< HEAD
  Lemma step_sb_choiceI Z (c : C Y) (c' : C Z) (k : Y -> ctree E C X) (k' : Z -> ctree E C X) (R : rel _ _) :
    (forall x, exists y, sbt R (k x) (k' y)) ->
    (forall y, exists x, sbt R (k x) (k' y)) ->
    sbt R (ChoiceI c k) (ChoiceI c' k').
=======
  Lemma step_sb_brD E X n m (k : fin n -> ctree E X) (k' : fin m -> ctree E X) (R : rel _ _) :
    (forall x, exists y, sbt R (k x) (k' y)) ->
    (forall y, exists x, sbt R (k x) (k' y)) ->
    sbt R (BrD n k) (BrD m k').
>>>>>>> master
  Proof.
    apply step_sb_brD_gen.
  Qed.

<<<<<<< HEAD
  Lemma step_sb_choiceI_id_gen (c : C Y) (k k' : Y -> ctree E C X) (R : rel _ _) :
    (forall x, sb R (k x) (k' x)) ->
    sb R (ChoiceI c k) (ChoiceI c k').
=======
  Lemma step_sb_brD_id_gen {E X} n (k k' : fin n -> ctree E X) (R : rel _ _) :
    (forall x, sb R (k x) (k' x)) ->
    sb R (BrD n k) (BrD n k').
>>>>>>> master
  Proof.
    intros; apply step_sb_brD_gen.
    intros x; exists x; apply H.
    intros x; exists x; apply H.
  Qed.

<<<<<<< HEAD
  Lemma step_sb_choiceI_id (c : C Y) (k k' : Y -> ctree E C X) (R : rel _ _) :
    (forall x, sbt R (k x) (k' x)) ->
    sbt R (ChoiceI c k) (ChoiceI c k').
=======
  Lemma step_sb_brD_id {E X} n (k k' : fin n -> ctree E X) (R : rel _ _) :
    (forall x, sbt R (k x) (k' x)) ->
    sbt R (BrD n k) (BrD n k').
>>>>>>> master
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
  Context {HasTau : C1 -< C}.
  Context {X Y : Type}.

  Lemma sb_ret : forall x y,
      x = y ->
      Ret x ~ (Ret y : ctree E C X).
  Proof.
    intros * <-.
    now step.
  Qed.

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
<<<<<<< HEAD
  Lemma sb_tauI : forall (t : ctree E C X),
      tauI t ~ t.
=======
  Lemma sb_guard E X : forall (t : ctree E X),
      Guard t ~ t.
>>>>>>> master
  Proof.
    intros t; play.
    - inv_trans.
      etrans.
    - eauto 6 with trans.
  Qed.

<<<<<<< HEAD
  Lemma sb_tauI_l : forall (t u : ctree E C X),
      t ~ u ->
      tauI t ~ u.
=======
 Lemma sb_guard_l E X : forall (t u : ctree E X),
      t ~ u ->
      Guard t ~ u.
>>>>>>> master
  Proof.
    intros * EQ; now rewrite sb_guard.
  Qed.

<<<<<<< HEAD
  Lemma sb_tauI_r : forall (t u : ctree E C X),
      t ~ u ->
      t ~ tauI u.
=======
  Lemma sb_guard_r E X : forall (t u : ctree E X),
      t ~ u ->
      t ~ Guard u.
>>>>>>> master
  Proof.
    intros * EQ; now rewrite sb_guard.
  Qed.

<<<<<<< HEAD
  Lemma sb_tauI_lr : forall (t u : ctree E C X),
      t ~ u ->
      tauI t ~ tauI u.
=======
  Lemma sb_guard_lr E X : forall (t u : ctree E X),
      t ~ u ->
      Guard t ~ Guard u.
>>>>>>> master
  Proof.
    intros * EQ; now rewrite !sb_guard.
  Qed.

<<<<<<< HEAD
  Lemma sb_tauV : forall (t u : ctree E C X),
      t ~ u ->
      tauV t ~ tauV u.
  Proof.
    intros * EQ; step.
    apply @step_sb_tauV; auto.
=======
  Lemma sb_step E X : forall (t u : ctree E X),
      t ~ u ->
      Step t ~ Step u.
  Proof.
    intros * EQ; step.
    apply step_sb_step; auto.
>>>>>>> master
  Qed.


(*|
Br
|*)
  (* TODO: Double check that this is needed, it should be taus in all contexts I can think of *)
<<<<<<< HEAD
  Lemma sb_choiceI1 `{HasFin : Cn -< C} : forall (k : fin 1 -> ctree E C X),
      chooseIn k ~ k F1.
=======
  Lemma sb_brD1 E X : forall (k : fin 1 -> ctree E X),
      BrD 1 k ~ k F1.
>>>>>>> master
  Proof.
    intros; step; econstructor.
    - intros ? ? ?. inv H.
      apply Eqdep.EqdepTheory.inj_pair2 in H4; subst.
      dependent destruction x; exists t', l; etrans; auto.
      inversion x.
    - intros ? ? ?; cbn.
      eauto 6 with trans.
  Qed.

<<<<<<< HEAD
  Lemma sb_choiceV I J (ci : C I) (cj : C J)
        (k : I -> ctree E C X) (k' : J -> ctree E C X) :
    (forall x, exists y, k x ~ k' y) ->
    (forall y, exists x, k x ~ k' y) ->
    ChoiceV ci k ~ ChoiceV cj k'.
  Proof.
    intros * EQs1 EQs2; step.
    apply @step_sb_choiceV; auto.
  Qed.

  Lemma sb_choiceV_id I (c : C I)
        (k k' : I -> ctree E C X) :
    (forall x, k x ~ k' x) ->
    ChoiceV c k ~ ChoiceV c k'.
  Proof.
    intros * EQs; step.
    apply @step_sb_choiceV_id; auto.
  Qed.

  Lemma sb_choiceI I J (ci : C I) (cj : C J)
        (k : I -> ctree E C X) (k' : J -> ctree E C X) :
    (forall x, exists y, k x ~ k' y) ->
    (forall y, exists x, k x ~ k' y) ->
    ChoiceI ci k ~ ChoiceI cj k'.
  Proof.
    intros; step.
    eapply @step_sb_choiceI; auto.
=======
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
>>>>>>> master
    intros x; destruct (H x) as (y & EQ).
    exists y; now step in EQ.
    intros y; destruct (H0 y) as (x & EQ).
    exists x; now step in EQ.
  Qed.

<<<<<<< HEAD
  Lemma sb_choiceI_id I (c : C I)
        (k k' : I -> ctree E C X) :
    (forall x, k x ~ k' x) ->
    ChoiceI c k ~ ChoiceI c k'.
=======
  Lemma sb_brD_id {E X} n (k k' : fin n -> ctree E X)  :
    (forall x, k x ~ k' x) ->
    BrD n k ~ BrD n k'.
>>>>>>> master
  Proof.
    intros; step.
    apply @step_sb_brD_id; intros x.
    specialize (H x).
    now step in H.
  Qed.

<<<<<<< HEAD
  Lemma sb_choiceI_idempotent {HasFin : Cn -< C} : forall n (k: fin (S n) -> ctree E C X) t,
      (forall x, k x ~ t) ->
      chooseIn k ~ t.
  Proof.
    intros * EQ.
    rewrite <- sb_tauI with (t:=t).
    apply sb_choiceI; intros.
    exists tt; apply EQ.
    exists F1; apply EQ.
=======
  Lemma sb_brD_idempotent E X n: forall (k: fin (S n) -> ctree E X) t,
      (forall x, k x ~ t) ->
      BrD (S n) k ~ t.
  Proof.
    intros * EQ.
    rewrite <- sb_guard with (t:=t).
    apply sb_brD; intros; exists F1; apply EQ.
>>>>>>> master
  Qed.

End Sb_Proof_System.

<<<<<<< HEAD
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
<<<<<<< HEAD
  Lemma spinV_gen_nonempty : forall {Z X Y} (c: C X) (c': C Y) (x: X) (y: Y), @spinV_gen E C Z X c ~ spinV_gen c'.
  Proof.
    intros R.
    coinduction S CIH; symmetric.
    intros * ? ? l p' TR.
    rewrite ctree_eta in TR; cbn in TR.
    apply trans_choiceV_inv in TR as (_ & EQ & ->).
    eexists. eexists.
    rewrite ctree_eta; cbn.
    split; [econstructor |]. exact y.
    reflexivity.
    rewrite EQ; eauto.
  Qed.

  Lemma spinI_gen_bisim : forall {Z X Y} (c: C X) (c': C Y),
      @spinI_gen E C Z X c ~ spinI_gen c'.
  Proof.
    intros R.
    coinduction S _; symmetric.
    cbn; intros * TR.
    exfalso; eapply spinI_gen_is_stuck, TR.
  Qed.
=======
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
>>>>>>> master

(*|
BrD2 is associative, commutative, idempotent, merges into BrD3, and admits _a lot_ of units.
|*)
<<<<<<< HEAD

  Lemma chooseI2_assoc {X} : forall (t u v : ctree E C X),
	    chooseI2 (chooseI2 t u) v ~ chooseI2 t (chooseI2 u v).
  Proof.
    intros.
    play; inv_trans; eauto 7 with trans.
  Qed.

  Lemma chooseI2_commut {X} : forall (t u : ctree E C X),
	    chooseI2 t u ~ chooseI2 u t.
  Proof.
=======
Lemma brD2_assoc {E X} : forall (t u v : ctree E X),
	  brD2 (brD2 t u) v ~ brD2 t (brD2 u v).
Proof.
  intros.
  play; inv_trans; etrans.
Qed.

Lemma brD2_commut {E X} : forall (t u : ctree E X),
	  brD2 t u ~ brD2 u t.
Proof.
>>>>>>> master
(*|
Note: could use a symmetry argument here as follows to only play one direction of the game.
[coinduction ? _; symmetric.]
but automation just handles it...
|*)
    intros.
    play; inv_trans; eauto 6 with trans.
  Qed.

<<<<<<< HEAD
  Lemma chooseI2_idem {X} : forall (t : ctree E C X),
	    chooseI2 t t ~ t.
  Proof.
    intros.
    play; inv_trans; eauto 6 with trans.
  Qed.

  Lemma chooseI2_merge {X} : forall (t u v : ctree E C X),
	    chooseI2 (chooseI2 t u) v ~ chooseI3 t u v.
  Proof.
    intros.
    play; inv_trans; eauto 7 with trans.
  Qed.

  Lemma chooseI2_is_stuck {X} : forall (u v : ctree E C X),
      is_stuck u ->
	    chooseI2 u v ~ v.
  Proof.
    intros * ST.
    play.
    - inv_trans.
      exfalso; eapply ST, TR. (* automate stuck transition trying to step? *)
      exists t', l; eauto.             (* automate trivial case *)
    - eauto 6 with trans.
  Qed.

  Lemma chooseI2_stuckV_l {X} : forall (t : ctree E C X),
	    chooseI2 stuckV t ~ t.
  Proof.
    intros; apply chooseI2_is_stuck, stuckV_is_stuck.
  Qed.

  Lemma chooseI2_stuckI_l {X} : forall (t : ctree E C X),
	    chooseI2 stuckI t ~ t.
  Proof.
    intros; apply chooseI2_is_stuck, stuckI_is_stuck.
  Qed.

  Lemma chooseI2_stuckV_r {X} : forall (t : ctree E C X),
	    chooseI2 t stuckV ~ t.
  Proof.
    intros; rewrite chooseI2_commut; apply chooseI2_stuckV_l.
  Qed.

  Lemma chooseI2_stuckI_r {X} : forall (t : ctree E C X),
	    chooseI2 t stuckI ~ t.
  Proof.
    intros; rewrite chooseI2_commut; apply chooseI2_stuckI_l.
  Qed.

  Lemma chooseI2_spinI_l {X} : forall (t : ctree E C X),
	    chooseI2 spinI t ~ t.
  Proof.
    intros; apply chooseI2_is_stuck, spinI_is_stuck.
  Qed.

  Lemma chooseI2_spinI_r {X} : forall (t : ctree E C X),
	    chooseI2 t spinI ~ t.
  Proof.
    intros; rewrite chooseI2_commut; apply chooseI2_is_stuck, spinI_is_stuck.
  Qed.
=======
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
    exfalso; eapply ST, TR. (* automate stuck transition trying to step? *)
    exists t'; auto.             (* automate trivial case *)
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
>>>>>>> master

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

<<<<<<< HEAD
(*|
 For the next few lemmas, we need to know that [X] is inhabited in order to
 take a step
|*)
  Lemma sbisim_vis_inv_type {X X1 X2}
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

  Lemma sbisim_ChoiceV_inv {X Y Z}
        c1 c2 (k1 : X -> ctree E C Z) (k2 : Y -> ctree E C Z) :
    ChoiceV c1 k1 ~ ChoiceV c2 k2 ->
    (forall i1, exists i2, k1 i1 ~ k2 i2).
  Proof.
    intros EQ i1.
=======
(** For the next few lemmas, we need to know that [X] is inhabited in order to
    take a step *)
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
>>>>>>> master
    eplayL.
    inv_trans.
    eexists; eauto.
  Qed.

<<<<<<< HEAD
  Notation inhabited X := (exists x: X, True).

(*|
Annoying case: [Vis e k ~ ChoiceV c k'] is true if [e : E void] and [c : C void].
We rule out this case in this definition.
|*)
  Definition are_bisim_incompat {X} (t u : ctree E C X) : Type :=
    match observe t, observe u with
    | RetF _, RetF _
    | VisF _ _, VisF _ _
    | ChoiceF true _ _, ChoiceF true _ _
    | ChoiceF false _ _, _
    | _, ChoiceF false _ _ => False
    | ChoiceF true n _, RetF _ => True
    | RetF _,  ChoiceF true n _ => True
    | @ChoiceF _ _ _ _ X true _ _, @VisF _ _ _ _ Y _ _ =>
        inhabited X \/ inhabited Y
    | @VisF _ _ _ _ Y _ _, @ChoiceF _ _ _ _ X true _ _ =>
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
=======
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
>>>>>>> master

  Ltac sb_abs h :=
    eapply sbisim_absurd; [| eassumption]; cbn; try reflexivity.

  Lemma sbisim_ret_vis_inv {X Y}(r : Y) (e : E X) (k : X -> ctree E C Y) :
    Ret r ~ Vis e k -> False.
  Proof.
    intros * abs. sb_abs abs.
  Qed.

<<<<<<< HEAD
  Lemma sbisim_ret_ChoiceV_inv {X Y} (r : Y) (c : C X) (k : X -> ctree E C Y) :
    Ret r ~ ChoiceV c k -> False.
  Proof.
    intros * abs; sb_abs abs.
  Qed.
=======
Lemma sbisim_ret_BrS_inv {E R} (r : R) n (k : fin n -> ctree E R) :
  Ret r ~ BrS n k -> False.
Proof.
  intros * abs; sb_abs abs.
Qed.
>>>>>>> master

(*|
For this to be absurd, we need one of the return types to be inhabited.
|*)
<<<<<<< HEAD
  Lemma sbisim_vis_ChoiceV_inv {X Y Z}
        (e : E X) (k1 : X -> ctree E C Z) (c : C Y) k2 (y : Y) :
    Vis e k1 ~ ChoiceV c k2 -> False.
  Proof.
    intros * abs.
    sb_abs abs. eauto.
  Qed.

  Lemma sbisim_vis_ChoiceV_inv' {X Y Z}
        (e : E X) (k1 : X -> ctree E C Z) (c : C Y) k2 (x : X) :
    Vis e k1 ~ ChoiceV c k2 -> False.
  Proof.
    intros * abs.
    sb_abs abs. eauto.
  Qed.
=======
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
>>>>>>> master

(*|
Not fond of these two, need to give some thoughts about them
|*)
<<<<<<< HEAD
  Lemma sbisim_ret_ChoiceI_inv {X Y} (r : Y) (c : C X) (k : X -> ctree E C Y) :
    Ret r ~ ChoiceI c k ->
    exists x, Ret r ~ k x.
  Proof.
    intro. step in H. destruct H as [Hf Hb]. cbn in *.
    edestruct Hf as (x & ? & Ht & Hs & ?); [apply trans_ret |].
    apply trans_choiceI_inv in Ht.
    destruct Ht as [i Ht]. exists i.
    step. split.
    - repeat intro. inv H0. exists x, (val r). split; intuition. rewrite <- Hs.
      rewrite ctree_eta. rewrite <- H4. rewrite choice0_always_stuck. reflexivity.
    - repeat intro. eapply trans_choiceI in H0; eauto. specialize (Hb _ _ H0).
      destruct Hb as (? & ? & ? & ? & ?). subst. inv H1. exists stuckI, (val r).
      intuition.
      cbn. rewrite <- H2. symmetry. rewrite ctree_eta.
      rewrite <- H5. rewrite choice0_always_stuck. auto.
  Qed.

(* Lemma sbisim_ChoiceI_Tau_inv {X} (k : fin 1 -> ctree E C R) t x : *)
(*   ChoiceI (subevent _ Tau) k ~ t -> *)
(*   k x ~ t. *)
(* Proof. *)
(*   intro. step in H. step. destruct H. cbn in *. split; repeat intro. *)
(*   - apply H. econstructor; apply H1. *)
(*   - edestruct H0. apply H1. exists x0; auto. *)
(*     inv H2. apply Eqdep.EqdepTheory.inj_pair2 in H7, H8. subst. *)
(*     assert (x = x1). *)
(*     { *)
(*       clear H H0 H1 H3 H9 l t' x0 t k E R. *)
(*       remember 1%nat. *)
(*       destruct x. *)
(*       - dependent destruction x1; auto. *)
(*         inv Heqn. inv x1. *)
(*       - inv Heqn. inv x. *)
(*     } *)
(*     subst. auto. *)
(* Qed. *)

End WithParams.
=======
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
>>>>>>> master
