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
From Stdlib Require Import
  Lia
  Basics
  Fin
  RelationClasses
  Program.Equality
  Logic.Eqdep.

From Coinduction Require Import all.

From ITree Require Import Core.Subevent.

From CTree Require Import
  CTree
  Utils
  Eq.Equ
  Eq.Shallow
  Eq.Trans
  Eq.SSim
  Eq.CSSim.

From RelationAlgebra Require Export
  rel srel.

Import CoindNotations.
Set Implicit Arguments.
Import CTree.
Import CTreeNotations.
Import EquNotations.

(* TODO: Decide where to set this *)
Arguments trans : simpl never.

(*|
Strong Bisimulation
-------------------
Relation relaxing [equ] to become insensitive to:
- the amount of _invisible_ brs taken;
- the particular branches taken during (any kind of) brs.
|*)

Section StrongBisim.
  Context {E F C D : Type -> Type} {X Y : Type}.
  Notation S := (ctree E C X).
  Notation S' := (ctree F D Y).

(*|
In the heterogeneous case, the relation is not symmetric.
|*)
  Program Definition sb L : mon (S -> S' -> Prop) :=
    {| body R t u := ss L R t u /\ ss (flip L) (flip R) u t |}.
  Next Obligation.
    split; intros; [edestruct H0 as (? & ? & ?) | edestruct H1 as (? & ? & ?)]; eauto; eexists; eexists; intuition; eauto.
  Qed.

  #[global] Instance Lequiv_sb_goal :
    Proper (Lequiv X Y ==> leq) sb.
  Proof.
    cbn -[sb]. split.
    - destruct H0 as [? _]. eapply Lequiv_ss_goal. apply H. apply H0.
    - destruct H0 as [_ ?]. eapply Lequiv_ss_goal with (x := flip x).
      red. cbn. intros. now apply H. apply H0.
  Qed.

  #[global] Instance weq_sb :
    Proper (weq ==> weq) sb.
  Proof.
    cbn -[weq]. split; intro.
    - eapply Lequiv_sb_goal. apply weq_Lequiv. apply H. auto.
    - eapply Lequiv_sb_goal. apply weq_Lequiv. symmetry. apply H. auto.
  Qed.

End StrongBisim.

Definition sbisim {E F C D X Y} L :=
  (gfp (@sb E F C D X Y L) : hrel _ _).

#[global] Instance Lequiv_sbisim : forall {E F C D X Y},
    Proper (Lequiv X Y ==> leq) (@sbisim E F C D X Y).
Proof.
  cbn. intros.
  - unfold sbisim.
    epose proof (gfp_leq (x := sb x) (y := sb y)). lapply H1.
    + intro. red in H2. cbn in H2. apply H2. apply H0.
    + now rewrite H.
Qed.

#[global] Instance weq_sbisim : forall {E F C D X Y},
    Proper (weq ==> weq) (@sbisim E F C D X Y).
Proof.
  cbn -[ss weq]. intros. apply gfp_weq. now apply weq_sb.
Qed.

(* This instance allows to use the symmetric tactic from coq-coinduction
   for homogeneous bisimulations *)
#[global] Instance sbisim_sym {E C X L} :
  Symmetric L ->
  Symmetrical converse (@sb E E C C X X L) (@ss E E C C X X L).
Proof.
  intros SYM. split; intro.
  - destruct H. split.
    + apply H.
    + cbn. intros. apply H0 in H1 as (? & ? & ? & ? & ?). apply SYM in H3. eauto.
  - destruct H. split.
    + apply H.
    + cbn. intros. apply H0 in H1 as (? & ? & ? & ? & ?). apply SYM in H3. eauto.
Qed.

Module SBisimNotations.

(*|
sb (bisimulation) notation
|*)
  Notation "t ~ u" := (sbisim eq t u) (at level 70).
  Notation "t (~ L ) u" := (sbisim L t u) (at level 70).
  Notation "t {{ ~ L }} u" := (sb L _ t u) (at level 79).
  Notation "t {{~}} u" := (sb eq _ t u) (at level 79).

End SBisimNotations.

Import SBisimNotations.

Ltac fold_sbisim :=
  repeat
    match goal with
    | h: context[gfp (@sb ?E ?F ?C ?D ?X ?Y ?L)] |- _  => fold (@sbisim E F C D X Y L) in h
    | |- context[gfp (@sb ?E ?F ?C ?D ?X ?Y ?L)]       => fold (@sbisim E F C D X Y L)
    end.

Tactic Notation "__step_sbisim" :=
  match goal with
  | |- context[@sbisim ?E ?F ?C ?D ?X ?Y ?LR] =>
      unfold sbisim;
      step;
      fold (@sbisim E F C D X Y L)
  end.
#[local] Tactic Notation "step" := __step_sbisim || __step_ssim || __step_cssim || step.

Ltac __step_in_sbisim H :=
  match type of H with
  | context [@sbisim ?E ?F ?C ?D ?X ?Y ?L] =>
      unfold sbisim in H;
      step in H;
      fold (@sbisim E F C D X Y L) in H
  end.
#[local] Tactic Notation "step" "in" ident(H) := __step_in_sbisim H || step in H.

Tactic Notation "__coinduction_sbisim" simple_intropattern(r) simple_intropattern(cih) :=
  first [unfold sbisim at 4 | unfold sbisim at 3 | unfold sbisim at 2 | unfold sbisim at 1]; coinduction r cih.
#[local] Tactic Notation "coinduction" simple_intropattern(r) simple_intropattern(cih) :=
  __coinduction_sbisim r cih || __coinduction_cssim r cih || __coinduction_ssim r cih || coinduction r cih.

(*|
  This section should describe lemmas proved for the
  heterogenous version of `css`, parametric on
  - Return types X, Y
  - Label types E, F
  - Branch effects C, D
|*)
Section sbisim_heterogenous_theory.

  Arguments label: clear implicits.
  Context {E F C D : Type -> Type} {X Y : Type}
    {L: rel (@label E) (@label F)}.

  Notation sb := (@sb E F C D X Y).
  Notation sbisim := (@sbisim E F C D X Y).

(*|
Strong bisimulation up-to [equ] is valid
----------------------------------------
|*)
  Lemma equ_clos_sb {c: Chain (sb L)}:
    forall x y, equ_clos `c x y -> `c x y.
  Proof.
    apply tower.
    - intros ? INC x y [x' y' x'' y'' EQ' EQ''] ??. red.
      apply INC; auto.
      econstructor; eauto.
      apply leq_infx in H.
      now apply H.
    - clear.
      intros c IH x y []; split.
      + intros l z x'z.
        rewrite Equt in x'z.
        apply HR in x'z as (? & ? & ? & ? & ?).
        do 2 eexists; intuition; eauto.
        rewrite <- Equu; eauto.
      + intros l z x'z.
        rewrite <- Equu in x'z.
        apply HR in x'z as (? & ? & ? & ? & ?).
        do 2 eexists; intuition; eauto.
        rewrite Equt; eauto.
  Qed.

(*|
    Aggressively providing instances for rewriting [equ] under all [sb]-related
    contexts.
|*)
  #[global] Instance equ_clos_sb_goal {c: Chain (sb L)} :
    Proper (equ eq ==> equ eq ==> flip impl) `c.
  Proof.
    cbn; intros ? ? eq1 ? ? eq2 H.
    apply equ_clos_sb; econstructor; [eauto | | symmetry; eauto]; assumption.
  Qed.

  #[global] Instance equ_clos_sb_ctx  {c: Chain (sb L)} :
    Proper (equ eq ==> equ eq ==> impl) `c.
  Proof.
    cbn; intros ? ? eq1 ? ? eq2 H.
    apply equ_clos_sb; econstructor; [symmetry; eauto | | eauto]; assumption.
  Qed.

  #[global] Instance equ_sb_closed_goal {r} : Proper (@equ E C X X eq ==> @equ F D Y Y eq ==> flip impl) (sb L r).
  Proof.
    intros t t' tt' u u' uu'.
    split.
    rewrite tt', uu'; apply H.
    rewrite tt', uu'; apply H.
  Qed.

  #[global] Instance equ_sb_closed_ctx {r} : Proper (@equ E C X X eq ==> @equ F D Y Y eq ==> impl) (sb L r).
  Proof.
    cbn -[sb]. intros. now subs.
  Qed.

(*|
Up-to-bisimulation enhancing function
|*)
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

(*|
stuck ctrees can be simulated by anything.
|*)
  Lemma is_stuck_sb (R : rel _ _) (t : ctree E C X) (t': ctree F D Y):
    is_stuck t -> is_stuck t' -> sb L R t t'.
  Proof.
    split; repeat intro.
    - now apply H in H1.
    - now apply H0 in H1.
  Qed.

  Lemma sbisim_clos_sb {c: Chain (sb L)}:
    forall x y, @sbisim_clos eq eq `c x y -> `c x y.
  Proof.
    apply tower.
    - intros ? INC x y [x' y' x'' y'' EQ' EQ''] ??. red.
      apply INC; auto.
      econstructor; eauto.
      apply leq_infx in H.
      now apply H.
    - clear.
      intros c IH x y []; split; intros ? ? TR.
      + destruct HR as [fwd bckd].
        step in Sbisimt; apply Sbisimt in TR; destruct TR as (? & ? & TR & Sbis & <-).
        apply fwd in TR; destruct TR as (? & ? & TR & Sbis' & HL).
        step in Sbisimu; apply Sbisimu in TR; destruct TR as (? & ? & TR & Sbis'' & <-).
        do 2 eexists; repeat split; eauto.
        apply IH.
        econstructor; eauto.
      + destruct HR as [fwd bwd].
        step in Sbisimu; apply Sbisimu in TR; destruct TR as (? & ? & TR & Sbis & <-).
        apply bwd in TR; destruct TR as (? & ? & TR & Sbis' & HL).
        step in Sbisimt; apply Sbisimt in TR; destruct TR as (? & ? & TR & Sbis'' & <-).
        do 2 eexists; repeat split; eauto.
        apply IH.
        econstructor; eauto.
  Qed.

  Lemma sbisim_cssim_subrelation_gen : forall x y, sbisim L x y -> cssim L x y.
  Proof.
    red.
    coinduction r cih; intros * SB.
    step in SB; destruct SB as [fwd bwd].
    split.
    - intros ?? TR; apply fwd in TR as (? & ? & ? & ? & ?); eauto 10.
    - intros ?? TR; apply bwd in TR as (? & ? & ? & ? & ?); eauto 10.
  Qed.

  Lemma sbisim_ssim_subrelation_gen : forall x y, sbisim L x y -> ssim L x y.
  Proof.
    now intros; apply cssim_ssim_subrelation_gen, sbisim_cssim_subrelation_gen.
  Qed.

End sbisim_heterogenous_theory.

Section sbisim_homogenous_theory.
  Context {E B: Type -> Type} {X: Type} (L: relation (@label E)).

  Notation sb  := (@sb E E B B X X).
  Notation sbisim := (@sbisim E E B B X X).

  #[global] Instance refl_sb {LR: Reflexive L} {C: Chain (sb L)}: Reflexive `C.
  Proof.
    apply Reflexive_chain.
    cbn; intros; split; intros * TR; do 2 eexists; eauto.
  Qed.

  #[global] Instance sb_sym {R} :
    Symmetric L ->
    Symmetric R ->
    Symmetric (sb L R).
  Proof.
    intros SYM SYM'. split; cbn; intros.
    - destruct H as [_ ?]. cbn in H.
      apply H in H0 as (? & ? & ? & ? & ?). eauto 7.
    - destruct H as [? _]. cbn in H.
      apply H in H0 as (? & ? & ? & ? & ?). eauto 7.
  Qed.

  #[global] Instance sym_sb {LT: Symmetric L} {C: Chain (sb L)}: Symmetric `C.
  Proof.
    apply Symmetric_chain.
    cbn; intros * HS * [fwd bwd]; split; intros ?? TR.
    - destruct (bwd _ _ TR) as (l' & y' & yy' & ? & ?); eauto 8.
    - destruct (fwd _ _ TR) as (l' & y' & yy' & ? & ?); eauto 8.
  Qed.

  #[global] Instance square_sb {LT: Transitive L} {C: Chain (sb L)}: Transitive `C.
  Proof.
    apply Transitive_chain.
    cbn. intros ????? [xy xy'] [yz yz']; split; intros ?? xx'.
    - destruct (xy _ _ xx') as (l' & y' & yy' & ? & ?).
      destruct (yz _ _ yy') as (l'' & z' & zz' & ? & ?).
      eauto 8.
    - destruct (yz' _ _ xx') as (l' & y' & yy' & ? & ?).
      destruct (xy' _ _ yy') as (l'' & z' & zz' & ? & ?).
      eauto 8.
  Qed.

(*| PreOrder |*)
  #[global] Instance Equivalence_sb {LPO: Equivalence L} {C: Chain (sb L)}: Equivalence `C.
  Proof. split; typeclasses eauto. Qed.

(*|
Hence [equ eq] is a included in [sbisim]
|*)
  #[global] Instance equ_sbisim_subrelation `{EqL: Equivalence _ L} : subrelation (equ eq) (sbisim L).
  Proof.
    red; intros.
    rewrite H; reflexivity.
  Qed.

  #[global] Instance is_stuck_sbisim : Proper (sbisim L ==> flip impl) is_stuck.
  Proof.
    cbn. intros ???????.
    step in H. destruct H as [? _].
    apply H in H1 as (? & ? & ? & ? & ?). now apply H0 in H1.
  Qed.

  #[global] Instance sbisim_cssim_subrelation : subrelation (sbisim L) (cssim L).
  Proof.
    red; apply sbisim_cssim_subrelation_gen.
  Qed.

  #[global] Instance sbisim_ssim_subrelation : subrelation (sbisim L) (ssim L).
  Proof.
    red; apply sbisim_ssim_subrelation_gen.
  Qed.

End sbisim_homogenous_theory.

(*|
Up-to [bind] context bisimulations
----------------------------------
We have proved in the module [Equ] that up-to bind context is
a valid enhancement to prove [equ].
We now prove the same result, but for strong and weak bisimulation.
|*)

Section bind.
  Obligation Tactic := trivial.
  Arguments label: clear implicits.
  Context {E F C D: Type -> Type} {X X' Y Y': Type}
    {L: rel (label E) (label F)} (R0 : rel X Y).

  Lemma bind_chain_gen
    (RR : rel (label E) (label F))
    (ISVR : is_update_val_rel L R0 RR)
    {R : Chain (@sb E F C D X' Y' L)} :
    forall (t : ctree E C X) (t' : ctree F D Y) (k : X -> ctree E C X') (k' : Y -> ctree F D Y'),
      sbisim RR t t' ->
      (forall x x', R0 x x' -> ` R (k x) (k' x')) ->
      ` R (bind t k) (bind t' k').
  Proof.
    apply tower.
    - intros ? INC ? ? ? ? tt' kk' ? ?.
      apply INC. apply H. apply tt'.
      intros x x' xx'. apply leq_infx in H. apply H. now apply kk'.
    - intros ? ? ? ? ? ? tt' kk'.
      step in tt'; destruct tt' as [fwd bwd].
      split; cbn; intros * STEP.
      + apply trans_bind_inv in STEP as [(?H & ?t' & STEP & EQ) | (v & STEPres & STEP)].
        * apply fwd in STEP as (? & ? & ? & ? & ?).
          do 2 eexists; split; [| split].
          apply trans_bind_l; eauto.
          ++ intro Hl. destruct Hl.
             apply ISVR in H3; etrans.
             inversion H3; subst. apply H0. constructor. apply H5. constructor.
          ++ rewrite EQ.
             apply H.
             apply H2.
             intros * HR.
             now apply (b_chain x), kk'.
          ++ apply ISVR in H3; etrans.
             destruct H3. exfalso. apply H0. constructor. eauto.
        * apply fwd in STEPres as (u' & ? & STEPres & EQ' & ?).
          apply ISVR in H0; etrans.
          dependent destruction H0.
          2 : exfalso; apply H0; constructor.
          pose proof (trans_val_inv STEPres) as EQ.
          rewrite EQ in STEPres.
          specialize (kk' v v2 H0).
          apply kk' in STEP as (u'' & ? & STEP & EQ'' & ?); cbn in *.
          do 2 eexists; split.
          eapply trans_bind_r; eauto.
          split; auto.
      + apply trans_bind_inv in STEP as [(?H & ?t' & STEP & EQ) | (v & STEPres & STEP)].
        * apply bwd in STEP as (? & ? & ? & ? & ?).
          do 2 eexists; split; [| split].
          apply trans_bind_l; eauto.
          ++ intro Hl. destruct Hl.
             apply ISVR in H3; etrans.
             inversion H3; subst. apply H0. constructor. apply H4. constructor.
          ++ rewrite EQ.
             apply H.
             apply H2.
             intros * HR.
             now apply (b_chain x), kk'.
          ++ apply ISVR in H3; etrans.
             destruct H3. exfalso. apply H0. constructor. eauto.
        * apply bwd in STEPres as (u' & ? & STEPres & EQ' & ?).
          apply ISVR in H0; etrans.
          dependent destruction H0.
          2 : exfalso; apply H1; constructor.
          pose proof (trans_val_inv STEPres) as EQ.
          rewrite EQ in STEPres.
          specialize (kk' v1 v H0).
          apply kk' in STEP as (u'' & ? & STEP & EQ'' & ?); cbn in *.
          do 2 eexists; split.
          eapply trans_bind_r; eauto.
          split; auto.
  Qed.

End bind.

(*|
Expliciting the reasoning rule provided by the up-to principles.
|*)
Lemma sbisim_clo_bind_gen {E F C D: Type -> Type} {X Y X' Y': Type} {L : rel (@label E) (@label F)}
  (R0 : rel X Y) L0
  (t1 : ctree E C X) (t2: ctree F D Y)
  (HL0 : is_update_val_rel L R0 L0)
  (k1 : X -> ctree E C X') (k2 : Y -> ctree F D Y') :
  t1 (~L0) t2 ->
  (forall x y, R0 x y -> k1 x (~L) k2 y) ->
  t1 >>= k1 (~L) t2 >>= k2.
Proof.
  now apply bind_chain_gen.
Qed.

Lemma sbisim_clo_bind {E F C D: Type -> Type} {X Y X' Y': Type} {L : rel (@label E) (@label F)}
  (R0 : rel X Y)
  (t1 : ctree E C X) (t2: ctree F D Y)
  (k1 : X -> ctree E C X') (k2 : Y -> ctree F D Y') :
  t1 (~update_val_rel L R0) t2 ->
  (forall x y, R0 x y -> k1 x (~L) k2 y) ->
  t1 >>= k1 (~L) t2 >>= k2.
Proof.
  now apply bind_chain_gen.
Qed.

Lemma sb_clo_bind_eq {E C} {X Y}
  (t1 t2 : ctree E C X)
  k1 k2
  {R : Chain (@sb E E C C Y Y eq)} :
  t1 ~ t2 ->
  (forall x, ` R (k1 x) (k2 x)) ->
  `R (t1 >>= k1) (t2 >>= k2).
Proof.
  intros; eapply bind_chain_gen with (R0 := eq); eauto.
  apply update_val_rel_eq.
  now intros ??->.
Qed.

Lemma sbisim_clo_bind_eq {E C D: Type -> Type} {X X': Type}
  (t1 : ctree E C X) (t2: ctree E D X)
  (k1 : X -> ctree E C X') (k2 : X -> ctree E D X') :
  t1 ~ t2 ->
  (forall x, k1 x ~ k2 x) ->
  t1 >>= k1 ~ t2 >>= k2.
Proof.
  intros; eapply sbisim_clo_bind_gen with (R0 := eq); eauto.
  apply update_val_rel_eq.
  now intros ??->.
Qed.

(*|
And in particular, we get the proper instance justifying rewriting [~] to the left of a [bind].
|*)
#[global] Instance bind_sbisim_cong_gen {E C X Y}
  {R : Chain (@sb E E C C Y Y eq)} :
  Proper (sbisim eq ==> pointwise_relation X (`R) ==> `R) (@bind E C X Y).
Proof.
  cbn; intros; eapply sb_clo_bind_eq; auto.
Qed.

#[global] Instance bind_sbisim_cong {E C X Y} :
  Proper (sbisim eq ==> pointwise_relation X (sbisim eq) ==> sbisim eq) (@bind E C X Y).
Proof.
  cbn; intros; eapply sb_clo_bind_eq; auto.
Qed.

Lemma sbisim_bind_eq {E C: Type -> Type} {X X': Type}
  (t : ctree E C X)
  (k1 : X -> ctree E C X') (k2 : X -> ctree E C X') :
  (forall x, k1 x ~ k2 x) ->
  t >>= k1 ~ t >>= k2.
Proof.
  intros; eapply sbisim_clo_bind_gen with (R0 := eq); eauto.
  apply update_val_rel_eq.
  now intros ??->.
Qed.

Lemma sb_chain_bind_eq {E C} {X Y}
  (t : ctree E C X) k1 k2
  {R : Chain (@sb E E C C Y Y eq)} :
  (forall x, elem R (k1 x) (k2 x)) ->
  elem R (t >>= k1) (t >>= k2).
Proof.
  intros; eapply SBisim.bind_chain_gen with (R0 := eq); eauto.
  apply update_val_rel_eq.
  now intros ??->.
Qed.

Lemma sb_chain_bind
  {E F C D: Type -> Type} {X Y X' Y': Type} {L : rel (@label E) (@label F)}
  (R0 : rel X Y)
  {R : Chain (@sb E F C D X' Y' L)} :
  forall (t : ctree E C X) (t' : ctree F D Y) (k : X -> ctree E C X') (k' : Y -> ctree F D Y'),
    t (~update_val_rel L R0) t' ->
    (forall x x', R0 x x' -> elem R (k x) (k' x')) ->
    elem R (bind t k) (bind t' k').
Proof.
  intros.
  eapply SBisim.bind_chain_gen; eauto.
  apply update_val_rel_correct.
Qed.

Ltac __upto_bind_sbisim' R :=
  first [apply sbisim_clo_bind with (R0 := R) |
          apply sb_chain_bind with (R0 := R)].
Tactic Notation "__upto_bind_sbisim" uconstr(t) := __upto_bind_sbisim' t.

Ltac __eupto_bind_sbisim :=
  first [eapply sbisim_clo_bind | eapply sb_chain_bind].

Ltac __upto_bind_sbisim_eq :=
  first [apply sbisim_bind_eq | apply sb_chain_bind_eq].

Lemma vis_chain_gen {E F C D: Type -> Type} {X X' Y Y': Type} L
  {R : Chain (@sb E F C D X' Y' L)} :
  forall (e : E X) (e' : F Y) (k : X -> ctree E C X') (k' : Y -> ctree F D Y')
    (right : X -> Y) (left : Y -> X),
    (forall x, L (obs e x) (obs e' (right x))) ->
    (forall y, L (obs e (left y)) (obs e' y)) ->
    (forall x, ` R (k x) (k' (right x))) ->
    (forall x', ` R (k (left x')) (k' x')) ->
    ` R (Vis e k) (Vis e' k').
Proof.
  intros.
  apply (b_chain R).
  split; intros ?? TR; inv_trans; subst.
  do 2 eexists; intuition; eauto.
  rewrite EQ; auto.
  do 2 eexists; intuition; eauto.
  rewrite EQ; apply H2.
  apply H0.
Qed.

Lemma vis_chain {E C X Y}
  {R : Chain (@sb E E C C X X eq)} :
  forall (e : E Y) (k : Y -> ctree E C X) (k' : Y -> ctree E C X),
    (forall x, ` R (k x) (k' x)) ->
    ` R (Vis e k) (Vis e k').
Proof.
  intros. eapply vis_chain_gen with (left := fun x => x) (right := fun x => x); auto.
Qed.

Ltac __play_sbisim := step; split; cbn; intros ? ? ?TR.

Ltac __playL_sbisim H :=
  step in H;
  let Hf := fresh "Hf" in
  destruct H as [Hf _];
  cbn in Hf; edestruct Hf as (? & ? & ?TR & ?EQ & ?);
  clear Hf; subst; [etrans |].

Ltac __eplayL_sbisim :=
  match goal with
  | h : @sbisim ?E _ ?C _ ?X _ ?RR _ _ |- _ =>
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
  | h : @sbisim ?E _ ?C _ ?X _ ?RR _ _ |- _ =>
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

  Arguments label : clear implicits.
  Context {E F C D : Type -> Type} {X Y: Type} {L : rel (label E) (label F)}.

  Lemma step_sb_ret_gen
    (x: X) (y: Y) (R : rel (ctree E C X) (ctree F D Y)) :
    R Stuck Stuck ->
    L (val x) (val y) ->
    (Proper (equ eq ==> equ eq ==> impl) R) ->
    sb L R (Ret x) (Ret y).
  Proof.
    intros Rstuck ValRefl PROP.
    split; apply step_ss_ret_gen; eauto.
    typeclasses eauto.
  Qed.

  Lemma step_sb_ret (x: X) (y: Y)
    {R : Chain (@sb E F C D X Y L)} :
    L (val x) (val y) ->
    sb L `R (Ret x) (Ret y).
  Proof.
    intros LH; subst.
    apply step_sb_ret_gen; eauto.
    - apply (b_chain R); split; apply is_stuck_sb; apply Stuck_is_stuck.
    - typeclasses eauto.
  Qed.

  Lemma sbisim_ret (x: X) (y: Y) :
    L (val x) (val y) ->
    @sbisim E F C D _ _ L (Ret x) (Ret y).
  Proof.
    intros. step. now apply step_sb_ret.
  Qed.

(*|
  The vis nodes are deterministic from the perspective of the labeled transition system,
  stepping is hence symmetric and we can just recover the itree-style rule.
|*)
  Lemma step_sb_vis_gen {X' Y'} (e: E X') (f: F Y')
    (k: X' -> ctree E C X) (k': Y' -> ctree F D Y) {R : rel _ _}:
    (Proper (equ eq ==> equ eq ==> impl) R) ->
    (forall x, exists y, R (k x) (k' y) /\ L (obs e x) (obs f y)) ->
    (forall y, exists x, R (k x) (k' y) /\ L (obs e x) (obs f y)) ->
    sb L R (Vis e k) (Vis f k').
  Proof.
    intros PR EQs EQs'.
    split; apply step_ss_vis_gen; eauto.
    typeclasses eauto.
  Qed.

  Lemma step_sb_vis {X' Y'}
    (e: E X') (f: F Y') (k: X' -> ctree E C X) (k': Y' -> ctree F D Y)
    {R : Chain (@sb E F C D X Y L)} :
    (forall x, exists y, ` R (k x) (k' y) /\ L (obs e x) (obs f y)) ->
    (forall y, exists x, ` R (k x) (k' y) /\ L (obs e x) (obs f y)) ->
    sb L `R (Vis e k) (Vis f k').
  Proof.
    intros EQs EQs'.
    apply step_sb_vis_gen; eauto.
    typeclasses eauto.
  Qed.

  Lemma sbisim_vis {X' Y'}
    (e: E X') (f: F Y') (k: X' -> ctree E C X) (k': Y' -> ctree F D Y) :
    (forall x, exists y, sbisim L (k x) (k' y) /\ L (obs e x) (obs f y)) ->
    (forall y, exists x, sbisim L (k x) (k' y) /\ L (obs e x) (obs f y)) ->
    sbisim L (Vis e k) (Vis f k').
  Proof.
    intros. step. now apply step_sb_vis.
  Qed.

  Lemma step_sb_vis_id_gen {X'} (e: E X') (f: F X')
    (k: X' -> ctree E C X) (k': X' -> ctree F D Y) {R : rel _ _}:
    (Proper (equ eq ==> equ eq ==> impl) R) ->
    (forall x, R (k x) (k' x) /\ L (obs e x) (obs f x)) ->
    sb L R (Vis e k) (Vis f k').
  Proof.
    intros; eapply step_sb_vis_gen; eauto.
  Qed.

  Lemma step_sb_vis_id {X'}
    (e: E X') (f: F X') (k: X' -> ctree E C X) (k': X' -> ctree F D Y)
    {R : Chain (@sb E F C D X Y L)} :
    (forall x, ` R (k x) (k' x) /\ L (obs e x) (obs f x)) ->
    sb L `R (Vis e k) (Vis f k').
  Proof.
    intros; eapply step_sb_vis; eauto.
  Qed.

  Lemma sbisim_vis_id {X'}
    (e: E X') (f: F X') (k: X' -> ctree E C X) (k': X' -> ctree F D Y) :
    (forall x, sbisim L (k x) (k' x) /\ L (obs e x) (obs f x)) ->
    sbisim L (Vis e k) (Vis f k').
  Proof.
    intros. step. now apply step_sb_vis_id.
  Qed.

  (*|
  Guard
|*)
  Lemma step_sb_guard_gen (t : ctree E C X) (u : ctree F D Y) {R : rel _ _} :
    sb L R t u ->
    sb L R (Guard t) (Guard u).
  Proof.
    split; apply step_ss_guard_gen; eauto; apply H.
  Qed.

  Lemma step_sb_guard_l_gen (t : ctree E C X) (u : ctree F D Y) {R : rel _ _} :
    sb L R t u ->
    sb L R (Guard t) u.
  Proof.
    split.
    apply step_ss_guard_l_gen; eauto; apply H.
    apply step_ss_guard_r_gen; eauto; apply H.
  Qed.

  Lemma step_sb_guard_r_gen (t : ctree E C X) (u : ctree F D Y) {R : rel _ _} :
    sb L R t u ->
    sb L R t (Guard u).
  Proof.
    split.
    apply step_ss_guard_r_gen; eauto; apply H.
    apply step_ss_guard_l_gen; eauto; apply H.
  Qed.

  Lemma step_sb_guard (t : ctree E C X) (u : ctree F D Y)
    {R : Chain (@sb E F C D X Y L)} :
    sb L (` R) t u ->
    sb L `R (Guard t) (Guard u).
  Proof.
    intros; apply step_sb_guard_gen; auto.
  Qed.

  Lemma step_sb_guard_l (t : ctree E C X) (u : ctree F D Y)
    {R : Chain (@sb E F C D X Y L)} :
    sb L (` R) t u ->
    sb L `R (Guard t) u.
  Proof.
    intros; apply step_sb_guard_l_gen; auto.
  Qed.

  Lemma step_sb_guard_r (t : ctree E C X) (u : ctree F D Y)
    {R : Chain (@sb E F C D X Y L)} :
    sb L (` R) t u ->
    sb L `R t (Guard u).
  Proof.
    intros; apply step_sb_guard_r_gen; auto.
  Qed.

  Lemma sbisim_guard (t : ctree E C X) (u : ctree F D Y) :
    sbisim L t u ->
    sbisim L (Guard t) (Guard u).
  Proof.
    intros * EQ; step; apply step_sb_guard; step in EQ; auto.
  Qed.

  Lemma sbisim_guard_l (t : ctree E C X) (u : ctree F D Y) :
    sbisim L t u ->
    sbisim L (Guard t) u.
  Proof.
    intros * EQ; step; apply step_sb_guard_l; step in EQ; auto.
  Qed.

  Lemma sbisim_guard_r (t : ctree E C X) (u : ctree F D Y) :
    sbisim L t u ->
    sbisim L t (Guard u).
  Proof.
    intros * EQ; step; apply step_sb_guard_r; step in EQ; auto.
  Qed.

(*|
br
|*)

  Lemma step_sb_br_gen {X' Y'} (c : C X') (d: D Y')
    (k : X' -> ctree E C X) (k' : Y' -> ctree F D Y) (R : rel _ _) :
    (forall x, exists y, sb L R (k x) (k' y)) ->
    (forall y, exists x, sb L R (k x) (k' y)) ->
    sb L R (Br c k) (Br d k').
  Proof.
    intros EQs1 EQs2.
    split; apply step_ss_br_gen; intros.
    - destruct (EQs1 x) as [z [FW _]]. eauto.
    - destruct (EQs2 x) as [z [_ BA]]. eauto.
  Qed.

  Lemma step_sb_br_id_gen {X'} (c : C X') (d: D X')
    (k : X' -> ctree E C X) (k' : X' -> ctree F D Y) (R : rel _ _) :
    (forall x, sb L R (k x) (k' x)) ->
    sb L R (Br c k) (Br d k').
  Proof.
    intros EQs.
    split; apply step_ss_br_id_gen; intros.
    - destruct (EQs x); auto.
    - destruct (EQs x); auto.
  Qed.

  Lemma step_sb_br_l_gen {X'} (c : C X')
    (k : X' -> ctree E C X) (u : ctree F D Y) (R : rel _ _) :
    X' ->
    (forall x, sb L R (k x) u) ->
    sb L R (Br c k) u.
  Proof.
    intros x EQs.
    split.
    - apply step_ss_br_l_gen; intros; apply EQs.
    - intros ?? TR.
      eapply step_ss_br_r_gen with (x := x); eauto.
      apply EQs.
  Qed.

  Lemma step_sb_br_r_gen {Y'} (c : D Y')
    (t : ctree E C X) (k : Y' -> ctree F D Y) (R : rel _ _) :
    Y' ->
    (forall x, sb L R t (k x)) ->
    sb L R t (Br c k).
  Proof.
    intros x EQs.
    split.
    - apply step_ss_br_r_gen with (x := x); intros; apply EQs.
    - apply step_ss_br_l_gen; intros; apply EQs.
  Qed.

  Lemma step_sb_br {X' Y'}
    (c : C X') (d: D Y')
    (k : X' -> ctree E C X) (k' : Y' -> ctree F D Y)
    {R : Chain (@sb E F C D X Y L)} :
    (forall x, exists y, sb L (` R) (k x) (k' y)) ->
    (forall y, exists x, sb L (` R) (k x) (k' y)) ->
    sb L `R (Br c k) (Br d k').
  Proof.
    intros; apply step_sb_br_gen; auto.
  Qed.

  Lemma step_sb_br_id {X'}
    (c : C X') (d: D X')
    (k : X' -> ctree E C X) (k' : X' -> ctree F D Y)
    {R : Chain (@sb E F C D X Y L)} :
    (forall x, sb L (` R) (k x) (k' x)) ->
    sb L `R (Br c k) (Br d k').
  Proof.
    intros; apply step_sb_br_id_gen; auto.
  Qed.

  Lemma step_sb_br_l {X'}
    (c : C X')
    (k : X' -> ctree E C X) (u : ctree F D Y)
    {R : Chain (@sb E F C D X Y L)} :
    X' ->
    (forall x, sb L (` R) (k x) u) ->
    sb L `R (Br c k) u.
  Proof.
    intros; apply step_sb_br_l_gen; auto.
  Qed.

  Lemma step_sb_br_r {Y'}
    (d : D Y')
    (t : ctree E C X) (k' : Y' -> ctree F D Y)
    {R : Chain (@sb E F C D X Y L)} :
    Y' ->
    (forall x, sb L (` R) t (k' x)) ->
    sb L `R t (Br d k').
  Proof.
    intros; apply step_sb_br_r_gen; auto.
  Qed.

  Lemma sbisim_br {X' Y'}
    (c : C X') (d: D Y')
    (k : X' -> ctree E C X) (k' : Y' -> ctree F D Y) :
    (forall x, exists y, sbisim L (k x) (k' y)) ->
    (forall y, exists x, sbisim L (k x) (k' y)) ->
    sbisim L (Br c k) (Br d k').
  Proof.
    intros H1 H2; step; apply step_sb_br; eauto.
    intros x; destruct (H1 x); eexists; step in H; eauto.
    intros x; destruct (H2 x); eexists; step in H; eauto.
  Qed.

  Lemma sbisim_br_id {X'}
    (c : C X') (d: D X')
    (k : X' -> ctree E C X) (k' : X' -> ctree F D Y) :
    (forall x, sbisim L (k x) (k' x)) ->
    sbisim L (Br c k) (Br d k').
  Proof.
    intros; step; apply step_sb_br_id; eauto.
    intros x; specialize (H x); step in H; auto.
  Qed.

  Lemma sbisim_br_l {X'}
    (c : C X')
    (k : X' -> ctree E C X) (u : ctree F D Y) :
    X' ->
    (forall x, sbisim L (k x) u) ->
    sbisim L (Br c k) u.
  Proof.
    intros; step; apply step_sb_br_l; eauto.
    intros x; specialize (H x); step in H; auto.
  Qed.

  Lemma sbisim_br_r {Y'}
    (d: D Y')
    (t : ctree E C X) (k' : Y' -> ctree F D Y) :
    Y' ->
    (forall x, sbisim L t (k' x)) ->
    sbisim L t (Br d k').
  Proof.
    intros; step; apply step_sb_br_r; eauto.
    intros x; specialize (H x); step in H; auto.
  Qed.

(*|
  Same goes for step nodes.
|*)
  Lemma step_sb_step_gen (t : ctree E C X) (u : ctree F D Y) {R : rel _ _} :
    (Proper (equ eq ==> equ eq ==> iff) R) ->
    L τ τ ->
    R t u ->
    sb L R (Step t) (Step u).
  Proof.
    split; apply step_ss_step_gen; eauto.
    repeat intro; edestruct H; eauto.
    unfold flip.
    repeat intro; edestruct H; eauto.
  Qed.

  Lemma step_sb_step (t : ctree E C X) (u : ctree F D Y)
    {R : Chain (@sb E F C D X Y L)} :
    L τ τ ->
    ` R t u ->
    sb L `R (Step t) (Step u).
  Proof.
    intros.
    apply step_sb_step_gen; eauto.
    split; intros HR.
    now rewrite <- H1, <- H2.
    now rewrite H1, H2.
  Qed.

  Lemma sbisim_step (t : ctree E C X) (u : ctree F D Y) :
    L τ τ ->
    sbisim L t u ->
    sbisim L (Step t) (Step u).
  Proof.
    intros. step. apply step_sb_step; auto.
  Qed.

(*|
BrS
|*)

  Lemma step_sb_brS_gen {X' Y'} (c : C X') (d: D Y')
    (k : X' -> ctree E C X) (k' : Y' -> ctree F D Y) (R : rel _ _) :
    (Proper (equ eq ==> equ eq ==> iff) R) ->
    L τ τ ->
    (forall x, exists y, R (k x) (k' y)) ->
    (forall y, exists x, R (k x) (k' y)) ->
    sb L R (BrS c k) (BrS d k').
  Proof.
    intros HP EQτ EQs1 EQs2.
    apply step_sb_br_gen.
    - intros x; destruct (EQs1 x) as [y ?]; exists y.
      apply step_sb_step_gen; auto.
    - intros y; destruct (EQs2 y) as [x ?]; exists x.
      apply step_sb_step_gen; auto.
  Qed.

  Lemma step_sb_brS_id_gen {X'} (c : C X') (d: D X')
    (k : X' -> ctree E C X) (k' : X' -> ctree F D Y) (R : rel _ _) :
    (Proper (equ eq ==> equ eq ==> iff) R) ->
    L τ τ ->
    (forall x, R (k x) (k' x)) ->
    sb L R (BrS c k) (BrS d k').
  Proof.
    intros HP EQτ EQs.
    apply step_sb_br_id_gen.
    intros.
    apply step_sb_step_gen; auto.
  Qed.

  Lemma step_sb_brS
    {X' Y'} (c : C X') (d: D Y')
    (k : X' -> ctree E C X) (k' : Y' -> ctree F D Y)
    {R : Chain (@sb E F C D X Y L)} :
    L τ τ ->
    (forall x, exists y, ` R (k x) (k' y)) ->
    (forall y, exists x, ` R (k x) (k' y)) ->
    sb L `R (BrS c k) (BrS d k').
  Proof.
    intros.
    apply step_sb_brS_gen; eauto.
    split; intros HR.
    now rewrite <- H3, <- H2.
    now rewrite H3, H2.
  Qed.

  Lemma step_sb_brS_id
    {X'} (c : C X') (d: D X')
    (k : X' -> ctree E C X) (k' : X' -> ctree F D Y)
    {R : Chain (@sb E F C D X Y L)} :
    L τ τ ->
    (forall x, ` R (k x) (k' x)) ->
    sb L `R (BrS c k) (BrS d k').
  Proof.
    intros.
    apply step_sb_br_id.
    intros.
    split; intros ?? TR; inv_trans; do 2 eexists; split; etrans; subst; split; auto.
    rewrite EQ; apply H0.
    rewrite EQ; apply H0.
  Qed.

  Lemma sbisim_brS
    {X' Y'} (c : C X') (d: D Y')
    (k : X' -> ctree E C X) (k' : Y' -> ctree F D Y) :
    L τ τ ->
    (forall x, exists y, sbisim L (k x) (k' y)) ->
    (forall y, exists x, sbisim L (k x) (k' y)) ->
    sbisim L (BrS c k) (BrS d k').
  Proof.
    intros. step. now apply step_sb_brS.
  Qed.

  Lemma sbisim_brS_id
    {X'} (c : C X') (d: D X')
    (k : X' -> ctree E C X) (k' : X' -> ctree F D Y) :
    L τ τ ->
    (forall x, sbisim L (k x) (k' x)) ->
    sbisim L (BrS c k) (BrS d k').
  Proof.
    intros. step. now apply step_sb_brS_id.
  Qed.

End Proof_Rules.

(*|
Proof system for [~]
--------------------

We specialize the proof system established in the previous section to [~] for clarity.
|*)
Section Sb_Proof_System.
  Arguments label: clear implicits.
  Context {E C: Type -> Type} {X: Type}.

  Lemma sb_ret : forall x y,
      x = y ->
      (Ret x: ctree E C X) ~ (Ret y: ctree E C X).
  Proof.
    intros * EQ; step.
    now apply step_sb_ret; subst.
  Qed.

  Lemma sb_vis {Y}: forall (e: E X) (k k': X -> ctree E C Y),
      (forall x, k x ~ k' x) ->
      Vis e k ~ Vis e k'.
  Proof.
    intros.
    apply vis_chain, H.
  Qed.

  (*|
    Visible vs. Invisible Taus
    ~~~~~~~~~~~~~~~~~~~~~~~~~~
    Invisible taus can be stripped-out w.r.t. to [sbisim], but not visible ones
|*)
  Lemma sb_guard: forall (t : ctree E C X),
      Guard t ~ t.
  Proof.
    intros t; play.
    - inv_trans; etrans.
    - eauto 6 with trans.
  Qed.

  Lemma sb_guard_l: forall (t u : ctree E C X),
      t ~ u ->
      Guard t ~ u.
  Proof.
    intros * EQ; now rewrite sb_guard.
  Qed.

  Lemma sb_guard_r: forall (t u : ctree E C X),
      t ~ u ->
      t ~ Guard u.
  Proof.
    intros * EQ; now rewrite sb_guard.
  Qed.

  Lemma sb_guard_lr: forall (t u : ctree E C X),
      t ~ u ->
      Guard t ~ Guard u.
  Proof.
    intros * EQ; now rewrite !sb_guard.
  Qed.

  Lemma sb_step: forall (t u : ctree E C X),
      t ~ u ->
      Step t ~ Step u.
  Proof.
    intros; apply sbisim_step; auto.
  Qed.

  Lemma sb_br I J (ci : C I) (cj : C J)
    (k : I -> ctree E C X) (k' : J -> ctree E C X) :
    (forall x, exists y, k x ~ k' y) ->
    (forall y, exists x, k x ~ k' y) ->
    Br ci k ~ Br cj k'.
  Proof.
    intros; apply sbisim_br; auto.
  Qed.

  Lemma sb_br_id I (c : C I)
    (k k' : I -> ctree E C X) :
    (forall x, k x ~ k' x) ->
    Br c k ~ Br c k'.
  Proof.
    intros; apply sbisim_br_id; auto.
  Qed.

  Lemma sb_br_l {Y} c (y : Y) (k: Y -> ctree E C X) (t: ctree E C X):
    (forall x, k x ~ t) ->
    Br c k ~ t.
  Proof.
    intros; apply sbisim_br_l; auto.
  Qed.

  Lemma sb_brS I J (ci : C I) (cj : C J)
    (k : I -> ctree E C X) (k' : J -> ctree E C X) :
    (forall x, exists y, k x ~ k' y) ->
    (forall y, exists x, k x ~ k' y) ->
    BrS ci k ~ BrS cj k'.
  Proof.
    intros; apply sbisim_brS; auto.
  Qed.

  Lemma sb_brS_id I (c : C I)
    (k k' : I -> ctree E C X) :
    (forall x, k x ~ k' x) ->
    BrS c k ~ BrS c k'.
  Proof.
    intros; apply sbisim_brS_id; auto.
  Qed.

  Lemma sb_unfold_forever : forall (k: X -> ctree E C X) (i: X),
      forever k i ~ r <- k i ;; forever k r.
  Proof.
    intros.
    rewrite unfold_forever.
    apply sbisim_clo_bind_eq; auto.
    intros; now rewrite sb_guard.
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
  + admits any Stuck computation as a unit

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
    coinduction S CIH. symmetric.
    intros ** L t' TR;
      rewrite ctree_eta in TR; cbn in TR;
      apply trans_brS_inv in TR as (_ & EQ & ->);
      eexists; eexists;
      rewrite ctree_eta; cbn.
    split; [econstructor|].
    - exact y.
    - constructor; reflexivity.
    - rewrite EQ; eauto.
  Qed.

  Lemma spin_gen_bisim : forall {Z X Y} (c: C X) (c': C Y),
      @spin_gen E C Z X c ~ @spin_gen E C Z Y c'.
  Proof.
    intros R.
    coinduction S _; split; cbn;
      intros * TR; exfalso; eapply spinD_gen_is_stuck, TR.
  Qed.

(*|
  Br2 is associative, commutative, idempotent, merges into Br3, and admits _a lot_ of units.
|*)
  Lemma br2_assoc X : forall (t u v : ctree E C X),
	    br2 (br2 t u) v ~ br2 t (br2 u v).
  Proof.
    intros.
    play; inv_trans; eauto 7 with trans.
  Qed.

  Lemma br2_commut {X} : forall (t u : ctree E C X),
	    br2 t u ~ br2 u t.
  Proof.
    intros.
    play; inv_trans; eauto 6 with trans.
  Qed.

  Lemma br2_idem {X} : forall (t : ctree E C X),
	    br2 t t ~ t.
  Proof.
    intros.
    play; inv_trans; eauto 6 with trans.
  Qed.

  Lemma br2_merge {X} : forall (t u v : ctree E C X),
	    br2 (br2 t u) v ~ br3 t u v.
  Proof.
    intros.
    play; inv_trans; eauto 7 with trans.
  Qed.

  Lemma br2_is_stuck {X} : forall (u v : ctree E C X),
      is_stuck u ->
	    br2 u v ~ v.
  Proof.
    intros * ST.
    play.
    - inv_trans.
      exfalso; eapply ST, TR. (* automate stuck transition trying to step? *)
      exists l, t'; eauto.             (* automate trivial case *)
    - eauto 6 with trans.
  Qed.

  Lemma br2_stuck_l {X} : forall (t : ctree E C X),
	    br2 Stuck t ~ t.
  Proof.
    intros; apply br2_is_stuck, Stuck_is_stuck.
  Qed.

  Lemma br2_stuck_r {X} : forall (t : ctree E C X),
	    br2 t Stuck ~ t.
  Proof.
    intros; rewrite br2_commut; apply br2_stuck_l.
  Qed.

  Lemma br2_spin_l {X} : forall (t : ctree E C X),
	    br2 spin t ~ t.
  Proof.
    intros; apply br2_is_stuck, spin_is_stuck.
  Qed.

  Lemma br2_spin_r {X} : forall (t : ctree E C X),
	    br2 t spin ~ t.
  Proof.
    intros; rewrite br2_commut; apply br2_is_stuck, spin_is_stuck.
  Qed.

(*|
BrS2 is commutative and "almost" idempotent
|*)
  Lemma brS2_commut : forall X (t u : ctree E C X),
	    brS2 t u ~ brS2 u t.
  Proof.
    intros.
    play; inv_trans; subst.
    all: do 2 eexists; split; [| split; [rewrite EQ; reflexivity| reflexivity]]; etrans.
  Qed.

  Lemma brS2_idem : forall X (t : ctree E C X),
	    brS2 t t ~ Step t.
  Proof.
    intros.
    play; inv_trans; subst.
    all: do 2 eexists; split; [| split; [rewrite EQ; reflexivity| reflexivity]]; etrans.
  Qed.

(*|
Inversion principles
--------------------
|*)
  Lemma sbisim_ret_inv X (r1 r2 : X) :
    (Ret r1 : ctree E C X) ~ (Ret r2 : ctree E C X) -> r1 = r2.
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

  Lemma sbisim_brS_inv {X Y Z}
    c1 c2 (k1 : X -> ctree E C Z) (k2 : Y -> ctree E C Z) :
    BrS c1 k1 ~ BrS c2 k2 ->
    (forall i1, exists i2, k1 i1 ~ k2 i2) /\ (forall i2, exists i1, k1 i1 ~ k2 i2).
  Proof.
    intros EQ; split; intros i.
    eplayL; inv_trans; eauto.
    eplayR; inv_trans; eauto.
  Qed.

(*|
    Annoying case: [Vis e k ~ BrS c k'] is true if [e : E void] and [c : C void].
    We rule out this case in this definition.
|*)
  Definition are_bisim_incompat {X} (t u : ctree E C X) : Type :=
    match observe t, observe u with
    | RetF _, RetF _
    | VisF _ _, VisF _ _
    | BrF _ _, _
    | _, BrF _ _
    | GuardF _, _
    | _, GuardF _
    | StepF _, StepF _
    | StuckF, StuckF
      => False
    | @VisF _ _ _ _ X _ _, StuckF
    | StuckF, @VisF _ _ _ _ X _ _ =>
        inhabited X
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
    destruct ot, ou.
    all: try now inv IC.
    all: try now unshelve (inv IC; playR in EQ; inv_trans); auto.
    all: try now unshelve (inv IC; playL in EQ; inv_trans); auto.
  Qed.

  Ltac sb_abs h :=
    eapply sbisim_absurd; [| eassumption]; cbn; try reflexivity.

  Lemma sbisim_ret_vis_inv {X Y} (r : Y) (e : E X) (k : X -> ctree E C Y) :
    (Ret r : ctree E C _) ~ Vis e k -> False.
  Proof.
    intros * abs. sb_abs abs.
  Qed.

  Lemma sbisim_ret_BrS_inv {X Y} (r : Y) (c : C X) (k : X -> ctree E C Y) :
    (Ret r : ctree E C _) ~ BrS c k -> False.
  Proof.
    intros EQ; playL in EQ; inv_trans.
  Qed.

(*|
  For this to be absurd, we need one of the return types to be inhabited.
|*)
  Lemma sbisim_vis_BrS_inv {X Y Z}
    (e : E X) (k1 : X -> ctree E C Z) (c : C Y) (k2: Y -> ctree E C Z) (y : Y) :
    Vis e k1 ~ BrS c k2 -> False.
  Proof.
    unshelve (intros EQ; playR in EQ; inv_trans); auto.
  Qed.

  Lemma sbisim_vis_BrS_inv' {X Y Z}
    (e : E X) (k1 : X -> ctree E C Z) (c : C Y) (k2: Y -> ctree E C Z) (x : X) :
    Vis e k1 ~ BrS c k2 -> False.
  Proof.
    unshelve (intros EQ; playL in EQ; inv_trans); auto.
  Qed.

(*|
Not fond of this, need to give some thoughts about them
|*)
  Lemma sbisim_ret_Br_inv {X Y} (r : Y) (c : C X) (k : X -> ctree E C Y) :
    (Ret r : ctree E C _) ~ Br c k ->
    exists x, (Ret r : ctree E C _) ~ k x.
  Proof.
    intros EQ; generalize EQ; intros EQ'; playL in EQ; inv_trans.
    pose proof trans_val_inv TR as H; rewrite H in TR; clear x0 EQ H.
    exists x; play.
    - inv_trans; subst.
      do 2 eexists; intuition; eauto.
      now rewrite EQ.
    - playR in EQ'.
      apply trans_ret_inv in TR1; intuition; subst.
      do 2 eexists; intuition; eauto.
      apply trans_val_inv in TR0.
      rewrite TR0; eauto.
  Qed.

End WithParams.

Section StrongSimulations.

  Section Heterogeneous.

    Context {E F C D: Type -> Type} {X Y: Type}
      {L: rel (@label E) (@label F)}.

    Notation ss := (@ss E F C D X Y).
    Notation ssim  := (@ssim E F C D X Y).

    Lemma sbisim_clos_ss {c: Chain (ss L)}:
      forall x y, sbisim_clos (LE := eq) (LF := eq) `c x y -> `c x y.
    Proof.
      apply tower.
      - intros ? INC x y [x' y' x'' y'' EQ' EQ''] ??. red.
        apply INC; auto.
        econstructor; eauto.
        apply leq_infx in H.
        now apply H.
      - clear.
        intros c IH x y []; intros ? ? TR.
        step in Sbisimt; apply Sbisimt in TR; destruct TR as (? & ? & TR & Sbis & <-).
        apply HR in TR; destruct TR as (? & ? & TR & Sbis' & HL).
        step in Sbisimu; apply Sbisimu in TR; destruct TR as (? & ? & TR & Sbis'' & <-).
        do 2 eexists; repeat split; eauto.
        apply IH.
        econstructor; eauto.
    Qed.

(*|
  Instances for rewriting [sbisim] under all [ss]-related contexts
|*)
    #[global] Instance sbisim_eq_clos_ss_goal `{R : Chain (ss L)}:
      Proper (sbisim eq ==> sbisim eq ==> flip impl) `R.
    Proof.
      repeat intro.
      apply sbisim_clos_ss.
      econstructor; [eassumption | | symmetry in H0; eassumption].
      eauto.
    Qed.

    #[global] Instance sbisim_eq_clos_ss_ctx `{R : Chain (ss L)} :
      Proper (sbisim eq ==> sbisim eq ==> impl) `R.
    Proof.
      repeat intro. symmetry in H, H0. eapply sbisim_eq_clos_ss_goal; eauto.
    Qed.

    #[global] Instance sbisim_eq_clos_ssim_goal:
      Proper (sbisim eq ==> sbisim eq ==> flip impl) (ssim L).
    Proof.
      apply sbisim_eq_clos_ss_goal.
    Qed.

    #[global] Instance sbisim_eq_clos_ssim_ctx :
      Proper (sbisim eq ==> sbisim eq ==> impl) (ssim L).
    Proof.
      apply sbisim_eq_clos_ss_ctx.
    Qed.

    Lemma ss_sb : forall RR (t : ctree E C X) (t' : ctree F D Y),
        ss L RR t t' ->
        SSim.ss (flip L) (flip RR) t' t ->
        sb L RR t t'.
    Proof.
      split; cbn; intros.
      - apply H in H1 as (? & ? & ? & ? & ?); eauto.
      - apply H0 in H1 as (? & ? & ? & ? & ?); eauto.
    Qed.

  End Heterogeneous.

  Section Homogeneous.

    Context {E C: Type -> Type} {X: Type}
      {L: rel (@label E) (@label E)}.
    Notation ss := (@ss E E C C X X).
    Notation ssim  := (@ssim E E C C X X).

    #[global] Instance sbisim_clos_ssim_goal `{Symmetric _ L} `{Transitive _ L} :
      Proper (sbisim L ==> sbisim L ==> flip impl) (ssim L).
    Proof.
      repeat intro.
      transitivity y0. transitivity y.
      - now apply sbisim_ssim_subrelation in H1.
      - now exact H3.
      - symmetry in H2; now apply sbisim_ssim_subrelation in H2.
    Qed.

    #[global] Instance sbisim_clos_ssim_ctx `{Equivalence _ L}:
      Proper (sbisim L ==> sbisim L ==> impl) (ssim L).
    Proof.
      repeat intro. symmetry in H0, H1. eapply sbisim_clos_ssim_goal; eauto.
    Qed.

  End Homogeneous.

  Section two_ss_is_not_sb.

    Lemma split_sb_eq : forall {E C X} RR
                          (t t' : ctree E C X),
        ss eq RR t t' ->
        ss eq (flip RR) t' t ->
        sb eq RR t t'.
    Proof.
      intros.
      split; eauto.
      simpl in *; intros.
      destruct (H0 _ _ H1) as (? & ? & ? & ? & ?).
      destruct (H _ _ H2) as (? & ? & ? & ? & ?).
      subst; eauto.
    Qed.

    Lemma split_sbisim_eq : forall {E B X} (t u : ctree E B X),
        t ~ u <-> ss eq (sbisim eq) t u /\ ss eq (sbisim eq) u t.
    Proof.
      split; intro.
      - step in H. split; [apply H |].
        symmetry in H. apply H.
      - step. split; [apply H |].
        destruct H as [_ ?].
        eapply weq_ss with (y := eq). { cbn. split; auto. }
        eapply (Hbody (ss eq)). 2: apply H.
        cbn. intros. now symmetry.
    Qed.

    #[local] Definition t1 : ctree void1 B2 unit :=
      Step (Ret tt).

    #[local] Definition t2 : ctree void1 B2 unit :=
      brS2 (Ret tt) (Stuck).

    Lemma ssim_sbisim_nequiv :
      ssim eq t1 t2 /\ ssim eq t2 t1 /\ ~ sbisim eq t1 t2.
    Proof.
      unfold t1, t2. intuition.
      - unfold brS2.
        step.
        intros ?? TR.
        inv_trans; subst.
        exists τ, (Ret tt); split.
        apply Transbr with true.
        constructor; reflexivity.
        split; auto.
        rewrite EQ; auto.
      - step; intros ?? TR.
        inv_trans; subst.
        exists τ, (Ret tt); intuition; now rewrite EQ.
        exists τ, (Ret tt). intuition.
        rewrite EQ; apply Stuck_ssim.
      - step in H. cbn in H. destruct H as [_ ?].
        specialize (H τ Stuck). lapply H; [| etrans].
        intros. destruct H0 as (? & ? & ? & ? & ?).
        inv_trans. step in H1. cbn in H1. destruct H1 as [? _].
        specialize (H0 (val tt) Stuck). lapply H0.
        2: subst; etrans.
        intro; destruct H1 as (? & ? & ? & ? & ?).
        now apply Stuck_is_stuck in H1.
    Qed.

  End two_ss_is_not_sb.

End StrongSimulations.

Section CompleteStrongSimulations.

  Context {E F C D: Type -> Type} {X Y: Type}
    {L: rel (@label E) (@label F)}.

  Notation css := (@css E F C D X Y).
  Notation cssim  := (@cssim E F C D X Y).

(*|
A bisimulation trivially gives a simulation.
|*)
  Lemma sb_css : forall RR (t : ctree E C X) (t' : ctree F D Y),
      sb L RR t t' -> css L RR t t'.
  Proof.
    intros; split.
    - apply H.
    - intros. apply H in H0 as (? & ? & ? & ? & ?). eauto.
  Qed.

  Lemma sbisim_clos_css {c: Chain (css L)}:
    forall x y, sbisim_clos (LE := eq) (LF := eq) `c x y -> `c x y.
  Proof.
    apply tower.
    - intros ? INC x y [x' y' x'' y'' EQ' EQ''] ??. red.
      apply INC; auto.
      econstructor; eauto.
      apply leq_infx in H.
      now apply H.
    - clear.
      intros c IH x y []; split; intros ? ? TR.
      + step in Sbisimt; apply Sbisimt in TR; destruct TR as (? & ? & TR & Sbis & <-).
        apply HR in TR; destruct TR as (? & ? & TR & Sbis' & HL).
        step in Sbisimu; apply Sbisimu in TR; destruct TR as (? & ? & TR & Sbis'' & <-).
        do 2 eexists; repeat split; eauto.
        apply IH.
        econstructor; eauto.
      + playR in Sbisimu.
        apply HR in TR0 as (? & ? & ?).
        playR in Sbisimt.
        eauto.
  Qed.

(*|
  Instances for rewriting [sbisim] under all [css]-related contexts
|*)
  #[global] Instance sbisim_eq_clos_css_goal `{R : Chain (css L)}:
    Proper (sbisim eq ==> sbisim eq ==> flip impl) `R.
  Proof.
    repeat intro.
    apply sbisim_clos_css.
    econstructor; [eassumption | | symmetry in H0; eassumption].
    eauto.
  Qed.

  #[global] Instance sbisim_eq_clos_css_ctx `{R : Chain (css L)} :
    Proper (sbisim eq ==> sbisim eq ==> impl) `R.
  Proof.
    repeat intro. symmetry in H, H0. eapply sbisim_eq_clos_css_goal; eauto.
  Qed.

  #[global] Instance sbisim_eq_clos_cssim_goal:
    Proper (sbisim eq ==> sbisim eq ==> flip impl) (cssim L).
  Proof.
    apply sbisim_eq_clos_css_goal.
  Qed.

  #[global] Instance sbisim_eq_clos_cssim_ctx :
    Proper (sbisim eq ==> sbisim eq ==> impl) (cssim L).
  Proof.
    apply sbisim_eq_clos_css_ctx.
  Qed.

  #[global] Instance sbisim_clos_cssim_goal:
    Proper (sbisim eq ==> sbisim eq ==> flip impl) (cssim L).
  Proof.
    cbn; intros; eapply sbisim_clos_css; econstructor; eauto.
    now symmetry.
  Qed.

  #[global] Instance sbisim_clos_cssim_ctx :
    Proper (sbisim eq ==> sbisim eq ==> impl) (cssim L).
  Proof.
    repeat intro. symmetry in H, H0. eapply sbisim_clos_cssim_goal; eauto.
  Qed.

(*|
A strong bisimulation gives two strong simulations,
but two strong simulations do not always give a strong bisimulation.
This property is true if we only allow choices with 0 or 1 branch,
but we prove a counter-example for a ctree with a binary choice.
|*)
  Lemma css_sb : forall RR (t : ctree E C X) (t' : ctree F D Y),
      css L RR t t' ->
      CSSim.css (flip L) (flip RR) t' t ->
      sb L RR t t'.
  Proof.
    split; cbn; intros.
    - apply H in H1 as (? & ? & ? & ? & ?); eauto.
    - apply H0 in H1 as (? & ? & ? & ? & ?); eauto.
  Qed.

End CompleteStrongSimulations.

