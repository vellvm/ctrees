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
     Eq.Trans.

From RelationAlgebra Require Export
     rel srel.

Import CoindNotations.
Import CTree.
Set Implicit Arguments.

(* TODO: Decide where to set this *)
Arguments trans : simpl never.

Section StrongSim.
(*|
The function defining strong simulations: [trans] plays must be answered
using [trans].
The [ss] definition stands for [strong simulation]. The bisimulation [sb]
is obtained by expliciting the symmetric aspect of the definition following
Pous'16 in order to be able to exploit symmetry arguments in proofs
(see [square_st] for an illustration).
|*)
  Program Definition ss {E F C D : Type -> Type} {X Y : Type}
    (L : rel (@label E) (@label F)) :
    mon (ctree E C X -> ctree F D Y -> Prop) :=
    {| body R t u :=
      forall l t', trans l t t' -> exists l' u', trans l' u u' /\ R t' u' /\ L l l'
    |}.
  Next Obligation.
    edestruct H0 as (u' & l' & ?); eauto.
    eexists; eexists; intuition; eauto.
  Qed.

  #[global] Instance weq_ss : forall {E F C D X Y}, Proper (weq ==> weq) (@ss E F C D X Y).
  Proof.
    cbn. intros. split.
    - intros. apply H0 in H1 as (? & ? & ? & ? & ?).
      exists x0, x1. intuition. now apply H.
    - intros. apply H0 in H1 as (? & ? & ? & ? & ?).
      exists x0, x1. intuition. now apply H.
  Qed.

End StrongSim.

Definition ssim {E F C D X Y} L :=
  (gfp (@ss E F C D X Y L): hrel _ _).

Module SSimNotations.

  Infix "≲" := (ssim eq) (at level 70).
  Notation "t (≲ Q ) u" := (ssim Q t u) (at level 79).
  Notation "t '[≲' R ']' u" := (ss R (` _) t u) (at level 90, only printing).
  Notation "t '[≲]' u" := (ss eq (` _) t u) (at level 90, only printing).

End SSimNotations.

Import SSimNotations.

Ltac fold_ssim :=
  repeat
    match goal with
    | h: context[gfp (@ss ?E ?F ?C ?D ?X ?Y ?L)] |- _ => fold (@ssim E F C D X Y L) in h
    | |- context[gfp (@ss ?E ?F ?C ?D ?X ?Y ?L)]      => fold (@ssim E F C D X Y L)
    end.

Import CTreeNotations.
Import EquNotations.

Tactic Notation "__step_ssim" :=
  match goal with
  | |- context[@ssim ?E ?F ?C ?D ?X ?Y ?LR] =>
      unfold ssim;
      step;
      fold (@ssim E F C D X Y L)
  end.

#[local] Tactic Notation "step" := __step_ssim || step.

Ltac __step_in_ssim H :=
  match type of H with
  | context[@ssim ?E ?F ?C ?D ?X ?Y ?LR] =>
      unfold ssim in H;
      step in H;
      fold (@ssim E F C D X Y L) in H
  end.

#[local] Tactic Notation "step" "in" ident(H) := __step_in_ssim H || step in H.

Tactic Notation "__coinduction_ssim" simple_intropattern(r) simple_intropattern(cih) :=
  first [unfold ssim at 4 | unfold ssim at 3 | unfold ssim at 2 | unfold ssim at 1]; coinduction r cih.
#[local] Tactic Notation "coinduction" simple_intropattern(r) simple_intropattern(cih) := __coinduction_ssim r cih || coinduction r cih.

Section ssim_homogenous_theory.
  Context {E B: Type -> Type} {X: Type}
          {L: relation (@label E)}.

  Notation ss := (@ss E E B B X X).

  #[global] Instance refl_sst {LR: Reflexive L} {C: Chain (ss L)}: Reflexive `C.
  Proof.
    apply Reflexive_chain.
    cbn; eauto.
  Qed.

  #[global] Instance square_sst {LT: Transitive L} {C: Chain (ss L)}: Transitive `C.
  Proof.
    apply Transitive_chain.
    cbn. intros ????? xy yz.
    intros ?? xx'.
    destruct (xy _ _ xx') as (l' & y' & yy' & ? & ?).
    destruct (yz _ _ yy') as (l'' & z' & zz' & ? & ?).
    eauto 8.
  Qed.

  (*| PreOrder |*)
  #[global] Instance PreOrder_sst {LPO: PreOrder L} {C: Chain (ss L)}: PreOrder `C.
  Proof. split; typeclasses eauto. Qed.

End ssim_homogenous_theory.

(*|
Parametric theory of [ss] with heterogenous [L]
|*)
Section ssim_heterogenous_theory.
  Arguments label: clear implicits.
  Context {E F C D: Type -> Type} {X Y: Type}
          {L: rel (@label E) (@label F)}.

  Notation ss := (@ss E F C D X Y).
  Notation ssim  := (@ssim E F C D X Y).

(*|
   Strong simulation up-to [equ] is valid
   ----------------------------------------
|*)

  Lemma equ_clos_sst {c: Chain (ss L)}:
    forall x y, equ_clos `c x y -> `c x y.
  Proof.
    apply tower.
    - intros ? INC x y [x' y' x'' y'' EQ' EQ''] ??. red.
      apply INC; auto.
      econstructor; eauto.
      apply leq_infx in H.
      now apply H.
    - intros a b ?? [x' y' x'' y'' EQ' EQ''] ? ? tr.
      rewrite EQ' in tr.
      edestruct EQ'' as (l' & ? & ? & ? & ?); [eauto |].
      exists l',x0; intuition.
      rewrite <- Equu; auto.
  Qed.

  #[global] Instance equ_clos_sst_goal {c: Chain (ss L)} :
    Proper (equ eq ==> equ eq ==> flip impl) `c.
  Proof.
    cbn; intros ? ? eq1 ? ? eq2 H.
    apply equ_clos_sst; econstructor; [eauto | | symmetry; eauto]; assumption.
  Qed.

  #[global] Instance equ_clos_sst_ctx  {c: Chain (ss L)} :
    Proper (equ eq ==> equ eq ==> impl) `c.
  Proof.
    cbn; intros ? ? eq1 ? ? eq2 H.
    apply equ_clos_sst; econstructor; [symmetry; eauto | | eauto]; assumption.
  Qed.

  #[global] Instance equ_ss_closed_goal {r} :
    Proper (equ eq ==> equ eq ==> flip impl) (ss L r).
  Proof.
    intros t t' tt' u u' uu'; cbn; intros.
    rewrite tt' in H0. apply H in H0 as (l' & ? & ? & ? & ?).
    do 2 eexists; eauto. rewrite uu'. eauto.
  Qed.

  #[global] Instance equ_ss_closed_ctx {r} :
    Proper (equ eq ==> equ eq ==> impl) (ss L r).
  Proof.
    intros t t' tt' u u' uu'; cbn; intros.
    rewrite <- tt' in H0. apply H in H0 as (l' & ? & ? & ? & ?).
    do 2 eexists; eauto. rewrite <- uu'. eauto.
  Qed.

(*|
  stuck ctrees can be simulated by anything.
|*)
  Lemma is_stuck_ss (R : rel _ _) (t : ctree E C X) (t': ctree F D Y):
    is_stuck t -> ss L R t t'.
  Proof.
    repeat intro. now apply H in H0.
  Qed.

  Lemma is_stuck_ssim (t: ctree E C X) (t': ctree F D Y):
    is_stuck t -> ssim L t t'.
  Proof.
    intros. step. now apply is_stuck_ss.
  Qed.

  Lemma Stuck_ss (R : rel _ _) (t : ctree F D Y) : ss L R Stuck t.
  Proof.
    repeat intro. now apply Stuck_is_stuck in H.
  Qed.

  Lemma Stuck_ssim (t : ctree F D Y) : ssim L Stuck t.
  Proof.
    intros. step. apply Stuck_ss.
  Qed.

  Lemma spin_ss (R : rel _ _) (t : ctree F D Y): ss L R spin t.
  Proof.
    repeat intro. now apply spin_is_stuck in H.
  Qed.

  Lemma spin_ssim : forall (t' : ctree F D Y),
      ssim L spin t'.
  Proof.
    intros. step. apply spin_ss.
  Qed.

End ssim_heterogenous_theory.

Definition Lequiv {E F} X Y (L L' : rel (@label E) (@label F)) :=
  forall l l', wf_val X l -> wf_val Y l' ->
  L l l' <-> L' l l'.

#[global] Instance weq_Lequiv : forall {E F} X Y,
  subrelation weq (@Lequiv E F X Y).
Proof.
  red. red. intros. apply H.
Qed.

#[global] Instance Equivalence_Lequiv : forall {E F} X Y,
  Equivalence (@Lequiv E F X Y).
Proof.
  split; cbn; intros.
  - now apply weq_Lequiv.
  - red. intros. red in H. rewrite H; auto.
  - red. intros.
    etransitivity. apply H; auto. apply H0; auto.
Qed.

#[global] Instance Lequiv_ss_goal : forall {E F C D X Y},
  Proper (Lequiv X Y ==> leq) (@ss E F C D X Y).
Proof.
  cbn. intros.
  apply H0 in H1 as ?. destruct H2 as (? & ? & ? & ? & ?).
  exists x0, x1. split; auto. split; auto. apply H; etrans.
Qed.

#[global] Instance Lequiv_ssim : forall {E F C D X Y},
  Proper (Lequiv X Y ==> leq) (@ssim E F C D X Y).
Proof.
  cbn. intros.
  - unfold ssim.
    epose proof (gfp_leq (x := ss x) (y := ss y)). lapply H1.
    + intro. red in H2. cbn in H2. apply H2. unfold ssim in H0. apply H0.
    + now rewrite H.
Qed.

#[global] Instance weq_ssim : forall {E F C D X Y},
  Proper (weq ==> weq) (@ssim E F C D X Y).
Proof.
  cbn -[ss weq]. intros. apply gfp_weq. now apply weq_ss.
Qed.

(*|
Up-to [bind] context simulations
----------------------------------
We have proved in the module [Equ] that up-to bind context is
a valid enhancement to prove [equ].
We now prove the same result, but for strong simulation.
|*)

Section bind.
  Arguments label: clear implicits.
  Obligation Tactic := idtac.

  Context {E F C D: Type -> Type} {X X' Y Y': Type}
    (L : hrel (@label E) (@label F)) (R0 : rel X Y).

  (* Mix of R0 for val and L for tau/obs. *)
  Variant update_val_rel : @label E -> @label F -> Prop :=
  | update_Val (v1 : X) (v2 : Y) : R0 v1 v2 -> update_val_rel (val v1) (val v2)
  | update_NonVal l1 l2 : ~is_val l1 -> ~is_val l2 -> L l1 l2 -> update_val_rel l1 l2
  .

  Lemma update_val_rel_val : forall (v1 : X) (v2 : Y),
    update_val_rel (val v1) (val v2) ->
    R0 v1 v2.
  Proof.
    intros. remember (val v1) as l1. remember (val v2) as l2.
    destruct H.
    - apply val_eq_inv in Heql1, Heql2. now subst.
    - subst. exfalso. now apply H.
  Qed.

  Lemma update_val_rel_val_l : forall (v1 : X) l2,
    update_val_rel (val v1) l2 ->
    exists v2 : Y, l2 = val v2 /\ R0 v1 v2.
  Proof.
    intros. remember (val v1) as l1. destruct H.
    - apply val_eq_inv in Heql1. subst. eauto.
    - subst. exfalso. apply H. constructor.
  Qed.

  Lemma update_val_rel_val_r : forall l1 (v2 : Y),
    update_val_rel l1 (val v2) ->
    exists v1 : X, l1 = val v1 /\ R0 v1 v2.
  Proof.
    intros. remember (val v2) as l2. destruct H.
    - apply val_eq_inv in Heql2. subst. eauto.
    - subst. exfalso. apply H0. constructor.
  Qed.

  Lemma update_val_rel_nonval_l : forall l1 l2,
    update_val_rel l1 l2 ->
    ~is_val l1 ->
    ~is_val l2 /\ L l1 l2.
  Proof.
    intros. destruct H.
    - exfalso. apply H0. constructor.
    - auto.
  Qed.

  Lemma update_val_rel_nonval_r : forall l1 l2,
    update_val_rel l1 l2 ->
    ~is_val l2 ->
    ~is_val l1 /\ L l1 l2.
  Proof.
    intros. destruct H.
    - exfalso. apply H0. constructor.
    - auto.
  Qed.

  #[global] Instance Respects_val_update_val_rel :
    Respects_val update_val_rel.
  Proof.
    constructor. intros. destruct H.
    - split; etrans.
    - tauto.
  Qed.

  Definition is_update_val_rel (L0 : rel (@label E) (@label F)) : Prop :=
    Lequiv X Y update_val_rel L0.

  Lemma update_val_rel_correct : is_update_val_rel update_val_rel.
  Proof.
    red. red. reflexivity.
  Qed.

(*|
Specialization of [bind_ctx] to a function acting with [ssim] on the bound value,
and with the argument (pointwise) on the continuation.
|*)
  Lemma bind_chain_gen
    (RR : rel (label E) (label F))
    (ISVR : is_update_val_rel RR)
    {R : Chain (@ss E F C D X' Y' L)} :
    forall (t : ctree E C X) (t' : ctree F D Y) (k : X -> ctree E C X') (k' : Y -> ctree F D Y'),
      ssim RR t t' ->
      (forall x x', R0 x x' -> elem R (k x) (k' x')) ->
      elem R (bind t k) (bind t' k').
  Proof.
    apply tower.
    - intros ? INC ? ? ? ? tt' kk' ? ?.
      apply INC. apply H. apply tt'.
      intros x x' xx'. apply leq_infx in H. apply H. now apply kk'.
    - intros ? ? ? ? ? ? tt' kk'.
      step in tt'.
      cbn; intros * STEP.
      apply trans_bind_inv in STEP as [(?H & ?t' & STEP & EQ) | (v & STEPres & STEP)].
      + apply tt' in STEP as (? & ? & ? & ? & ?).
        do 2 eexists; split; [| split].
        apply trans_bind_l; eauto.
        * intro Hl. destruct Hl.
          apply ISVR in H3; etrans.
          inversion H3; subst. apply H0. constructor. apply H5. constructor.
        * rewrite EQ.
          apply H.
          apply H2.
          intros * HR.
          now apply (b_chain x), kk'.
        * apply ISVR in H3; etrans.
          destruct H3. exfalso. apply H0. constructor. eauto.
      + apply tt' in STEPres as (u' & ? & STEPres & EQ' & ?).
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
  Qed.

End bind.

Theorem update_val_rel_eq {E X} : Lequiv X X (@update_val_rel E E X X eq eq) eq.
Proof.
  split; intro.
  - inv H1; reflexivity.
  - subst. destruct l'.
    + constructor; auto.
      all: intro; inv H1.
    + constructor; auto.
      all: intro; inv H1.
    + red in H. specialize (H X0 v eq_refl). subst.
      constructor. reflexivity.
Qed.

#[global] Instance update_val_rel_Lequiv {E F X Y X' Y'} :
  Proper (Lequiv X' Y' ==> weq ==> Lequiv X Y) (@update_val_rel E F X Y).
Proof.
  cbn. red. intros.
  red in H. split; intro.
  - inv H3.
    + left. apply H0. auto.
    + right; auto.
      apply H; auto; now apply wf_val_nonval.
  - inv H3.
    + left. apply H0. auto.
    + right; auto.
      apply H; auto; now apply wf_val_nonval.
Qed.

#[global] Instance is_update_val_rel_Lequiv {E F X Y X' Y'} :
  Proper (Lequiv X' Y' ==> weq ==> Lequiv X Y ==> flip impl) (@is_update_val_rel E F X Y).
Proof.
  cbn -[weq]. red. intros. red in H2. subst. now rewrite H, H0, H1.
Qed.

Theorem update_val_rel_update_val_rel {E F X0 X1 Y0 Y1}
    (L : rel (@label E) (@label F)) (R0 : rel X0 Y0) (R1 : rel X1 Y1) :
  update_val_rel (update_val_rel L R0) R1 == update_val_rel L R1.
Proof.
  split; intro.
  - destruct H.
    + now constructor.
    + destruct H1. { exfalso. now apply H. }
      constructor; auto.
  - destruct H.
    + now constructor.
    + constructor; auto.
      constructor; auto.
Qed.

Theorem is_update_val_rel_update_val_rel_eq {E X Y Z} :
  forall (R : rel X Y),
  @Lequiv E E Z Z (@update_val_rel E E Z Z (update_val_rel eq R) eq) eq.
Proof.
  intros. rewrite update_val_rel_update_val_rel.
  now rewrite update_val_rel_eq.
Qed.

#[global] Instance Symmetric_update_val_rel {E X} L R0 :
  Symmetric L ->
  Symmetric R0 ->
  Symmetric (@update_val_rel E E X X L R0).
Proof.
  cbn. intros. destruct H1; constructor; auto.
Qed.

#[global] Instance Transitive_update_val_rel :
  forall {E X} (L : relation (@label E)) (R0 : relation X),
  Transitive L ->
  Transitive R0 ->
  Transitive (update_val_rel L R0).
Proof.
  red. intros. destruct y.
  - inv H1. inv H2. constructor; auto. etransitivity; eassumption.
  - inv H1. inv H2. constructor; auto. etransitivity; eassumption.
  - inv H1; [| exfalso; etrans].
    inv H2; [| exfalso; etrans].
    invert. constructor. eauto.
Qed.

Definition lift_val_rel {E X Y} := @update_val_rel E E X Y eq.

(*|
Specializing the congruence principle for [≲]
|*)
Lemma ssim_clo_bind_gen {E F C D: Type -> Type} {X Y X' Y': Type}  {L : rel (@label E) (@label F)}
      (R0 : rel X Y) L0
      (HL0 : is_update_val_rel L R0 L0)
      (t1 : ctree E C X) (t2: ctree F D Y)
      (k1 : X -> ctree E C X') (k2 : Y -> ctree F D Y'):
  ssim L0 t1 t2 ->
  (forall x y, R0 x y -> ssim L (k1 x) (k2 y)) ->
  ssim L (t1 >>= k1) (t2 >>= k2).
Proof.
  intros.
  eapply bind_chain_gen; eauto.
Qed.

Lemma ssim_clo_bind {E F C D: Type -> Type} {X Y X' Y': Type} {L : rel (@label E) (@label F)}
      (R0 : rel X Y)
      (t1 : ctree E C X) (t2: ctree F D Y)
      (k1 : X -> ctree E C X') (k2 : Y -> ctree F D Y'):
  t1 (≲update_val_rel L R0) t2 ->
  (forall x y, R0 x y -> k1 x (≲L) k2 y) ->
  t1 >>= k1 (≲L) t2 >>= k2.
Proof.
  intros.
  eapply bind_chain_gen; eauto using update_val_rel_correct.
Qed.

Lemma ssim_clo_bind_eq {E C D: Type -> Type} {X X': Type}
      (t1 : ctree E C X) (t2: ctree E D X)
      (k1 : X -> ctree E C X') (k2 : X -> ctree E D X'):
  t1 ≲ t2 ->
  (forall x, k1 x ≲ k2 x) ->
  t1 >>= k1 ≲ t2 >>= k2.
Proof.
  intros.
  eapply bind_chain_gen; eauto.
  - apply update_val_rel_eq.
  - intros; subst. apply H0.
Qed.

(*|
And in particular, we can justify rewriting [≲] to the left of a [bind].

NOTE: we shouldn't have to impose [eq] to the right.
|*)
#[global] Instance ssim_bind_chain {E C X Y}
  {R : Chain (@ss E E C C Y Y eq)} :
  Proper (ssim eq ==>
            (pointwise_relation _ (elem R)) ==>
            (elem R)) (@bind E C X Y).
Proof.
  repeat intro; eapply bind_chain_gen; eauto.
  - apply update_val_rel_eq.
  - intros. now subst.
Qed.

#[global] Instance bind_ssim_cong_gen {E C X X'} :
  Proper (ssim eq ==> pointwise_relation X (ssim eq) ==> ssim eq) (@CTree.bind E C X X').
Proof.
  cbn. intros. now apply ssim_clo_bind_eq.
Qed.

Ltac __play_ssim := step; cbn; intros ? ? ?TR.

Ltac __play_ssim_in H :=
  step in H;
  cbn in H; edestruct H as (? & ? & ?TR & ?EQ & ?HL);
  clear H; [etrans |].

Ltac __eplay_ssim :=
  match goal with
  | h : @ssim ?E ?F ?C ?D ?X ?Y _ _ ?L |- _ =>
      __play_ssim_in h
  end.

#[local] Tactic Notation "play" := __play_ssim.
#[local] Tactic Notation "play" "in" ident(H) := __play_ssim_in H.
#[local] Tactic Notation "eplay" := __eplay_ssim.

Section Proof_Rules.

  Arguments label: clear implicits.
  Context {E C: Type -> Type}
          {X : Type}.

  Lemma step_ss_ret_gen {Y F D}(x : X) (y : Y) (R L : rel _ _) :
    R Stuck Stuck ->
    (Proper (equ eq ==> equ eq ==> impl) R) ->
    L (val x) (val y) ->
    ss L R (Ret x : ctree E C X) (Ret y : ctree F D Y).
  Proof.
    intros Rstuck PROP Lval.
    cbn; intros ? ? TR; inv_trans; subst;
      cbn; eexists; eexists; intuition; etrans;
      now rewrite EQ.
  Qed.

  Lemma step_ss_ret {Y F D} (x : X) (y : Y) (L : rel _ _)
    {R : Chain (@ss E F C D X Y L)} :
    L (val x) (val y) ->
    ss L `R (Ret x : ctree E C X) (Ret y : ctree F D Y).
  Proof.
    intros.
    apply step_ss_ret_gen.
    - apply (b_chain R).
      apply is_stuck_ss; apply Stuck_is_stuck.
    - typeclasses eauto.
    - apply H.
  Qed.

  Lemma step_ss_ret_l_gen {Y F D} (x : X) (y : Y) (u u' : ctree F D Y) (L R : rel _ _) :
    R Stuck Stuck ->
    (Proper (equ eq ==> equ eq ==> impl) R) ->
    L (val x) (val y) ->
    trans (val y) u u' ->
    ss L R (Ret x : ctree E C X) u.
  Proof.
    intros. cbn. intros.
    apply trans_val_inv in H2 as ?.
    inv_trans. subst. setoid_rewrite EQ.
    etrans.
  Qed.

  Lemma step_ss_ret_l {Y F D} (x : X) (y : Y) (u u' : ctree F D Y) (L : rel _ _)
    {R : Chain (@ss E F C D X Y L)} :
    L (val x) (val y) ->
    trans (val y) u u' ->
    ss L ` R (Ret x : ctree E C X) u.
  Proof.
    intros.
    eapply step_ss_ret_l_gen; eauto.
    - apply (b_chain R).
      apply is_stuck_ss; apply Stuck_is_stuck.
    - typeclasses eauto.
  Qed.

  Lemma ssim_ret {Y F D} (x : X) (y : Y) (L : rel _ _) :
    L (val x) (val y) ->
    ssim L (Ret x : ctree E C X) (Ret y : ctree F D Y).
  Proof.
    intros. step. now apply step_ss_ret.
  Qed.

(*|
 The vis nodes are deterministic from the perspective of the labeled
 transition system, stepping is hence symmetric and we can just recover
 the itree-style rule.
|*)
  Lemma step_ss_vis_gen {Y Z Z' F D} (e : E Z) (f: F Z')
    (k : Z -> ctree E C X) (k' : Z' -> ctree F D Y) (R L: rel _ _) :
    (Proper (equ eq ==> equ eq ==> impl) R) ->
    (forall x, exists y, R (k x) (k' y) /\ L (obs e x) (obs f y)) ->
    ss L R (Vis e k) (Vis f k').
  Proof.
    intros.
    cbn; intros ? ? TR; inv_trans; subst;
      destruct (H0 x) as (x' & RR & LL);
      cbn; eexists; eexists; intuition.
    - rewrite EQ; eauto.
    - assumption.
  Qed.

  Lemma step_ss_vis {Y Z Z' F D} (e : E Z) (f: F Z')
        (k : Z -> ctree E C X) (k' : Z' -> ctree F D Y) (L : rel _ _)
    {R : Chain (@ss E F C D X Y L)} :
    (forall x, exists y, ` R (k x) (k' y) /\ L (obs e x) (obs f y)) ->
    ss L ` R (Vis e k) (Vis f k').
  Proof.
    intros * EQ.
    apply step_ss_vis_gen; auto.
    typeclasses eauto.
  Qed.

  Lemma ssim_vis {Y Z Z' F D} (e : E Z) (f: F Z')
        (k : Z -> ctree E C X) (k' : Z' -> ctree F D Y) (L : rel _ _) :
    (forall x, exists y, ssim L (k x) (k' y) /\ L (obs e x) (obs f y)) ->
    ssim L (Vis e k) (Vis f k').
  Proof.
    intros. step. apply step_ss_vis; auto.
  Qed.

  Lemma step_ss_vis_id_gen {Y Z F D} (e : E Z) (f: F Z)
        (k : Z -> ctree E C X) (k' : Z -> ctree F D Y) (R L: rel _ _) :
    (Proper (equ eq ==> equ eq ==> impl) R) ->
    (forall x, R (k x) (k' x) /\ L (obs e x) (obs f x)) ->
    ss L R (Vis e k) (Vis f k').
  Proof.
    intros. apply step_ss_vis_gen. { typeclasses eauto. }
    eauto.
  Qed.

  Lemma step_ss_vis_id {Y Z F D} (e : E Z) (f: F Z)
        (k : Z -> ctree E C X) (k' : Z -> ctree F D Y) (L : rel _ _)
    {R : Chain (@ss E F C D X Y L)} :
    (forall x, ` R (k x) (k' x) /\ L (obs e x) (obs f x)) ->
    ss L ` R (Vis e k) (Vis f k').
  Proof.
    intros * EQ.
    apply step_ss_vis_id_gen; auto.
    typeclasses eauto.
  Qed.

  Lemma ssim_vis_id {Y Z F D} (e : E Z) (f: F Z)
        (k : Z -> ctree E C X) (k' : Z -> ctree F D Y) (L : rel _ _) :
    (forall x, ssim L (k x) (k' x) /\ L (obs e x) (obs f x)) ->
    ssim L (Vis e k) (Vis f k').
  Proof.
    intros. step. now apply step_ss_vis_id.
  Qed.

(*|
  Same goes for visible tau nodes.
|*)
  Lemma step_ss_step_gen {Y F D}
        (t : ctree E C X) (t': ctree F D Y) (R L: rel _ _):
    (Proper (equ eq ==> equ eq ==> impl) R) ->
    L τ τ ->
    (R t t') ->
    ss L R (Step t) (Step t').
  Proof.
    intros PR ? EQs.
    intros ? ? TR; inv_trans; subst.
    cbn; do 2 eexists; split; [etrans | split; [rewrite EQ; eauto|assumption]].
  Qed.

  Lemma step_ss_step {Y F D}
        (t: ctree E C X) (t': ctree F D Y) (L : rel _ _)
        {R : Chain (@ss E F C D X Y L)} :
    (` R t t') ->
    L τ τ ->
    ss L ` R (Step t) (Step t').
  Proof.
    intros.
    apply step_ss_step_gen; auto.
    typeclasses eauto.
  Qed.

  Lemma step_ssim_step {Y F D}
        (t: ctree E C X) (t': ctree F D Y) (L : rel _ _) :
    (ssim L t t') ->
    L τ τ ->
    ssim L (Step t) (Step t').
  Proof.
    intros.
    step. apply step_ss_step; auto.
  Qed.

(*|
    For invisible nodes, the situation is different: we may kill them, but that execution
    cannot act as going under the guard.
|*)
  Lemma step_ss_br_l_gen {Y F D Z} (c : C Z)
        (k : Z -> ctree E C X) (t': ctree F D Y) (R L: rel _ _):
    (forall x, ss L R (k x) t') ->
    ss L R (Br c k) t'.
  Proof.
    intros EQs.
    intros ? ? TR; inv_trans; subst.
    apply EQs in TR; destruct TR as (u' & TR' & EQ').
    eauto.
  Qed.

  Lemma step_ss_br_l {Y F D Z} (c : C Z)
        (k : Z -> ctree E C X) (t: ctree F D Y) (L: rel _ _)
        {R : Chain (@ss E F C D X Y L)} :
    (forall x,  ss L `R (k x) t) ->
    ss L `R (Br c k) t.
  Proof.
    intros.
    intros ? ? TR; inv_trans; subst.
    apply H in TR as (? & ? & ?).
    eauto.
  Qed.

  Lemma ssim_br_l {Y F D Z} (c : C Z)
        (k : Z -> ctree E C X) (t: ctree F D Y) (L: rel _ _):
    (forall x, ssim L (k x) t) ->
    ssim L (Br c k) t.
  Proof.
    intros. step. apply step_ss_br_l_gen. intros.
    specialize (H x). step in H. apply H.
  Qed.

  Lemma step_ss_br_r_gen {Y F D Z} (c : D Z) x
        (k : Z -> ctree F D Y) (t: ctree E C X) (R L: rel _ _):
    ss L R t (k x) ->
    ss L R t (Br c k).
  Proof.
    cbn. intros.
    apply H in H0 as (? & ? & ? & ? & ?).
    exists x0; etrans.
  Qed.

  Lemma step_ss_br_r {Y F D Z} (c : D Z) x
        (k : Z -> ctree F D Y) (t: ctree E C X) (L: rel _ _)
        {R : Chain (@ss E F C D X Y L)} :
    ss L `R t (k x) ->
    ss L `R t (Br c k).
  Proof.
    apply step_ss_br_r_gen.
  Qed.

  Lemma ssim_br_r {Y F D Z} (c : D Z) x
        (k : Z -> ctree F D Y) (t: ctree E C X) (L: rel _ _):
    ssim L t (k x) ->
    ssim L t (Br c k).
  Proof.
    intros. step. apply step_ss_br_r_gen with (x := x). now step in H.
  Qed.

  Lemma step_ss_br_gen {Y F D n m} (a: C n) (b: D m)
    (k : n -> ctree E C X) (k' : m -> ctree F D Y) (R L : rel _ _) :
    (forall x, exists y, ss L R (k x) (k' y)) ->
    ss L R (Br a k) (Br b k').
  Proof.
    intros EQs.
    apply step_ss_br_l_gen.
    intros. destruct (EQs x) as [x' ?].
    now apply step_ss_br_r_gen with (x:=x').
  Qed.

  Lemma step_ss_br {Y F D n m} (cn: C n) (cm: D m)
    (k : n -> ctree E C X) (k' : m -> ctree F D Y) (L : rel _ _)
    {R : Chain (@ss E F C D X Y L)} :
    (forall x, exists y, ss L `R (k x) (k' y)) ->
    ss L `R (Br cn k) (Br cm k').
  Proof.
    apply step_ss_br_gen.
  Qed.

  Lemma ssim_br {Y F D n m} (cn: C n) (cm: D m)
    (k : n -> ctree E C X) (k' : m -> ctree F D Y) (L : rel _ _) :
    (forall x, exists y, ssim L (k x) (k' y)) ->
    ssim L (Br cn k) (Br cm k').
  Proof.
    intros. step. apply step_ss_br_gen.
    intros. destruct (H x). step in H0. exists x0. apply H0.
  Qed.

  Lemma step_ss_br_id_gen {Y F D n} (c: C n) (d: D n)
        (k : n -> ctree E C X) (k' : n -> ctree F D Y)
        (R L : rel _ _) :
    (forall x, ss L R (k x) (k' x)) ->
    ss L R (Br c k) (Br d k').
  Proof.
   intros; apply step_ss_br_gen.
   eauto.
  Qed.

  Lemma step_ss_br_id {Y F D n} (c: C n) (d: D n)
    (k : n -> ctree E C X) (k': n -> ctree F D Y) (L: rel _ _)
    {R : Chain (@ss E F C D X Y L)} :
    (forall x, ss L `R (k x) (k' x)) ->
    ss L `R (Br c k) (Br d k').
  Proof.
    intros; apply step_ss_br; eauto.
  Qed.

  Lemma ssim_br_id {Y F D n} (c: C n) (d: D n)
    (k : n -> ctree E C X) (k': n -> ctree F D Y) (L: rel _ _) :
    (forall x, ssim L (k x) (k' x)) ->
    ssim L (Br c k) (Br d k').
  Proof.
    intros. apply ssim_br. eauto.
  Qed.

  Lemma step_ss_guard_gen {Y F D}
        (t: ctree E C X) (t': ctree F D Y) (R L: rel _ _):
    ss L R t t' ->
    ss L R (Guard t) (Guard t').
  Proof.
    intros EQ.
    intros ? ? TR; inv_trans; subst.
    apply EQ in TR; destruct TR as (u' & ? & TR' & ? & EQ').
    do 2 eexists; split.
    constructor. apply TR'.
    eauto.
  Qed.

  Lemma step_ss_guard_l_gen {Y F D}
        (t: ctree E C X) (t': ctree F D Y) (R L: rel _ _):
    ss L R t t' ->
    ss L R (Guard t) t'.
  Proof.
    intros EQ.
    intros ? ? TR; inv_trans; subst.
    apply EQ in TR; destruct TR as (u' & ? & TR' & ? & EQ').
    eauto.
  Qed.

  Lemma step_ss_guard_r_gen {Y F D}
    (t: ctree E C X) (t': ctree F D Y) (R L: rel _ _):
    ss L R t t' ->
    ss L R t (Guard t').
  Proof.
    intros EQ.
    intros ? ? TR; inv_trans; subst.
    apply EQ in TR; destruct TR as (u' & ? & TR' & ? & EQ').
    do 2 eexists; split.
    constructor. apply TR'.
    eauto.
  Qed.

  Lemma step_ss_guard_l {Y F D}
    (t: ctree E C X) (t': ctree F D Y) (L: rel _ _)
    {R : Chain (@ss E F C D X Y L)} :
    ss L `R t t' ->
    ss L `R (Guard t) t'.
  Proof.
    intros.
    intros ? ? TR; inv_trans; subst.
    apply H in TR as (? & ? & TR' & ?).
    eauto.
  Qed.

  Lemma step_ss_guard_r {Y F D}
    (t: ctree E C X) (t': ctree F D Y) (L: rel _ _)
    {R : Chain (@ss E F C D X Y L)} :
    ss L `R t t' ->
    ss L `R t (Guard t').
  Proof.
    intros.
    intros ? ? TR; inv_trans; subst.
    apply H in TR as (? & ? & TR' & ?).
    do 2 eexists; split; [constructor; apply TR' |]; eauto.
  Qed.

  Lemma step_ss_guard {Y F D}
    (t: ctree E C X) (t': ctree F D Y) (L: rel _ _)
    {R : Chain (@ss E F C D X Y L)} :
    ss L `R t t' ->
    ss L `R (Guard t) (Guard t').
  Proof.
    intros.
    intros ? ? TR; inv_trans; subst.
    apply H in TR as (? & ? & TR' & ?).
    do 2 eexists; split; [constructor; apply TR' |]; eauto.
  Qed.

  Lemma ssim_guard_l {Y F D}
        (t: ctree E C X) (t': ctree F D Y) (L: rel _ _):
    ssim L t t' ->
    ssim L (Guard t) t'.
  Proof.
    intros; step; apply step_ss_guard_l; step in H; auto.
  Qed.

  Lemma ssim_guard_r {Y F D}
        (t: ctree E C X) (t': ctree F D Y) (L: rel _ _):
    ssim L t t' ->
    ssim L t (Guard t').
  Proof.
    intros; step; apply step_ss_guard_r; step in H; auto.
  Qed.

  Lemma ssim_guard {Y F D}
        (t: ctree E C X) (t': ctree F D Y) (L: rel _ _):
    ssim L t t' ->
    ssim L (Guard t) (Guard t').
  Proof.
    intros; step; apply step_ss_guard; step in H; auto.
  Qed.

(*|
    When matching visible brs one against another, in general we need to explain how
    we map the branches from the left to the branches to the right.
    A useful special case is the one where the arity coincide and we simply use the identity
    in both directions. We can in this case have [n] rather than [2n] obligations.
|*)
  Lemma step_ss_brS_gen {Z Z' Y F D} (c : C Z) (d : D Z')
        (k : Z -> ctree E C X) (k' : Z' -> ctree F D Y) (R L: rel _ _) :
    (Proper (equ eq ==> equ eq ==> impl) R) ->
    (forall x, exists y, R (k x) (k' y)) ->
    L τ τ ->
    ss L R (BrS c k) (BrS d k').
  Proof.
    intros.
    eapply step_ss_br_gen.
    intros.
    specialize (H0 x) as [y ?].
    exists y.
    eapply step_ss_step_gen; auto.
  Qed.

  Lemma step_ss_brS {Z Z' Y F D} (c : C Z) (c' : D Z')
        (k : Z -> ctree E C X) (k' : Z' -> ctree F D Y) (L: rel _ _)
        {R : Chain (@ss E F C D X Y L)} :
    (forall x, exists y, (elem R) (k x) (k' y)) ->
    L τ τ ->
    ss L ` R (BrS c k) (BrS c' k').
  Proof.
    intros.
    eapply step_ss_br.
    intros x; specialize (H x) as [y ?].
    exists y.
    eapply step_ss_step; auto.
  Qed.

  Lemma ssim_brS {Z Z' Y F D} (c : C Z) (c' : D Z')
        (k : Z -> ctree E C X) (k' : Z' -> ctree F D Y) (L: rel _ _) :
    (forall x, exists y, ssim L (k x) (k' y)) ->
    L τ τ ->
    ssim L (BrS c k) (BrS c' k').
  Proof.
    intros.
    apply ssim_br.
    intros x; specialize (H x) as [y ?]; exists y.
    apply step_ssim_step; auto.
  Qed.

  Lemma step_ss_brS_id_gen {Z Y D F} (c : C Z) (d: D Z)
        (k: Z -> ctree E C X) (k': Z -> ctree F D Y) (R L : rel _ _) :
    (Proper (equ eq ==> equ eq ==> impl) R) ->
    (forall x, R (k x) (k' x)) ->
    L τ τ ->
    ss L R (BrS c k) (BrS d k').
  Proof.
    intros; apply step_ss_brS_gen; eauto.
  Qed.

  Lemma step_ss_brS_id {Z Y D F} (c : C Z) (d : D Z)
        (k: Z -> ctree E C X) (k': Z -> ctree F D Y) (L : rel _ _)
        {R : Chain (@ss E F C D X Y L)} :
    (forall x, `R (k x) (k' x)) ->
    L τ τ ->
    ss L ` R (BrS c k) (BrS d k').
  Proof.
    intros.
    apply step_ss_brS; eauto.
  Qed.

  Lemma ssim_brS_id {Z Y D F} (c : C Z) (d : D Z)
        (k: Z -> ctree E C X) (k': Z -> ctree F D Y) (L : rel _ _) :
    (forall x, ssim L (k x) (k' x)) ->
    L τ τ ->
    ssim L (BrS c k) (BrS d k').
  Proof.
    intros.
    apply ssim_brS; eauto.
  Qed.

(*|
    Note that with visible schedules, nary-spins are equivalent only
    if neither are empty, or if both are empty: they match each other's
    τ challenge infinitely often.
    With invisible schedules, they are always equivalent: neither of them
    produce any challenge for the other.
|*)
  Lemma spinS_gen_nonempty : forall {Z X Y D F} {L: rel (label E) (label F)}
                               (x: X) (y: Y)
                               (c: C X) (c': D Y),
      L τ τ ->
      ssim L (@spinS_gen E C Z X c) (@spinS_gen F D Z Y c').
  Proof.
    intros until L; intros x y.
    coinduction S CIH; simpl. intros ? ? ? ? ? TR;
      rewrite ctree_eta in TR; cbn in TR.
      apply trans_brS_inv in TR as (_ & EQ & ->).
      eexists; eexists.
      rewrite ctree_eta; cbn.
      split; [econstructor|].
      + exact y.
      + constructor. reflexivity.
      + rewrite EQ; eauto.
  Qed.

(*|
Inversion principles
--------------------
|*)
  Lemma ssim_ret_inv {F D Y} {L: rel (label E) (label F)} (r1 : X) (r2 : Y) :
    ssim L (Ret r1 : ctree E C X) (Ret r2 : ctree F D Y) ->
    L (val r1) (val r2).
  Proof.
    intro.
    eplay.
    inv_trans; subst; assumption.
  Qed.

  Lemma ss_ret_l_inv {F D Y L R} :
    forall r (u : ctree F D Y),
    ss L R (Ret r : ctree E C X) u ->
    exists l' u', trans l' u u' /\ R Stuck u' /\ L (val r) l'.
  Proof.
    intros. apply H; etrans.
  Qed.

  Lemma ssim_ret_l_inv {F D Y L} :
    forall r (u : ctree F D Y),
    ssim L (Ret r : ctree E C X) u ->
    exists l' u', trans l' u u' /\ L (val r) l'.
  Proof.
    intros. step in H.
    apply ss_ret_l_inv in H as (? & ? & ? & ? & ?). etrans.
  Qed.

  Lemma ssim_vis_inv_type {D Y X1 X2}
    (e1 : E X1) (e2 : E X2) (k1 : X1 -> ctree E C X) (k2 : X2 -> ctree E D Y) (x1 : X1):
    ssim eq (Vis e1 k1) (Vis e2 k2) ->
    X1 = X2.
  Proof.
    intros.
    step in H; cbn in H.
    edestruct H as (? & ? & ? & ? & ?).
    etrans.
    inv_trans; subst; auto.
    eapply obs_eq_invT; eauto.
    Unshelve.
    exact x1.
  Qed.

  Lemma ssbt_vis_inv {F D Y X1 X2} {L: rel (label E) (label F)}
    (e1 : E X1) (e2 : F X2) (k1 : X1 -> ctree E C X) (k2 : X2 -> ctree F D Y) (x : X1)
    {R : Chain (@ss E F C D X Y L)} :
    ss L (elem R) (Vis e1 k1) (Vis e2 k2) ->
    (exists y, L (obs e1 x) (obs e2 y))  /\ (forall x, exists y, ` R (k1 x) (k2 y)).
  Proof.
    intros.
    split; intros; edestruct H as (? & ? & ? & ? & ?);
      etrans; subst;
      inv_trans; subst; eexists; auto.
    - now eapply H2.
    - now apply H1.
  Qed.

  Lemma ssim_vis_inv {F D Y X1 X2} {L: rel (label E) (label F)}
        (e1 : E X1) (e2 : F X2) (k1 : X1 -> ctree E C X) (k2 : X2 -> ctree F D Y) (x : X1):
    ssim L (Vis e1 k1) (Vis e2 k2) ->
    (exists y, L (obs e1 x) (obs e2 y)) /\ (forall x, exists y, ssim L (k1 x) (k2 y)).
  Proof.
    intros.
    split.
      - eplay.
        inv_trans; subst; exists x2; eauto.
      - intros y.
        step in H.
        cbn in H.
        edestruct H as (l' & u' & TR & IN & HL).
        apply trans_vis with (x := y).
        inv_trans.
        eexists.
        apply IN.
  Qed.

  Lemma ss_vis_l_inv {F D Y Z L R} :
    forall (e : E Z) (k : Z -> ctree E C X) (u : ctree F D Y) x,
    ss L R (Vis e k) u ->
    exists l' u', trans l' u u' /\ R (k x) u' /\ L (obs e x) l'.
  Proof.
    intros. apply H; etrans.
  Qed.

  Lemma ssim_vis_l_inv {F D Y Z L} :
    forall (e : E Z) (k : Z -> ctree E C X) (u : ctree F D Y) x,
    ssim L (Vis e k) u ->
    exists l' u', trans l' u u' /\ ssim L (k x) u' /\ L (obs e x) l'.
  Proof.
    intros. step in H.
    now simple apply ss_vis_l_inv with (x := x) in H.
  Qed.

  Lemma ss_step_inv {F D Y} {L: rel (label E) (label F)} {R : Chain (@ss E F C D X Y L)}
        (t1 : ctree E C X) (t2 : ctree F D Y) :
    ss L (elem R) (Step t1) (Step t2) ->
    (elem R t1 t2).
  Proof.
    intros EQ.
    edestruct EQ as (l & t & TR & REL & HL); etrans.
    now inv_trans.
  Qed.

  Lemma ssim_step_inv {F D Y} {L: rel (label E) (label F)}
        (t1 : ctree E C X) (t2 : ctree F D Y) :
    ssim L (Step t1) (Step t2) ->
    ssim L t1 t2.
  Proof.
    intros EQ. step in EQ. now apply ss_step_inv.
  Qed.

  Lemma ss_step_l_inv {F D Y L R} :
    forall (t : ctree E C X) (u : ctree F D Y),
    ss L R (Step t) u ->
    exists l' u', trans l' u u' /\ R t u' /\ L τ l'.
  Proof.
    etrans.
  Qed.

  Lemma ssim_step_l_inv {F D Y L} :
    forall (t : ctree E C X) (u : ctree F D Y),
    Step t (≲L) u ->
    exists l' u', trans l' u u' /\ t (≲L) u' /\ L τ l'.
  Proof.
    intros. step in H. etrans.
  Qed.

  Lemma ssbt_brS_inv {F D Y} {L: rel (label E) (label F)} {R : Chain (@ss E F C D X Y L)}
        n m (cn: C n) (cm: D m) (k1 : n -> ctree E C X) (k2 : m -> ctree F D Y) :
    ss L (elem R) (BrS cn k1) (BrS cm k2) ->
    (forall i1, exists i2, elem R (k1 i1) (k2 i2)).
  Proof.
    intros EQ i1.
    edestruct EQ as (l & t & TR & REL & HL); etrans.
    inv_trans. subst. eauto.
  Qed.

  Lemma ssim_brS_inv {F D Y} {L: rel (label E) (label F)}
        n m (cn: C n) (cm: D m) (k1 : n -> ctree E C X) (k2 : m -> ctree F D Y) :
    ssim L (BrS cn k1) (BrS cm k2) ->
    (forall i1, exists i2, ssim L (k1 i1) (k2 i2)).
  Proof.
    intros EQ i1.
    eplay.
    subst; inv_trans.
    eexists; eauto.
  Qed.

  Lemma ss_brS_l_inv {F D Y Z L R} :
    forall (c : C Z) (k : Z -> ctree E C X) (u : ctree F D Y) x,
    ss L R (BrS c k) u ->
    exists l' u', trans l' u u' /\ R (k x) u' /\ L τ l'.
  Proof.
    intros. apply H; etrans.
  Qed.

  Lemma ssim_brS_l_inv {F D Y Z L} :
    forall (c : C Z) (k : Z -> ctree E C X) (u : ctree F D Y) x,
    ssim L (BrS c k) u ->
    exists l' u', trans l' u u' /\ ssim L (k x) u' /\ L τ l'.
  Proof.
    intros. step in H.
    now simple apply ss_brS_l_inv with (x := x) in H.
  Qed.

  Lemma ss_br_l_inv {F D Y} {L: rel (label E) (label F)}
        n (c: C n) (t : ctree F D Y) (k : n -> ctree E C X) R:
    ss L R (Br c k) t ->
    forall x, ss L R (k x) t.
  Proof.
    cbn. intros.
    eapply trans_br in H0; [| reflexivity].
    apply H in H0 as (? & ? & ? & ? & ?); subst.
    eauto.
  Qed.

  Lemma ssim_br_l_inv {F D Y} {L: rel (label E) (label F)}
        n (c: C n) (t : ctree F D Y) (k : n -> ctree E C X):
    ssim L (Br c k) t ->
    forall x, ssim L (k x) t.
  Proof.
    intros. step. step in H. eapply ss_br_l_inv. apply H.
  Qed.

  Lemma ss_guard_l_inv {F D Y} {L: rel (label E) (label F)}
    (t : ctree E C X) (u : ctree F D Y) R:
    ss L R (Guard t) u ->
    ss L R t u.
  Proof.
    cbn. intros.
    eapply trans_guard in H0.
    apply H in H0 as (? & ? & ? & ? & ?); subst.
    eauto.
  Qed.

  Lemma ssim_guard_l_inv {F D Y} {L: rel (label E) (label F)}
    (t : ctree E C X) (u : ctree F D Y):
    ssim L (Guard t) u ->
    ssim L t u.
  Proof.
    intros. step. step in H. eapply ss_guard_l_inv. apply H.
  Qed.

  (* This one isn't very convenient... *)
  Lemma ssim_br_r_inv {F D Y} {L: rel (label E) (label F)}
        n (c: D n) (t : ctree E C X) (k : n -> ctree F D Y):
    ssim L t (Br c k) ->
    forall l t', trans l t t' ->
    exists l' x t'' , trans l' (k x) t'' /\ L l l' /\ (ssim L t' t'').
  Proof.
    cbn. intros. step in H. apply H in H0 as (? & ? & ? & ? & ?); subst. inv_trans.
    do 3 eexists; eauto.
  Qed.

End Proof_Rules.
