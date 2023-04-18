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

  #[global] Instance weq_ss : forall {E F C D X Y} `{B0 -< C} `{B0 -< D}, Proper (weq ==> weq) (@ss E F C D X Y _ _).
  Proof.
    cbn. intros. split.
    - intros. apply H2 in H3 as (? & ? & ? & ? & ?).
      exists x0, x1. split. apply H3. split. apply H4. apply H1. apply H5.
    - intros. apply H2 in H3 as (? & ? & ? & ? & ?).
      exists x0, x1. split. apply H3. split. apply H4. apply H1. apply H5.
  Qed.

End StrongSim.

Definition ssim {E F C D X Y} `{HasStuck : B0 -< C} `{HasStuck' : B0 -< D} L :=
  (gfp (@ss E F C D X Y _ _ L): hrel _ _).

#[global] Instance weq_ssim : forall {E F C D X Y} `{B0 -< C} `{B0 -< D},
  Proper (weq ==> weq) (@ssim E F C D X Y _ _).
Proof.
  intros. split.
  - intro. unfold ssim.
    epose proof (gfp_weq (ss x) (ss y)). lapply H3.
    + intro. red in H4. cbn in H4. rewrite <- H4. unfold ssim in H2. apply H2.
    + now rewrite H1.
  - intro. unfold ssim.
    epose proof (gfp_weq (ss x) (ss y)). lapply H3.
    + intro. red in H4. cbn in H4. rewrite H4. unfold ssim in H2. apply H2.
    + now rewrite H1.
Qed.

Module SSimNotations.

  (*| ss (simulation) notation |*)
  Notation sst L := (t (ss L)).
  Notation ssbt L := (bt (ss L)).
  Notation ssT L := (T (ss L)).
  Notation ssbT L := (bT (ss L)).

  Notation "t (≲ L ) u" := (ssim L t u) (at level 70).
  Notation "t ≲ u" := (ssim eq t u) (at level 70). (* FIXME we should ensure that return types are the same. *)
  Notation "t [≲ L ] u" := (ss L _ t u) (at level 79).
  Notation "t [≲] u" := (ss eq _ t u) (at level 79).
  Notation "t {≲ L } u" := (sst L _ t u) (at level 79).
  Notation "t {≲} u" := (sst eq _ t u) (at level 79).
  Notation "t {{≲ L }} u" := (ssbt L _ t u) (at level 79).
  Notation "t {{≲}} u" := (ssbt eq _ t u) (at level 79).

End SSimNotations.

Import SSimNotations.

Ltac fold_ssim :=
  repeat
    match goal with
    | h: context[gfp (@ss ?E ?F ?C ?D ?X ?Y _ _ ?L)] |- _ => fold (@ssim E F C D X Y _ _ L) in h
    | |- context[gfp (@ss ?E ?F ?C ?D ?X ?Y _ _ ?L)]      => fold (@ssim E F C D X Y _ _ L)
    end.

Ltac __coinduction_ssim R H :=
  (try unfold ssim);
  apply_coinduction; fold_ssim; intros R H.

Tactic Notation "__step_ssim" :=
  match goal with
  | |- context[@ssim ?E ?F ?C ?D ?X ?Y _ _ ?LR] =>
      unfold ssim;
      step;
      fold (@ssim E F C D X Y _ _ L)
  end.

#[local] Tactic Notation "step" := __step_ssim || step.

#[local] Tactic Notation "coinduction" simple_intropattern(R) simple_intropattern(H) :=
  __coinduction_ssim R H || coinduction R H.

Ltac __step_in_ssim H :=
  match type of H with
  | context[@ssim ?E ?F ?C ?D ?X ?Y _ _ ?LR] =>
      unfold ssim in H;
      step in H;
      fold (@ssim E F C D X Y _ _ L) in H
  end.

#[local] Tactic Notation "step" "in" ident(H) := __step_in_ssim H || step in H.

Import CTreeNotations.
Import EquNotations.

Section ssim_homogenous_theory.
  Context {E C: Type -> Type} {X: Type}
          {L: relation (@label E)}
          {HasStuck1: B0 -< C}.

  Notation ss := (@ss E E C C X X _ _).
  Notation ssim := (@ssim E E C C X X _ _).
  Notation sst L := (coinduction.t (ss L)).
  Notation ssbt L := (coinduction.bt (ss L)).
  Notation ssT L := (coinduction.T (ss L)).

  (*|
    Various results on reflexivity and transitivity.
  |*)
  Lemma refl_sst `{Reflexive _ L}: const seq <= (sst L).
  Proof.
    apply leq_t. cbn.
    intros. unfold seq in H0. subst. eauto.
  Qed.

  Lemma square_sst `{Transitive _ L}: square <= (sst L).
  Proof.
    apply Coinduction; cbn.
    intros R x z [y xy yz] l x' xx'.
    destruct (xy _ _ xx') as (l' & y' & yy' & ? & ?).
    destruct (yz _ _ yy') as (l'' & z' & zz' & ? & ?).
    exists l'', z'.
    split.
    assumption.
    split.
    apply (f_Tf (ss L)).
    exists y'; eauto.
    transitivity l'; auto.
  Qed.

  (*| Reflexivity |*)
  #[global] Instance Reflexive_sst R `{Reflexive _ L}: Reflexive (sst L R).
  Proof. apply build_reflexive; apply ft_t; apply (refl_sst). Qed.

  Corollary Reflexive_ssim `{Reflexive _ L}: Reflexive (ssim L).
  Proof. now apply Reflexive_sst. Qed.

  #[global] Instance Reflexive_ssbt R `{Reflexive _ L}: Reflexive (ssbt L R).
  Proof. apply build_reflexive; apply fbt_bt; apply refl_sst. Qed.

  #[global] Instance Reflexive_ssT f R `{Reflexive _ L}: Reflexive (ssT L f R).
  Proof. apply build_reflexive; apply fT_T; apply refl_sst. Qed.

  (*| Transitivity |*)
  #[global] Instance Transitive_sst R `{Transitive _ L}: Transitive (sst L R).
  Proof. apply build_transitive; apply ft_t; apply (square_sst). Qed.

  Corollary Transitive_ssim `{Transitive _ L}: Transitive (ssim L).
  Proof. now apply Transitive_sst. Qed.

  #[global] Instance Transitive_ssbt R `{Transitive _ L}: Transitive (ssbt L R).
  Proof. apply build_transitive; apply fbt_bt; apply square_sst. Qed.

  #[global] Instance Transitive_ssT f R `{Transitive _ L}: Transitive (ssT L f R).
  Proof. apply build_transitive; apply fT_T; apply square_sst. Qed.

  (*| PreOrder |*)
  #[global] Instance PreOrder_sst R `{PreOrder _ L}: PreOrder (sst L R).
  Proof. split; typeclasses eauto. Qed.

  Corollary PreOrder_ssim `{PreOrder _ L}: PreOrder (ssim L).
  Proof. split; typeclasses eauto. Qed.

  #[global] Instance PreOrder_ssbt R `{PreOrder _ L}: PreOrder (ssbt L R).
  Proof. split; typeclasses eauto. Qed.

  #[global] Instance PreOrder_ssT f R `{PreOrder _ L}: PreOrder (ssT L f R).
  Proof. split; typeclasses eauto. Qed.

End ssim_homogenous_theory.

(*|
Parametric theory of [ss] with heterogenous [L]
|*)
Section ssim_heterogenous_theory.
  Arguments label: clear implicits.
  Context {E F C D: Type -> Type} {X Y: Type}
          {L: rel (@label E) (@label F)}
          {HasStuck1: B0 -< C} {HasStuck2: B0 -< D}.

  Notation ss := (@ss E F C D X Y _ _).
  Notation ssim  := (@ssim E F C D X Y _ _).
  Notation sst L := (coinduction.t (ss L)).
  Notation ssbt L := (coinduction.bt (ss L)).
  Notation ssT L := (coinduction.T (ss L)).

(*|
   Strong simulation up-to [equ] is valid
   ----------------------------------------
|*)
  Lemma equ_clos_sst : equ_clos <= (sst L).
  Proof.
    apply Coinduction; cbn.
    intros R x y [x' y' x'' y'' EQ' EQ''] l z x'z.
    rewrite EQ' in x'z.
    destruct (EQ'' _ _ x'z) as (l' & ? & ? & ? & ?).
    exists l', x0.
    split.
    - rewrite <- Equu; auto.
    - split; auto.
      eapply (f_Tf (ss L)).
      econstructor; auto; auto.
  Qed.

  #[global] Instance equ_clos_sst_goal {RR} :
    Proper (equ eq ==> equ eq ==> flip impl) (sst L RR).
  Proof.
    cbn; intros ? ? eq1 ? ? eq2 H.
    apply (ft_t equ_clos_sst); econstructor; [eauto | | symmetry; eauto]; assumption.
  Qed.

  #[global] Instance equ_clos_sst_ctx {RR} :
    Proper (equ eq ==> equ eq ==> impl) (sst L RR).
  Proof.
    cbn; intros ? ? eq1 ? ? eq2 H.
    apply (ft_t equ_clos_sst); econstructor; [symmetry; eauto | | eauto]; assumption.
  Qed.

  #[global] Instance equ_ssbt_closed_goal {r} :
    Proper (equ eq ==> equ eq ==> flip impl) (ssbt L r).
  Proof.
    cbn. intros.
    apply (fbt_bt equ_clos_sst); econstructor; eauto.
    now symmetry.
  Qed.

  #[global] Instance equ_ssbt_closed_ctx {r} :
    Proper (equ eq ==> equ eq ==> impl) (ssbt L r).
  Proof.
    cbn; intros.
    now rewrite H, H0 in H1.
  Qed.

  #[global] Instance equ_clos_ssT_goal RR f :
    Proper (equ eq ==> equ eq ==> flip impl) (ssT L f RR).
  Proof.
    cbn; intros ? ? eq1 ? ? eq2 H.
    apply (fT_T equ_clos_sst); econstructor; [eauto | | symmetry; eauto]; assumption.
  Qed.

  #[global] Instance equ_clos_ssT_ctx RR f :
    Proper (equ eq ==> equ eq ==> impl) (ssT L f RR).
  Proof.
    cbn; intros ? ? eq1 ? ? eq2 H.
    apply (fT_T equ_clos_sst); econstructor; [symmetry; eauto | | eauto]; assumption.
  Qed.

  #[global] Instance equ_clos_ssim_goal :
    Proper (equ eq ==> equ eq ==> flip impl) (ssim L).
  Proof.
    cbn; intros ? ? eq1 ? ? eq2 H.
    apply (ft_t equ_clos_sst); econstructor; [eauto | | symmetry; eauto]; assumption.
  Qed.

  #[global] Instance equ_clos_ssim_ctx :
    Proper (equ eq ==> equ eq ==> impl) (ssim L).
  Proof.
    cbn; intros ? ? eq1 ? ? eq2 H.
    apply (ft_t equ_clos_sst); econstructor; [symmetry; eauto | | eauto]; assumption.
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

  Lemma stuckD_ss (R : rel _ _) (t : ctree F D Y) : ss L R stuckD t.
  Proof.
    repeat intro. now apply stuckD_is_stuck in H.
  Qed.

  Lemma stuckD_ssim (t : ctree F D Y) : ssim L stuckD t.
  Proof.
    intros. step. apply stuckD_ss.
  Qed.

  Lemma spinD_ss (R : rel _ _) (t : ctree F D Y) `{HasTau: B1 -< C}: ss L R spinD t.
  Proof.
    repeat intro. now apply spinD_is_stuck in H.
  Qed.

  Lemma spinD_ssim : forall (t' : ctree F D Y) `{HasTau: B1 -< C},
      ssim L spinD t'.
  Proof.
    intros. step. apply spinD_ss.
  Qed.

End ssim_heterogenous_theory.


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
          `{HasStuck : B0 -< C} `{HasStuck' : B0 -< D}
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

  Definition is_update_val_rel (L0 : rel (@label E) (@label F)) : Prop :=
    forall l1 l2, wf_val X l1 -> wf_val Y l2 -> (L0 l1 l2 <-> update_val_rel l1 l2).

  Theorem update_val_rel_correct : is_update_val_rel update_val_rel.
  Proof.
    red. reflexivity.
  Qed.

(*|
Specialization of [bind_ctx] to a function acting with [ssim] on the bound value,
and with the argument (pointwise) on the continuation.
|*)
  Program Definition bind_ctx_ssim L0 : mon (rel (ctree E C X') (ctree F D Y')) :=
    {|body := fun R => @bind_ctx E F C D X Y X' Y' (ssim L0) (pointwise R0 R) |}.
  Next Obligation.
    intros ?? ? H. apply leq_bind_ctx. intros ?? H' ?? H''.
    apply in_bind_ctx. apply H'. intros t t' HS. apply H, H'', HS.
  Qed.

(*|
    The resulting enhancing function gives a valid up-to technique
|*)
  Lemma bind_ctx_ssim_t L0 (*{RV: Respects_val L}*):
    is_update_val_rel L0 -> bind_ctx_ssim L0 <= (sst L).
  Proof.
    intro HL0. apply Coinduction.
    intros R. apply (leq_bind_ctx _).
    intros t1 t2 tt k1 k2 kk.
    step in tt.
    simpl; intros l u STEP;
      apply trans_bind_inv in STEP as [(H & t' & STEP & EQ) | (v & STEPres & STEP)];
      cbn in *.
    apply tt in STEP as (u' & l' & STEP & EQ' & ?).
    do 2 eexists. split.
    apply trans_bind_l; eauto.
    + intro Hl. destruct Hl.
      apply HL0 in H0; etrans.
      inversion H0; subst. apply H. constructor. apply H2. constructor.
    + split.
      * apply (fT_T equ_clos_sst).
        econstructor; [exact EQ | | reflexivity].
        apply (fTf_Tf (ss L)).
        apply in_bind_ctx; auto.
        intros ? ? ?.
        apply (b_T (ss L)).
        red in kk; cbn; now apply kk.
      * apply HL0 in H0; etrans.
        destruct H0. exfalso. apply H. constructor. apply H2.
    + apply tt in STEPres as (u' & ? & STEPres & EQ' & ?).
      apply HL0 in H; etrans.
      dependent destruction H. 2: { exfalso. apply H. constructor. }
      pose proof (trans_val_inv STEPres) as EQ.
      rewrite EQ in STEPres.
      specialize (kk v v2 H).
      apply kk in STEP as (u'' & ? & STEP & EQ'' & ?); cbn in *.
      do 2 eexists; split.
      eapply trans_bind_r; eauto.
      split; auto.
      eapply (id_T (ss L)); auto.
  Qed.

End bind.

Theorem is_update_val_rel_eq {E X} : @is_update_val_rel E E X X eq eq eq.
Proof.
  split; intro.
  - subst. destruct l2.
    + constructor; auto.
      all: intro; inv H1.
    + constructor; auto.
      all: intro; inv H1.
    + red in H. specialize (H X0 v eq_refl). subst.
      constructor. reflexivity.
  - inv H1; reflexivity.
Qed.

Theorem update_val_rel_eq {E X} : forall l l', wf_val X l ->
  @update_val_rel E E X X eq eq l l' <-> l = l'.
Proof.
  split; intro.
  - destruct H0; now subst.
  - subst. destruct l'.
    3: { specialize (H X0 v eq_refl). subst. now left. }
    all: constructor; auto; intro; inversion H0.
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

(*|
Expliciting the reasoning rule provided by the up-to principles.
|*)
Lemma sst_clo_bind_gen {E F C D: Type -> Type} {X Y X' Y': Type} {L : rel (@label E) (@label F)}
      `{HasStuck: B0 -< C} `{HasStuck': B0 -< D}
      (R0 : rel X Y) L0
      (t1 : ctree E C X) (t2: ctree F D Y)
      (HL0 : is_update_val_rel L R0 L0)
      (k1 : X -> ctree E C X') (k2 : Y -> ctree F D Y') RR:
  t1 (≲L0) t2 ->
  (forall x y, R0 x y -> (sst L RR) (k1 x) (k2 y)) ->
  sst L RR (t1 >>= k1) (t2 >>= k2).
Proof.
  intros ? ?.
  apply (ft_t (@bind_ctx_ssim_t E F C D X X' Y Y' _ _ L R0 L0 HL0)).
  apply in_bind_ctx; eauto.
Qed.

Lemma sst_clo_bind {E F C D: Type -> Type} {X Y X' Y': Type} {L : rel (@label E) (@label F)}
      `{HasStuck: B0 -< C} `{HasStuck': B0 -< D}
      (R0 : rel X Y)
      (t1 : ctree E C X) (t2: ctree F D Y)
      (k1 : X -> ctree E C X') (k2 : Y -> ctree F D Y') RR:
  t1 (≲update_val_rel L R0) t2 ->
  (forall x y, R0 x y -> (sst L RR) (k1 x) (k2 y)) ->
  sst L RR (t1 >>= k1) (t2 >>= k2).
Proof.
  intros ? ?.
  eapply sst_clo_bind_gen; eauto.
  apply update_val_rel_correct.
Qed.

Lemma sst_clo_bind_eq {E C D: Type -> Type} {X X': Type}
      `{HasStuck: B0 -< C} `{HasStuck': B0 -< D}
      (t1 : ctree E C X) (t2: ctree E D X)
      (k1 : X -> ctree E C X') (k2 : X -> ctree E D X') RR:
  t1 ≲ t2 ->
  (forall x, sst eq RR (k1 x) (k2 x)) ->
  sst eq RR (t1 >>= k1) (t2 >>= k2).
Proof.
  intros ? ?.
  eapply sst_clo_bind_gen.
  - apply is_update_val_rel_eq.
  - assumption.
  - intros. now subst.
Qed.

Lemma ssbt_clo_bind_gen {E F C D: Type -> Type} {X Y X' Y': Type} {L : rel (@label E) (@label F)}
      `{HasStuck: B0 -< C} `{HasStuck': B0 -< D}
      (R0 : rel X Y) L0
      (t1 : ctree E C X) (t2: ctree F D Y)
      (HL0 : is_update_val_rel L R0 L0)
      (k1 : X -> ctree E C X') (k2 : Y -> ctree F D Y') RR:
  t1 (≲L0) t2 ->
  (forall x y, R0 x y -> (ssbt L RR) (k1 x) (k2 y)) ->
  ssbt L RR (t1 >>= k1) (t2 >>= k2).
Proof.
  intros ? ?.
  apply (fbt_bt (@bind_ctx_ssim_t E F C D X X' Y Y' _ _ L R0 L0 HL0)).
  apply in_bind_ctx; eauto.
Qed.

Lemma ssbt_clo_bind {E F C D: Type -> Type} {X Y X' Y': Type} {L : rel (@label E) (@label F)}
      `{HasStuck: B0 -< C} `{HasStuck': B0 -< D}
      (R0 : rel X Y)
      (t1 : ctree E C X) (t2: ctree F D Y)
      (k1 : X -> ctree E C X') (k2 : Y -> ctree F D Y') RR:
  t1 (≲update_val_rel L R0) t2 ->
  (forall x y, R0 x y -> (ssbt L RR) (k1 x) (k2 y)) ->
  ssbt L RR (t1 >>= k1) (t2 >>= k2).
Proof.
  intros ? ?.
  eapply ssbt_clo_bind_gen; eauto.
  apply update_val_rel_correct.
Qed.

Lemma ssbt_clo_bind_eq {E C D: Type -> Type} {X X': Type}
      `{HasStuck: B0 -< C} `{HasStuck': B0 -< D}
      (t1 : ctree E C X) (t2: ctree E D X)
      (k1 : X -> ctree E C X') (k2 : X -> ctree E D X') RR:
  t1 ≲ t2 ->
  (forall x, ssbt eq RR (k1 x) (k2 x)) ->
  ssbt eq RR (t1 >>= k1) (t2 >>= k2).
Proof.
  intros ? ?.
  eapply ssbt_clo_bind_gen.
  - apply is_update_val_rel_eq.
  - assumption.
  - intros. now subst.
Qed.

(*|
Specializing the congruence principle for [≲]
|*)
Lemma ssim_clo_bind_gen {E F C D: Type -> Type} {X Y X' Y': Type}  {L : rel (@label E) (@label F)}
      `{HasStuck: B0 -< C} `{HasStuck': B0 -< D}
      (R0 : rel X Y) L0
      (HL0 : is_update_val_rel L R0 L0)
      (t1 : ctree E C X) (t2: ctree F D Y)
      (k1 : X -> ctree E C X') (k2 : Y -> ctree F D Y'):
  ssim L0 t1 t2 ->
  (forall x y, R0 x y -> ssim L (k1 x) (k2 y)) ->
  ssim L (t1 >>= k1) (t2 >>= k2).
Proof.
  intros. eapply sst_clo_bind_gen; eauto.
Qed.

Lemma ssim_clo_bind {E F C D: Type -> Type} {X Y X' Y': Type} {L : rel (@label E) (@label F)}
      `{HasStuck: B0 -< C} `{HasStuck': B0 -< D}
      (R0 : rel X Y)
      (t1 : ctree E C X) (t2: ctree F D Y)
      (k1 : X -> ctree E C X') (k2 : Y -> ctree F D Y'):
  t1 (≲update_val_rel L R0) t2 ->
  (forall x y, R0 x y -> k1 x (≲L) k2 y) ->
  t1 >>= k1 (≲L) t2 >>= k2.
Proof.
  intros. eapply sst_clo_bind; eauto.
Qed.

Lemma ssim_clo_bind_eq {E C D: Type -> Type} {X X': Type}
      `{HasStuck: B0 -< C} `{HasStuck': B0 -< D}
      (t1 : ctree E C X) (t2: ctree E D X)
      (k1 : X -> ctree E C X') (k2 : X -> ctree E D X'):
  t1 ≲ t2 ->
  (forall x, k1 x ≲ k2 x) ->
  t1 >>= k1 ≲ t2 >>= k2.
Proof.
  intros. apply sst_clo_bind_eq; auto.
Qed.

(*|
And in particular, we can justify rewriting [≲] to the left of a [bind].
|*)
(*Lemma bind_ssim_cong_gen {E C X X'} RR {HasStuck: B0 -< C}
      {L: relation (@label E)} (R0 : relation X):
  Proper (ssim L ==> (fun f g => forall x y, sst L RR (f x) (g y)) ==> sst L RR) (@bind E C X X').
Proof.
  do 4 red; intros.
  eapply sst_clo_bind; auto.
Qed.*)

Tactic Notation "__upto_bind_ssim" uconstr(R0) :=
  match goal with
    |- @ssim ?E ?F ?C ?D ?X ?Y _ _ ?L (CTree.bind (T := ?T) _ _) (CTree.bind (T := ?T') _ _) =>
      apply (ssim_clo_bind_gen R0 (update_val_rel L R0) (update_val_rel_correct L R0))
  | |- body (t (@ss ?E ?F ?C ?D ?X ?Y _ _ ?L)) ?R (CTree.bind (T := ?T) _ _) (CTree.bind (T := ?T') _ _) =>
      apply (ft_t (@bind_ctx_ssim_t E F C D T X T' Y _ _ L R0
        (update_val_rel L R0) (update_val_rel_correct L R0))), in_bind_ctx
  | |- body (bt (@ss ?E ?F ?C ?D ?X ?Y _ _ ?L)) ?R (CTree.bind (T := ?T) _ _) (CTree.bind (T := ?T') _ _) =>
      apply (fbt_bt (@bind_ctx_ssim_t E F C D T X T' Y _ _ L R0
        (update_val_rel L R0) (update_val_rel_correct L R0))), in_bind_ctx
  end.

Tactic Notation "__upto_bind_eq_ssim" uconstr(R0) :=
  match goal with
  | |- @ssim ?E ?F ?C ?D ?X ?Y _ _ ?L (CTree.bind (T := ?T) _ _) (CTree.bind (T := ?T') _ _) =>
      __upto_bind_ssim R0; [reflexivity | intros ?]
  | _ => __upto_bind_ssim R0; [reflexivity | intros ? ? ?EQl]
  end.

Ltac __play_ssim := step; cbn; intros ? ? ?TR.

Ltac __play_ssim_in H :=
  step in H;
  cbn in H; edestruct H as (? & ? & ?TR & ?EQ & ?HL);
  clear H; [etrans |].

Ltac __eplay_ssim :=
  match goal with
  | h : @ssim ?E ?F ?C ?D ?X ?Y _ _ ?L _ _ |- _ =>
      __play_ssim_in h
  end.

#[local] Tactic Notation "play" := __play_ssim.
#[local] Tactic Notation "play" "in" ident(H) := __play_ssim_in H.
#[local] Tactic Notation "eplay" := __eplay_ssim.

Section Proof_Rules.

  Arguments label: clear implicits.
  Context {E C: Type -> Type}
          {X : Type}
          {HasStuck: B0 -< C}.

  Lemma step_ss_ret_gen {Y F D} `{HasStuck': B0 -< D}(x : X) (y : Y) (R L : rel _ _) :
    R stuckD stuckD ->
    (Proper (equ eq ==> equ eq ==> impl) R) ->
    L (val x) (val y) ->
    ss L R (Ret x : ctree E C X) (Ret y : ctree F D Y).
  Proof.
    intros Rstuck PROP Lval.
    cbn; intros ? ? TR; inv_trans; subst;
      cbn; eexists; eexists; intuition; etrans;
      now rewrite EQ.
  Qed.

  Lemma step_ss_ret {Y F D} `{HasStuck': B0 -< D} (x : X) (y : Y) (R L : rel _ _) :
    L (val x) (val y) ->
    ssbt L R (Ret x : ctree E C X) (Ret y : ctree F D Y).
  Proof.
    intros.
    apply step_ss_ret_gen.
    - step. intros.
      apply is_stuck_ss; apply stuckD_is_stuck.
    - typeclasses eauto.
    - apply H.
  Qed.

  Lemma ssim_ret {Y F D} `{HasStuck': B0 -< D} (x : X) (y : Y) (L : rel _ _) :
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
  Lemma step_ss_vis_gen {Y Z Z' F D} `{HasStuck': B0 -< D} (e : E Z) (f: F Z')
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

  Lemma step_ss_vis {Y Z Z' F D} `{HasStuck': B0 -< D} (e : E Z) (f: F Z')
        (k : Z -> ctree E C X) (k' : Z' -> ctree F D Y) (R L : rel _ _) :
    (forall x, exists y, sst L R (k x) (k' y) /\ L (obs e x) (obs f y)) ->
    ssbt L R (Vis e k) (Vis f k').
  Proof.
    intros * EQ.
    apply step_ss_vis_gen; auto.
    typeclasses eauto.
  Qed.

  Lemma ssim_vis {Y Z Z' F D} `{HasStuck': B0 -< D} (e : E Z) (f: F Z')
        (k : Z -> ctree E C X) (k' : Z' -> ctree F D Y) (L : rel _ _) :
    (forall x, exists y, ssim L (k x) (k' y) /\ L (obs e x) (obs f y)) ->
    ssim L (Vis e k) (Vis f k').
  Proof.
    intros. step. now apply step_ss_vis.
  Qed.

  Lemma step_ss_vis_id_gen {Y Z F D} `{HasStuck': B0 -< D} (e : E Z) (f: F Z)
        (k : Z -> ctree E C X) (k' : Z -> ctree F D Y) (R L: rel _ _) :
    (Proper (equ eq ==> equ eq ==> impl) R) ->
    (forall x, R (k x) (k' x) /\ L (obs e x) (obs f x)) ->
    ss L R (Vis e k) (Vis f k').
  Proof.
    intros. apply step_ss_vis_gen. { typeclasses eauto. }
    eauto.
  Qed.

  Lemma step_ss_vis_id {Y Z F D} `{HasStuck': B0 -< D} (e : E Z) (f: F Z)
        (k : Z -> ctree E C X) (k' : Z -> ctree F D Y) (R L : rel _ _) :
    (forall x, sst L R (k x) (k' x) /\ L (obs e x) (obs f x)) ->
    ssbt L R (Vis e k) (Vis f k').
  Proof.
    intros * EQ.
    apply step_ss_vis_id_gen; auto.
    typeclasses eauto.
  Qed.

  Lemma ssim_vis_id {Y Z F D} `{HasStuck': B0 -< D} (e : E Z) (f: F Z)
        (k : Z -> ctree E C X) (k' : Z -> ctree F D Y) (L : rel _ _) :
    (forall x, ssim L (k x) (k' x) /\ L (obs e x) (obs f x)) ->
    ssim L (Vis e k) (Vis f k').
  Proof.
    intros. step. now apply step_ss_vis_id.
  Qed.

  (*|
    Same goes for visible tau nodes.
    |*)
  Lemma step_ss_step_gen {Y F D} `{HasTau: B1 -< C} `{HasStuck': B0 -< D} `{HasTau': B1 -< D}
        (t : ctree E C X) (t': ctree F D Y) (R L: rel _ _):
    (Proper (equ eq ==> equ eq ==> impl) R) ->
    L tau tau ->
    (R t t') ->
    ss L R (Step t) (Step t').
  Proof.
    intros PR ? EQs.
    intros ? ? TR; inv_trans; subst.
    cbn; do 2 eexists; split; [etrans | split; [rewrite EQ; eauto|assumption]].
  Qed.

  Lemma step_ss_step {Y F D} `{HasStuck': B0 -< D} `{HasTau: B1 -< C} `{HasTau': B1 -< D}
        (t: ctree E C X) (t': ctree F D Y) (R L : rel _ _) :
    (sst L R t t') ->
    L tau tau ->
    ssbt L R (Step t) (Step t').
  Proof.
    intros. apply step_ss_step_gen; auto.
    typeclasses eauto.
  Qed.

  (*|
    When matching visible brs one against another, in general we need to explain how
    we map the branches from the left to the branches to the right.
    A useful special case is the one where the arity coincide and we simply use the identity
    in both directions. We can in this case have [n] rather than [2n] obligations.
    |*)
  Lemma step_ss_brS_gen {Z Z' Y F D} `{HasStuck': B0 -< D} (c : C Z) (d : D Z')
        (k : Z -> ctree E C X) (k' : Z' -> ctree F D Y) (R L: rel _ _) :
    (Proper (equ eq ==> equ eq ==> impl) R) ->
    (forall x, exists y, R (k x) (k' y)) ->
    L tau tau ->
    ss L R (BrS c k) (BrS d k').
  Proof.
    intros PROP EQs ? ? ? TR; inv_trans; subst.
    destruct (EQs x) as [y HR].
    cbn; do 2 eexists; split; [etrans | split; [rewrite EQ; eauto|assumption]].
  Qed.

  Lemma step_ss_brS {Z Z' Y F D} `{HasStuck' : B0 -< D} (c : C Z) (c' : D Z')
        (k : Z -> ctree E C X) (k' : Z' -> ctree F D Y) (R L: rel _ _) :
    (forall x, exists y, sst L R (k x) (k' y)) ->
    L tau tau ->
    ssbt L R (BrS c k) (BrS c' k').
  Proof.
    intros.
    apply step_ss_brS_gen; auto.
    typeclasses eauto.
  Qed.

  Lemma ssim_brS {Z Z' Y F D} `{HasStuck' : B0 -< D} (c : C Z) (c' : D Z')
        (k : Z -> ctree E C X) (k' : Z' -> ctree F D Y) (L: rel _ _) :
    (forall x, exists y, ssim L (k x) (k' y)) ->
    L tau tau ->
    ssim L (BrS c k) (BrS c' k').
  Proof.
    intros. step. now apply step_ss_brS.
  Qed.

  Lemma step_ss_brS_id_gen {Z Y D F} `{HasStuck': B0 -< D} (c : C Z) (d: D Z)
        (k: Z -> ctree E C X) (k': Z -> ctree F D Y) (R L : rel _ _) :
    (Proper (equ eq ==> equ eq ==> impl) R) ->
    (forall x, exists y, R (k x) (k' y)) ->
    L tau tau ->
    ss L R (BrS c k) (BrS d k').
  Proof.
    intros; apply step_ss_brS_gen; eauto.
  Qed.

  Lemma step_ss_brS_id {Z Y D F} `{HasStuck': B0 -< D} (c : C Z) (d : D Z)
        (k: Z -> ctree E C X) (k': Z -> ctree F D Y) (R L : rel _ _) :
    (forall x, exists y, sst L R (k x) (k' y)) ->
    L tau tau ->
    ssbt L R (BrS c k) (BrS d k').
  Proof.
    intros.
    apply step_ss_brS_id_gen; eauto.
    typeclasses eauto.
  Qed.

  Lemma ssim_brS_id {Z Y D F} `{HasStuck': B0 -< D} (c : C Z) (d : D Z)
        (k: Z -> ctree E C X) (k': Z -> ctree F D Y) (L : rel _ _) :
    (forall x, exists y, ssim L (k x) (k' y)) ->
    L tau tau ->
    ssim L (BrS c k) (BrS d k').
  Proof.
    intros. step. now apply step_ss_brS_id.
  Qed.

  Lemma ssim_step {Y F D} `{HasStuck': B0 -< D} `{HasTau: B1 -< C} `{HasTau': B1 -< D}
        (t: ctree E C X) (t': ctree F D Y) (L : rel _ _) :
    ssim L t t' ->
    L tau tau ->
    ssim L (Step t) (Step t').
  Proof.
    intros. apply ssim_brS_id; eauto.
  Qed.

  (*|
    For invisible nodes, the situation is different: we may kill them, but that execution
    cannot act as going under the guard.
    |*)
  Lemma step_ss_guard_gen {Y F D} `{HasStuck': B0 -< D} `{HasTau: B1 -< C} `{HasTau': B1 -< D}
        (t: ctree E C X) (t': ctree F D Y) (R L: rel _ _):
    ss L R t t' ->
    ss L R (Guard t) (Guard t').
  Proof.
    intros EQ.
    intros ? ? TR; inv_trans; subst.
    apply EQ in TR as (? & ? & ? & ? & ?); subst.
    do 2 eexists; split; [etrans | split; trivial].
  Qed.

  Lemma step_ss_guard {Y F D} `{HasStuck': B0 -< D} `{HasTau: B1 -< C} `{HasTau': B1 -< D}
        (t: ctree E C X) (t': ctree F D Y) (R L: rel _ _):
    ssbt L R t t' ->
    ssbt L R (Guard t) (Guard t').
  Proof.
    apply step_ss_guard_gen.
  Qed.

  Lemma step_ss_brD_l_gen {Y F D Z} `{HasStuck': B0 -< D} (c : C Z)
        (k : Z -> ctree E C X) (t': ctree F D Y) (R L: rel _ _):
    (forall x, ss L R (k x) t') ->
    ss L R (BrD c k) t'.
  Proof.
    intros EQs.
    intros ? ? TR; inv_trans; subst.
    apply EQs in TR; destruct TR as (u' & TR' & EQ').
    eauto.
  Qed.

  Lemma step_ss_brD_l {Y F D Z} `{HasStuck': B0 -< D} (c : C Z)
        (k : Z -> ctree E C X) (t: ctree F D Y) (R L: rel _ _):
    (forall x, ssbt L R (k x) t) ->
    ssbt L R (BrD c k) t.
  Proof.
    apply step_ss_brD_l_gen.
  Qed.

  Lemma ssim_brD_l {Y F D Z} `{HasStuck': B0 -< D} (c : C Z)
        (k : Z -> ctree E C X) (t: ctree F D Y) (L: rel _ _):
    (forall x, ssim L (k x) t) ->
    ssim L (BrD c k) t.
  Proof.
    intros. step. apply step_ss_brD_l. intros.
    specialize (H x). step in H. apply H.
  Qed.

  Lemma step_ss_brD_r_gen {Y F D Z} `{HasStuck': B0 -< D} (c : D Z) x
        (k : Z -> ctree F D Y) (t: ctree E C X) (R L: rel _ _):
    ss L R t (k x) ->
    ss L R t (BrD c k).
  Proof.
    cbn. intros.
    apply H in H0 as (? & ? & ? & ? & ?).
    exists x0; etrans.
  Qed.

  Lemma step_ss_brD_r {Y F D Z} `{HasStuck': B0 -< D} (c : D Z) x
        (k : Z -> ctree F D Y) (t: ctree E C X) (R L: rel _ _):
    ssbt L R t (k x) ->
    ssbt L R t (BrD c k).
  Proof.
    intros. eapply step_ss_brD_r_gen. apply H.
  Qed.

  Lemma ssim_brD_r {Y F D Z} `{HasStuck': B0 -< D} (c : D Z) x
        (k : Z -> ctree F D Y) (t: ctree E C X) (L: rel _ _):
    ssim L t (k x) ->
    ssim L t (BrD c k).
  Proof.
    intros. step. apply step_ss_brD_r with (x := x). now step in H.
  Qed.

  Lemma step_ss_brD_gen {Y F D n m} `{HasStuck': B0 -< D} (a: C n) (b: D m)
    (k : n -> ctree E C X) (k' : m -> ctree F D Y) (R L : rel _ _) :
    (forall x, exists y, ss L R (k x) (k' y)) ->
    ss L R (BrD a k) (BrD b k').
  Proof.
    intros EQs.
    apply step_ss_brD_l_gen.
    intros. destruct (EQs x) as [x' ?].
    now apply step_ss_brD_r_gen with (x:=x').
  Qed.

  Lemma step_ss_brD {Y F D n m} `{HasStuck': B0 -< D} (cn: C n) (cm: D m)
    (k : n -> ctree E C X) (k' : m -> ctree F D Y) (L R : rel _ _) :
    (forall x, exists y, ssbt L R (k x) (k' y)) ->
    ssbt L R (BrD cn k) (BrD cm k').
  Proof.
    apply step_ss_brD_gen.
  Qed.

  Lemma ssim_brD {Y F D n m} `{HasStuck': B0 -< D} (cn: C n) (cm: D m)
    (k : n -> ctree E C X) (k' : m -> ctree F D Y) (L : rel _ _) :
    (forall x, exists y, ssim L (k x) (k' y)) ->
    ssim L (BrD cn k) (BrD cm k').
  Proof.
    intros. step. apply step_ss_brD.
    intros. destruct (H x). step in H0. exists x0. apply H0.
  Qed.

  Lemma step_ss_brD_id_gen {Y F D n m} `{HasStuck': B0 -< D} (c: C n) (d: D m)
        (k : n -> ctree E C X) (k' : m -> ctree F D Y)
        (R L : rel _ _) :
    (forall x, exists y, ss L R (k x) (k' y)) ->
    ss L R (BrD c k) (BrD d k').
  Proof.
   intros; apply step_ss_brD_gen.
    intros x; destruct (H x) as [y ?]; exists y; apply H0.
  Qed.

  Lemma step_ss_brD_id {Y F D n m} `{HasStuck': B0 -< D} (c: C n) (d: D m)
    (k : n -> ctree E C X) (k': m -> ctree F D Y) (R L: rel _ _) :
    (forall x, exists y, ssbt L R (k x) (k' y)) ->
    ssbt L R (BrD c k) (BrD d k').
  Proof.
    apply step_ss_brD_id_gen.
  Qed.

  Lemma ssim_brD_id {Y F D n m} `{HasStuck': B0 -< D} (c: C n) (d: D m)
    (k : n -> ctree E C X) (k': m -> ctree F D Y) (L: rel _ _) :
    (forall x, exists y, ssim L (k x) (k' y)) ->
    ssim L (BrD c k) (BrD d k').
  Proof.
    intros. step. apply step_ss_brD_id.
    intros. destruct (H x). step in H0. exists x0. assumption.
  Qed.

(*|
    Note that with visible schedules, nary-spins are equivalent only
    if neither are empty, or if both are empty: they match each other's
    tau challenge infinitely often.
    With invisible schedules, they are always equivalent: neither of them
    produce any challenge for the other.
|*)
  Lemma spinS_gen_nonempty : forall {Z X Y D F} {L: rel (label E) (label F)} `{HasStuck': B0 -< D}
                               (c: C X) (c': C Y) (x: X) (y: Y),
      L tau tau ->
      ssim L (@spinS_gen E C Z X c) (@spinS_gen F C Z Y c').
  Proof.
    intros until L.
    coinduction S CIH; simpl; intros ? ? ? ? ? ? ? ? TR;
      rewrite ctree_eta in TR; cbn in TR;
      apply trans_brS_inv in TR as (_ & EQ & ->);
      eexists; eexists;
      rewrite ctree_eta; cbn.
      split; [econstructor|].
      + exact y.
      + reflexivity.
      + rewrite EQ; eauto.
  Qed.

(*|
Inversion principles
--------------------
|*)
  Lemma ssim_ret_inv {F D Y} {L: rel (label E) (label F)} `{HasStuck': B0 -< D} (r1 : X) (r2 : Y) :
    ssim L (Ret r1 : ctree E C X) (Ret r2 : ctree F D Y) ->
    L (val r1) (val r2).
  Proof.
    intro.
    eplay.
    inv_trans; subst; assumption.
  Qed.

  Lemma ssim_vis_inv_type {D Y X1 X2} `{HasStuck': B0 -< D}
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

  Lemma ssbt_vis_inv {F D Y X1 X2} {L: rel (label E) (label F)} `{HasStuck': B0 -< D}
    (e1 : E X1) (e2 : F X2) (k1 : X1 -> ctree E C X) (k2 : X2 -> ctree F D Y) (x : X1) R:
    ssbt L R (Vis e1 k1) (Vis e2 k2) ->
    (exists y, L (obs e1 x) (obs e2 y))  /\ (forall x, exists y, sst L R (k1 x) (k2 y)).
  Proof.
    intros.
    split; intros; edestruct H as (? & ? & ? & ? & ?);
      etrans; subst;
      inv_trans; subst; eexists; auto.
    - now eapply H2.
    - now apply H1.
  Qed.

  Lemma ssim_vis_inv {F D Y X1 X2} {L: rel (label E) (label F)} `{HasStuck': B0 -< D}
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

  Lemma ssim_brS_inv {F D Y} {L: rel (label E) (label F)} `{HasStuck': B0 -< D}
        n m (cn: C n) (cm: D m) (k1 : n -> ctree E C X) (k2 : m -> ctree F D Y) :
    ssim L (BrS cn k1) (BrS cm k2) ->
    (forall i1, exists i2, ssim L (k1 i1) (k2 i2)).
  Proof.
    intros EQ i1.
    eplay.
    subst; inv_trans.
    eexists; eauto.
  Qed.

  Lemma ss_brD_l_inv {F D Y} {L: rel (label E) (label F)} `{HasStuck': B0 -< D}
        n (c: C n) (t : ctree F D Y) (k : n -> ctree E C X) R:
    ss L R (BrD c k) t ->
    forall x, ss L R (k x) t.
  Proof.
    cbn. intros.
    eapply trans_brD in H0; [| reflexivity].
    apply H in H0 as (? & ? & ? & ? & ?); subst.
    eauto.
  Qed.

  Lemma ssim_brD_l_inv {F D Y} {L: rel (label E) (label F)} `{HasStuck': B0 -< D}
        n (c: C n) (t : ctree F D Y) (k : n -> ctree E C X):
    ssim L (BrD c k) t ->
    forall x, ssim L (k x) t.
  Proof.
    intros. step. step in H. eapply ss_brD_l_inv. apply H.
  Qed.

  (* This one isn't very convenient... *)
  Lemma ssim_brD_r_inv {F D Y} {L: rel (label E) (label F)} `{HasStuck': B0 -< D}
        n (c: D n) (t : ctree E C X) (k : n -> ctree F D Y):
    ssim L t (BrD c k) ->
    forall l t', trans l t t' ->
    exists l' x t'' , trans l' (k x) t'' /\ L l l' /\ (ssim L t' t'').
  Proof.
    cbn. intros. step in H. apply H in H0 as (? & ? & ? & ? & ?); subst. inv_trans.
    do 3 eexists; eauto.
  Qed.

End Proof_Rules.
