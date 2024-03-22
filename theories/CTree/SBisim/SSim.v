From Coq Require Import
     Lia
     Basics
     Fin
     RelationClasses
     Program.Equality
     Logic.Eqdep.

From Coinduction Require Import
     coinduction rel tactics.

From CTree Require Import
  Events.Core
  CTree.Core
  CTree.Equ
  CTree.Trans.

Import Ctree.
Local Open Scope ctree_scope.
Set Implicit Arguments.
Generalizable All Variables.

(* TODO: Decide where to set this *)
Arguments trans : simpl never.

Section StrongSim.
  Context {E F : Type} `{HE: Encode E} `{HF: Encode F} {X Y : Type}.
  (*| The function defining strong simulations: [trans] plays must be answered
    using [trans]. |*)
  Program Definition ss (L : rel (label E) (label F)) :
    mon (ctree E X -> ctree F Y -> Prop) :=
    {| body R t u :=
        forall l t', trans l t t' -> exists l' u', trans l' u u' /\ R t' u' /\ L l l'
    |}.
  Next Obligation.
    unfold Proper, respectful, impl; intros.
    edestruct H0 as (u' & l' & ?).
    - apply H1. 
    - exists u', l'; intuition.
  Qed.

  #[global] Instance weq_ss: Proper (weq ==> weq) ss.
  Proof.
    unfold Proper, respectful, weq; cbn; red; split; intros.
    - apply H0 in H1 as (? & ? & ? & ? & ?).
      exists x0, x1. split. apply H1. split. apply H2. apply H. apply H3.
    - intros. apply H0 in H1 as (? & ? & ? & ? & ?).
      exists x0, x1. split. apply H1. split. apply H2. apply H. apply H3.
  Qed.

  Definition ssim L := gfp (ss L).

  #[global] Instance weq_ssim :
    Proper (weq ==> weq) ssim.
  Proof.
    intros. split.
    - intro. unfold ssim.
      epose proof (gfp_weq (ss x) (ss y)). lapply H1.
      + intro. red in H2. cbn in H2. rewrite <- H2. unfold ssim in H0. apply H0.
      + now rewrite H.
    - intro. unfold ssim.
      epose proof (gfp_weq (ss x) (ss y)). lapply H1.
      + intro. red in H2. cbn in H2. rewrite H2. apply H0.
      + now rewrite H.
  Qed.

End StrongSim.

(*| ss (simulation) notation |*)
Notation sst L := (t (ss L)).
Notation ssbt L := (bt (ss L)).
Notation ssT L := (T (ss L)).
Notation ssbT L := (bT (ss L)).

Notation "t (≲ L ) u" := (ssim L t u) (at level 70): ctree_scope.
Notation "t ≲ u" := (ssim eq t u) (at level 70): ctree_scope.
Notation "t [≲ L ] u" := (ss L _ t u) (at level 79): ctree_scope.
Notation "t [≲] u" := (ss eq _ t u) (at level 79): ctree_scope.
Notation "t {≲ L } u" := (sst L _ t u) (at level 79): ctree_scope.
Notation "t {≲} u" := (sst eq _ t u) (at level 79): ctree_scope.
Notation "t {{≲ L }} u" := (ssbt L _ t u) (at level 79): ctree_scope.
Notation "t {{≲}} u" := (ssbt eq _ t u) (at level 79): ctree_scope.

Ltac fold_ssim :=
  repeat
    match goal with
    | h: context[gfp (@ss ?E ?F ?HE ?HF ?X ?Y ?L)] |- _ => fold (@ssim E F HE HF X Y L) in h
    | |- context[gfp (@ss ?E ?F ?HE ?HF ?X ?Y ?L)]      => fold (@ssim E F HE HF X Y L)
    end.

Ltac __coinduction_ssim R H :=
  unfold ssim; apply_coinduction; fold_ssim; intros R H.

#[global] Tactic Notation "__step_ssim" :=
  match goal with
  | |- context[@ssim ?E ?F ?C ?D ?X ?Y _ _ ?LR] =>
      unfold ssim;
      step;
      fold (@ssim E F C D X Y _ _ L)
  end.

#[local] Tactic Notation "step" := __step_ssim || step.

#[local] Tactic Notation "coinduction" simple_intropattern(R) simple_intropattern(H) :=
  __coinduction_ssim R H || coinduction R H.

#[global] Ltac __step_in_ssim H :=
  match type of H with
  | context[@ssim ?E ?F ?C ?D ?X ?Y ?LR] =>
      unfold ssim in H;
      step in H;
      fold (@ssim E F C D X Y L) in H
  end.

#[local] Tactic Notation "step" "in" ident(H) :=
  __step_in_ssim H || step in H.

Import CTreeNotations.

Section ssim_homogenous_theory.
  Context {E: Type} `{HE: Encode E} {X: Type}
          {L: relation (label E)}.

  Notation ss := (@ss E E HE HE X X).
  Notation ssim := (@ssim E E HE HE X X).
  Notation sst L := (coinduction.t (ss L)).
  Notation ssbt L := (coinduction.bt (ss L)).
  Notation ssT L := (coinduction.T (ss L)).

  (*| Various results on reflexivity and transitivity. |*)
  Lemma refl_sst `{Reflexive _ L}: const eq <= (sst L).
  Proof.    
    apply leq_t; cbn; unfold impl; red; intros; subst; eauto.
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

(*| The LTS can not take a step [tau, vis, ret] |*)
Definition is_stuck `{Encode E} {X} (t: ctree E X) := ( ~ exists l u, trans l t u).
Arguments is_stuck /.

Lemma stuck_is_stuck `{HE: Encode E} {X}:
  @is_stuck E HE X stuck.
Proof.
  red; intros * abs; inv abs.
  destruct H as (s' & TR).
  ind_trans TR.
  eapply IHTR; auto. 
Qed.
Global Hint Resolve stuck_is_stuck: ctree.

(*| Parametric theory of [ss] with heterogenous relation on labels [L] |*)
Section ssim_heterogenous_theory.
  Context {E F: Type} `{HE: Encode E} `{HF: Encode F} {X Y: Type} {L: rel (label E) (label F)}.

  Notation ss := (@ss E F HE HF X Y).
  Notation ssim  := (@ssim E F HE HF X Y).
  Notation sst L := (coinduction.t (ss L)).
  Notation ssbt L := (coinduction.bt (ss L)).
  Notation ssT L := (coinduction.T (ss L)).

  (*| Strong simulation up-to [equ] is valid |*)
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
    unfold Proper, respectful, impl, flip; intros.
    apply (fbt_bt equ_clos_sst); econstructor; eauto.
    now symmetry.
  Qed.

  #[global] Instance equ_ssbt_closed_ctx {r} :
    Proper (equ eq ==> equ eq ==> impl) (ssbt L r).
  Proof.
    unfold Proper, respectful, impl, flip; intros.
    now rewrite H, H0 in H1.
  Qed.

  #[global] Instance equ_clos_ssT_goal RR f :
    Proper (equ eq ==> equ eq ==> flip impl) (ssT L f RR).
  Proof.
    unfold Proper, respectful, impl, flip; intros ? ? eq1 ? ? eq2 H.
    apply (fT_T equ_clos_sst); econstructor; [eauto | | symmetry; eauto]; assumption.
  Qed.

  #[global] Instance equ_clos_ssT_ctx RR f :
    Proper (equ eq ==> equ eq ==> impl) (ssT L f RR).
  Proof.
    unfold Proper, respectful, impl, flip; intros ? ? eq1 ? ? eq2 H.
    apply (fT_T equ_clos_sst); econstructor; [symmetry; eauto | | eauto]; assumption.
  Qed.

  #[global] Instance equ_clos_ssim_goal :
    Proper (equ eq ==> equ eq ==> flip impl) (ssim L).
  Proof.
    unfold Proper, respectful, impl, flip; intros ? ? eq1 ? ? eq2 H.
    apply (ft_t equ_clos_sst); econstructor; [eauto | | symmetry; eauto]; assumption.
  Qed.

  #[global] Instance equ_clos_ssim_ctx :
    Proper (equ eq ==> equ eq ==> impl) (ssim L).
  Proof.
    unfold Proper, respectful, impl, flip; intros ? ? eq1 ? ? eq2 H.
    apply (ft_t equ_clos_sst); econstructor; [symmetry; eauto | | eauto]; assumption.
  Qed.

  #[global] Instance equ_ss_closed_goal {r} :
    Proper (equ eq ==> equ eq ==> flip impl) (ss L r).
  Proof.
    unfold Proper, respectful, impl, flip, ss; cbn; intros t t' tt' u u' uu'; intros.
    rewrite tt' in H0. apply H in H0 as (l' & ? & ? & ? & ?).
    do 2 eexists; eauto. rewrite uu'. eauto.
  Qed.

  #[global] Instance equ_ss_closed_ctx {r} :
    Proper (equ eq ==> equ eq ==> impl) (ss L r).
  Proof.
    unfold Proper, respectful, impl, flip, ss; cbn; intros t t' tt' u u' uu'; intros.
    rewrite <- tt' in H0. apply H in H0 as (l' & ? & ? & ? & ?).
    do 2 eexists; eauto. rewrite <- uu'. eauto.
  Qed.
    
  (*| stuck ctrees can be simulated by anything. |*)
  Lemma is_stuck_ss (R : rel _ _) (t : ctree E X) (t': ctree F Y):
    is_stuck t -> ss L R t t'.
  Proof.
    repeat intro.
    exfalso; apply H.
    now (exists l, t'0).
  Qed.

  Lemma is_stuck_ssim (t: ctree E X) (t': ctree F Y):
    is_stuck t -> ssim L t t'.
  Proof.
    intros; step.
    cbn; intros.
    exfalso; apply H.
    now (exists l, t'0).
  Qed.

  Lemma stuck_ss (R : rel _ _) (t : ctree F Y) : ss L R stuck t.
  Proof.
    apply is_stuck_ss.
    apply stuck_is_stuck.
  Qed.

  Lemma stuckD_ssim (t : ctree F Y) : ssim L stuck t.
  Proof.
    intros. step. apply stuck_ss.
  Qed.

End ssim_heterogenous_theory.


(*|
Up-to [bind] context simulations
----------------------------------
We have proved in the module [Equ] that up-to bind context is
a valid enhancement to prove [equ].
We now prove the same result, but for strong simulation.
|*)

Section ssim_heterogenous_bind.
  Context {E F: Type} `{HE: Encode E} `{HF: Encode F} {X X' Y Y': Type}
          (L : rel (label E) (label F)) (RR : rel X Y).

  (* Mix of R0 for val and L for tau/obs. *)
  Variant update_val_rel : label E -> label F -> Prop :=
  | update_Val (v1 : X) (v2 : Y) : RR v1 v2 -> update_val_rel (val v1) (val v2)
  | update_NonVal l1 l2 : ~is_val l1 -> ~is_val l2 -> L l1 l2 -> update_val_rel l1 l2.

  Lemma update_val_rel_val : forall (v1 : X) (v2 : Y),
    update_val_rel (val v1) (val v2) ->
    RR v1 v2.
  Proof.
    intros. remember (val v1) as l1. remember (val v2) as l2.
    destruct H.
    - dependent destruction Heql1.
      dependent destruction Heql2.
      apply H. 
    - subst. exfalso. now apply H.
  Qed.

  Lemma update_val_rel_val_l : forall (v1 : X) l2,
    update_val_rel (val v1) l2 ->
    exists v2 : Y, l2 = val v2 /\ RR v1 v2.
  Proof.
    intros. remember (val v1) as l1. destruct H.
    - dependent destruction Heql1; eauto.
    - subst. exfalso. apply H. constructor.
  Qed.

  Lemma update_val_rel_val_r : forall l1 (v2 : Y),
    update_val_rel l1 (val v2) ->
    exists v1 : X, l1 = val v1 /\ RR v1 v2.
  Proof.
    intros. remember (val v2) as l2. destruct H.
    - dependent destruction Heql2. eauto.
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

  Definition is_update_val_rel (L0 : rel (label E) (label F)) : Prop :=
    forall l1 l2, wf_val X l1 -> wf_val Y l2 -> (L0 l1 l2 <-> update_val_rel l1 l2).

  Theorem update_val_rel_correct : is_update_val_rel update_val_rel.
  Proof.
    red. reflexivity.
  Qed.

  (*| Specialization of [bind_ctx] to a function acting with [ssim] on the bound value,
    and with the argument (pointwise) on the continuation. |*)
  Program Definition bind_ctx_ssim L0 : mon (rel (ctree E X') (ctree F Y')) :=
    {|body := fun R => @bind_ctx E F HE HF X Y X' Y' (ssim L0) (pointwise RR R) |}.
  Next Obligation.
    unfold Proper, respectful, impl; cbn; intros.
    revert H0.
    apply leq_bind_ctx. intros ?? H' ?? H''.
    apply in_bind_ctx. apply H'. intros t t' HS. apply H, H'', HS.
  Qed.

  (*| The resulting enhancing function gives a valid up-to technique |*)
  Lemma bind_ctx_ssim_t L0: 
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
      inv H0.
      * now apply H. 
      * now apply H2.
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
      rewrite <- EQ in STEPres.
      specialize (kk v v2 H).
      apply kk in STEP as (u'' & ? & STEP & EQ'' & ?); cbn in *.
      do 2 eexists; split.
      eapply trans_bind_r; eauto.
      split; auto.
      eapply (id_T (ss L)); auto.
  Qed.

End ssim_heterogenous_bind.

Theorem is_update_val_rel_eq `{HE: Encode E} {X} : @is_update_val_rel E E _ _ X X eq eq eq.
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

Theorem update_val_rel_eq `{HE: Encode E} {X} : forall l l', wf_val X l ->
  @update_val_rel E E _ _ X X eq eq l l' <-> l = l'.
Proof.
  split; intro.
  - destruct H0; now subst.
  - subst. destruct l'.
    3: { specialize (H X0 v eq_refl). subst. now left. }
    all: constructor; auto; intro; inversion H0.
Qed.

Theorem update_val_rel_update_val_rel `{HE: Encode E} `{HF: Encode F} {X0 X1 Y0 Y1}
    (L : rel (label E) (label F)) (R0 : rel X0 Y0) (R1 : rel X1 Y1) :
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

(*| Expliciting the reasoning rule provided by the up-to principles. |*)
Lemma sst_clo_bind_gen `{HE: Encode E} `{HF: Encode F} {X Y X' Y': Type} {L : rel (label E) (label F)}
      (R0 : rel X Y) L0
      (t1 : ctree E X) (t2: ctree F Y)
      (HL0 : is_update_val_rel L R0 L0)
      (k1 : X -> ctree E X') (k2 : Y -> ctree F Y') RR:
  t1 (≲L0) t2 ->
  (forall x y, R0 x y -> (sst L RR) (k1 x) (k2 y)) ->
  sst L RR (t1 >>= k1) (t2 >>= k2).
Proof.
  intros ? ?.
  apply (ft_t (@bind_ctx_ssim_t E F HE HF X X' Y Y' L R0 L0 HL0)).
  apply in_bind_ctx; eauto.
Qed.

Lemma sst_clo_bind `{HE: Encode E} `{HF: Encode F} {X Y X' Y': Type} {L : rel (label E) (label F)}
      (R0 : rel X Y)
      (t1 : ctree E X) (t2: ctree F Y)
      (k1 : X -> ctree E X') (k2 : Y -> ctree F Y') RR:
  t1 (≲update_val_rel L R0) t2 ->
  (forall x y, R0 x y -> (sst L RR) (k1 x) (k2 y)) ->
  sst L RR (t1 >>= k1) (t2 >>= k2).
Proof.
  intros ? ?.
  eapply sst_clo_bind_gen; eauto.
  apply update_val_rel_correct.
Qed.

Lemma sst_clo_bind_eq `{HE: Encode E} `{HF: Encode F} {X X': Type}
      (t1 : ctree E X) (t2: ctree E X)
      (k1 : X -> ctree E X') (k2 : X -> ctree E X') RR:
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

Lemma ssbt_clo_bind_gen `{HE: Encode E} `{HF: Encode F} {X Y X' Y': Type}
  {L : rel (label E) (label F)}
      (R0 : rel X Y) L0
      (t1 : ctree E X) (t2: ctree F Y)
      (HL0 : is_update_val_rel L R0 L0)
      (k1 : X -> ctree E X') (k2 : Y -> ctree F Y') RR:
  t1 (≲L0) t2 ->
  (forall x y, R0 x y -> (ssbt L RR) (k1 x) (k2 y)) ->
  ssbt L RR (t1 >>= k1) (t2 >>= k2).
Proof.
  intros ? ?.
  apply (fbt_bt (@bind_ctx_ssim_t E F HE HF X X' Y Y' L R0 L0 HL0)).
  apply in_bind_ctx; eauto.
Qed.

Lemma ssbt_clo_bind `{HE: Encode E} `{HF: Encode F} {X Y X' Y': Type}
  {L : rel (label E) (label F)}
      (R0 : rel X Y)
      (t1 : ctree E X) (t2: ctree F Y)
      (k1 : X -> ctree E X') (k2 : Y -> ctree F Y') RR:
  t1 (≲update_val_rel L R0) t2 ->
  (forall x y, R0 x y -> (ssbt L RR) (k1 x) (k2 y)) ->
  ssbt L RR (t1 >>= k1) (t2 >>= k2).
Proof.
  intros ? ?.
  eapply ssbt_clo_bind_gen; eauto.
  apply update_val_rel_correct.
Qed.

Lemma ssbt_clo_bind_eq `{HE: Encode E} `{HF: Encode F} {X X': Type}
      (t1 : ctree E X) (t2: ctree E X)
      (k1 : X -> ctree E X') (k2 : X -> ctree E X') RR:
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

(*| Specializing the congruence principle for [≲] |*)
Lemma ssim_clo_bind_gen `{HE: Encode E} `{HF: Encode F} {X Y X' Y': Type}
  {L : rel (label E) (label F)}
      (R0 : rel X Y) L0
      (HL0 : is_update_val_rel L R0 L0)
      (t1 : ctree E X) (t2: ctree F Y)
      (k1 : X -> ctree E X') (k2 : Y -> ctree F Y'):
  ssim L0 t1 t2 ->
  (forall x y, R0 x y -> ssim L (k1 x) (k2 y)) ->
  ssim L (t1 >>= k1) (t2 >>= k2).
Proof.
  intros. eapply sst_clo_bind_gen; eauto.
Qed.

Lemma ssim_clo_bind `{HE: Encode E} `{HF: Encode F} {X Y X' Y': Type}
  {L : rel (label E) (label F)}
  (R0 : rel X Y)
  (t1 : ctree E X) (t2: ctree F Y)
  (k1 : X -> ctree E X') (k2 : Y -> ctree F Y'):
  t1 (≲update_val_rel L R0) t2 ->
  (forall x y, R0 x y -> k1 x (≲L) k2 y) ->
  t1 >>= k1 (≲L) t2 >>= k2.
Proof.
  intros. eapply sst_clo_bind; eauto.
Qed.

Lemma ssim_clo_bind_eq `{HE: Encode E} `{HF: Encode F} {X X': Type}
      (t1 : ctree E X) (t2: ctree E X)
      (k1 : X -> ctree E X') (k2 : X -> ctree E X'):
  t1 ≲ t2 ->
  (forall x, k1 x ≲ k2 x) ->
  t1 >>= k1 ≲ t2 >>= k2.
Proof.
  intros. apply sst_clo_bind_eq; auto.
Qed.

Tactic Notation "__upto_bind_ssim" uconstr(R0) :=
  match goal with
    |- @ssim ?E ?F ?C ?D ?X ?Y ?L (Ctree.bind (X := ?T) _ _) (Ctree.bind (X := ?T') _ _) =>
      apply (ssim_clo_bind_gen R0 (update_val_rel L R0) (update_val_rel_correct L R0))
  | |- body (t (@ss ?E ?F ?C ?D ?X ?Y ?L)) ?R (Ctree.bind (X := ?T) _ _) (Ctree.bind (X := ?T') _ _) =>
      apply (ft_t (@bind_ctx_ssim_t E F C D T X T' Y L R0
        (update_val_rel L R0) (update_val_rel_correct L R0))), in_bind_ctx
  | |- body (bt (@ss ?E ?F ?C ?D ?X ?Y ?L)) ?R (Ctree.bind (X := ?T) _ _) (Ctree.bind (X := ?T') _ _) =>
      apply (fbt_bt (@bind_ctx_ssim_t E F C D T X T' Y L R0
        (update_val_rel L R0) (update_val_rel_correct L R0))), in_bind_ctx
  end.

Tactic Notation "__upto_bind_eq_ssim" uconstr(R0) :=
  match goal with
  | |- @ssim ?E ?F ?C ?D ?X ?Y ?L (Ctree.bind (X := ?T) _ _) (Ctree.bind (X := ?T') _ _) =>
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
  | h : @ssim ?E ?F ?C ?D ?X ?Y ?L _ _ |- _ =>
      __play_ssim_in h
  end.

#[local] Tactic Notation "play" := __play_ssim.
#[local] Tactic Notation "play" "in" ident(H) := __play_ssim_in H.
#[local] Tactic Notation "eplay" := __eplay_ssim.

Section Proof_Rules.
  Context `{HE: Encode E} `{HF: Encode F} {X : Type}.

  Lemma step_ss_ret_gen {Y} (x : X) (y : Y) (R L : rel _ _) :
    R stuck stuck ->
    (Proper (equ eq ==> equ eq ==> impl) R) ->
    L (val x) (val y) ->
    ss L R (Ret x : ctree E X) (Ret y : ctree F Y).
  Proof.
    intros Rstuck PROP Lval.
    cbn; intros ? ? TR.
    apply trans_ret_inv in TR as (? & ->).
    exists (val y), stuck; split; etrans.
    rewrite H; auto.
  Qed.

  Lemma step_ss_ret {Y} (x : X) (y : Y) (R L : rel _ _) :
    L (val x) (val y) ->
    ssbt L R (Ret x : ctree E X) (Ret y : ctree F Y).
  Proof.
    intros.
    apply step_ss_ret_gen.
    - step. intros.
      apply is_stuck_ss.
      eapply stuck_is_stuck. 
    - typeclasses eauto.
    - apply H.
  Qed.

  Lemma ssim_ret {Y} (x : X) (y : Y) (L : rel _ _) :
    L (val x) (val y) ->
    ssim L (Ret x : ctree E X) (Ret y : ctree F Y).
  Proof.
    intros. step. now apply step_ss_ret.
  Qed.

(*|
 The vis nodes are deterministic from the perspective of the labeled
 transition system, stepping is hence symmetric and we can just recover
 the itree-style rule.
|*)
  Lemma step_ss_vis_gen {Y} (e : E) (f: F)
        (k : encode e -> ctree E X) (k' : encode f -> ctree F Y) (R L: rel _ _) :
    (Proper (equ eq ==> equ eq ==> impl) R) ->
    (forall x, exists y, R (k x) (k' y) /\ L (obs e x) (obs f y)) ->
    ss L R (Vis e k) (Vis f k').
  Proof.
    intros.
    cbn; intros ? ? TR.
    apply trans_vis_inv in TR as (x & ? & ->).
    destruct (H0 x) as (x' & RR & LL);
      cbn; eexists; eexists; intuition.
    - rewrite H1; eauto.
    - assumption.
  Qed.

  Lemma step_ss_vis {Y} (e : E) (f: F)
        (k : encode e -> ctree E X) (k': encode f  -> ctree F Y) (R L : rel _ _) :
    (forall x, exists y, sst L R (k x) (k' y) /\ L (obs e x) (obs f y)) ->
    ssbt L R (Vis e k) (Vis f k').
  Proof.
    intros * EQ.
    apply step_ss_vis_gen; auto.
    typeclasses eauto.
  Qed.

  Lemma ssim_vis {Y} (e : E) (f: F)
        (k : encode e -> ctree E X) (k' : encode f -> ctree F Y) (L : rel _ _) :
    (forall x, exists y, ssim L (k x) (k' y) /\ L (obs e x) (obs f y)) ->
    ssim L (Vis e k) (Vis f k').
  Proof.
    intros. step. now apply step_ss_vis.
  Qed.

  (*| Same goes for visible tau nodes. |*)
  Lemma step_ss_step_gen {Y}
        (t : ctree E X) (t': ctree F Y) (R L: rel _ _):
    (Proper (equ eq ==> equ eq ==> impl) R) ->
    L tau tau ->
    (R t t') ->
    ss L R (step t) (step t').
  Proof.
    intros PR ? EQs.
    intros ? ? TR.
    apply trans_br_inv in TR as ([] & ? & ->).
    all: exists tau, t'; split; [etrans|]; split; [rewrite H0|]; auto.
  Qed.

  Lemma step_ss_step {Y} (t: ctree E X) (t': ctree F Y) (R L : rel _ _) :
    (sst L R t t') ->
    L tau tau ->
    ssbt L R (step t) (step t').
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
  Lemma step_ss_br_gen {Y n m} (k : fin' n -> ctree E X) (k' : fin' m -> ctree F Y)
    (R L: rel _ _) :
    (Proper (equ eq ==> equ eq ==> impl) R) ->
    (forall x, exists y, R (k x) (k' y)) ->
    L tau tau ->
    ss L R (Br n k) (Br m k').
  Proof.
    intros PROP EQs ? ? ? TR.
    apply trans_br_inv in TR as (? & ? & ->).
    destruct (EQs x) as [y HR].
    cbn; do 2 eexists; split; [etrans | split; [rewrite H0; eauto|assumption]].
  Qed.

  Lemma step_ss_br {Y n m} (k : fin' n -> ctree E X) (k' : fin' m -> ctree F Y)
    (R L: rel _ _) :
    (forall x, exists y, sst L R (k x) (k' y)) ->
    L tau tau ->
    ssbt L R (Br n k) (Br m k').
  Proof.
    intros.
    apply step_ss_br_gen; auto.
    typeclasses eauto.
  Qed.

  Lemma ssim_br {Y n m} (k : fin' n -> ctree E X) (k' : fin' m -> ctree F Y) (L: rel _ _) :
    (forall x, exists y, ssim L (k x) (k' y)) ->
    L tau tau ->
    ssim L (Br n k) (Br m k').
  Proof.
    intros. step. now apply step_ss_br.
  Qed.

  Lemma step_ss_br_id_gen {Y n} (k: fin' n -> ctree E X) (k': fin' n -> ctree F Y)
    (R L : rel _ _) :
    (Proper (equ eq ==> equ eq ==> impl) R) ->
    (forall x, exists y, R (k x) (k' y)) ->
    L tau tau ->
    ss L R (Br n k) (Br n k').
  Proof.
    intros; apply step_ss_br_gen; eauto.
  Qed.

  Lemma step_ss_br_id {Y n} (k: fin' n -> ctree E X) (k': fin' n -> ctree F Y) (R L : rel _ _) :
    (forall x, exists y, sst L R (k x) (k' y)) ->
    L tau tau ->
    ssbt L R (Br n k) (Br n k').
  Proof.
    intros.
    apply step_ss_br_id_gen; eauto.
    typeclasses eauto.
  Qed.

  Lemma ssim_br_id {Y n} (k: fin' n -> ctree E X) (k': fin' n -> ctree F Y) (L : rel _ _) :
    (forall x, exists y, ssim L (k x) (k' y)) ->
    L tau tau ->
    ssim L (Br n k) (Br n k').
  Proof.
    intros. step. now apply step_ss_br_id.
  Qed.

  Lemma ssim_step {Y} (t: ctree E X) (t': ctree F Y) (L : rel _ _) :
    ssim L t t' ->
    L tau tau ->
    ssim L (step t) (step t').
  Proof.
    intros. apply ssim_br_id; eauto.
  Qed.

  (*|
    For invisible nodes, the situation is different: we may kill them, but that execution
    cannot act as going under the guard.
    |*)
  Lemma step_ss_guard_gen {Y} (t: ctree E X) (t': ctree F Y) (R L: rel _ _):
    ss L R t t' ->
    ss L R (Guard t) (Guard t').
  Proof.
    intros EQ.
    intros ? ? TR.
    apply trans_guard_inv in TR.
    apply EQ in TR as (? & ? & ? & ? & ?); subst.
    do 2 eexists; split; [etrans | split; trivial].
  Qed.

  Lemma step_ss_guard {Y} (t: ctree E X) (t': ctree F Y) (R L: rel _ _):
    ssbt L R t t' ->
    ssbt L R (Guard t) (Guard t').
  Proof.
    apply step_ss_guard_gen.
  Qed.

  (*| Inversion principles |*)
  Lemma ssim_ret_inv {Y} {L: rel (label E) (label F)} r1 r2:
    ssim L (Ret r1 : ctree E X) (Ret r2 : ctree F Y) ->
    L (val r1) (val r2).
  Proof.
    intro.
    eplay.
    now trans in TR. 
  Qed.

  Lemma ssbt_vis_inv {Y} {L: rel (label E) (label F)}
    (e: E) (f : F) (k1 : encode e -> ctree E X) (k2 : encode f -> ctree F Y) x R:
    ssbt L R (Vis e k1) (Vis f k2) ->
    (exists y, L (obs e x) (obs f y))  /\ (forall x, exists y, sst L R (k1 x) (k2 y)).
  Proof.
    intros.
    split; intros; edestruct H as (? & ? & ? & ? & ?);
      etrans; trans in H0; eexists; eauto.
    rewrite <- Eqt; apply H1.
  Qed.

  Lemma ssim_vis_inv {Y} {L: rel (label E) (label F)}
        (e: E) (f : F) (k1 : encode e -> ctree E X) (k2 : encode f -> ctree F Y) x:
    ssim L (Vis e k1) (Vis f k2) ->
    (exists y, L (obs e x) (obs f y)) /\ (forall x, exists y, ssim L (k1 x) (k2 y)).
  Proof.
    intros.
    split.
    - eplay.
      trans in TR.
      exists x2; eauto.
    - intros y.
      step in H.
      cbn in H.
      edestruct H as (l' & u' & TR & IN & HL).
      apply trans_vis with (x := y).
      trans in TR.
      exists x0.
      rewrite <- Eqt.
      apply IN.
  Qed.

  Lemma ssim_br_inv {Y n m} {L: rel (label E) (label F)}
    (k1 : fin' n -> ctree E X) (k2 : fin' m -> ctree F Y) :
    ssim L (Br n k1) (Br m k2) ->
    (forall i1, exists i2, ssim L (k1 i1) (k2 i2)).
  Proof.
    intros EQ i1.
    eplay.
    trans in TR.
    rewrite Eqt in EQ0.
    (exists n0); eauto.
  Qed.

End Proof_Rules.
