From Coq Require Import
     Lia Basics Fin
     Logic.Eqdep.

From Coinduction Require Import
     coinduction rel tactics.

From ITree Require Import Core.Subevent.

From CTree Require Import
     CTree
     Utils
     Eq.Equ
     Eq.SBisim
     Eq.Shallow
     Eq.Trans.

From RelationAlgebra Require Export
     rel srel.

Import CTree.
Set Implicit Arguments.

(* TODO: Decide where to set this *)
Arguments trans : simpl never.

#[local] Tactic Notation "step" := __step_sbisim || step.
#[local] Tactic Notation "coinduction" simple_intropattern(R) simple_intropattern(H) :=
  __coinduction_sbisim R H || coinduction R H.
#[local] Tactic Notation "step" "in" ident(H) := __step_in_sbisim H || step in H.

Module SSim0Notations.

  Notation "t ≲ u" := (ssim0 eq t u) (at level 70).
  Notation "t [≲] u" := (ss0 eq _ t u) (at level 79).
  Notation "t {≲} u" := (t (ss0 eq) _ t u) (at level 79).
  Notation "t {{≲}} u" := (bt (ss0 eq) _ t u) (at level 79).

  Notation "t ( ≲ L ) u" := (ssim0 L t u) (at level 70).
  Notation "t [ ≲ L ] u" := (ss0 L _ t u) (at level 79).
  Notation "t { ≲ L } u" := (t (ss0 L) _ t u) (at level 79).
  Notation "t {{ ≲ L }} u" := (bt (ss0 L) _ t u) (at level 79).

End SSim0Notations.

Import CTreeNotations.
Import EquNotations.
Import SBisimNotations.

Section ssim0_theory.

  Context {E C : Type -> Type} {X : Type}
          {L: relation (@label E)}
          {HasStuck: B0 -< C} {EqL: Equivalence L}.

  Notation ss0 := (@ss0 E E C C X X _ _ L).
  Notation ssim0 := (@ssim0 E E C C X X _ _ L).
  Notation sst0 := (coinduction.t ss0).
  Notation ssbt0 := (coinduction.bt ss0).
  Notation ssT0 := (coinduction.T ss0).

(*|
Various results on reflexivity and transitivity.
|*)
  Lemma refl_sst0: const seq <= sst0.
  Proof.
    apply leq_t. cbn.
    intros. unfold seq in H. subst. eauto.
  Qed.

  Lemma square_sst0 : square <= sst0.
  Proof.
    apply Coinduction; cbn.
    intros R x z [y xy yz] l x' xx'.
    destruct (xy _ _ xx') as (l' & y' & yy' & ? & ?).
    destruct (yz _ _ yy') as (l'' & z' & zz' & ? & ?).
    exists l'', z'.
    split.
    assumption.
    split.
    apply (f_Tf ss0).
    exists y'; eauto.
    transitivity l'; auto.
  Qed.

  #[global] Instance PreOrder_sst0 R : PreOrder (sst0 R).
  Proof. apply PreOrder_t. apply refl_sst0. apply square_sst0. Qed.

  Corollary PreOrder_ssim0: PreOrder ssim0.
  Proof. apply PreOrder_sst0. Qed.

  #[global] Instance PreOrder_ssbt0 R : PreOrder (ssbt0 R).
	Proof. apply rel.PreOrder_bt. now apply refl_sst0. apply square_sst0. Qed.

  #[global] Instance PreOrder_ssT0 f R: PreOrder ((T ss0) f R).
  Proof. apply rel.PreOrder_T. now apply refl_sst0. apply square_sst0. Qed.

(*|
Aggressively providing instances for rewriting hopefully faster
[sbisim] under all [ss1]-related contexts (consequence of the transitivity
of the companion).
|*)

  #[global] Instance sbisim_clos_ssim0_goal :
    Proper (sbisim L ==> sbisim L ==> flip impl) ssim0.
  Proof.
    repeat intro.
    symmetry in H0. apply sbisim_ssim0 in H, H0.
    transitivity y0. transitivity y. all: auto.
  Qed.

  #[global] Instance sbisim_clos_ssim0_ctx :
    Proper (sbisim L ==> sbisim L ==> impl) ssim0.
  Proof.
    repeat intro. symmetry in H, H0. eapply sbisim_clos_ssim0_goal; eauto.
  Qed.

  #[global] Instance sbisim_clos_sst_goal RR :
    Proper (sbisim L ==> sbisim L ==> flip impl) (sst0 RR).
  Proof.
    cbn; intros ? ? eq1 ? ? eq2 H.
    symmetry in eq2. apply sbisim_ssim0 in eq1, eq2.
    rewrite eq1, <- eq2.
    auto.
  Qed.

  #[global] Instance sbisim_clos_sst_ctx RR :
    Proper (sbisim L ==> sbisim L ==> impl) (sst0 RR).
  Proof.
    cbn; intros ? ? eq1 ? ? eq2 ?.
    rewrite <- eq1, <- eq2.
    auto.
  Qed.

  #[global] Instance sbisim_clos_ssT_goal RR f :
    Proper (sbisim L ==> sbisim L ==> flip impl) (ssT0 f RR).
  Proof.
    cbn; intros ? ? eq1 ? ? eq2 ?.
    symmetry in eq2. apply sbisim_ssim0 in eq1, eq2.
    rewrite eq1, <- eq2.
    auto.
  Qed.

  #[global] Instance sbisim_clos_ssT_ctx RR f :
    Proper (sbisim L ==> sbisim L ==> impl) (ssT0 f RR).
  Proof.
    cbn; intros ? ? eq1 ? ? eq2 ?.
    rewrite <- eq1, <- eq2.
    auto.
  Qed.

(*|
Strong simulation up-to [equ] is valid
----------------------------------------
|*)
  Lemma equ_clos_sst0 : equ_clos <= sst0.
  Proof.
    apply Coinduction; cbn.
    intros R x y [x' y' x'' y'' EQ' EQ''] l z x'z.
    rewrite EQ' in x'z.
    destruct (EQ'' _ _ x'z) as (l' & ? & ? & ? & ?).
    exists l', x0.
    split.
    - rewrite <- Equu; auto.
    - split; auto.
      eapply (f_Tf ss0).
      econstructor; auto; auto.
  Qed.

  #[global] Instance equ_clos_sst0_goal RR :
    Proper (equ eq ==> equ eq ==> flip impl) (sst0 RR).
  Proof.
    cbn; intros ? ? eq1 ? ? eq2 H.
    apply (ft_t equ_clos_sst0); econstructor; [eauto | | symmetry; eauto]; assumption.
  Qed.

  #[global] Instance equ_clos_sst0_ctx RR :
    Proper (equ eq ==> equ eq ==> impl) (sst0 RR).
  Proof.
    cbn; intros ? ? eq1 ? ? eq2 H.
    apply (ft_t equ_clos_sst0); econstructor; [symmetry; eauto | | eauto]; assumption.
  Qed.

  #[global] Instance equ_ssbt0_closed_goal {r} :
    Proper (equ eq ==> equ eq ==> flip impl) (ssbt0 r).
  Proof.
    cbn. intros.
    now rewrite <- H, <- H0 in H1.
  Qed.

  #[global] Instance equ_ssbt0_closed_ctx {r} :
    Proper (equ eq ==> equ eq ==> impl) (ssbt0 r).
  Proof.
    cbn. intros.
    now rewrite H, H0 in H1.
  Qed.

  #[global] Instance equ_clos_ssT0_goal RR f :
    Proper (equ eq ==> equ eq ==> flip impl) (ssT0 f RR).
  Proof.
    cbn; intros ? ? eq1 ? ? eq2 H.
    apply (fT_T equ_clos_sst0); econstructor; [eauto | | symmetry; eauto]; assumption.
  Qed.

  #[global] Instance equ_clos_ssT0_ctx RR f :
    Proper (equ eq ==> equ eq ==> impl) (ssT0 f RR).
  Proof.
    cbn; intros ? ? eq1 ? ? eq2 H.
    apply (fT_T equ_clos_sst0); econstructor; [symmetry; eauto | | eauto]; assumption.
  Qed.

  #[global] Instance equ_clos_ssim0_goal :
    Proper (equ eq ==> equ eq ==> flip impl) ssim0.
  Proof.
    cbn; intros ? ? eq1 ? ? eq2 H.
    apply (ft_t equ_clos_sst0); econstructor; [eauto | | symmetry; eauto]; assumption.
  Qed.

  #[global] Instance equ_clos_ssim0_ctx :
    Proper (equ eq ==> equ eq ==> impl) ssim0.
  Proof.
    cbn; intros ? ? eq1 ? ? eq2 H.
    apply (ft_t equ_clos_sst0); econstructor; [symmetry; eauto | | eauto]; assumption.
  Qed.

  #[global] Instance equ_ss0_closed_goal {r} : Proper (equ eq ==> equ eq ==> flip impl) (ss0 r).
  Proof.
    intros t t' tt' u u' uu'; cbn; intros.
    rewrite tt' in H0. apply H in H0 as (l' & ? & ? & ? & ?).
    do 2 eexists; eauto. rewrite uu'. eauto.
  Qed.

  #[global] Instance equ_ss0_closed_ctx {r} : Proper (equ eq ==> equ eq ==> impl) (ss0 r).
  Proof.
    intros t t' tt' u u' uu'; cbn; intros.
    rewrite <- tt' in H0. apply H in H0 as (l' & ? & ? & ? & ?).
    do 2 eexists; eauto. rewrite <- uu'. eauto.
  Qed.

  (*|
    stuck ctrees can be simulated by anything.
    |*)
  Lemma is_stuck_ss0 (R : rel _ _) (t t' : ctree E C X) :
    is_stuck t -> ss0 R t t'.
  Proof.
    repeat intro. now apply H in H0.
  Qed.

  Lemma is_stuck_ssim0 (t t' : ctree E C X) :
    is_stuck t -> ssim0 t t'.
  Proof.
    intros. step. now apply is_stuck_ss0.
  Qed.

  Lemma stuckD_ss0 (R : rel _ _) (t : ctree E C X) : ss0 R stuckD t.
  Proof.
    repeat intro. now apply stuckD_is_stuck in H.
  Qed.

  Lemma stuckD_ssim0 (t : ctree E C X) : ssim0 stuckD t.
  Proof.
    intros. step. apply stuckD_ss0.
  Qed.

  
  Lemma spinD_ss0 (R : rel _ _) (t : ctree E C X) `{HasTau: B1 -< C}: ss0 R spinD t.
  Proof.
    repeat intro. now apply spinD_is_stuck in H.
  Qed.

  Lemma spinD_ssim0 : forall (t' : ctree E C X) `{HasTau: B1 -< C},
      ssim0 spinD t'.
  Proof.
    intros. step. apply spinD_ss0.
  Qed.

End ssim0_theory.

Import SSim0Notations.

(*|
Up-to [bind] context simulations
----------------------------------
We have proved in the module [Equ] that up-to bind context is
a valid enhancement to prove [equ].
We now prove the same result, but for strong simulation.
|*)

Section bind.
  Obligation Tactic := idtac.

  Context {E C: Type -> Type} {X Y : Type}
          {HasStuck: B0 -< C}.

(*|
Specialization of [bind_ctx] to a function acting with [ssim] on the bound value,
and with the argument (pointwise) on the continuation.
|*)
  Program Definition bind_ctx_ssim0 : mon (rel (ctree E C Y) (ctree E C Y)) :=
    {|body := fun R => @bind_ctx E E C C X X Y Y (ssim0 eq) (pointwise eq R) |}.
  Next Obligation.
    intros ?? H. apply leq_bind_ctx. intros ?? H' ?? H''.
    apply in_bind_ctx. apply H'. intros t t' HS. apply H, H'', HS.
  Qed.

  (* LEF: Make parametric on `L` *)
(*|
The resulting enhancing function gives a valid up-to technique
|*)
  Lemma bind_ctx_ssim0_t :
    bind_ctx_ssim0 <= (sst0 eq).
  Proof.
    intro HL.
    apply Coinduction.
    intros R. apply (leq_bind_ctx _).
    intros t1 t2 tt k1 k2 kk.
    step in tt.
    intros l u STEP.
    apply trans_bind_inv in STEP as [(H & t' & STEP & EQ) | (v & STEPres & STEP)]; cbn in *.
    - apply tt in STEP as (l' & u' & STEP & ? & EQ'); subst.
      do 2 eexists; split.
      + eapply trans_bind_l; eauto.
      + split.
        apply (fT_T equ_clos_sst0).
        econstructor; [exact EQ | | reflexivity].
        apply (fTf_Tf (ss0 eq)).
        apply in_bind_ctx; auto.
        intros ? ? ->.
        apply (b_T (ss0 eq)).
        red in kk. red. red. now apply kk. reflexivity.
    - apply tt in STEPres as (l' & u' & STEPres & ? & ?); subst.
      pose proof (trans_val_inv STEPres) as EQ.
      rewrite EQ in STEPres.
      specialize (kk v v eq_refl).
      apply kk in STEP as (l'' & u'' & STEP & ? & EQ''); subst; cbn in *.
      do 2 eexists.
      split.
      + eapply trans_bind_r; cbn in *; eauto.
      + split. eapply (id_T (ss0 eq)); auto.
        reflexivity.
  Qed.

End bind.

(*|
Expliciting the reasoning rule provided by the up-to principles.
|*)
Lemma sst_clo_bind (E C : Type -> Type) (X Y : Type) :
  forall (t1 t2 : ctree E C X) (k1 k2 : X -> ctree E C Y) RR `{HasStuck: B0 -< C},
		t1 ≲ t2 ->
    (forall x, (sst0 eq RR) (k1 x) (k2 x)) ->
    sst0 eq RR (t1 >>= k1) (t2 >>= k2)
.
Proof.
  intros.
  apply (ft_t (@bind_ctx_ssim0_t E C X Y _)).
  apply in_bind_ctx; auto.
  intros ? ? <-; auto.
Qed.

(*|
Specializing the congruence principle for [≲]
|*)
Lemma ssim0_clo_bind (E C: Type -> Type) (X Y : Type) :
  forall (t1 t2 : ctree E C X) (k1 k2 : X -> ctree E C Y) `{HasStuck: B0 -< C},
		t1 ≲ t2 ->
    (forall x, k1 x ≲ k2 x) ->
    t1 >>= k1 ≲ t2 >>= k2
.
Proof.
  intros * EQ EQs.
  apply (ft_t (@bind_ctx_ssim0_t E C X Y _)).
  apply in_bind_ctx; auto.
  intros ? ? <-; auto.
  apply EQs.
Qed.

(*|
And in particular, we can justify rewriting [≲] to the left of a [bind].
|*)
Lemma bind_ssim0_cong_gen {E C X Y} RR {HasStuck: B0 -< C}:
  Proper (ssim0 eq ==> pointwise_relation X (sst0 eq RR) ==> sst0 eq RR) (@bind E C X Y).

Proof.
  repeat red; intros; eapply sst_clo_bind; eauto.
Qed.

Ltac __upto_bind_ssim0 :=
  match goal with
    |- @ssim0 ?E ?F ?C ?D ?X ?Y _ _ (CTree.bind (T := ?T) _ _) (CTree.bind (T := ?T') _ _) =>
      apply ssim0_clo_bind
  | |- body (t (@ss0 ?E ?F ?C ?D ?X ?Y _ _)) ?R (CTree.bind (T := ?T) _ _) (CTree.bind (T := ?T) _ _) =>
      apply (ft_t (@bind_ctx_ssim0_t E C T X _)), in_bind_ctx
  | |- body (bt (@ss0 ?E ?F ?C ?D ?X ?Y _ _)) ?R (CTree.bind (T := ?T) _ _) (CTree.bind (T := ?T) _ _) =>
      apply (fbt_bt (@bind_ctx_ssim0_t E C T X _)), in_bind_ctx
  end.

Ltac __upto_bind_eq_ssim0 :=
  match goal with
  | |- @ssim0 ?E ?F ?C ?D ?X ?Y _ _ (CTree.bind (T := ?T) _ _) (CTree.bind (T := ?T') _ _) =>
      __upto_bind_ssim0; [reflexivity | intros ?]
  | _ => __upto_bind_ssim0; [reflexivity | intros ? ? <-]
  end.

Ltac __play_ssim0 := step; cbn; intros ? ? ?TR.

Ltac __play_ssim0_in H :=
  step in H;
  cbn in H; edestruct H as [? ?TR ?EQ];
  clear H; [etrans |].

Ltac __eplay_ssim0 :=
  match goal with
  | h : @ssim0 ?E _ ?C _ ?X _ _ _ ?L _ _ |- _ =>
      __play_ssim0_in h
  end.

#[local] Tactic Notation "play" := __play_ssim0.
#[local] Tactic Notation "play" "in" ident(H) := __play_ssim0_in H.
#[local] Tactic Notation "eplay" := __eplay_ssim0.

Section Proof_Rules.

  Context {E C: Type -> Type} {X Y : Type} {HasStuck: B0 -< C}.

  Lemma step_ss0_ret_gen (x y : X) (R : rel _ _) :
    R stuckD stuckD ->
    (Proper (equ eq ==> equ eq ==> impl) R) ->
    x = y ->
    ss0 eq R (Ret x : ctree E C X) (Ret y).
  Proof.
    intros Rstuck PROP <-.
    cbn; intros ? ? TR; inv_trans; subst.
    cbn; do 2 eexists. 
    split.
    - etrans.
    - split. now rewrite EQ. reflexivity.
  Qed.

  Lemma step_ss0_ret (x y : X) (R : rel _ _) :
    x = y ->
    ssbt0 eq R (Ret x : ctree E C X) (Ret y).
  Proof.
    apply step_ss0_ret_gen.
    reflexivity.
    typeclasses eauto.
  Qed.

  (*|
    The vis nodes are deterministic from the perspective of the labeled transition system,
    stepping is hence symmetric and we can just recover the itree-style rule.
    |*)
  Lemma step_ss0_vis_gen (e : E X) (k k' : X -> ctree E C Y) (R : rel _ _) :
    (Proper (equ eq ==> equ eq ==> impl) R) ->
    (forall x, R (k x) (k' x)) ->
    ss0 eq R (Vis e k) (Vis e k').
  Proof.
    intros PR EQs.
    intros ? ? TR; inv_trans; subst.
    cbn; do 2 eexists; split; [etrans | split; [rewrite EQ; eauto|reflexivity]].
  Qed.

  Lemma step_ss0_vis (e : E X) (k k' : X -> ctree E C Y) (R : rel _ _) :
    (forall x, sst0 eq R (k x) (k' x)) ->
    ssbt0 eq R (Vis e k) (Vis e k').
  Proof.
    intros * EQ.
    apply step_ss0_vis_gen; auto.
    typeclasses eauto.
  Qed.

  (*|
    Same goes for visible tau nodes.
    |*)
   Lemma step_ss0_step_gen (t t' : ctree E C X) (R : rel _ _) {HasTau: B1 -< C}:
    (Proper (equ eq ==> equ eq ==> impl) R) ->
    (R t t') ->
    ss0 eq R (Step t) (Step t').
  Proof.
    intros PR EQs.
    intros ? ? TR; inv_trans; subst.
    cbn; do 2 eexists; split; [etrans | split; [rewrite EQ; eauto|reflexivity]].
  Qed.

  Lemma step_ss0_step (t t' : ctree E C X) (R : rel _ _) {HasTau: B1 -< C}:
    (sst0 eq R t t') ->
    ssbt0 eq R (Step t) (Step t').
  Proof.
    intros. apply step_ss0_step_gen; auto.
    typeclasses eauto.
  Qed.

  (*|
    When matching visible brs one against another, in general we need to explain how
    we map the branches from the left to the branches to the right.
    A useful special case is the one where the arity coincide and we simply use the identity
    in both directions. We can in this case have [n] rather than [2n] obligations.
    |*)
  Lemma step_ss0_brS_gen Z (c : C Y) (c' : C Z) (k : Y -> ctree E C X) (k' : Z -> ctree E C X) (R : rel _ _) :
    (Proper (equ eq ==> equ eq ==> impl) R) ->
    (forall x, exists y, R (k x) (k' y)) ->
    ss0 eq R (BrS c k) (BrS c' k').
  Proof.
    intros PROP EQs ? ? TR; inv_trans; subst.
    destruct (EQs x) as [y HR].
    cbn; do 2 eexists; split; [etrans | split; [rewrite EQ; eauto|reflexivity]].
  Qed.

  Lemma step_ss0_brS Z (c : C Y) (c' : C Z) (k : Y -> ctree E C X) (k' : Z -> ctree E C X) (R : rel _ _) :
    (forall x, exists y, sst0 eq R (k x) (k' y)) ->
    ssbt0 eq R (BrS c k) (BrS c' k').
  Proof.
    intros.    
    apply step_ss0_brS_gen; auto.
    typeclasses eauto.
  Qed.

  Lemma step_ss0_brS_id_gen (c : C Y) (k k' : Y -> ctree E C X) (R : rel _ _) :
    (Proper (equ eq ==> equ eq ==> impl) R) ->
    (forall x, R (k x) (k' x)) ->
    ss0 eq R (BrS c k) (BrS c k').
  Proof.
    intros; apply step_ss0_brS_gen; eauto.
  Qed.
  
  Lemma step_ss0_brS_id (c : C Y) (k k' : Y -> ctree E C X) (R : rel _ _) :
    (forall x, sst0 eq R (k x) (k' x)) ->
    ssbt0 eq R (BrS c k) (BrS c k').
  Proof.
    intros.
    apply step_ss0_brS_id_gen.
    typeclasses eauto.
    eauto.
  Qed.

  (*|
    For invisible nodes, the situation is different: we may kill them, but that execution
    cannot act as going under the guard.
    |*)
  Lemma step_ss0_guard_gen (t t' : ctree E C X) (R : rel _ _) {HasTau: B1 -< C}:
    ss0 eq R t t' ->
    ss0 eq R (Guard t) (Guard t').
  Proof.
    intros EQ.
    intros ? ? TR; inv_trans; subst.
    apply EQ in TR as (? & ? & ? & ? & ?); subst.
    do 2 eexists; split; [etrans | split; trivial].
  Qed.

  Lemma step_ss0_guard (t t' : ctree E C X) (R : rel _ _) {HasTau: B1 -< C} :
    ssbt0 eq R t t' ->
    ssbt0 eq R (Guard t) (Guard t').
  Proof.
    apply step_ss0_guard_gen.
  Qed.

  Lemma step_ss0_brD_l_gen n (c : C n) (k : n -> ctree E C X) (t': ctree E C X) (R: rel _ _):
    (forall x, ss0 eq R (k x) t') ->
    ss0 eq R (BrD c k) t'.
  Proof.
    intros EQs.
    intros ? ? TR; inv_trans; subst.
    apply EQs in TR; destruct TR as [u' TR' EQ'].
    eauto.
  Qed.

  Lemma step_ss0_brD_l n (c : C n) 
    (k : n -> ctree E C X) (t' : ctree E C X) (R : rel _ _) :
    (forall x, ssbt0 eq R (k x) t') ->
    ssbt0 eq R (BrD c k) t'.
  Proof.
    apply step_ss0_brD_l_gen.
  Qed.

  Lemma step_ss0_brD_r_gen n (c: C n) (k : n -> ctree E C X) (t: ctree E C X) x R:
    ss0 eq R t (k x) ->
    ss0 eq R t (BrD c k).
  Proof.
    cbn. intros.
    apply H in H0 as (? & ? & ? & ? & ?).
    exists x0; etrans.
  Qed.

  Lemma step_ss0_brD_r n (c: C n) (k : n -> ctree E C X) (t: ctree E C X) x R:
    ssbt0 eq R t (k x) ->
    ssbt0 eq R t (BrD c k).
  Proof.
    intros. eapply step_ss0_brD_r_gen. apply H.
  Qed.

  Lemma step_ss0_brD_gen n m (cn: C n) (cm: C m)
    (k : n -> ctree E C X) (k' : m -> ctree E C X) (R : rel _ _) :
    (forall x, exists y, ss0 eq R (k x) (k' y)) ->
    ss0 eq R (BrD cn k) (BrD cm k').
  Proof.
    intros EQs.
    apply step_ss0_brD_l_gen.
    intros. destruct (EQs x) as [x' ?].
    now apply step_ss0_brD_r_gen with (x := x').
  Qed.

  Lemma step_ss0_brD n m (cn: C n) (cm: C m)
    (k : n -> ctree E C X) (k' : m -> ctree E C X) (R : rel _ _) :
    (forall x, exists y, ssbt0 eq R (k x) (k' y)) ->
    ssbt0 eq R (BrD cn k) (BrD cm k').
  Proof.
    apply step_ss0_brD_gen.
  Qed.

  Lemma step_ss0_brD_id_gen n (c: C n)
    (k k' : n -> ctree E C X) (R : rel _ _) :
    (forall x, ss0 eq R (k x) (k' x)) ->
    ss0 eq R (BrD c k) (BrD c k').
  Proof.
    intros; apply step_ss0_brD_gen.
    intros x; exists x; apply H.
  Qed.

  Lemma step_ss0_brD_id n (c: C n)
    (k k' : n -> ctree E C X) (R : rel _ _) :
    (forall x, ssbt0 eq R (k x) (k' x)) ->
    ssbt0 eq R (BrD c k) (BrD c k').
  Proof.
    apply step_ss0_brD_id_gen.
  Qed.

End Proof_Rules.

Section WithParams.

  Context {E C: Type -> Type} {X : Type} {HasStuck: B0 -< C}.

  (*|
    Note that with visible schedules, nary-spins are equivalent only
    if neither are empty, or if both are empty: they match each other's
    tau challenge infinitely often.
    With invisible schedules, they are always equivalent: neither of them
    produce any challenge for the other.
  |*)
  Lemma spinS_gen_nonempty : forall {Z X Y} (c: C X) (c': C Y) (x: X) (y: Y),
      @spinS_gen E C Z X c ≲ @spinS_gen E C Z Y c'.
  Proof.
    intros R.
    coinduction S CIH; cbn; intros ? ? ? ? ? ? ? ? TR.
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
  Lemma ssim0_ret_inv (r1 r2 : X) :
    (Ret r1 : ctree E C X) ≲ Ret r2 ->
    r1 = r2.
  Proof.
    intro.
    eplay.
    destruct TR as (? & ? & ? & <-).
    now inv_trans.    
  Qed.

  Lemma ssim0_vis_inv_type {X1 X2}
        (e1 : E X1) (e2 : E X2) (k1 : X1 -> ctree E C X) (k2 : X2 -> ctree E C X) (x : X1):
    Vis e1 k1 ≲ Vis e2 k2 ->
    X1 = X2.
  Proof.
    intros.
    eplay.
    destruct TR as (? & ? & ? & <-).
    inv_trans. inv EQl; eauto.
    Unshelve. exact x.
  Qed.

  Lemma ssbt0_eq_vis_inv {Y} (e1 e2 : E Y) (k1 k2 : Y -> ctree E C X) (x : Y) R :
    ssbt0 eq R (Vis e1 k1) (Vis e2 k2) ->
    e1 = e2 /\ forall x, sst0 eq R (k1 x) (k2 x).
  Proof.
    intros.
    split.
    - edestruct H as [? ? ?].
      etrans. destruct H0 as (? & ? & ? & ?). subst. now inv_trans.
    - intros.
      edestruct H as [? ? ?].
      etrans.
      destruct H0 as (? & ? & ? & ?). subst. simpl in *.
      inv H0. apply inj_pair2 in H4, H5,H6, H7; subst.
      rewrite H3.
      rewrite ctree_eta in H1; cbn in H1.
  Admitted.

  Lemma ssim0_eq_vis_inv {Y} (e1 e2 : E Y) (k1 k2 : Y -> ctree E C X) (x : Y) :
    Vis e1 k1 ≲ Vis e2 k2 ->
    e1 = e2 /\ forall x, k1 x ≲ k2 x.
  Proof.
    intros.
    (* Why doesn't apply work directly here? *)
    epose proof (proj1 (enhanced_gfp (@ss0 E E C C X X _ _ eq) _ _)). apply H0 in H. clear H0.
    step in H. apply ssbt0_eq_vis_inv in H; auto.
    destruct H. split; auto.
    intro. subst. specialize (H0 x0).    
    apply (proj1 (t_gfp_bt (@ss0 E E C C X X _ _ eq) _ _)) in H0. apply H0.
  Qed.

  Lemma ssim0_brS_inv
        n m (cn: C n) (cm: C m) (k1 : n -> ctree E C X) (k2 : m -> ctree E C X) :
    BrS cn k1 ≲ BrS cm k2 ->
    (forall i1, exists i2, k1 i1 ≲ k2 i2).
  Proof.
    intros EQ i1.
    eplay.
    destruct TR as (? & ? & ? & ?); subst.
    inv_trans.
    eexists; eauto.
  Qed.

  Lemma ss0_brD_l_inv n (c: C n)
    (t : ctree E C X) (k : n -> ctree E C X) R:
    ss0 eq R (BrD c k) t ->
    forall x, ss0 eq R (k x) t.
  Proof.
    cbn. intros.
    eapply trans_brD in H0; [| reflexivity].
    apply H in H0 as (? & ? & ? & ? & ?); subst.
    eauto.
  Qed.

  Lemma ssim0_brD_l_inv n (c: C n)
    (t : ctree E C X) (k : n -> ctree E C X):
    BrD c k ≲ t ->
    forall x, k x ≲ t.
  Proof.
    intros. step. step in H. eapply ss0_brD_l_inv. apply H.
  Qed.

  (* This one isn't very convenient... *)
  Lemma ssim0_brD_r_inv n (c: C n)
    (t : ctree E C X) (k : n -> ctree E C X):
    t ≲ BrD c k ->
    forall l t', trans l t t' ->
    exists x t'', trans l (k x) t'' /\ t' ≲ t''.
  Proof.
    cbn. intros. step in H. apply H in H0 as (? & ? & ? & ? & ?); subst. inv_trans.
    eauto.
  Qed.

End WithParams.

(*|
A strong bisimulation gives two strong simulations,
but two strong simulations do not always give a strong bisimulation.
This property is true if we only allow brs with 0 or 1 branch,
but we prove a counter-example for a ctree with a binary br.
|*)

Lemma ss0_sb : forall {E C X} RR {HasStuck: B0 -< C}
  (t t' : ctree E C X),
  ss0 eq RR t t' ->
  ss0 eq (flip RR) t' t ->
  sb eq RR t t'.
Proof.
  intros.
  split; eauto.
  simpl in *; intros.
  destruct (H0 _ _ H1) as (? & ? & ? & ? & ?).
  destruct (H _ _ H2) as (? & ? & ? & ? & ?).
  subst; eauto.
Qed.

#[local] Definition t1 : ctree void1 (B0 +' B1) unit :=
  Step (Ret tt).

#[local] Definition t2 : ctree void1 (B0 +' B2) unit :=
  brS2 (Ret tt) (stuckD).

Lemma ssim0_hsbisim_nequiv :
  ssim0 eq t1 t2 /\ ssim0 eq t2 t1 /\ ~ sbisim eq t1 t2.
Proof.
  unfold t1, t2. intuition.
  - step.
Admitted.
(* LEF: Hm, not sure how to work with the preorder of branch effects... 
apply step_ss0_brS; auto.
    intros _. exists Fin.F1. reflexivity.
  - step. apply step_ss0_brS; auto.
    intro. exists Fin.F1. destruct x.
    + reflexivity.
    + step. apply stuckD_ss0.
  - step in H. cbn in H. destruct H as [_ ?].
    specialize (H tau stuckD). lapply H; [| etrans].
    intros. destruct H0 as [? ? ?].
    inv_trans. step in H1. cbn in H1. destruct H1 as [? _].
    specialize (H0 (val tt) stuckD). lapply H0. 2: { rewrite EQ. etrans. }
    intro. destruct H1 as [? ? ?].
    now apply stuckD_is_stuck in H1.
Qed.
*)
