From Coq Require Import Lia Basics Fin.

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

Set Implicit Arguments.

(* TODO: Decide where to set this *)
Arguments trans : simpl never.

#[local] Tactic Notation "step" := __step_sbisim || step.
#[local] Tactic Notation "coinduction" simple_intropattern(R) simple_intropattern(H) :=
  __coinduction_sbisim R H || coinduction R H.
#[local] Tactic Notation "step" "in" ident(H) := __step_in_sbisim H || step in H.

Module SSim0Notations.

  Notation "t ≲ u" := (ssim0 t u) (at level 70).
  Notation "t [≲] u" := (ss0 _ t u) (at level 79).
  Notation "t {≲} u" := (t (ss0 _) t u) (at level 79).
  Notation "t {{≲}} u" := (bt (ss0 _) t u) (at level 79).

End SSim0Notations.

Import EquNotations.
Import SBisimNotations.

Section ssim0_theory.

  Context {E : Type -> Type} {X : Type}.
  Notation ss0 := (@ss0 E X).
  Notation ssim0 := (@ssim0 E X).
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
    apply Coinduction.
    intros R x z [y xy yz] l x' xx'.
    destruct (xy _ _ xx') as [y' yy' x'y'].
    destruct (yz _ _ yy') as [z' zz' y'z'].
    exists z'. assumption.
    apply (f_Tf ss0).
    eexists; eauto.
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
    Proper (sbisim ==> sbisim ==> flip impl) ssim0.
  Proof.
    repeat intro.
    symmetry in H0. apply sbisim_ssim0 in H, H0.
    transitivity y0. transitivity y. all: auto.
  Qed.

  #[global] Instance sbisim_clos_ssim0_ctx :
    Proper (sbisim ==> sbisim ==> impl) ssim0.
  Proof.
    repeat intro. symmetry in H, H0. eapply sbisim_clos_ssim0_goal; eauto.
  Qed.

  #[global] Instance sbisim_clos_sst_goal RR :
    Proper (sbisim ==> sbisim ==> flip impl) (sst0 RR).
  Proof.
    cbn; intros ? ? eq1 ? ? eq2 H.
    symmetry in eq2. apply sbisim_ssim0 in eq1, eq2.
    rewrite eq1, <- eq2.
    auto.
  Qed.

  #[global] Instance sbisim_clos_sst_ctx RR :
    Proper (sbisim ==> sbisim ==> impl) (sst0 RR).
  Proof.
    cbn; intros ? ? eq1 ? ? eq2 ?.
    rewrite <- eq1, <- eq2.
    auto.
  Qed.

  #[global] Instance sbisim_clos_ssT_goal RR f :
    Proper (sbisim ==> sbisim ==> flip impl) (ssT0 f RR).
  Proof.
    cbn; intros ? ? eq1 ? ? eq2 ?.
    symmetry in eq2. apply sbisim_ssim0 in eq1, eq2.
    rewrite eq1, <- eq2.
    auto.
  Qed.

  #[global] Instance sbisim_clos_ssT_ctx RR f :
    Proper (sbisim ==> sbisim ==> impl) (ssT0 f RR).
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
    apply Coinduction.
    intros R t u EQ l t1 TR. cbn in EQ. inv EQ.
    cbn in *. rewrite Equt in TR.
    apply HR in TR.
    destruct TR.
    exists x.
    rewrite <- Equu; auto.
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
    rewrite tt' in H0. apply H in H0 as [? ? ?].
    eexists; eauto. rewrite uu'. eauto.
  Qed.

  #[global] Instance equ_ss0_closed_ctx {r} : Proper (equ eq ==> equ eq ==> impl) (ss0 r).
  Proof.
    intros t t' tt' u u' uu'; cbn; intros.
    rewrite <- tt' in H0. apply H in H0 as [? ? ?].
    eexists; eauto. rewrite <- uu'. eauto.
  Qed.

(*|
stuck ctrees can be simulated by anything.
|*)

  Lemma is_stuck_ss0 (R : rel _ _) (t t' : ctree E X) :
    is_stuck t -> ss0 R t t'.
  Proof.
    repeat intro. now apply H in H0.
  Qed.

  Lemma is_stuck_ssim0 (t t' : ctree E X) :
    is_stuck t -> ssim0 t t'.
  Proof.
    intros. step. now apply is_stuck_ss0.
  Qed.

  Lemma stuckD_ss0 (R : rel _ _) (t : ctree E X) : ss0 R CTree.stuckD t.
  Proof.
    repeat intro. now apply stuckD_is_stuck in H.
  Qed.

  Lemma stuckD_ssim0 (t : ctree E X) : ssim0 CTree.stuckD t.
  Proof.
    intros. step. apply stuckD_ss0.
  Qed.

  Lemma spinD_ss0 (R : rel _ _) (t : ctree E X) : ss0 R CTree.spinD t.
  Proof.
    repeat intro. now apply spinD_is_stuck in H.
  Qed.

  Lemma spinD_ssim0 : forall (t' : ctree E X),
      ssim0 CTree.spinD t'.
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

 Context {E : Type -> Type} {X Y : Type}.

(*|
Specialization of [bind_ctx] to a function acting with [ssim] on the bound value,
and with the argument (pointwise) on the continuation.
|*)
  Program Definition bind_ctx_ssim0 : mon (rel (ctree E Y) (ctree E Y)) :=
    {|body := fun R => @bind_ctx E X X Y Y ssim0 (pointwise eq R) |}.
  Next Obligation.
    intros ?? H. apply leq_bind_ctx. intros ?? H' ?? H''.
    apply in_bind_ctx. apply H'. intros t t' HS. apply H, H'', HS.
  Qed.

(*|
The resulting enhancing function gives a valid up-to technique
|*)
  Lemma bind_ctx_ssim0_t :
    bind_ctx_ssim0 <= sst0.
  Proof.
    intro HL.
    apply Coinduction.
    intros R. apply (leq_bind_ctx _).
    intros t1 t2 tt k1 k2 kk.
    step in tt.
    intros l u STEP.
    apply trans_bind_inv in STEP as [(H & t' & STEP & EQ) | (v & STEPres & STEP)]; cbn in *.
    - apply tt in STEP as [u' STEP EQ'].
      eexists.
      apply trans_bind_l; eauto.
      apply (fT_T equ_clos_sst0).
      econstructor; [exact EQ | | reflexivity].
      apply (fTf_Tf ss0).
      apply in_bind_ctx; auto.
      intros ? ? ->.
      apply (b_T ss0).
      red in kk. red. red. now apply kk.
    - apply tt in STEPres as [u' STEPres EQ'].
      pose proof (trans_val_inv STEPres) as EQ.
      rewrite EQ in STEPres.
      specialize (kk v v eq_refl).
      apply kk in STEP as [u'' STEP EQ'']; cbn in *.
      eexists.
      eapply trans_bind_r; cbn in *; eauto.
      eapply (id_T ss0); auto.
  Qed.

End bind.

Import CTree.
Import CTreeNotations.

(*|
Expliciting the reasoning rule provided by the up-to principles.
|*)
Lemma sst_clo_bind (E : Type -> Type) (X Y : Type) :
  forall (t1 t2 : ctree E X) (k1 k2 : X -> ctree E Y) RR,
		t1 ≲ t2 ->
    (forall x, (sst0 RR) (k1 x) (k2 x)) ->
    sst0 RR (t1 >>= k1) (t2 >>= k2)
.
Proof.
  intros.
  apply (ft_t (@bind_ctx_ssim0_t E X Y)).
  apply in_bind_ctx; auto.
  intros ? ? <-; auto.
Qed.

(*|
Specializing the congruence principle for [≲]
|*)
Lemma ssim0_clo_bind (E : Type -> Type) (X Y : Type) :
  forall (t1 t2 : ctree E X) (k1 k2 : X -> ctree E Y),
		t1 ≲ t2 ->
    (forall x, k1 x ≲ k2 x) ->
    t1 >>= k1 ≲ t2 >>= k2
.
Proof.
  intros * EQ EQs.
  apply (ft_t (@bind_ctx_ssim0_t E X Y)).
  apply in_bind_ctx; auto.
  intros ? ? <-; auto.
  apply EQs.
Qed.

(*|
And in particular, we can justify rewriting [≲] to the left of a [bind].
|*)
Lemma bind_ssim0_cong_gen {E X Y} RR :
  Proper (ssim0 ==> pointwise_relation X (sst0 RR) ==> sst0 RR) (@bind E X Y).
Proof.
  repeat red; intros; eapply sst_clo_bind; eauto.
Qed.

Ltac __upto_bind_ssim0 :=
  match goal with
    |- @ssim0 _ ?X (CTree.bind (T := ?T) _ _) (CTree.bind (T := ?T') _ _) =>
      apply ssim0_clo_bind
  | |- body (t (@ss0 ?E ?X)) ?R (CTree.bind (T := ?T) _ _) (CTree.bind (T := ?T) _ _) =>
      apply (ft_t (@bind_ctx_ssim0_t E T X)), in_bind_ctx
  | |- body (bt (@ss0 ?E ?X)) ?R (CTree.bind (T := ?T) _ _) (CTree.bind (T := ?T) _ _) =>
      apply (fbt_bt (@bind_ctx_ssim0_t E T X)), in_bind_ctx
  end.
Ltac __upto_bind_eq_ssim0 :=
  match goal with
  | |- @ssim0 _ ?X (CTree.bind (T := ?T) _ _) (CTree.bind (T := ?T') _ _) =>
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
  | h : @ssim0 ?E ?X _ _ |- _ =>
      __play_ssim0_in h
  end.

#[local] Tactic Notation "play" := __play_ssim0.
#[local] Tactic Notation "play" "in" ident(H) := __play_ssim0_in H.
#[local] Tactic Notation "eplay" := __eplay_ssim0.

Section Proof_Rules.

  Context {E : Type -> Type}.
  Context {X Y : Type}.

  Lemma step_ss0_ret_gen (x y : X) (R : rel _ _) :
    R stuckD stuckD ->
    (Proper (equ eq ==> equ eq ==> impl) R) ->
    x = y ->
    ss0 R (Ret x : ctree E X) (Ret y).
  Proof.
    intros Rstuck PROP <-.
    cbn; intros ? ? TR; inv_trans; subst.
    cbn; eexists; etrans.
    now rewrite EQ.
  Qed.

  Lemma step_ss0_ret (x y : X) (R : rel _ _) :
    x = y ->
    ssbt0 R (Ret x : ctree E X) (Ret y).
  Proof.
    apply step_ss0_ret_gen.
    reflexivity.
    typeclasses eauto.
  Qed.

(*|
The vis nodes are deterministic from the perspective of the labeled transition system,
stepping is hence symmetric and we can just recover the itree-style rule.
|*)
  Lemma step_ss0_vis_gen (e : E X) (k k' : X -> ctree E Y) (R : rel _ _) :
    (Proper (equ eq ==> equ eq ==> impl) R) ->
    (forall x, R (k x) (k' x)) ->
    ss0 R (Vis e k) (Vis e k').
  Proof.
    intros PR EQs.
    intros ? ? TR; inv_trans; subst.
    cbn; eexists; etrans. rewrite EQ; auto.
  Qed.

  Lemma step_ss0_vis (e : E X) (k k' : X -> ctree E Y) (R : rel _ _) :
    (forall x, sst0 R (k x) (k' x)) ->
    ssbt0 R (Vis e k) (Vis e k').
  Proof.
    intros * EQ.
    apply step_ss0_vis_gen; auto.
    typeclasses eauto.
  Qed.

(*|
Same goes for visible tau nodes.
|*)
   Lemma step_ss0_step_gen (t t' : ctree E X) (R : rel _ _) :
    (Proper (equ eq ==> equ eq ==> impl) R) ->
    (R t t') ->
    ss0 R (Step t) (Step t').
  Proof.
    intros PR EQs.
    intros ? ? TR; inv_trans; subst.
    cbn; eexists; etrans; rewrite EQ; auto.
  Qed.

  Lemma step_ss0_step (t t' : ctree E X) (R : rel _ _) :
    (sst0 R t t') ->
    ssbt0 R (Step t) (Step t').
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

  Lemma step_ss0_brS_gen n m (k : fin n -> ctree E X) (k' : fin m -> ctree E X) (R : rel _ _) :
    (Proper (equ eq ==> equ eq ==> impl) R) ->
    (forall x, exists y, R (k x) (k' y)) ->
    ss0 R (BrS n k) (BrS m k').
  Proof.
    intros PROP EQs ? ? TR; inv_trans; subst.
    destruct (EQs x) as [y HR].
    eexists.
    etrans.
    rewrite EQ; eauto.
  Qed.

  Lemma step_ss0_brS n m (k : fin n -> ctree E X) (k' : fin m -> ctree E X) (R : rel _ _) :
    (forall x, exists y, sst0 R (k x) (k' y)) ->
    ssbt0 R (BrS n k) (BrS m k').
  Proof.
    intros ? EQs.
    apply step_ss0_brS_gen; auto.
    typeclasses eauto.
  Qed.

  Lemma step_ss0_brS_id_gen n
    (k k' : fin n -> ctree E X) (R : rel _ _) :
    (Proper (equ eq ==> equ eq ==> impl) R) ->
    (forall x, R (k x) (k' x)) ->
    ss0 R (BrS n k) (BrS n k').
  Proof.
    intros PROP ? EQs.
    apply step_ss0_brS_gen; auto.
    intros x; exists x; auto.
  Qed.

  Lemma step_ss0_brS_id n
    (k k' : fin n -> ctree E X) (R : rel _ _) :
    (forall x, sst0 R (k x) (k' x)) ->
    ssbt0 R (BrS n k) (BrS n k').
  Proof.
    apply step_ss0_brS_id_gen.
    typeclasses eauto.
  Qed.

(*|
For invisible nodes, the situation is different: we may kill them, but that execution
cannot act as going under the guard.
|*)
  Lemma step_ss0_tauI_gen (t t' : ctree E X) (R : rel _ _) :
    ss0 R t t' ->
    ss0 R (Guard t) (Guard t').
  Proof.
    intros EQ.
    intros ? ? TR; inv_trans; subst.
    apply EQ in TR as [? ? ?].
    etrans.
  Qed.

  Lemma step_ss0_tauI (t t' : ctree E X) (R : rel _ _) :
    ssbt0 R t t' ->
    ssbt0 R (Guard t) (Guard t').
  Proof.
    apply step_ss0_tauI_gen.
  Qed.

  Lemma step_ss0_brD_l_gen n
    (k : fin n -> ctree E X) (t' : ctree E X) (R : rel _ _) :
    (forall x, ss0 R (k x) t') ->
    ss0 R (BrD n k) t'.
  Proof.
    intros EQs.
    intros ? ? TR; inv_trans; subst.
    apply EQs in TR; destruct TR as [u' TR' EQ'].
    eauto.
  Qed.

  Lemma step_ss0_brD_l n
    (k : fin n -> ctree E X) (t' : ctree E X) (R : rel _ _) :
    (forall x, ssbt0 R (k x) t') ->
    ssbt0 R (BrD n k) t'.
  Proof.
    apply step_ss0_brD_l_gen.
  Qed.

  Lemma step_ss0_brD_r_gen :
    forall (t : ctree E X) n (k : fin n -> ctree E X) x R,
    ss0 R t (k x) ->
    ss0 R t (BrD n k).
  Proof.
    cbn. intros.
    apply H in H0 as [? ? ?].
    exists x0; etrans.
  Qed.

  Lemma step_ss0_brD_r :
    forall (t : ctree E X) n (k : fin n -> ctree E X) x R,
    ssbt0 R t (k x) ->
    ssbt0 R t (BrD n k).
  Proof.
    intros. eapply step_ss0_brD_r_gen. apply H.
  Qed.

  Lemma step_ss0_brD_gen n m
    (k : fin n -> ctree E X) (k' : fin m -> ctree E X) (R : rel _ _) :
    (forall x, exists y, ss0 R (k x) (k' y)) ->
    ss0 R (BrD n k) (BrD m k').
  Proof.
    intros EQs.
    apply step_ss0_brD_l_gen.
    intros. destruct (EQs x) as [x' ?].
    now apply step_ss0_brD_r_gen with (x := x').
  Qed.

  Lemma step_ss0_brD n m
    (k : fin n -> ctree E X) (k' : fin m -> ctree E X) (R : rel _ _) :
    (forall x, exists y, ssbt0 R (k x) (k' y)) ->
    ssbt0 R (BrD n k) (BrD m k').
  Proof.
    apply step_ss0_brD_gen.
  Qed.

  Lemma step_ss0_brD_id_gen n
    (k k' : fin n -> ctree E X) (R : rel _ _) :
    (forall x, ss0 R (k x) (k' x)) ->
    ss0 R (BrD n k) (BrD n k').
  Proof.
    intros; apply step_ss0_brD_gen.
    intros x; exists x; apply H.
  Qed.

  Lemma step_ss0_brD_id n
    (k k' : fin n -> ctree E X) (R : rel _ _) :
    (forall x, ssbt0 R (k x) (k' x)) ->
    ssbt0 R (BrD n k) (BrD n k').
  Proof.
    apply step_ss0_brD_id_gen.
  Qed.

End Proof_Rules.

Section WithParams.

  Context {E : Type -> Type}.
  Context {X : Type}.

(*|
Note that with visible schedules, nary-spins are equivalent only
if neither are empty, or if both are empty: they match each other's
tau challenge infinitely often.
With invisible schedules, they are always equivalent: neither of them
produce any challenge for the other.
|*)
  Lemma spinS_nary_n_m : forall n m,
    n > 0 -> m > 0 ->
    ssim0 (@spinS_nary E X n) (spinS_nary m).
  Proof.
    intros.
    red. coinduction R CH.
    intros l t' TR.
    destruct m as [|m]; [lia |].
    rewrite ctree_eta in TR; cbn in TR.
    apply trans_brS_inv in TR as (_ & EQ & ->).
    eexists.
    rewrite ctree_eta; cbn.
    econstructor. exact Fin.F1.
    reflexivity.
    rewrite EQ; auto.
  Qed.

(*|
Inversion principles
--------------------
|*)
  Lemma ssim0_ret_inv (r1 r2 : X) :
    (Ret r1 : ctree E X) ≲ Ret r2 ->
    r1 = r2.
  Proof.
    intro.
    eplay. etrans. inv_trans. auto.
  Qed.

  Lemma ssim0_vis_inv_type {X1 X2}
        (e1 : E X1) (e2 : E X2) (k1 : X1 -> ctree E X) (k2 : X2 -> ctree E X) (x : X1):
    Vis e1 k1 ≲ Vis e2 k2 ->
    X1 = X2.
  Proof.
    intros.
    eplay.
    inv TR; auto.
    Unshelve. auto.
  Qed.

  Lemma ssbt0_eq_vis_inv {Y} (e1 e2 : E Y) (k1 k2 : Y -> ctree E X) (x : Y) R :
    ssbt0 R (Vis e1 k1) (Vis e2 k2) ->
    e1 = e2 /\ forall x, sst0 R (k1 x) (k2 x).
  Proof.
    intros.
    split.
    - cbn in H. edestruct H as [? ? ?].
      etrans. subst. now inv_trans.
    - cbn. intros. edestruct H as [? ? ?].
      etrans. subst. inv_trans. subst. apply H1.
    Unshelve. auto.
  Qed.

  Lemma ssim0_eq_vis_inv {Y} (e1 e2 : E Y) (k1 k2 : Y -> ctree E X) (x : Y) :
    Vis e1 k1 ≲ Vis e2 k2 ->
    e1 = e2 /\ forall x, k1 x ≲ k2 x.
  Proof.
    intros.
    (* Why doesn't apply work directly here? *)
    epose proof (proj1 (enhanced_gfp (@ss0 E X) _ _)). apply H0 in H. clear H0.
    step in H. apply ssbt0_eq_vis_inv in H; auto.
    destruct H. split; auto.
    intro. subst. specialize (H0 x0).
    apply (proj1 (t_gfp_bt (@ss0 E X) _ _)) in H0. apply H0.
  Qed.

  Lemma ssim0_brS_inv
        n1 n2 (k1 : fin n1 -> ctree E X) (k2 : fin n2 -> ctree E X) :
    BrS n1 k1 ≲ BrS n2 k2 ->
    (forall i1, exists i2, k1 i1 ≲ k2 i2).
  Proof.
    intros EQ i1.
    eplay.
    inv_trans.
    eexists; eauto.
  Qed.

  Lemma ss0_brD_l_inv : forall n
    (t : ctree E X) (k : fin n -> ctree E X) R,
    ss0 R (BrD n k) t ->
    forall x, ss0 R (k x) t.
  Proof.
    cbn. intros.
    eapply trans_brD in H0; [| reflexivity].
    apply H in H0 as [? ? ?].
    exists x0; auto.
  Qed.

  Lemma ssim0_brD_l_inv : forall n
    (t : ctree E X) (k : fin n -> ctree E X),
    BrD n k ≲ t ->
    forall x, k x ≲ t.
  Proof.
    intros. step. step in H. eapply ss0_brD_l_inv. apply H.
  Qed.

  (* This one isn't very convenient... *)
  Lemma ssim0_brD_r_inv : forall n
    (t : ctree E X) (k : fin n -> ctree E X),
    t ≲ BrD n k ->
    forall l t', trans l t t' ->
    exists x t'', trans l (k x) t'' /\ t' ≲ t''.
  Proof.
    cbn. intros. step in H. apply H in H0 as [? ? ?]. inv_trans.
    eauto.
  Qed.

End WithParams.

(*|
A strong bisimulation gives two strong simulations,
but two strong simulations do not always give a strong bisimulation.
This property is true if we only allow brs with 0 or 1 branch,
but we prove a counter-example for a ctree with a binary br.
|*)

Lemma ss0_sb : forall {E X} RR
  (t t' : ctree E X),
  ss0 RR t t' ->
  ss0 (flip RR) t' t ->
  sb RR t t'.
Proof.
  split; auto.
Qed.

#[local] Definition t1 : ctree void1 unit :=
  Step (Ret tt).

#[local] Definition t2 : ctree void1 unit :=
  brS2 (Ret tt) (stuckD).

Lemma ssim0_hsbisim_nequiv :
  ssim0 t1 t2 /\ ssim0 t2 t1 /\ ~ sbisim t1 t2.
Proof.
  unfold t1, t2. intuition.
  - step. apply step_ss0_brS; auto.
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
