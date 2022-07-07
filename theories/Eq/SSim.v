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

Import EquNotations.
Import SBisimNotations.

Arguments trans : simpl never.

#[local] Tactic Notation "step" := __step_sbisim || step.
#[local] Tactic Notation "coinduction" simple_intropattern(R) simple_intropattern(H) :=
  __coinduction_sbisim R H || coinduction R H.
#[local] Tactic Notation "step" "in" ident(H) := __step_in_sbisim H || step in H.

Section ssim_theory.

  Context {E : Type -> Type} {X : Type}.
  Notation ss := (@ss E X).
  Notation ssim := (@ssim E X).
  Notation sst := (coinduction.t ss).
  Notation ssbt := (coinduction.bt ss).
  Notation ssT := (coinduction.T ss).

(*|
Various results on reflexivity and transitivity.
|*)
  Lemma refl_sst: const seq <= sst.
  Proof.
    apply leq_t. cbn.
    intros. unfold seq in H. subst. eauto.
  Qed.

  Lemma square_sst : square <= sst.
  Proof.
    apply Coinduction.
    intros R x z [y xy yz] l x' xx'.
    destruct (xy _ _ xx') as [y' yy' x'y'].
    destruct (yz _ _ yy') as [z' zz' y'z'].
    exists z'. assumption.
    apply (f_Tf ss).
    eexists; eauto.
  Qed.

  #[global] Instance PreOrder_sst R : PreOrder (sst R).
  Proof. apply PreOrder_t. apply refl_sst. apply square_sst. Qed.

  Corollary PreOrder_ssim: PreOrder ssim.
  Proof. apply PreOrder_sst. Qed.

  #[global] Instance PreOrder_ssbt R : PreOrder (ssbt R).
	Proof. apply rel.PreOrder_bt. now apply refl_sst. apply square_sst. Qed.

  #[global] Instance PreOrder_ssT f R: PreOrder ((T ss) f R).
  Proof. apply rel.PreOrder_T. now apply refl_sst. apply square_sst. Qed.

(*|
Aggressively providing instances for rewriting hopefully faster
[sbisim] under all [ss1]-related contexts (consequence of the transitivity
of the companion).
|*)

  #[global] Instance sbisim_clos_ssim_goal :
    Proper (sbisim ==> sbisim ==> flip impl) ssim.
  Proof.
    repeat intro.
    symmetry in H0. apply sbisim_ssim in H, H0.
    transitivity y0. transitivity y. all: auto.
  Qed.

  #[global] Instance sbisim_clos_ssim_ctx :
    Proper (sbisim ==> sbisim ==> impl) ssim.
  Proof.
    repeat intro. symmetry in H, H0. eapply sbisim_clos_ssim_goal; eauto.
  Qed.

  #[global] Instance sbisim_clos_sst_goal RR :
    Proper (sbisim ==> sbisim ==> flip impl) (sst RR).
  Proof.
    cbn; intros ? ? eq1 ? ? eq2 H.
    symmetry in eq2. apply sbisim_ssim in eq1, eq2.
    rewrite eq1, <- eq2.
    auto.
  Qed.

  #[global] Instance sbisim_clos_sst_ctx RR :
    Proper (sbisim ==> sbisim ==> impl) (sst RR).
  Proof.
    cbn; intros ? ? eq1 ? ? eq2 ?.
    rewrite <- eq1, <- eq2.
    auto.
  Qed.

  #[global] Instance sbisim_clos_ssT_goal RR f :
    Proper (sbisim ==> sbisim ==> flip impl) (ssT f RR).
  Proof.
    cbn; intros ? ? eq1 ? ? eq2 ?.
    symmetry in eq2. apply sbisim_ssim in eq1, eq2.
    rewrite eq1, <- eq2.
    auto.
  Qed.

  #[global] Instance sbisim_clos_ssT_ctx RR f :
    Proper (sbisim ==> sbisim ==> impl) (ssT f RR).
  Proof.
    cbn; intros ? ? eq1 ? ? eq2 ?.
    rewrite <- eq1, <- eq2.
    auto.
  Qed.

(*|
Strong simulation up-to [equ] is valid
----------------------------------------
|*)
  Lemma equ_clos_sst : equ_clos <= sst.
  Proof.
    apply Coinduction.
    intros R t u EQ l t1 TR. cbn in EQ. inv EQ.
    cbn in *. rewrite Equt in TR.
    apply HR in TR.
    destruct TR.
    exists x.
    rewrite <- Equu; auto.
    eapply (f_Tf ss).
    econstructor; auto; auto.
  Qed.

  #[global] Instance equ_clos_sst_goal RR :
    Proper (equ eq ==> equ eq ==> flip impl) (sst RR).
  Proof.
    cbn; intros ? ? eq1 ? ? eq2 H.
    apply (ft_t equ_clos_sst); econstructor; [eauto | | symmetry; eauto]; assumption.
  Qed.

  #[global] Instance equ_clos_sst_ctx RR :
    Proper (equ eq ==> equ eq ==> impl) (sst RR).
  Proof.
    cbn; intros ? ? eq1 ? ? eq2 H.
    apply (ft_t equ_clos_sst); econstructor; [symmetry; eauto | | eauto]; assumption.
  Qed.

  #[global] Instance equ_ssbt_closed_goal {r} :
    Proper (equ eq ==> equ eq ==> flip impl) (ssbt r).
  Proof.
    cbn. intros.
    now rewrite <- H, <- H0 in H1.
  Qed.

  #[global] Instance equ_ssbt_closed_ctx {r} :
    Proper (equ eq ==> equ eq ==> impl) (ssbt r).
  Proof.
    cbn. intros.
    now rewrite H, H0 in H1.
  Qed.

  #[global] Instance equ_clos_ssT_goal RR f :
    Proper (equ eq ==> equ eq ==> flip impl) (ssT f RR).
  Proof.
    cbn; intros ? ? eq1 ? ? eq2 H.
    apply (fT_T equ_clos_sst); econstructor; [eauto | | symmetry; eauto]; assumption.
  Qed.

  #[global] Instance equ_clos_ssT_ctx RR f :
    Proper (equ eq ==> equ eq ==> impl) (ssT f RR).
  Proof.
    cbn; intros ? ? eq1 ? ? eq2 H.
    apply (fT_T equ_clos_sst); econstructor; [symmetry; eauto | | eauto]; assumption.
  Qed.

  #[global] Instance equ_clos_ssim_goal :
    Proper (equ eq ==> equ eq ==> flip impl) ssim.
  Proof.
    cbn; intros ? ? eq1 ? ? eq2 H.
    apply (ft_t equ_clos_sst); econstructor; [eauto | | symmetry; eauto]; assumption.
  Qed.

  #[global] Instance equ_clos_ssim_ctx :
    Proper (equ eq ==> equ eq ==> impl) ssim.
  Proof.
    cbn; intros ? ? eq1 ? ? eq2 H.
    apply (ft_t equ_clos_sst); econstructor; [symmetry; eauto | | eauto]; assumption.
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
stuck ctrees can be simulated by anything.
|*)

  Lemma is_stuck_ss (R : rel _ _) (t t' : ctree E X) :
    is_stuck t -> ss R t t'.
  Proof.
    repeat intro. now apply H in H0.
  Qed.

  Lemma is_stuck_ssim (t t' : ctree E X) :
    is_stuck t -> ssim t t'.
  Proof.
    intros. step. now apply is_stuck_ss.
  Qed.

  Lemma stuckD_ss (R : rel _ _) (t : ctree E X) : ss R CTree.stuckD t.
  Proof.
    repeat intro. now apply stuckD_is_stuck in H.
  Qed.

  Lemma stuckD_ssim (t : ctree E X) : ssim CTree.stuckD t.
  Proof.
    intros. step. apply stuckD_ss.
  Qed.

  Lemma spinD_ss (R : rel _ _) (t : ctree E X) : ss R CTree.spinD t.
  Proof.
    repeat intro. now apply spinD_is_stuck in H.
  Qed.

  Lemma spinD_ssim : forall (t' : ctree E X),
      CTree.spinD ≲ t'.
  Proof.
    intros. step. apply spinD_ss.
  Qed.

End ssim_theory.

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
  Program Definition bind_ctx_ssim : mon (rel (ctree E Y) (ctree E Y)) :=
    {|body := fun R => @bind_ctx E X X Y Y ssim (pointwise eq R) |}.
  Next Obligation.
    intros ?? H. apply leq_bind_ctx. intros ?? H' ?? H''.
    apply in_bind_ctx. apply H'. intros t t' HS. apply H, H'', HS.
  Qed.

(*|
The resulting enhancing function gives a valid up-to technique
|*)
  Lemma bind_ctx_ssim_t :
    bind_ctx_ssim <= sst.
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
      apply (fT_T equ_clos_sst).
      econstructor; [exact EQ | | reflexivity].
      apply (fTf_Tf ss).
      apply in_bind_ctx; auto.
      intros ? ? ->.
      apply (b_T ss).
      red in kk. red. red. now apply kk.
    - apply tt in STEPres as [u' STEPres EQ'].
      pose proof (trans_val_inv STEPres) as EQ.
      rewrite EQ in STEPres.
      specialize (kk v v eq_refl).
      apply kk in STEP as [u'' STEP EQ'']; cbn in *.
      eexists.
      eapply trans_bind_r; cbn in *; eauto.
      eapply (id_T ss); auto.
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
    (forall x, (sst RR) (k1 x) (k2 x)) ->
    sst RR (t1 >>= k1) (t2 >>= k2)
.
Proof.
  intros.
  apply (ft_t (@bind_ctx_ssim_t E X Y)).
  apply in_bind_ctx; auto.
  intros ? ? <-; auto.
Qed.

(*|
Specializing the congruence principle for [≲]
|*)
Lemma ssim_clo_bind (E : Type -> Type) (X Y : Type) :
  forall (t1 t2 : ctree E X) (k1 k2 : X -> ctree E Y),
		t1 ≲ t2 ->
    (forall x, k1 x ≲ k2 x) ->
    t1 >>= k1 ≲ t2 >>= k2
.
Proof.
  intros * EQ EQs.
  apply (ft_t (@bind_ctx_ssim_t E X Y)).
  apply in_bind_ctx; auto.
  intros ? ? <-; auto.
  apply EQs.
Qed.

(*|
And in particular, we can justify rewriting [≲] to the left of a [bind].
|*)
Lemma bind_ssim_cong_gen {E X Y} RR :
  Proper (ssim ==> pointwise_relation X (sst RR) ==> sst RR) (@bind E X Y).
Proof.
  repeat red; intros; eapply sst_clo_bind; eauto.
Qed.

Ltac __upto_bind_ssim :=
  match goal with
    |- @ssim _ ?X (CTree.bind (T := ?T) _ _) (CTree.bind (T := ?T') _ _) =>
      apply ssim_clo_bind
  | |- body (t (@ss ?E ?X)) ?R (CTree.bind (T := ?T) _ _) (CTree.bind (T := ?T) _ _) =>
      apply (ft_t (@bind_ctx_ssim_t E T X)), in_bind_ctx
  | |- body (bt (@ss ?E ?X)) ?R (CTree.bind (T := ?T) _ _) (CTree.bind (T := ?T) _ _) =>
      apply (fbt_bt (@bind_ctx_ssim_t E T X)), in_bind_ctx
  end.
Ltac __upto_bind_eq_ssim :=
  match goal with
  | |- @ssim _ ?X (CTree.bind (T := ?T) _ _) (CTree.bind (T := ?T') _ _) =>
    __upto_bind_ssim; [reflexivity | intros ?]
  | _ => __upto_bind_ssim; [reflexivity | intros ? ? <-]
  end.

Ltac __play_ssim := step; cbn; intros ? ? ?TR.

Ltac __play_ssim_in H :=
  step in H;
  cbn in H; edestruct H as [? ?TR ?EQ];
  clear H; [etrans |].

Ltac __eplay_ssim :=
  match goal with
  | h : @ssim ?E ?X _ _ |- _ =>
      __play_ssim_in h
  end.

#[local] Tactic Notation "play" := __play_ssim.
#[local] Tactic Notation "play" "in" ident(H) := __play_ssim_in H.
#[local] Tactic Notation "eplay" := __eplay_ssim.

Section Proof_Rules.

  Context {E : Type -> Type}.
  Context {X Y : Type}.

  Lemma step_ss_ret_gen (x y : X) (R : rel _ _) :
    R stuckD stuckD ->
    (Proper (equ eq ==> equ eq ==> impl) R) ->
    x = y ->
    ss R (Ret x : ctree E X) (Ret y).
  Proof.
    intros Rstuck PROP <-.
    cbn; intros ? ? TR; inv_trans; subst.
    cbn; eexists; etrans.
    now rewrite EQ.
  Qed.

  Lemma step_ss_ret (x y : X) (R : rel _ _) :
    x = y ->
    ssbt R (Ret x : ctree E X) (Ret y).
  Proof.
    apply step_ss_ret_gen.
    reflexivity.
    typeclasses eauto.
  Qed.

(*|
The vis nodes are deterministic from the perspective of the labeled transition system,
stepping is hence symmetric and we can just recover the itree-style rule.
|*)
  Lemma step_ss_vis_gen (e : E X) (k k' : X -> ctree E Y) (R : rel _ _) :
    (Proper (equ eq ==> equ eq ==> impl) R) ->
    (forall x, R (k x) (k' x)) ->
    ss R (Vis e k) (Vis e k').
  Proof.
    intros PR EQs.
    intros ? ? TR; inv_trans; subst.
    cbn; eexists; etrans. rewrite EQ; auto.
  Qed.

  Lemma step_ss_vis (e : E X) (k k' : X -> ctree E Y) (R : rel _ _) :
    (forall x, sst R (k x) (k' x)) ->
    ssbt R (Vis e k) (Vis e k').
  Proof.
    intros * EQ.
    apply step_ss_vis_gen; auto.
    typeclasses eauto.
  Qed.

(*|
Same goes for visible tau nodes.
|*)
   Lemma step_ss_step_gen (t t' : ctree E X) (R : rel _ _) :
    (Proper (equ eq ==> equ eq ==> impl) R) ->
    (R t t') ->
    ss R (Step t) (Step t').
  Proof.
    intros PR EQs.
    intros ? ? TR; inv_trans; subst.
    cbn; eexists; etrans; rewrite EQ; auto.
  Qed.

  Lemma step_ss_step (t t' : ctree E X) (R : rel _ _) :
    (sst R t t') ->
    ssbt R (Step t) (Step t').
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

  Lemma step_ss_brS_gen n m (k : fin n -> ctree E X) (k' : fin m -> ctree E X) (R : rel _ _) :
    (Proper (equ eq ==> equ eq ==> impl) R) ->
    (forall x, exists y, R (k x) (k' y)) ->
    ss R (BrS n k) (BrS m k').
  Proof.
    intros PROP EQs ? ? TR; inv_trans; subst.
    destruct (EQs n0) as [x HR].
    eexists.
    etrans.
    rewrite EQ; eauto.
  Qed.

  Lemma step_ss_brS n m (k : fin n -> ctree E X) (k' : fin m -> ctree E X) (R : rel _ _) :
    (forall x, exists y, sst R (k x) (k' y)) ->
    ssbt R (BrS n k) (BrS m k').
  Proof.
    intros ? EQs.
    apply step_ss_brS_gen; auto.
    typeclasses eauto.
  Qed.

  Lemma step_ss_brS_id_gen n
    (k k' : fin n -> ctree E X) (R : rel _ _) :
    (Proper (equ eq ==> equ eq ==> impl) R) ->
    (forall x, R (k x) (k' x)) ->
    ss R (BrS n k) (BrS n k').
  Proof.
    intros PROP ? EQs.
    apply step_ss_brS_gen; auto.
    intros x; exists x; auto.
  Qed.

  Lemma step_ss_brS_id n
    (k k' : fin n -> ctree E X) (R : rel _ _) :
    (forall x, sst R (k x) (k' x)) ->
    ssbt R (BrS n k) (BrS n k').
  Proof.
    apply step_ss_brS_id_gen.
    typeclasses eauto.
  Qed.

(*|
For invisible nodes, the situation is different: we may kill them, but that execution
cannot act as going under the guard.
|*)
  Lemma step_ss_tauI_gen (t t' : ctree E X) (R : rel _ _) :
    ss R t t' ->
    ss R (Guard t) (Guard t').
  Proof.
    intros EQ.
    intros ? ? TR; inv_trans; subst.
    apply EQ in TR as [? ? ?].
    etrans.
  Qed.

  Lemma step_ss_tauI (t t' : ctree E X) (R : rel _ _) :
    ssbt R t t' ->
    ssbt R (Guard t) (Guard t').
  Proof.
    apply step_ss_tauI_gen.
  Qed.

  Lemma step_ss_brD_l_gen n
    (k : fin n -> ctree E X) (t' : ctree E X) (R : rel _ _) :
    (forall x, ss R (k x) t') ->
    ss R (BrD n k) t'.
  Proof.
    intros EQs.
    intros ? ? TR; inv_trans; subst.
    apply EQs in TR; destruct TR as [u' TR' EQ'].
    eauto.
  Qed.

  Lemma step_ss_brD_l n
    (k : fin n -> ctree E X) (t' : ctree E X) (R : rel _ _) :
    (forall x, ssbt R (k x) t') ->
    ssbt R (BrD n k) t'.
  Proof.
    apply step_ss_brD_l_gen.
  Qed.

  Lemma step_ss_brD_r_gen :
    forall (t : ctree E X) n (k : fin n -> ctree E X) x R,
    ss R t (k x) ->
    ss R t (BrD n k).
  Proof.
    cbn. intros.
    apply H in H0 as [? ? ?].
    exists x0; etrans.
  Qed.

  Lemma step_ss_brD_r :
    forall (t : ctree E X) n (k : fin n -> ctree E X) x R,
    ssbt R t (k x) ->
    ssbt R t (BrD n k).
  Proof.
    intros. eapply step_ss_brD_r_gen. apply H.
  Qed.

  Lemma step_ss_brD_gen n m
    (k : fin n -> ctree E X) (k' : fin m -> ctree E X) (R : rel _ _) :
    (forall x, exists y, ss R (k x) (k' y)) ->
    ss R (BrD n k) (BrD m k').
  Proof.
    intros EQs.
    apply step_ss_brD_l_gen.
    intros. destruct (EQs x) as [x' ?].
    now apply step_ss_brD_r_gen with (x := x').
  Qed.

  Lemma step_ss_brD n m
    (k : fin n -> ctree E X) (k' : fin m -> ctree E X) (R : rel _ _) :
    (forall x, exists y, ssbt R (k x) (k' y)) ->
    ssbt R (BrD n k) (BrD m k').
  Proof.
    apply step_ss_brD_gen.
  Qed.

  Lemma step_ss_brD_id_gen n
    (k k' : fin n -> ctree E X) (R : rel _ _) :
    (forall x, ss R (k x) (k' x)) ->
    ss R (BrD n k) (BrD n k').
  Proof.
    intros; apply step_ss_brD_gen.
    intros x; exists x; apply H.
  Qed.

  Lemma step_ss_brD_id n
    (k k' : fin n -> ctree E X) (R : rel _ _) :
    (forall x, ssbt R (k x) (k' x)) ->
    ssbt R (BrD n k) (BrD n k').
  Proof.
    apply step_ss_brD_id_gen.
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
    ssim (@spinS_nary E X n) (spinS_nary m).
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
  Lemma ssim_ret_inv (r1 r2 : X) :
    (Ret r1 : ctree E X) ≲ Ret r2 ->
    r1 = r2.
  Proof.
    intro.
    eplay. etrans. inv_trans. auto.
  Qed.

  Lemma ssim_vis_inv_type {X1 X2}
        (e1 : E X1) (e2 : E X2) (k1 : X1 -> ctree E X) (k2 : X2 -> ctree E X) (x : X1):
    Vis e1 k1 ≲ Vis e2 k2 ->
    X1 = X2.
  Proof.
    intros.
    eplay.
    inv TR; auto.
    Unshelve. auto.
  Qed.

  Lemma ssbt_eq_vis_inv {Y} (e1 e2 : E Y) (k1 k2 : Y -> ctree E X) (x : Y) R :
    ssbt R (Vis e1 k1) (Vis e2 k2) ->
    e1 = e2 /\ forall x, sst R (k1 x) (k2 x).
  Proof.
    intros.
    split.
    - cbn in H. edestruct H as [? ? ?].
      etrans. subst. now inv_trans.
    - cbn. intros. edestruct H as [? ? ?].
      etrans. subst. inv_trans. subst. apply H1.
    Unshelve. auto.
  Qed.

  Lemma t_gfp_bt : forall {X} `{CompleteLattice X} (b : mon X),
    weq (t b (gfp (bt b))) (gfp b).
  Proof.
    intros. cbn.
    rewrite <- enhanced_gfp. rewrite t_gfp.
    reflexivity.
  Qed.

  Lemma ssim_eq_vis_inv {Y} (e1 e2 : E Y) (k1 k2 : Y -> ctree E X) (x : Y) :
    Vis e1 k1 ≲ Vis e2 k2 ->
    e1 = e2 /\ forall x, k1 x ≲ k2 x.
  Proof.
    intros.
    (* Why doesn't apply work directly here? *)
    epose proof (proj1 (enhanced_gfp (@ss E X) _ _)). apply H0 in H. clear H0.
    step in H. apply ssbt_eq_vis_inv in H; auto.
    destruct H. split; auto.
    intro. subst. specialize (H0 x0).
    apply (proj1 (t_gfp_bt (@ss E X) _ _)) in H0. apply H0.
  Qed.

  Lemma ssim_brS_inv
        n1 n2 (k1 : fin n1 -> ctree E X) (k2 : fin n2 -> ctree E X) :
    BrS n1 k1 ≲ BrS n2 k2 ->
    (forall i1, exists i2, k1 i1 ≲ k2 i2).
  Proof.
    intros EQ i1.
    eplay.
    inv_trans.
    eexists; eauto.
  Qed.

  Lemma ss_brD_l_inv : forall n
    (t : ctree E X) (k : fin n -> ctree E X) R,
    ss R (BrD n k) t ->
    forall x, ss R (k x) t.
  Proof.
    cbn. intros.
    eapply trans_brD in H0; [| reflexivity].
    apply H in H0 as [? ? ?].
    exists x0; auto.
  Qed.

  Lemma ssim_brD_l_inv : forall n
    (t : ctree E X) (k : fin n -> ctree E X),
    BrD n k ≲ t ->
    forall x, k x ≲ t.
  Proof.
    intros. step. step in H. eapply ss_brD_l_inv. apply H.
  Qed.

  Lemma ssim_brD_r_inv : forall n
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
We prove a counter-example for a ctree with a binary br.
|*)

#[local] Definition t1 : ctree void1 unit :=
  Step (Ret tt).

#[local] Definition t2 : ctree void1 unit :=
  brS2 (Ret tt) (stuckD).

Lemma ssim_hsbisim_nequiv :
  ssim t1 t2 /\ ssim t2 t1 /\ ~ sbisim t1 t2.
Proof.
  unfold t1, t2. intuition.
  - step. apply step_ss_brS; auto.
    intros _. exists Fin.F1. reflexivity.
  - step. apply step_ss_brS; auto.
    intro. exists Fin.F1. destruct x.
    + reflexivity.
    + step. apply stuckD_ss.
  - step in H. cbn in H. destruct H as [_ ?].
    specialize (H tau stuckD). lapply H; [| etrans].
    intros. destruct H0 as [? ? ?].
    inv_trans. step in H1. cbn in H1. destruct H1 as [? _].
    specialize (H0 (val tt) stuckD). lapply H0. 2: { rewrite EQ. etrans. }
    intro. destruct H1 as [? ? ?].
    now apply stuckD_is_stuck in H1.
Qed.
