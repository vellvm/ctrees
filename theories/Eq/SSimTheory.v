From Coq Require Import Lia Basics Fin.

From Coinduction Require Import
     coinduction rel tactics.

From ITree Require Import Core.Subevent.

From CTree Require Import
     CTree
     Utils
     Eq.Equ
     Eq.SBisim
<<<<<<< HEAD
=======
     Eq.SSim0Theory
>>>>>>> master
     Eq.Shallow
     Eq.Trans.

From RelationAlgebra Require Export
     rel srel.

Set Implicit Arguments.

Import EquNotations.
Import SBisimNotations.

(* TODO: Decide where to set this *)
Arguments trans : simpl never.

#[local] Tactic Notation "step" := __step_sbisim || step.
#[local] Tactic Notation "coinduction" simple_intropattern(R) simple_intropattern(H) :=
  __coinduction_sbisim R H || coinduction R H.
#[local] Tactic Notation "step" "in" ident(H) := __step_in_sbisim H || step in H.

<<<<<<< HEAD
Lemma ssim_subrelation : forall {E C X} `{C0 -< C} (t t' : ctree E C X) L L',
  subrelation L L' -> ssim L t t' -> ssim L' t t'.
Proof.
  intros. revert t t' H1. coinduction R CH.
  intros. step in H1. simpl. intros.
  cbn in H1. apply H1 in H2 as (? & ? & ? & ? & ?).
  apply H0 in H4. exists x, x0. auto.
Qed.

Section ssim_theory.

  Context {E F C D : Type -> Type} {X Y : Type}.
  Context `{HasStuck : C0 -< C} `{HasStuck' : C0 -< D}.
  Notation ss1 := (@ss E E C C X X _ _).
  Notation sse := (ss1 eq).
  Notation ss := (@ss E F C D X Y).
  Notation ssim1  := (@ssim E E C C X X).
  Notation ssim  := (@ssim E F C D X Y).
  Notation sst L := (coinduction.t (ss L)).
  Notation sst1 L := (coinduction.t (ss1 L)).
  Notation ssbt L := (coinduction.bt (ss L)).
  Notation ssbt1 L := (coinduction.bt (ss1 L)).
  Notation ssT L := (coinduction.T (ss L)).
  Notation ssT1 L := (coinduction.T (ss1 L)).
=======
Section ssim_theory.

  Context {E : Type -> Type} {X : Type}.
  Notation ss := (@ss E X).
  Notation ssim := (@ssim E X).
  Notation sst := (coinduction.t ss).
  Notation ssbt := (coinduction.bt ss).
  Notation ssT := (coinduction.T ss).
>>>>>>> master

(*|
Various results on reflexivity and transitivity.
|*)
<<<<<<< HEAD
  Lemma refl_sst1: forall L, `(Reflexive L) -> const seq <= sst1 L.
  Proof.
    intros. apply leq_t.
    cbn. intros. unfold seq in H0. subst. eauto.
  Qed.

  #[global] Instance Reflexive_ss1: forall L R, `(Reflexive L) -> `(Reflexive R) -> Reflexive (ss1 L R).
  Proof.
    intros L R HL HR t l t' tt'.
    exists t', l. auto.
  Qed.

  #[global] Instance Reflexive_ssim1: Reflexive (ssim1 eq).
  Proof.
    cbn. coinduction R CH.
    apply Reflexive_ss1; auto.
  Qed.

  #[global] Instance Reflexive_ssim_flip: Reflexive (ssim1 (flip eq)).
  Proof.
    cbn. coinduction R CH.
    apply Reflexive_ss1; auto.
  Qed.

  Lemma square_sst1 : forall (L : relation label), `(Transitive L) -> square <= sst1 L.
  Proof.
    intros L HL.
    apply Coinduction.
    intros R x z [y xy yz] l x' xx'.
    destruct (xy _ _ xx') as (y' & ? & yy' & x'y' & ?).
    destruct (yz _ _ yy') as (z' & ? & zz' & y'z' & ?).
    exists z', x1. split; [ assumption |]. split; [| now transitivity x0 ].
    apply (f_Tf (ss1 L)).
    eexists; eauto.
  Qed.

  Lemma Transitive_ss: forall L R, `(Transitive L) -> `(Transitive R) -> Transitive (ss1 L R).
  Proof.
    intros L R HL HR x y z xy yz l x' xx'.
    destruct (xy _ _ xx') as (y' & ? & yy' & x'y' & ?).
    destruct (yz _ _ yy') as (z' & ? & zz' & y'z' & ?).
    exists z', x1. intuition. now transitivity y'. now transitivity x0.
  Qed.

  #[global] Instance PreOrder_sst1 L R `(PreOrder _ L) : PreOrder (sst1 L R).
  Proof. apply PreOrder_t. apply refl_sst1. apply H. apply square_sst1. apply H. Qed.

  Corollary PreOrder_ssim1 L: `(PreOrder L) -> PreOrder (ssim1 L).
  Proof. apply PreOrder_sst1. Qed.

  #[global] Instance PreOrder_sbt (L : relation _) R : `(PreOrder L) -> PreOrder (ssbt1 L R).
	Proof. intro. apply rel.PreOrder_bt. now apply refl_sst1. apply square_sst1. apply H. Qed.

  #[global] Instance PreOrder_sT L f R: `(PreOrder L) -> PreOrder ((T (ss1 L)) f R).
  Proof. intro. apply rel.PreOrder_T. now apply refl_sst1. apply square_sst1. apply H. Qed.

(*|
Aggressively providing instances for rewriting hopefully faster
[sbisim] under relevant [ss]-related contexts (consequence of the transitivity
of the companion).
|*)

  Lemma sbisim_clos_ss : forall L, sbisim_clos <= sst L.
  Proof.
    intro. apply Coinduction.
    cbn. intros.
    destruct H.
    step in Sbisimt. apply Sbisimt in H0 as (? & ? & ? & ? & ?). subst.
    apply HR in H as (? & ? & ? & ? & ?).
    step in Sbisimu. apply Sbisimu in H as (? & ? & ? & ? & ?). subst.
    exists x3, x4. split; [assumption|]. split; [|assumption].
    eapply (f_Tf (ss L)).
    econstructor; eauto.
  Qed.

  #[global] Instance sbisim_clos_ssim_goal L :
    Proper (sbisim ==> sbisim ==> flip impl) (ssim L).
  Proof.
    cbn.
    coinduction R CH. intros.
    symmetry in H0.
    do 2 red. cbn. intros.
    step in H. apply H in H2 as ?. destruct H3 as (? & ? & ? & ? & ?). subst.
    step in H1. apply H1 in H3 as (? & ? & ? & ? & ?).
    step in H0. apply H0 in H3 as (? & ? & ? & ? & ?). subst.
    exists x5, x6.
    split; [assumption |].
    split; [| assumption].
    symmetry in H7. eapply CH; eassumption.
  Qed.

  #[global] Instance sbisim_clos_ssim_ctx L :
    Proper (sbisim ==> sbisim ==> impl) (ssim L).
=======
  Lemma refl_sst: const seq <= sst.
  Proof.
    apply leq_t. cbn.
    intros. unfold seq in H. subst. eauto.
  Qed.

  Lemma square_sst : square <= sst.
  Proof.
    apply Coinduction.
    intros R x z [y xy yz].
    split.
    - intros l x' xx'.
      destruct (proj1 xy _ _ xx') as [y' yy' x'y'].
      destruct (proj1 yz _ _ yy') as [z' zz' y'z'].
      exists z'. assumption.
      apply (f_Tf ss).
      eexists; eauto.
    - intros l z' zz'.
      destruct (proj2 yz _ _ zz') as (l' & y' & yy').
      destruct (proj2 xy _ _ yy') as (l'' & x' & xx').
      eauto.
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
>>>>>>> master
  Proof.
    repeat intro. symmetry in H, H0. eapply sbisim_clos_ssim_goal; eauto.
  Qed.

<<<<<<< HEAD
  #[global] Instance sbisim_clos_sst_goal L RR :
    Proper (sbisim ==> sbisim ==> flip impl) (sst L RR).
  Proof.
    cbn; intros ? ? eq1 ? ? eq2 H.
    apply (ft_t (sbisim_clos_ss L)). cbn.
    econstructor; eauto.
    now rewrite eq2.
  Qed.

  #[global] Instance sbisim_clos_sst_ctx L RR :
    Proper (sbisim ==> sbisim ==> impl) (sst L RR).
=======
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
>>>>>>> master
  Proof.
    cbn; intros ? ? eq1 ? ? eq2 ?.
    rewrite <- eq1, <- eq2.
    auto.
  Qed.

<<<<<<< HEAD
  #[global] Instance sbisim_clos_ssT_goal L RR f :
    Proper (sbisim ==> sbisim ==> flip impl) (ssT L f RR).
  Proof.
    cbn; intros ? ? eq1 ? ? eq2 H.
    apply (fT_T (sbisim_clos_ss L)). cbn.
    econstructor; eauto.
    now rewrite eq2.
  Qed.

  #[global] Instance sbisim_clos_ssT_ctx L RR f :
    Proper (sbisim ==> sbisim ==> impl) (ssT L f RR).
=======
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
>>>>>>> master
  Proof.
    cbn; intros ? ? eq1 ? ? eq2 ?.
    rewrite <- eq1, <- eq2.
    auto.
  Qed.

(*|
Strong simulation up-to [equ] is valid
----------------------------------------
|*)
<<<<<<< HEAD
  Lemma equ_clos_ss {L} : equ_clos <= t (ss L).
  Proof.
    apply Coinduction.
    intros R t u EQ l t1 TR. cbn in EQ. inv EQ.
    cbn in *. rewrite Equt in TR.
    apply HR in TR.
    destruct TR as (? & ? & ? & ? & ?). subst.
    exists x. exists x0. intuition.
    rewrite <- Equu; auto.
    eapply (f_Tf (ss L)).
    econstructor; auto; auto.
  Qed.

  #[global] Instance equ_clos_sst_goal L RR :
    Proper (equ eq ==> equ eq ==> flip impl) (sst L RR).
  Proof.
    cbn; intros ? ? eq1 ? ? eq2 H.
    apply (ft_t equ_clos_ss); econstructor; [eauto | | symmetry; eauto]; assumption.
  Qed.

  #[global] Instance equ_clos_sst_ctx L RR :
    Proper (equ eq ==> equ eq ==> impl) (sst L RR).
  Proof.
    cbn; intros ? ? eq1 ? ? eq2 H.
    apply (ft_t equ_clos_ss); econstructor; [symmetry; eauto | | eauto]; assumption.
  Qed.

  #[global] Instance equ_ssbt_closed_goal {L r} :
    Proper (equ eq ==> equ eq ==> flip impl) (ssbt L r).
  Proof.
    cbn; repeat intro. do 5 red in H1.
    setoid_rewrite <- H in H1. setoid_rewrite <- H0 in H1.
    auto.
  Qed.

  #[global] Instance equ_ssbt_closed_ctx {L r} :
    Proper (equ eq ==> equ eq ==> impl) (ssbt L r).
  Proof.
    cbn; repeat intro. do 5 red in H1.
    setoid_rewrite H in H1. setoid_rewrite H0 in H1.
    auto.
  Qed.

  #[global] Instance equ_clos_ssT_goal L RR f :
    Proper (equ eq ==> equ eq ==> flip impl) (ssT L f RR).
  Proof.
    cbn; intros ? ? eq1 ? ? eq2 H.
    apply (fT_T equ_clos_ss); econstructor; [eauto | | symmetry; eauto]; assumption.
  Qed.

  #[global] Instance equ_clos_ssT_ctx L RR f :
    Proper (equ eq ==> equ eq ==> impl) (ssT L f RR).
  Proof.
    cbn; intros ? ? eq1 ? ? eq2 H.
    apply (fT_T equ_clos_ss); econstructor; [symmetry; eauto | | eauto]; assumption.
  Qed.

  #[global] Instance equ_clos_ssim_goal L :
    Proper (equ eq ==> equ eq ==> flip impl) (ssim L).
  Proof.
    cbn; intros ? ? eq1 ? ? eq2 H.
    apply (ft_t equ_clos_ss); econstructor; [eauto | | symmetry; eauto]; assumption.
  Qed.

  #[global] Instance equ_clos_ssim_ctx L :
    Proper (equ eq ==> equ eq ==> impl) (ssim L).
  Proof.
    cbn; intros ? ? eq1 ? ? eq2 H.
    apply (ft_t equ_clos_ss); econstructor; [symmetry; eauto | | eauto]; assumption.
  Qed.

  #[global] Instance equ_ss_closed_goal {L r} : Proper (equ eq ==> equ eq ==> flip impl) (ss L r).
  Proof.
    intros t t' tt' u u' uu'; cbn; intros.
    rewrite tt' in H0. apply H in H0 as (? & ? & ? & ? & ?).
    eexists; eexists; eauto. rewrite uu'. eauto.
  Qed.

  #[global] Instance equ_ss_closed_ctx {L r} : Proper (equ eq ==> equ eq ==> impl) (ss L r).
  Proof.
    intros t t' tt' u u' uu'; cbn; intros.
    rewrite <- tt' in H0. apply H in H0 as (? & ? & ? & ? & ?).
    eexists; eexists; eauto. rewrite <- uu'. eauto.
  Qed.

(*|
stuck ctrees can be simulated by anything.
|*)

  Lemma is_stuck_ss (R : rel _ _) (t : ctree E C X) (t' : ctree F D Y) L :
    is_stuck t -> ss L R t t'.
  Proof.
    repeat intro. now apply H in H0.
  Qed.

  Lemma is_stuck_ssim (t : ctree E C X) (t' : ctree F D Y) L :
    is_stuck t -> ssim L t t'.
  Proof.
    intros. step. now apply is_stuck_ss.
  Qed.

  Lemma stuckI_ss (R : rel _ _) (t : ctree F D Y) L : ss L R (stuckI : ctree E C X) t.
  Proof.
    repeat intro. now apply stuckI_is_stuck in H.
  Qed.

  Lemma stuckI_ssim (t : ctree F D Y) L : ssim L (stuckI : ctree E C X) t.
  Proof.
    intros. step. apply stuckI_ss.
  Qed.

  Lemma spinI_gen_ss Z (R : rel _ _) (t : ctree F D Y) (x : C Z) L : ss L R (CTree.spinI_gen x : ctree E C X) t.
  Proof.
    repeat intro. now apply spinI_gen_is_stuck in H.
  Qed.

  Lemma spinI_gen_ssim : forall {Z} (c: C Z) (t' : ctree F D Y) L,
      @CTree.spinI_gen E C X Z c (≲L) t'.
  Proof.
    intros. step. apply spinI_gen_ss.
=======
  Lemma equ_clos_sst : equ_clos <= sst.
  Proof.
    apply Coinduction.
    intros R t u EQ. inv EQ. cbn in *. split.
    - intros l t1 TR.
      rewrite Equt in TR.
      apply HR in TR as [].
      exists x.
      rewrite <- Equu; auto.
      eapply (f_Tf ss).
      econstructor; auto; auto.
    - intros l u1 TR.
      rewrite <- Equu in TR.
      setoid_rewrite Equt.
      now apply HR in TR.
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
    intros t t' tt' u u' uu'; cbn; split; intros.
    - rewrite tt' in H0. apply H in H0 as [? ? ?].
      eexists; eauto. rewrite uu'. eauto.
    - rewrite uu' in H0. apply H in H0. now setoid_rewrite tt'.
  Qed.

  #[global] Instance equ_ss_closed_ctx {r} : Proper (equ eq ==> equ eq ==> impl) (ss r).
  Proof.
    intros t t' tt' u u' uu'; cbn; split; intros.
    - rewrite <- tt' in H0. apply H in H0 as [? ? ?].
      eexists; eauto. rewrite <- uu'. eauto.
    - rewrite <- uu' in H0. apply H in H0. now setoid_rewrite <- tt'.
  Qed.

  Lemma is_stuck_ss : forall (t u : ctree E X) R, ss R t u -> is_stuck t <-> is_stuck u.
  Proof.
    split; intros; intros ? ? ?.
    - apply H in H1 as (? & ? & ?). now apply H0 in H1.
    - apply H in H1 as []. now apply H0 in H1.
  Qed.

  Lemma is_stuck_ssim : forall (t u : ctree E X), t ≲ u -> is_stuck t <-> is_stuck u.
  Proof.
    intros. step in H. eapply is_stuck_ss; eauto.
  Qed.

  Lemma ss_is_stuck : forall (t u : ctree E X) R, is_stuck t -> is_stuck u -> ss R t u.
  Proof.
    split; intros.
    - cbn. intros. now apply H in H1.
    - now apply H0 in H1.
  Qed.

  Lemma ssim_is_stuck : forall (t u : ctree E X), is_stuck t -> is_stuck u -> t ≲ u.
  Proof.
    intros. step. now apply ss_is_stuck.
>>>>>>> master
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

<<<<<<< HEAD
 Context {E F C D: Type -> Type} {X X' Y Y': Type}.
 Context `{HasStuck : C0 -< C} `{HasStuck' : C0 -< D}.
 Context (L : hrel (@label E) (@label F)).
=======
 Context {E : Type -> Type} {X Y : Type}.
>>>>>>> master

(*|
Specialization of [bind_ctx] to a function acting with [ssim] on the bound value,
and with the argument (pointwise) on the continuation.
|*)
<<<<<<< HEAD
  Program Definition bind_ctx_ssim : mon (rel (ctree E C X') (ctree F D Y')) :=
    {|body := fun R => @bind_ctx E F C D X Y X' Y' (ssim L) (pointwise (fun x y => L (val x) (val y)) R) |}.
  Next Obligation.
    intros ?? H. apply leq_bind_ctx. intros ?? H' ?? H''.
    apply in_bind_ctx. apply H'. intros t t' HS. apply H, H'', HS.
=======
  Program Definition bind_ctx_ssim : mon (rel (ctree E Y) (ctree E Y)) :=
    {|body := fun R => @bind_ctx E X X Y Y ssim
        (pointwise eq (fun t u => R t u /\ exists l t', trans l t t')) |}.
  Next Obligation.
    intros ?? H. apply leq_bind_ctx. intros ?? H' ?? H''.
    apply in_bind_ctx. apply H'. intros t t' HS. red in H''. split.
    - apply H, H'', HS.
    - subst. specialize (H'' t' t' eq_refl). apply H''.
>>>>>>> master
  Qed.

(*|
The resulting enhancing function gives a valid up-to technique
|*)
  Lemma bind_ctx_ssim_t :
<<<<<<< HEAD
    respects_val L ->
    bind_ctx_ssim <= sst L.
=======
    bind_ctx_ssim <= sst.
>>>>>>> master
  Proof.
    intro HL.
    apply Coinduction.
    intros R. apply (leq_bind_ctx _).
    intros t1 t2 tt k1 k2 kk.
<<<<<<< HEAD
    step in tt.
    intros l u STEP.
    apply trans_bind_inv in STEP as [(H & t' & STEP & EQ) | (v & STEPres & STEP)]; cbn in *.
    - apply tt in STEP as (u' & l' & STEP & EQ' & ?).
      eexists. exists l'. split.
      apply trans_bind_l; eauto.
      { intro Hl. destruct Hl. apply HL in H0 as [_ ?]. specialize (H0 (Is_val _)). auto. }
      split; auto.
      apply (fT_T equ_clos_ss).
      econstructor; [exact EQ | | reflexivity].
      apply (fTf_Tf (ss L)).
      apply in_bind_ctx; auto.
      intros ? ? ?.
      apply (b_T (ss L)).
      red in kk. red. red. now apply kk.
    - apply tt in STEPres as (u' & ? & STEPres & EQ' & ?).
      specialize (HL _ _ H) as [? _]. specialize (H0 (Is_val _)). destruct H0.
      pose proof (trans_val_invT STEPres). subst.
      pose proof (trans_val_inv STEPres) as EQ.
      rewrite EQ in STEPres.
      specialize (kk v x H).
      apply kk in STEP as (u'' & ? & STEP & EQ'' & ?); cbn in *.
      eexists. eexists. split.
      eapply trans_bind_r; eauto.
      split; auto.
      eapply (id_T (ss L)); auto.
=======
    step in tt. split.
    - intros l u STEP.
      red in kk.
      apply trans_bind_inv in STEP as [(H & t' & STEP & EQ) | (v & STEPres & STEP)]; cbn in *.
      + apply tt in STEP as [u' STEP EQ'].
        eexists.
        apply trans_bind_l; eauto.
        apply (fT_T equ_clos_sst).
        econstructor; [exact EQ | | reflexivity].
        apply (fTf_Tf ss).
        apply in_bind_ctx; auto.
        intros ? ? ->. split.
        apply (b_T ss).
        now apply kk.
        now eapply kk.
      + apply tt in STEPres as [u' STEPres EQ'].
        pose proof (trans_val_inv STEPres) as EQ.
        rewrite EQ in STEPres.
        specialize (kk v v eq_refl).
        apply kk in STEP as [u'' STEP EQ'']; cbn in *.
        eexists.
        eapply trans_bind_r; cbn in *; eauto.
        eapply (id_T ss); auto.
    - intros l u STEP. red in kk.
      apply trans_bind_inv_l in STEP as (l' & t2' & STEP).
      apply tt in STEP as (l'' & t1' & EQ').
      destruct l''.
      + eexists _, _. apply trans_bind_l; [| eauto ]. intro. inv H.
      + eexists _, _. apply trans_bind_l; [| eauto ]. intro. inv H.
      + apply trans_val_invT in EQ' as ?. subst.
        apply trans_val_inv in EQ' as ?. rewrite H in EQ'.
        specialize (kk v v eq_refl). destruct kk as [_ (? & ? & ?)].
        eapply trans_bind_r in H0; eauto.
>>>>>>> master
  Qed.

End bind.

<<<<<<< HEAD
Lemma bind_ctx_ssim_eq_t {E C T X} `{C0 -< C} :
    (bind_ctx_ssim (X := T) (Y := T) eq : mon (relation (ctree E C X))) <= sst eq.
Proof.
  apply bind_ctx_ssim_t. red. intros. now subst.
Qed.

=======
>>>>>>> master
Import CTree.
Import CTreeNotations.

(*|
Expliciting the reasoning rule provided by the up-to principles.
|*)
<<<<<<< HEAD
Lemma sst_clo_bind (E F C D: Type -> Type) `{C0 -< C} `{C0 -< D} (X X' Y Y' : Type) L :
  forall (t1 : ctree E C X) (t2 : ctree F D X') (k1 : X -> ctree E C Y) (k2 : X' -> ctree F D Y') RR,
		t1 (≲L) t2 ->
    respects_val L ->
    (forall x y, L (val x) (val y) -> (sst L RR) (k1 x) (k2 y)) ->
    sst L RR (t1 >>= k1) (t2 >>= k2)
.
Proof.
  intros.
  apply (ft_t (@bind_ctx_ssim_t E F C D X Y X' Y' _ _ L H2)).
  apply in_bind_ctx; auto.
Qed.

(*|
Specializing the congruence principle for [~]
|*)
Lemma ssim_clo_bind (E F C D: Type -> Type) `{C0 -< C} `{C0 -< D} (X X' Y Y' : Type) L :
  forall (t1 : ctree E C X) (t2 : ctree F D X') (k1 : X -> ctree E C Y) (k2 : X' -> ctree F D Y'),
		t1 (≲L) t2 ->
    respects_val L ->
    (forall x x', L (val x) (val x') -> k1 x (≲L) k2 x') ->
    t1 >>= k1 (≲L) t2 >>= k2
.
Proof.
  intros.
  apply (ft_t (@bind_ctx_ssim_t E F C D X Y X' Y' _ _ L H2)).
  apply in_bind_ctx; auto.
=======
Lemma sst_clo_bind (E : Type -> Type) (X Y : Type) :
  forall (t1 t2 : ctree E X) (k1 k2 : X -> ctree E Y) RR,
		t1 ≲ t2 ->
    (forall x, (sst RR) (k1 x) (k2 x)) ->
    (forall x, exists l t', trans l (k1 x) t') ->
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
    (forall x, exists l t', trans l (k1 x) t') ->
    t1 >>= k1 ≲ t2 >>= k2
.
Proof.
  intros * EQ EQs ?.
  apply (ft_t (@bind_ctx_ssim_t E X Y)).
  apply in_bind_ctx; auto.
  intros ? ? <-; auto.
  split. apply EQs. apply H.
>>>>>>> master
Qed.

(*|
And in particular, we can justify rewriting [≲] to the left of a [bind].
|*)
<<<<<<< HEAD
Lemma bind_ssim_cong_gen {E F C D X X' Y Y'} `{C0 -< C} `{C0 -< D} RR (L : rel _ _) :
  forall (t : ctree E C X) (t' : ctree F D X')
      (k : X -> ctree E C Y) (k' : X' -> ctree F D Y'),
    respects_val L ->
    ssim L t t' ->
    (forall x x', L (val x) (val x') -> sst L RR (k x) (k' x')) ->
    sst L RR (CTree.bind t k) (CTree.bind t' k').
Proof.
  intros; eapply sst_clo_bind; red in H2; eauto.
=======
Lemma bind_ssim_cong_gen {E X Y} RR :
  forall (t1 t2 : ctree E X) (k1 k2 : X -> ctree E Y),
  t1 ≲ t2 ->
  (forall x, sst RR (k1 x) (k2 x)) ->
  (forall x, exists l t', trans l (k1 x) t') ->
  sst RR (t1 >>= k1) (t2 >>= k2).
Proof.
  intros; eapply sst_clo_bind; eauto.
>>>>>>> master
Qed.

Ltac __upto_bind_ssim :=
  match goal with
<<<<<<< HEAD
    |- @ssim _ _ _ _ ?X ?X' _ _ _ (CTree.bind (T := ?T) _ _) (CTree.bind (T := ?T') _ _) =>
      apply ssim_clo_bind
  | |- body (t (@ss ?E ?E ?C ?C ?X ?X _ _ eq)) ?R (CTree.bind (T := ?T) _ _) (CTree.bind (T := ?T) _ _) =>
      apply (ft_t (@bind_ctx_ssim_eq_t E C T X _)), in_bind_ctx
  | |- body (bt (@ss ?E ?E ?C ?C ?X ?X _ _ eq)) ?R (CTree.bind (T := ?T) _ _) (CTree.bind (T := ?T) _ _) =>
      apply (fbt_bt (@bind_ctx_ssim_eq_t E C T X _)), in_bind_ctx
  end.
Ltac __upto_bind_eq_ssim :=
  __upto_bind_ssim; [reflexivity | intros ? _ _].

Ltac __play_ssim := step; cbn; intros ? ? ?TR.

Ltac __play_ssim_in H :=
  step in H;
  cbn in H; edestruct H as (? & ? & ?TR & ?EQ & ?);
  clear H; subst; [etrans |].

Ltac __eplay_ssim :=
  match goal with
  | h : @ssim ?E ?F ?C ?D ?X ?Y _ _ ?L _ _ |- _ =>
=======
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

Ltac __play_ssim := step; cbn; split; [intros ? ? ?TR | etrans].

Ltac __play_ssim_in H :=
  step in H;
  cbn in H; edestruct H as [[? ?TR ?EQ] _];
  clear H; [etrans |].

Ltac __eplay_ssim :=
  match goal with
  | h : @ssim ?E ?X _ _ |- _ =>
>>>>>>> master
      __play_ssim_in h
  end.

#[local] Tactic Notation "play" := __play_ssim.
#[local] Tactic Notation "play" "in" ident(H) := __play_ssim_in H.
#[local] Tactic Notation "eplay" := __eplay_ssim.

Section Proof_Rules.

<<<<<<< HEAD
  Context {E F C D : Type -> Type}.
  Context {HasStuck : C0 -< C} {HasStuck' : C0 -< D}.
  Context {HasTau : C1 -< C} {HasTau' : C1 -< D}.
  Context {X X' Y Y' : Type}.
  Context {L : rel (@label E) (@label F)}.

  Lemma step_ss_ret_gen (x : X) (y : Y) (R : rel _ _) :
    R stuckI stuckI ->
    (Proper (equ eq ==> equ eq ==> impl) R) ->
    L (val x) (val y) ->
    ss L R (Ret x : ctree E C X) (Ret y : ctree F D Y).
  Proof.
    intros Rstuck PROP Lval.
    cbn; intros ? ? TR; inv_trans; subst.
    cbn; eexists; eexists; intuition; etrans.
    now rewrite EQ.
  Qed.

  Lemma step_ss_ret (x : X) (y : Y) (R : rel _ _) :
    L (val x) (val y) ->
    ssbt L R (Ret x : ctree E C X) (Ret y : ctree F D Y).
  Proof.
    intros.
    apply step_ss_ret_gen.
    - step. intros. now apply stuckI_ss.
    - typeclasses eauto.
    - apply H.
=======
  Context {E : Type -> Type}.
  Context {X Y : Type}.

  Lemma step_ss_ret_gen (x y : X) (R : rel _ _) :
    R stuckD stuckD ->
    (Proper (equ eq ==> equ eq ==> impl) R) ->
    x = y ->
    ss R (Ret x : ctree E X) (Ret y).
  Proof.
    split; [| etrans ].
    apply step_ss0_ret_gen; auto.
  Qed.

  Lemma step_ss_ret (x y : X) (R : rel _ _) :
    x = y ->
    ssbt R (Ret x : ctree E X) (Ret y).
  Proof.
    apply step_ss_ret_gen.
    reflexivity.
    typeclasses eauto.
>>>>>>> master
  Qed.

(*|
The vis nodes are deterministic from the perspective of the labeled transition system,
stepping is hence symmetric and we can just recover the itree-style rule.
|*)
<<<<<<< HEAD
  Lemma step_ss_vis_gen (l : rel _ _) (e : E X) (k : X -> ctree E C Y) (k' : X -> ctree E D Y') (R : rel _ _) :
    (Proper (equ eq ==> equ eq ==> impl) R) ->
    (forall x, R (k x) (k' x)) ->
    (forall x, l (obs e x) (obs e x)) ->
    ss l R (Vis e k) (Vis e k').
  Proof.
    intros PR EQs.
    intros ? ? ? TR; inv_trans; subst.
    cbn; eexists; eexists; intuition. rewrite EQ; auto.
  Qed.

  Lemma step_ss_vis (l : rel _ _) (e : E X) (k : X -> ctree E C Y) (k' : X -> ctree E D Y') (R : rel _ _) :
    (forall x, sst l R (k x) (k' x)) ->
    (forall x, l (obs e x) (obs e x)) ->
    ssbt l R (Vis e k) (Vis e k').
=======
  Lemma step_ss_vis_gen (e : E X) (k k' : X -> ctree E Y) (R : rel _ _) :
    (Proper (equ eq ==> equ eq ==> impl) R) ->
    (forall x, R (k x) (k' x)) ->
    ss R (Vis e k) (Vis e k').
  Proof.
    split.
    - apply step_ss0_vis_gen; auto.
    - intros. inv_trans. etrans.
    Unshelve. auto.
  Qed.

  Lemma step_ss_vis (e : E X) (k k' : X -> ctree E Y) (R : rel _ _) :
    (forall x, sst R (k x) (k' x)) ->
    ssbt R (Vis e k) (Vis e k').
>>>>>>> master
  Proof.
    intros * EQ.
    apply step_ss_vis_gen; auto.
    typeclasses eauto.
  Qed.

(*|
Same goes for visible tau nodes.
|*)
<<<<<<< HEAD
   Lemma step_ss_tauV_gen (t : ctree E C X) (t' : ctree F D Y) (R : rel _ _) :
    (Proper (equ eq ==> equ eq ==> impl) R) ->
    (R t t') ->
    L tau tau ->
    ss L R (tauV t) (tauV t').
  Proof.
    intros PR EQs.
    intros ? ? ? TR; inv_trans; subst.
    cbn; eexists; eexists; intuition; rewrite EQ; auto.
  Qed.

  Lemma step_ss_tauV (t : ctree E C X) (t' : ctree F D Y) (R : rel _ _) :
    L tau tau ->
    (sst L R t t') ->
    ssbt L R (tauV t) (tauV t').
  Proof.
    intros. apply step_ss_tauV_gen; auto.
=======
   Lemma step_ss_step_gen (t t' : ctree E X) (R : rel _ _) :
    (Proper (equ eq ==> equ eq ==> impl) R) ->
    (R t t') ->
    ss R (Step t) (Step t').
  Proof.
    split.
    - apply step_ss0_step_gen; auto.
    - etrans.
  Qed.

  Lemma step_ss_step (t t' : ctree E X) (R : rel _ _) :
    (sst R t t') ->
    ssbt R (Step t) (Step t').
  Proof.
    intros. apply step_ss_step_gen; auto.
>>>>>>> master
    typeclasses eauto.
  Qed.

(*|
<<<<<<< HEAD
When matching visible choices one against another, in general we need to explain how
=======
When matching visible brs one against another, in general we need to explain how
>>>>>>> master
we map the branches from the left to the branches to the right.
A useful special case is the one where the arity coincide and we simply use the identity
in both directions. We can in this case have [n] rather than [2n] obligations.
|*)
<<<<<<< HEAD

  Lemma step_ss_choiceV_gen C' Z `{C0 -< C'} (c : C Y) (c' : C' Z)
    (k : Y -> ctree E C X) (k' : Z -> ctree F C' X') (R : rel _ _) :
    (Proper (equ eq ==> equ eq ==> impl) R) ->
    L tau tau ->
    (forall x, exists y, R (k x) (k' y)) ->
    ss L R (ChoiceV c k) (ChoiceV c' k').
  Proof.
    intros PROP ? EQs.
    intros ? ? TR; inv_trans; subst.
    destruct (EQs x) as [z HR].
    eexists. eexists. intuition.
    rewrite EQ; eauto.
  Qed.

  Lemma step_ss_choiceV Z (c : C Y) (c' : D Z)
    (k : Y -> ctree E C X) (k' : Z -> ctree F D X') (R : rel _ _) :
    L tau tau ->
    (forall x, exists y, sst L R (k x) (k' y)) ->
    ssbt L R (ChoiceV c k) (ChoiceV c' k').
  Proof.
    intros ? EQs.
    apply step_ss_choiceV_gen; auto.
    typeclasses eauto.
  Qed.

  Lemma step_ss_choiceV_id_gen (c : C Y)
    (k : Y -> ctree E C X) (k' : Y -> ctree F C X') (R : rel _ _) :
    (Proper (equ eq ==> equ eq ==> impl) R) ->
    L tau tau ->
    (forall x, R (k x) (k' x)) ->
    ss L R (ChoiceV c k) (ChoiceV c k').
  Proof.
    intros PROP ? EQs.
    apply step_ss_choiceV_gen; auto.
    intros x; exists x; auto.
  Qed.

  Lemma step_ss_choiceV_id (c : C Y)
    (k : Y -> ctree E C X) (k' : Y -> ctree F C X') (R : rel _ _) :
    L tau tau ->
    (forall x, sst L R (k x) (k' x)) ->
    ssbt L R (ChoiceV c k) (ChoiceV c k').
  Proof.
    apply step_ss_choiceV_id_gen.
=======
  Lemma step_ss_brS_gen n m (k : fin (S n) -> ctree E X) (k' : fin m -> ctree E X) (R : rel _ _) :
    (Proper (equ eq ==> equ eq ==> impl) R) ->
    (forall x, exists y, R (k x) (k' y)) ->
    ss R (BrS (S n) k) (BrS m k').
  Proof.
    split.
    - apply step_ss0_brS_gen; auto.
    - etrans.
    Unshelve. apply Fin.F1.
  Qed.

  Lemma step_ss_brS n m (k : fin (S n) -> ctree E X) (k' : fin m -> ctree E X) (R : rel _ _) :
    (forall x, exists y, sst R (k x) (k' y)) ->
    ssbt R (BrS (S n) k) (BrS m k').
  Proof.
    apply step_ss_brS_gen; auto.
    typeclasses eauto.
  Qed.

  Lemma step_ss_brS_id_gen n
    (k k' : fin n -> ctree E X) (R : rel _ _) :
    (Proper (equ eq ==> equ eq ==> impl) R) ->
    (forall x, R (k x) (k' x)) ->
    ss R (BrS n k) (BrS n k').
  Proof.
    intros; destruct n.
    - apply ss_is_stuck; rewrite br0_always_stuck; apply stuckS_is_stuck.
    - apply step_ss_brS_gen; auto.
      intros x; exists x; auto.
  Qed.

  Lemma step_ss_brS_id n
    (k k' : fin n -> ctree E X) (R : rel _ _) :
    (forall x, sst R (k x) (k' x)) ->
    ssbt R (BrS n k) (BrS n k').
  Proof.
    apply step_ss_brS_id_gen.
>>>>>>> master
    typeclasses eauto.
  Qed.

(*|
For invisible nodes, the situation is different: we may kill them, but that execution
cannot act as going under the guard.
|*)
<<<<<<< HEAD
  Lemma step_ss_tauI_gen (t : ctree E C X) (t' : ctree F D Y) (R : rel _ _) :
    ss L R t t' ->
    ss L R (tauI t) (tauI t').
  Proof.
    intros EQ.
    intros ? ? TR; inv_trans; subst.
    apply EQ in TR as (? & ? & ? & ? & ?).
    eexists; eexists; intuition; subst; [apply trans_tauI; eauto | eauto | eauto].
  Qed.

  Lemma step_ss_tauI (t : ctree E C X) (t' : ctree F D Y) (R : rel _ _) :
    ssbt L R t t' ->
    ssbt L R (tauI t) (tauI t').
  Proof.
    apply step_ss_tauI_gen.
  Qed.

  Lemma step_ss_choiceI_l_gen C' Z `{C0 -< C'} (c : C Z)
    (k : Z -> ctree E C X) (t' : ctree F C' Y) (R : rel _ _) :
    (forall x, ss L R (k x) t') ->
    ss L R (ChoiceI c k) t'.
  Proof.
    intros EQs.
    intros ? ? TR; inv_trans; subst.
    apply EQs in TR; destruct TR as (u' & ? & TR' & EQ' & ?).
    eexists. eexists. subst. intuition; eauto.
  Qed.

  Lemma step_ss_choiceI_l C' Z `{C0 -< C'} (c : C Z)
    (k : Z -> ctree E C X) (t' : ctree F C' Y) (R : rel _ _) :
    (forall x, ssbt L R (k x) t') ->
    ssbt L R (ChoiceI c k) t'.
  Proof.
    apply step_ss_choiceI_l_gen.
  Qed.

  Lemma step_ss_choiceI_r_gen C' Z `{C0 -< C'} :
    forall (t : ctree E C X) (c : C' Z) (k : Z -> ctree F C' Y) x R,
    ss L R t (k x) ->
    ss L R t (ChoiceI c k).
  Proof.
    simpl. intros.
    apply H0 in H1 as (? & ? & ? & ? & ?). subst.
    exists x0, x1. intuition. econstructor. eauto.
  Qed.

  Lemma step_ss_choiceI_r Z : forall (t : ctree E C X) (c : D Z) (k : Z -> ctree F D Y) x R,
    ssbt L R t (k x) ->
    ssbt L R t (ChoiceI c k).
  Proof.
    intros. eapply step_ss_choiceI_r_gen. apply H.
  Qed.

  Lemma step_ss_choiceI_gen C' Z Z' `{C0 -< C'} (c : C Z) (c' : C' Z')
    (k : Z -> ctree E C X) (k' : Z' -> ctree F C' Y) (R : rel _ _) :
    (forall x, exists y, ss L R (k x) (k' y)) ->
    ss L R (ChoiceI c k) (ChoiceI c' k').
  Proof.
    intros EQs.
    apply step_ss_choiceI_l_gen.
    intros. destruct (EQs x) as [x' ?].
    now apply step_ss_choiceI_r_gen with (x := x').
  Qed.

  Lemma step_ss_choiceI C' Z Z' `{C0 -< C'} (c : C Z) (c' : C' Z')
    (k : Z -> ctree E C X) (k' : Z' -> ctree F C' Y) (R : rel _ _) :
    (forall x, exists y, ssbt L R (k x) (k' y)) ->
    ssbt L R (ChoiceI c k) (ChoiceI c' k').
  Proof.
    apply step_ss_choiceI_gen.
  Qed.

  Lemma step_ss_choiceI_id_gen Z (c : C Z)
    (k : Z -> ctree E C X) (k' : Z -> ctree F C Y) (R : rel _ _) :
    (forall x, ss L R (k x) (k' x)) ->
    ss L R (ChoiceI c k) (ChoiceI c k').
  Proof.
    intros; apply step_ss_choiceI_gen.
    intros x; exists x; apply H.
  Qed.

  Lemma step_ss_choiceI_id Z (c : C Z) (k : Z -> ctree E C X) (k' : Z -> ctree F C Y) (R : rel _ _) :
    (forall x, ssbt L R (k x) (k' x)) ->
    ssbt L R (ChoiceI c k) (ChoiceI c k').
  Proof.
    apply step_ss_choiceI_id_gen.
=======
  Lemma step_ss_guard_gen (t t' : ctree E X) (R : rel _ _) :
    ss R t t' ->
    ss R (Guard t) (Guard t').
  Proof.
    split.
    - destruct H. apply step_ss0_tauI_gen. auto.
    - intros. inv_trans.
      apply H in H0 as (? & ? & ?).
      etrans.
  Qed.

  Lemma step_ss_guard (t t' : ctree E X) (R : rel _ _) :
    ssbt R t t' ->
    ssbt R (Guard t) (Guard t').
  Proof.
    apply step_ss_guard_gen.
  Qed.

  Lemma step_ss_brD_l_gen n
    (k : fin (S n) -> ctree E X) (t' : ctree E X) (R : rel _ _) :
    (forall x, ss R (k x) t') ->
    ss R (BrD (S n) k) t'.
  Proof.
    intros EQs. split.
    - apply step_ss0_brD_l_gen. intro. now destruct (EQs x).
    - intros. apply (EQs Fin.F1) in H as (? & ? & ?).
      etrans.
  Qed.

  Lemma step_ss_brD_l n
    (k : fin (S n) -> ctree E X) (t' : ctree E X) (R : rel _ _) :
    (forall x, ssbt R (k x) t') ->
    ssbt R (BrD (S n) k) t'.
  Proof.
    apply step_ss_brD_l_gen.
  Qed.

  Lemma step_ss_brD_r_gen :
    forall (t : ctree E X) n (k : fin n -> ctree E X) x R,
    (exists l t', trans l t t') ->
    ss R t (k x) ->
    ss R t (BrD n k).
  Proof.
    cbn. split; intros.
    - apply H0 in H1 as [? ? ?].
      exists x0; etrans.
    - apply H.
  Qed.

  Lemma step_ss_brD_r :
    forall (t : ctree E X) n (k : fin n -> ctree E X) x R,
    (exists l t', trans l t t') ->
    ssbt R t (k x) ->
    ssbt R t (BrD n k).
  Proof.
    intros. eapply step_ss_brD_r_gen. apply H. apply H0.
  Qed.

  Lemma step_ss_brD_gen n m
    (k : fin n -> ctree E X) (k' : fin m -> ctree E X) x (R : rel _ _) :
    (exists l' t', trans l' (k x) t') ->
    (forall x, exists y, ss R (k x) (k' y)) ->
    ss R (BrD n k) (BrD m k').
  Proof.
    intros ? EQs. split; intros.
    - apply step_ss0_brD_gen. intros.
      destruct (EQs x0). destruct H0. eauto.
    - destruct H as (? & ? & ?). etrans.
  Qed.

  Lemma step_ss_brD n m
    (k : fin n -> ctree E X) (k' : fin m -> ctree E X) x (R : rel _ _) :
    (exists l' t', trans l' (k x) t') ->
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
    destruct n; intros.
    - apply ss_is_stuck; rewrite br0_always_stuck; apply stuckD_is_stuck.
    - split; cbn; intros.
      + inv_trans. apply H in TR as []. etrans.
      + inv_trans. apply H in TR as (? & ? & ?). etrans.
  Qed.

  Lemma step_ss_brD_id n
    (k k' : fin n -> ctree E X) (R : rel _ _) :
    (forall x, ssbt R (k x) (k' x)) ->
    ssbt R (BrD n k) (BrD n k').
  Proof.
    apply step_ss_brD_id_gen.
>>>>>>> master
  Qed.

End Proof_Rules.

Section WithParams.

<<<<<<< HEAD
  Context {E F C D : Type -> Type}.
  Context {HasStuck : C0 -< C}.
  Context {HasTau : C1 -< C}.
  Context {HasStuck' : C0 -< D}.
  Context {HasTau' : C1 -< D}.
  Context (L : rel (@label E) (@label F)).
=======
  Context {E : Type -> Type}.
  Context {X : Type}.
>>>>>>> master

(*|
Note that with visible schedules, nary-spins are equivalent only
if neither are empty, or if both are empty: they match each other's
tau challenge infinitely often.
With invisible schedules, they are always equivalent: neither of them
produce any challenge for the other.
|*)
<<<<<<< HEAD
  Lemma spinV_gen_nonempty : forall {Z Z' X Y} (c: C X) (c': D Y) (x: X) (y: Y) (L : rel _ _),
    L tau tau ->
    ssim L (@CTree.spinV_gen E C Z X c) (@CTree.spinV_gen F D Z' Y c').
  Proof.
    intros.
    red. coinduction R CH.
    intros l t' TR.
    rewrite ctree_eta in TR; cbn in TR.
    apply trans_choiceV_inv in TR as (_ & EQ & ->).
    eexists. eexists.
    rewrite ctree_eta; cbn.
    split; [econstructor |]. exact y.
    reflexivity.
    rewrite EQ; auto.
=======
  Lemma spinS_nary_n_m : forall n m,
    n > 0 -> m > 0 ->
    ssim (@spinS_nary E X n) (spinS_nary m).
  Proof.
    intros.
    red. coinduction R CH.
    setoid_rewrite ctree_eta. cbn.
    destruct n, m; try lia.
    eapply step_ss_brS.
    intros _. exists Fin.F1.
    apply CH.
>>>>>>> master
  Qed.

(*|
Inversion principles
--------------------
|*)
<<<<<<< HEAD
  Lemma ssim_ret_inv X Y (r1 : X) (r2 : Y) :
    (Ret r1 : ctree E C X) (≲L) (Ret r2 : ctree F D Y) ->
    L (val r1) (val r2).
  Proof.
    intro.
    eplay. inv_trans. now subst.
  Qed.

  Lemma ssim_vis_inv_type {X X1 X2}
        (e1 : E X1) (e2 : E X2) (k1 : X1 -> ctree E C X) (k2 : X2 -> ctree E C X) (x : X1):
=======
  Lemma ssim_ret_inv (r1 r2 : X) :
    (Ret r1 : ctree E X) ≲ Ret r2 ->
    r1 = r2.
  Proof.
    intro.
    eplay. etrans. inv_trans. auto.
  Qed.

  Lemma ssim_vis_inv_type {X1 X2}
        (e1 : E X1) (e2 : E X2) (k1 : X1 -> ctree E X) (k2 : X2 -> ctree E X) (x : X1):
>>>>>>> master
    Vis e1 k1 ≲ Vis e2 k2 ->
    X1 = X2.
  Proof.
    intros.
    eplay.
    inv TR; auto.
    Unshelve. auto.
  Qed.

<<<<<<< HEAD
  Lemma ssbt_eq_vis_inv {X Y} (e1 e2 : E Y) (k1 k2 : Y -> ctree E C X) (x : Y) R :
    ss eq (t (ss eq) R) (Vis e1 k1) (Vis e2 k2) ->
    e1 = e2 /\ forall x, sst eq R (k1 x) (k2 x).
  Proof.
    intros.
    split.
    - cbn in H. edestruct H as (? & ? & ? & ? & ?).
      etrans. subst. now inv_trans.
    - cbn. intros. edestruct H as (? & ? & ? & ? & ?).
=======
  Lemma ssbt_eq_vis_inv {Y} (e1 e2 : E Y) (k1 k2 : Y -> ctree E X) (x : Y) R :
    ssbt R (Vis e1 k1) (Vis e2 k2) ->
    e1 = e2 /\ forall x, sst R (k1 x) (k2 x).
  Proof.
    intros. split.
    - cbn in H. edestruct H as [[? ? ?] _].
      etrans. subst. now inv_trans.
    - cbn. intros. edestruct H as [[? ? ?] _].
>>>>>>> master
      etrans. subst. inv_trans. subst. apply H1.
    Unshelve. auto.
  Qed.

<<<<<<< HEAD
  Lemma t_gfp_bt : forall {X} `{CompleteLattice X} (b : mon X),
    weq (t b (gfp (bt b))) (gfp b).
  Proof.
    intros. cbn.
    rewrite <- enhanced_gfp. rewrite t_gfp.
    reflexivity.
  Qed.

  Lemma ssim_eq_vis_inv {X Y} (e1 e2 : E Y) (k1 k2 : Y -> ctree E C X) (x : Y) :
=======
  Lemma ssim_eq_vis_inv {Y} (e1 e2 : E Y) (k1 k2 : Y -> ctree E X) (x : Y) :
>>>>>>> master
    Vis e1 k1 ≲ Vis e2 k2 ->
    e1 = e2 /\ forall x, k1 x ≲ k2 x.
  Proof.
    intros.
    (* Why doesn't apply work directly here? *)
<<<<<<< HEAD
    epose proof (proj1 (enhanced_gfp (@ss E E C C X X _ _ eq) _ _)). apply H0 in H. clear H0.
    step in H. apply ssbt_eq_vis_inv in H; auto.
    destruct H. split; auto.
    intro. subst. specialize (H0 x0).
    apply (proj1 (t_gfp_bt (@ss E E C C X X _ _ eq) _ _)) in H0. apply H0.
  Qed.

  Lemma ssim_choiceV_inv {X Y Z Z'}
        c1 c2 (k1 : X -> ctree E C Z) (k2 : Y -> ctree F D Z') :
    ChoiceV c1 k1 (≲L) ChoiceV c2 k2 ->
    (forall i1, exists i2, k1 i1 (≲L) k2 i2).
=======
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
>>>>>>> master
  Proof.
    intros EQ i1.
    eplay.
    inv_trans.
    eexists; eauto.
  Qed.

<<<<<<< HEAD
  Lemma ss_choiceI_l_inv : forall {X Y Z}
    (t : ctree E C X) (c : D Y) (k : Y -> ctree F D Z) L R,
    ss L R (ChoiceI c k) t ->
    forall x, ss L R (k x) t.
  Proof.
    cbn. intros.
    eapply trans_choiceI in H0; [| reflexivity].
    apply H in H0 as (? & ? & ? & ? & ?).
    exists x0, x1. auto.
  Qed.

  Lemma ssim_choiceI_l_inv : forall {X Y Z}
    (t : ctree E C X) (c : D Y) (k : Y -> ctree F D Z) L,
    ChoiceI c k (≲L) t ->
    forall x, k x (≲L) t.
  Proof.
    intros. step. step in H. eapply ss_choiceI_l_inv. apply H.
  Qed.

  (* This one isn't very convenient... *)
  Lemma ssim_choiceI_r_inv : forall {X Y Z}
    (t : ctree E C X) (c : D Y) (k : Y -> ctree F D Z) L,
    ssim L t (ChoiceI c k) ->
    forall l t', trans l t t' ->
    exists x t'' l', trans l' (k x) t'' /\ ssim L t' t'' /\ L l l'.
  Proof.
    cbn. intros. step in H. apply H in H0 as (? & ? & ? & ? & ?). subst. inv_trans.
    exists x1, x, x0. auto.
  Qed.

End WithParams.

(*|
A strong bisimulation gives two strong simulations,
but two strong simulations do not always give a strong bisimulation.
This property is true if we only allow choices with 0 or 1 branch,
but we prove a counter-example for a ctree with a binary choice.
|*)

Lemma ss_hsb : forall {E F C D X Y} `{C0 -< C} `{C0 -< D} L RR
  (t : ctree E C X) (t' : ctree F D Y),
  ss L RR t t' ->
  ss (flip L) (flip RR) t' t ->
  hsb L RR t t'.
Proof.
  split; auto.
Qed.

Lemma ctree_C01_trans_det : forall {E X} l (t t' t'' : ctree E C01 X),
  trans l t t' -> trans l t t'' -> t' ≅ t''.
Proof.
  intros. do 3 red in H.
  rewrite ctree_eta in H0.
  genobs t ot. genobs t' ot'. rewrite ctree_eta, <- Heqot'.
  clear t t' Heqot Heqot'. revert t'' H0.
  dependent induction H; intros; inv_trans.
  - eapply IHtrans_; eauto.
    rewrite <- ctree_eta.
    destruct c, c, x, x0. assumption.
  - rewrite <- ctree_eta. destruct c, c, x, x0. now rewrite <- H, EQ.
  - subst. rewrite <- ctree_eta. now rewrite <- H, EQ.
  - rewrite EQ. apply choice0_always_stuck.
Qed.

Lemma ssim_hsbisim_equiv_gen : forall {E F X Y} (L : rel _ _) (t : ctree E C01 X) (t' : ctree F C01 Y),
  (forall x x' y, L x y -> L x' y -> x = x') ->
  (forall x y y', L x y -> L x y' -> y = y') ->
  ssim L t t' -> ssim (flip L) t' t -> hsbisim L t t'.
Proof.
  intros until 2. revert t t'.
  coinduction R CH. red. red. cbn. split; intros.
  - step in H1. cbn in H1.
    apply H1 in H3 as H3'. destruct H3' as (? & ? & ? & ? & ?).
    exists x, x0. intuition. apply CH.
    + apply H5.
    + step in H2. cbn in H2. apply H2 in H4 as (? & ? & ? & ? & ?).
      replace x2 with l in H4.
      2: { eapply H; eauto. }
      assert (t'0 ≅ x1) by (eapply ctree_C01_trans_det; eauto).
      now rewrite H9.
  - step in H2. cbn in H2.
    apply H2 in H3 as H3'. destruct H3' as (? & ? & ? & ? & ?).
    exists x, x0. intuition. apply CH.
    + step in H1. cbn in H1. apply H1 in H4 as (? & ? & ? & ? & ?).
      replace x2 with l in H4.
      2: { eapply H0; eauto. }
      assert (t'0 ≅ x1) by (eapply ctree_C01_trans_det; eauto).
      now rewrite H9.
    + apply H5.
Qed.

Lemma ssim_hsbisim_equiv : forall {E X} (t t' : ctree E C01 X),
  ssim eq t t' -> ssim eq t' t -> hsbisim eq t t'.
Proof.
  intros. apply ssim_hsbisim_equiv_gen; intros.
  - now subst.
  - now subst.
  - apply H.
  - apply ssim_subrelation with (L := eq); auto.
    red. intros. subst. reflexivity.
Qed.

#[local] Definition t1 : ctree void1 (C01 +' C2) unit :=
  tauV (Ret tt).

#[local] Definition t2 : ctree void1 (C01 +' C2) unit :=
  chooseV2 (Ret tt) (stuckI).

Lemma ssim_hsbisim_nequiv :
  ssim eq t1 t2 /\ ssim (flip eq) t2 t1 /\ ~ hsbisim eq t1 t2.
Proof.
  unfold t1, t2. intuition.
  - step. apply step_ss_choiceV; auto.
    intros _. exists true. reflexivity.
  - step. apply step_ss_choiceV; auto.
    intro. exists tt. destruct x.
    + reflexivity.
    + step. apply stuckI_ss.
  - step in H. cbn in H. destruct H as [_ ?].
    specialize (H tau stuckI). lapply H; [| etrans].
    intros. destruct H0 as (? & ? & ? & ? & ?). subst.
    inv_trans. step in H1. cbn in H1. destruct H1 as [? _].
    specialize (H0 (val tt) stuckI). lapply H0. 2: { rewrite EQ. etrans. }
    intro. destruct H1 as (? & ? & ? & ? & ?). subst.
    now apply stuckI_is_stuck in H1.
Qed.
=======
  Lemma ss_brD_l_inv : forall n
    (t : ctree E X) (k : fin n -> ctree E X) x R,
    ss R (BrD n k) t ->
    (exists l t', trans l (k x) t') ->
    ss R (k x) t.
  Proof.
    split.
    - apply ss0_brD_l_inv. now apply H.
    - intros. apply H0.
  Qed.

  Lemma ssim_brD_l_inv : forall n
    (t : ctree E X) (k : fin n -> ctree E X) x,
    BrD n k ≲ t ->
    (exists l t', trans l (k x) t') ->
    k x ≲ t.
  Proof.
    intros. step. step in H. eapply ss_brD_l_inv; auto.
  Qed.

  (* This one isn't very convenient... *)
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
>>>>>>> master
