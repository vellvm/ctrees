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

(* TODO: Decide where to set this *)
Arguments trans : simpl never.

#[local] Tactic Notation "step" := __step_sbisim || step.
#[local] Tactic Notation "coinduction" simple_intropattern(R) simple_intropattern(H) :=
  __coinduction_sbisim R H || coinduction R H.
#[local] Tactic Notation "step" "in" ident(H) := __step_in_sbisim H || step in H.

Section ssim_theory.

  Context {E F C D : Type -> Type} {X Y : Type}.
  Context `{HasStuck : C0 -< C} `{HasStuck' : C0 -< D}.
  Notation ss1 := (@ss E E C C X X _ _).
  Notation sse := (ss1 eq).
  Notation ss := (@ss E F C D X Y).
  Notation ssim1  := (@ssim E E C C X X).
  Notation ssim  := (@ssim E F C D X Y).
  Notation sst L := (coinduction.t (ss L)).
  Notation ssbt L := (coinduction.bt (ss L)).
  Notation ssT L := (coinduction.T (ss L)).

  Lemma Reflexive_ss: forall L R, Reflexive L -> Reflexive R -> Reflexive (ss1 L R).
  Proof.
    intros L R HL HR t l t' tt'.
    exists t', l. auto.
  Qed.

  #[global] Instance Reflexive_ssim: Reflexive (ssim1 eq).
  Proof.
    cbn. coinduction R CH.
    apply Reflexive_ss; auto.
  Qed.

  #[global] Instance Reflexive_ssim_flip: Reflexive (ssim1 (flip eq)).
  Proof.
    cbn. coinduction R CH.
    apply Reflexive_ss; auto.
  Qed.

  Lemma Transitive_ss: forall R, Transitive R -> Transitive (sse R).
  Proof.
    intros R H x y z xy yz l x' xx'.
    destruct (xy _ _ xx') as (y' & ? & yy' & x'y' & <-).
    destruct (yz _ _ yy') as (z' & ? & zz' & y'z' & <-).
    exists z', l. intuition. now transitivity y'.
  Qed.

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

(*|
Aggressively providing instances for rewriting [equ] under all [ss]-related
contexts.
|*)
  #[global] Instance equ_clos_ss_goal L RR :
    Proper (equ eq ==> equ eq ==> flip impl) (sst L RR).
  Proof.
    cbn; intros ? ? eq1 ? ? eq2 H.
    apply (ft_t equ_clos_ss); econstructor; [eauto | | symmetry; eauto]; assumption.
  Qed.

  #[global] Instance equ_clos_ss_ctx L RR :
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
stuckI and spinI can be simulated by any ctree.
|*)

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

 Context {E F C D: Type -> Type} {X X' Y Y': Type}.
 Context `{HasStuck : C0 -< C} `{HasStuck' : C0 -< D}.
 Context (L : hrel (@label E) (@label F)).

(*|
Specialization of [bind_ctx] to a function acting with [ssim] on the bound value,
and with the argument (pointwise) on the continuation.
|*)
  Program Definition bind_ctx_ssim : mon (rel (ctree E C X') (ctree F D Y')) :=
    {|body := fun R => @bind_ctx E F C D X Y X' Y' (ssim L) (pointwise (fun x y => L (val x) (val y)) R) |}.
  Next Obligation.
    intros ?? H. apply leq_bind_ctx. intros ?? H' ?? H''.
    apply in_bind_ctx. apply H'. intros t t' HS. apply H, H'', HS.
  Qed.

(*|
The resulting enhancing function gives a valid up-to technique
|*)
  Lemma bind_ctx_ssim_t :
    (forall l l', L l l' -> is_val l <-> is_val l') ->
    bind_ctx_ssim <= sst L.
  Proof.
    intro HL.
    apply Coinduction.
    intros R. apply (leq_bind_ctx _).
    intros t1 t2 tt k1 k2 kk.
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
  Qed.

End bind.

Import CTree.
Import CTreeNotations.

(*|
Expliciting the reasoning rule provided by the up-to principles.
|*)
Lemma sst_clo_bind (E F C D: Type -> Type) `{C0 -< C} `{C0 -< D} (X X' Y Y' : Type) L :
  forall (t1 : ctree E C X) (t2 : ctree F D X') (k1 : X -> ctree E C Y) (k2 : X' -> ctree F D Y') RR,
		t1 (≲L) t2 ->
    (forall l l', L l l' -> is_val l <-> is_val l') ->
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
    (forall l l', L l l' -> is_val l <-> is_val l') ->
    (forall x x', L (val x) (val x') -> k1 x (≲L) k2 x') ->
    t1 >>= k1 (≲L) t2 >>= k2
.
Proof.
  intros.
  apply (ft_t (@bind_ctx_ssim_t E F C D X Y X' Y' _ _ L H2)).
  apply in_bind_ctx; auto.
Qed.

(*|
And in particular, we can justify rewriting [≲] to the left of a [bind].
|*)
Lemma bind_ssim_cong_gen {E F C D X X' Y Y'} `{C0 -< C} `{C0 -< D} RR (L : rel _ _) :
  forall (t : ctree E C X) (t' : ctree F D X')
      (k : X -> ctree E C Y) (k' : X' -> ctree F D Y'),
    (forall l l', L l l' -> is_val l <-> is_val l') ->
    ssim L t t' ->
    (forall x x', L (val x) (val x') -> sst L RR (k x) (k' x')) ->
    sst L RR (CTree.bind t k) (CTree.bind t' k').
Proof.
  intros; eapply sst_clo_bind; red in H2; eauto.
Qed.

Ltac __upto_bind_ssim :=
  match goal with
    |- @ssim _ _ _ _ ?X ?X' _ _ _ (CTree.bind (T := ?T) _ _) (CTree.bind (T := ?T') _ _) =>
      apply ssim_clo_bind
  | |- body (t (@ss ?E ?E ?C ?C ?X ?X _ _ eq)) ?R (CTree.bind (T := ?T) _ _) (CTree.bind (T := ?T) _ _) =>
      apply (ft_t (@bind_ctx_ssim_eq_t E C T X _)), in_bind_ctx
  | |- body (bt (@ss ?E ?E ?C ?C ?X ?X _ _ eq)) ?R (CTree.bind (T := ?T) _ _) (CTree.bind (T := ?T) _ _) =>
      apply (fbt_bt (@bind_ctx_ssim_eq_t E C T X _)), in_bind_ctx
  end.
Ltac __upto_bind_eq_ssim :=
  __upto_bind_ssim; [reflexivity | intros ? _ _].

Ltac __play_ssim := step; cbn; intros ? ? ?TR ? ?.

Ltac __play_ssim_in H :=
  step in H;
  cbn in H; edestruct H as (? & ? & ?TR & ?EQ & ?);
  clear H; subst; [etrans |].

Ltac __eplay_ssim :=
  match goal with
  | h : @ssim ?E ?F ?C ?D ?X ?Y _ _ ?L _ _ |- _ =>
      __play_ssim_in h
  end.

#[local] Tactic Notation "play" := __play_ssim.
#[local] Tactic Notation "play" "in" ident(H) := __play_ssim_in H.
#[local] Tactic Notation "eplay" := __eplay_ssim.

Section Proof_Rules.

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
    R stuckI stuckI ->
    L (val x) (val y) ->
    ssbt L R (Ret x : ctree E C X) (Ret y : ctree F D Y).
  Proof.
    intros.
    apply step_ss_ret_gen.
    - step. intros. now apply stuckI_ss.
    - typeclasses eauto.
    - apply H0.
  Qed.

(*|
The vis nodes are deterministic from the perspective of the labeled transition system,
stepping is hence symmetric and we can just recover the itree-style rule.
|*)
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
  Proof.
    intros * EQ.
    apply step_ss_vis_gen; auto.
    typeclasses eauto.
  Qed.

(*|
Same goes for visible tau nodes.
|*)
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
    typeclasses eauto.
  Qed.

(*|
When matching visible choices one against another, in general we need to explain how
we map the branches from the left to the branches to the right.
A useful special case is the one where the arity coincide and we simply use the identity
in both directions. We can in this case have [n] rather than [2n] obligations.
|*)

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
    typeclasses eauto.
  Qed.

(*|
For invisible nodes, the situation is different: we may kill them, but that execution
cannot act as going under the guard.
|*)
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

  Lemma step_ss_choiceI_gen' C' Z `{C0 -< C'} (c : C Z)
    (k : Z -> ctree E C X) (t' : ctree F C' Y) (R : rel _ _) :
    (forall x, ss L R (k x) t') ->
    ss L R (ChoiceI c k) t'.
  Proof.
    intros EQs.
    intros ? ? TR; inv_trans; subst.
    apply EQs in TR; destruct TR as (u' & ? & TR' & EQ' & ?).
    eexists. eexists. subst. intuition; eauto.
  Qed.

  Lemma step_ss_choiceI_gen C' Z Z' `{C0 -< C'} (c : C Z) (c' : C' Z')
    (k : Z -> ctree E C X) (k' : Z' -> ctree F C' Y) (R : rel _ _) :
    (forall x, exists y, ss L R (k x) (k' y)) ->
    ss L R (ChoiceI c k) (ChoiceI c' k').
  Proof.
    intros EQs.
    apply step_ss_choiceI_gen'.
    intros z l t' TR.
    destruct (EQs z) as [x FF]. cbn in FF.
    apply FF in TR; destruct TR as (u' & ? & TR' & EQ' & ?).
    eexists. eexists. subst. intuition; eauto.
    econstructor. apply TR'.
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
  Qed.

End Proof_Rules.

Section WithParams.

  Context {E F C D : Type -> Type}.
  Context {HasStuck : C0 -< C}.
  Context {HasTau : C1 -< C}.
  Context {HasStuck' : C0 -< D}.
  Context {HasTau' : C1 -< D}.
  Context (L : rel (@label E) (@label F)).

(*|
Note that with visible schedules, nary-spins are equivalent only
if neither are empty, or if both are empty: they match each other's
tau challenge infinitely often.
With invisible schedules, they are always equivalent: neither of them
produce any challenge for the other.
|*)
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
  Qed.

(*|
Inversion principles
--------------------
|*)
  Lemma ssim_ret_inv X Y (r1 : X) (r2 : Y) :
    (Ret r1 : ctree E C X) (≲L) (Ret r2 : ctree F D Y) ->
    L (val r1) (val r2).
  Proof.
    intro.
    eplay. inv_trans. now subst.
  Qed.

  Lemma sbisim_ChoiceV_inv {X Y Z Z'}
        c1 c2 (k1 : X -> ctree E C Z) (k2 : Y -> ctree F D Z') :
    ChoiceV c1 k1 (≲L) ChoiceV c2 k2 ->
    (forall i1, exists i2, k1 i1 (≲L) k2 i2).
  Proof.
    intros EQ i1.
    eplay.
    inv_trans.
    eexists; eauto.
  Qed.

End WithParams.

Lemma ssim_subrelation : forall {E C X} `{C0 -< C} (t t' : ctree E C X) L L',
  subrelation L L' -> ssim L t t' -> ssim L' t t'.
Proof.
  intros. revert t t' H1. coinduction R CH.
  intros. step in H1. simpl. intros.
  cbn in H1. apply H1 in H2 as (? & ? & ? & ? & ?).
  apply H0 in H4. exists x, x0. auto.
Qed.

(*|
A strong bisimulation gives two strong simulations,
but two strong simulations do not always give a strong bisimulation.
This property is true if we only allow choices with 0 or 1 branch,
but we prove a counter-example for a ctree with a binary choice.
|*)

Lemma hsb_ss : forall {E F C D X Y} `{C0 -< C} `{C0 -< D} L RR
  (t : ctree E C X) (t' : ctree F D Y),
  hsb L RR t t' -> ss L RR t t'.
Proof.
  intros. apply H1.
Qed.

Lemma ss_hsb : forall {E F C D X Y} `{C0 -< C} `{C0 -< D} L RR
  (t : ctree E C X) (t' : ctree F D Y),
  ss L RR t t' ->
  ss (flip L) (flip RR) t' t ->
  hsb L RR t t'.
Proof.
  split; auto.
Qed.

Lemma hsbisim_ssim : forall {E F C D X Y} `{C0 -< C} `{C0 -< D} L
  (t : ctree E C X) (t' : ctree F D Y),
  hsbisim L t t' -> ssim L t t'.
Proof.
  intros until L.
  coinduction R CH. simpl. intros.
  step in H1.
  apply H1 in H2 as H3. destruct H3 as (? & ? & ? & ? & ?).
  exists x, x0. auto.
Qed.

Lemma sbisim_ssim_eq : forall {E C X} `{C0 -< C} (t t' : ctree E C X),
  sbisim t t' -> ssim eq t t'.
Proof.
  intros. apply hsbisim_eq_sbisim in H0.
  now apply hsbisim_ssim in H0 as H1.
Qed.

Lemma trans__trans : forall {E C X} `{C0 -< C} l
  (t t' : ctree E C X),
  trans_ l (observe t) (observe t') = trans l t t'.
Proof.
  reflexivity.
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
  - rewrite EQ. apply choiceStuckI_always_stuck.
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
  - step. cbn. intros. inv_trans. subst.
    exists (Ret tt), tau. intuition. rewrite EQ. reflexivity.
  - step. cbn. intros. inv_trans; subst.
    + exists (Ret tt), tau. intuition. rewrite EQ. reflexivity.
    + exists (Ret tt), tau. intuition. rewrite EQ. apply stuckI_ssim.
  - step in H. cbn in H. destruct H as [_ ?].
    specialize (H tau stuckI). lapply H; [| etrans].
    intros. destruct H0 as (? & ? & ? & ? & ?). subst.
    inv_trans. step in H1. cbn in H1. destruct H1 as [? _].
    specialize (H0 (val tt) stuckI). lapply H0. 2: { rewrite EQ. etrans. }
    intro. destruct H1 as (? & ? & ? & ? & ?). subst.
    now apply stuckI_is_stuck in H1.
Qed.
