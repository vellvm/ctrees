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
     Eq.SSim.

From RelationAlgebra Require Export
     rel srel.

Import CoindNotations.
Import CTree.
Set Implicit Arguments.

(* TODO: Decide where to set this *)
Arguments trans : simpl never.

Section CompleteStrongSim.

(*|
Complete strong simulation [css].
|*)
  Program Definition css {E F C D : Type -> Type} {X Y : Type}
    (L : rel (@label E) (@label F)) : mon (ctree E C X -> ctree F D Y -> Prop) :=
    {| body R t u :=
        ss L R t u /\ (forall l u', trans l u u' -> exists l' t', trans l' t t')
    |}.
  Next Obligation.
    split; eauto. intros.
    edestruct H0 as (? & ? & ? & ? & ?); repeat econstructor; eauto.
  Qed.

End CompleteStrongSim.

Definition cssim {E F C D X Y} L :=
  (gfp (@css E F C D X Y L) : hrel _ _).

Module CSSimNotations.

  (*| css (complete simulation) notation |*)
  Notation "t (⪅ L ) u" := (cssim L t u) (at level 70).
  Notation "t ⪅ u" := (cssim eq t u) (at level 70).
  Notation "t [⪅ L ] u" := (css L _ t u) (at level 79).
  Notation "t [⪅] u" := (css eq _ t u) (at level 79).

End CSSimNotations.

Import CSSimNotations.

Ltac fold_cssim :=
  repeat
    match goal with
    | h: context[gfp (@css ?E ?F ?C ?D ?X ?Y ?L)] |- _ => fold (@cssim E F C D X Y L) in h
    | |- context[gfp (@css ?E ?F ?C ?D ?X ?Y ?L)]      => fold (@cssim E F C D X Y L)
    end.

Tactic Notation "__step_cssim" :=
  match goal with
  | |- context[@cssim ?E ?F ?C ?D ?X ?Y ?LR] =>
      unfold cssim;
      step;
      fold (@cssim E F C D X Y L)
  end.

#[local] Tactic Notation "step" := __step_cssim || step.

Tactic Notation "__coinduction_cssim" simple_intropattern(r) simple_intropattern(cih) :=
  first [unfold cssim at 4 | unfold cssim at 3 | unfold cssim at 2 | unfold cssim at 1]; coinduction r cih.
#[local] Tactic Notation "coinduction" simple_intropattern(r) simple_intropattern(cih) :=
  __coinduction_cssim r cih || __coinduction_ssim r cih || coinduction r cih.

Ltac __step_in_cssim H :=
  match type of H with
  | context[@cssim ?E ?F ?C ?D ?X ?Y ?LR] =>
      unfold cssim in H;
      step in H;
      fold (@cssim E F C D X Y L) in H
  end.

#[local] Tactic Notation "step" "in" ident(H) := __step_in_cssim H || step in H.

Import CTreeNotations.
Import EquNotations.

Section cssim_homogenous_theory.

  Context {E B : Type -> Type} {X : Type}
          {L: relation (@label E)}.

  Notation css := (@css E E B B X X).
  Notation cssim  := (@cssim E E B B X X).

  Lemma cssim_subrelation : forall (t t' : ctree E B X) L',
      subrelation L L' -> cssim L t t' -> cssim L' t t'.
  Proof.
    intros. revert t t' H0. coinduction R CH.
    intros. step in H0. simpl; split; intros; cbn in H0; destruct H0 as [H0' H0''].
    - cbn in H0'; apply H0' in H1 as (? & ? & ? & ? & ?);
        apply H in H2. exists x, x0. auto.
    - apply H0'' in H1 as (? & ? & ?).
      do 2 eexists; apply H0.
  Qed.

(*|
    Various results on reflexivity and transitivity.
|*)
  #[global] Instance refl_csst {LR: Reflexive L} {C: Chain (css L)}: Reflexive `C.
  Proof.
    apply Reflexive_chain; cbn; eauto 9.
  Qed.

  #[global] Instance square_csst {LT: Transitive L} {C: Chain (css L)}: Transitive `C.
  Proof.
    apply Transitive_chain.
    cbn. intros ????? [xy xy'] [yz yz'].
    split.
    - intros ?? xx'.
      destruct (xy _ _ xx') as (l' & y' & yy' & ? & ?).
      destruct (yz _ _ yy') as (l'' & z' & zz' & ? & ?).
      eauto 8.
    - intros ?? xx'.
      destruct (yz' _ _ xx') as (l'' & z' & zz').
      destruct (xy' _ _ zz') as (l' & y' & yy').
      eauto 8.
  Qed.

  (*| PreOrder |*)
  #[global] Instance PreOrder_csst {LPO: PreOrder L} {C: Chain (css L)}: PreOrder `C.
  Proof. split; typeclasses eauto. Qed.

  #[global] Instance cssim_ssim_subrelation : subrelation (cssim L) (ssim L).
  Proof.
    red.
    coinduction r cih; intros * SB.
    step in SB; destruct SB as [fwd _].
    intros ?? TR; apply fwd in TR as (? & ? & ? & ? & ?); eauto 10.
  Qed.

End cssim_homogenous_theory.

Section cssim_heterogenous_theory.

  Arguments label: clear implicits.
  Context {E F C D: Type -> Type} {X Y: Type}
          {L: rel (@label E) (@label F)}.

  Notation css := (@css E F C D X Y).
  Notation cssim  := (@cssim E F C D X Y).

(*|
   Strong simulation up-to [equ] is valid
   ----------------------------------------
|*)

  Lemma equ_clos_csst {c: Chain (css L)}:
    forall x y, equ_clos `c x y -> `c x y.
  Proof.
    apply tower.
    - intros ? INC x y [x' y' x'' y'' EQ' EQ''] ??. red.
      apply INC; auto.
      econstructor; eauto.
      apply leq_infx in H.
      now apply H.
    - intros a b ?? [x' y' x'' y'' EQ' [SIM COMP]].
      split; intros ?? tr.
      + rewrite EQ' in tr.
        edestruct SIM as (l' & ? & ? & ? & ?); eauto.
        exists l',x0; intuition.
        rewrite <- Equu; auto.
      + rewrite <- Equu in tr.
        edestruct COMP as (l' & ? & ?); eauto.
        setoid_rewrite EQ'. eauto.
   Qed.

  #[global] Instance equ_clos_csst_goal {c: Chain (css L)} :
    Proper (equ eq ==> equ eq ==> flip impl) `c.
  Proof.
    cbn; intros ? ? eq1 ? ? eq2 H.
    apply equ_clos_csst; econstructor; [eauto | | symmetry; eauto]; assumption.
  Qed.

  #[global] Instance equ_clos_csst_ctx  {c: Chain (css L)} :
    Proper (equ eq ==> equ eq ==> impl) `c.
  Proof.
    cbn; intros ? ? eq1 ? ? eq2 H.
    apply equ_clos_csst; econstructor; [symmetry; eauto | | eauto]; assumption.
  Qed.

  #[global] Instance equ_css_closed_goal {r} : Proper (equ eq ==> equ eq ==> flip impl) (css L r).
  Proof.
    intros t t' tt' u u' uu'; cbn; intros [H H0]; split; intros l t0 TR.
    - rewrite tt' in TR. destruct (H _ _ TR) as (? & ? & ? & ? & ?).
      exists x, x0; auto; rewrite uu'; auto.
    - rewrite uu' in TR. destruct (H0 _ _ TR) as (? & ? & ?).
      exists x, x0; eauto; rewrite tt'; auto.
  Qed.

  #[global] Instance equ_css_closed_ctx {r} : Proper (equ eq ==> equ eq ==> impl) (css L r).
  Proof.
    intros t t' tt' u u' uu'; cbn; intros [H H0]; split; intros l t0 TR.
    - rewrite <- tt' in TR. destruct (H _ _ TR) as (? & ? & ? & ? & ?).
      exists x, x0; auto; rewrite <- uu'; auto.
    - rewrite <- uu' in TR. destruct (H0 _ _ TR) as (? & ? & ?).
      exists x, x0; auto; rewrite <- tt'; auto.
  Qed.

  Lemma is_stuck_css : forall (t: ctree E C X) (u: ctree F D Y) R,
      css L R t u -> is_stuck t <-> is_stuck u.
  Proof.
    split; intros; intros ? ? ?.
    - apply H in H1 as (? & ? & ?). now apply H0 in H1.
    - apply H in H1 as (? & ? & ? & ? & ?). now apply H0 in H1.
  Qed.

  Lemma is_stuck_cssim :  forall (t: ctree E C X) (u: ctree F D Y),
      t (⪅ L) u -> is_stuck t <-> is_stuck u.
  Proof.
    intros. step in H. eapply is_stuck_css; eauto.
  Qed.

  Lemma css_is_stuck : forall (t : ctree E C X) (u: ctree F D Y) R,
      is_stuck t -> is_stuck u -> css L R t u.
  Proof.
    split; intros.
    - cbn. intros. now apply H in H1.
    - now apply H0 in H1.
  Qed.

  Lemma cssim_is_stuck : forall (t : ctree E C X) (u: ctree F D Y),
      is_stuck t -> is_stuck u -> t (⪅ L) u.
  Proof.
    intros. step. now apply css_is_stuck.
  Qed.

  Lemma cssim_ssim_subrelation_gen : forall x y, cssim L x y -> ssim L x y.
  Proof.
    red.
    coinduction r cih; intros * SB.
    step in SB; destruct SB as [fwd _].
    intros ?? TR; apply fwd in TR as (? & ? & ? & ? & ?); eauto 10.
  Qed.

End cssim_heterogenous_theory.

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

(*|
Specialization of [bind_ctx] to a function acting with [cssim] on the bound value,
and with the argument (pointwise) on the continuation.
|*)
  Lemma bind_chain_gen
    (RR : rel (label E) (label F))
    (ISVR : is_update_val_rel L R0 RR)
    (HL: Respects_val RR)
    {R : Chain (@css E F C D X' Y' L)} :
    forall (t : ctree E C X) (t' : ctree F D Y) (k : X -> ctree E C X') (k' : Y -> ctree F D Y'),
      cssim RR t t' ->
      (forall x x', R0 x x' -> (elem R (k x) (k' x') /\ exists l t', trans l (k x) t')) ->
      elem R (bind t k) (bind t' k').
  Proof.
    apply tower.
    - intros ? INC ? ? ? ? tt' kk' ? ?.
      apply INC. apply H. apply tt'.
      intros x x' xx'. split. apply leq_infx in H. apply H. now apply kk'.
      edestruct kk'; eauto.
    - intros ? ? ? ? ? ? tt' kk'.
      step in tt'.
      destruct tt' as [tt tt'].
      split.
      + cbn; intros * STEP.
        apply trans_bind_inv in STEP as [(?H & ?t' & STEP & EQ) | (v & STEPres & STEP)].
        * apply tt in STEP as (? & ? & ? & ? & ?).
          do 2 eexists; split; [| split].
          apply trans_bind_l; eauto.
          ++ intro Hl. destruct Hl.
             apply ISVR in H3; etrans.
             inversion H3; subst. apply H0. constructor. apply H5. constructor.
          ++ rewrite EQ.
             apply H.
             apply H2.
             intros * HR.
             split.
             now apply (b_chain x), kk'.
             apply (kk' _ _ HR).
          ++ apply ISVR in H3; etrans.
             destruct H3. exfalso. apply H0. constructor. eauto.
        * apply tt in STEPres as (u' & ? & STEPres & EQ' & ?).
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
      + cbn; intros * STEP.
        apply trans_bind_inv_l in STEP as (l' & t2' & STEP).
        apply tt' in STEP as (l'' & t1' & TR1).
        destruct l''.
        do 2 eexists; apply trans_bind_l; eauto; intros abs; inv abs.
        do 2 eexists; apply trans_bind_l; eauto; intros abs; inv abs.
        do 2 eexists; apply trans_bind_l; eauto; intros abs; inv abs.
        apply trans_val_invT in TR1 as ?. subst X0.
        apply trans_val_inv in TR1 as ?. rewrite H0 in TR1.
        pose proof TR1 as tmp.
        apply tt in tmp as (? & ? & TR & ? & ?).
        assert (is_val x0) by (eapply HL; eauto; constructor).
        inv H3; pose proof trans_val_invT TR; subst X0.
        specialize (kk' v x2).
        destruct kk'.
        apply ISVR in H2; etrans.
        dependent destruction H2; auto. exfalso; apply H2; constructor.
        edestruct H4 as (? & ? & ?); eauto.
        eapply trans_bind_r in H5; eauto.
  Qed.

End bind.

(*|
Specializing the congruence principle for [⪅]
|*)
Lemma cssim_clo_bind_gen {E F C D: Type -> Type} {X Y X' Y': Type}  {L : rel (@label E) (@label F)}
      (R0 : rel X Y) L0
      (HL  : is_update_val_rel L R0 L0)
      (HLV : Respects_val L0)
      (t1 : ctree E C X) (t2: ctree F D Y)
      (k1 : X -> ctree E C X') (k2 : Y -> ctree F D Y'):
  cssim L0 t1 t2 ->
  (forall x y, R0 x y -> cssim L (k1 x) (k2 y)) ->
  (forall x, exists l t', trans l (k1 x) t') ->
  cssim L (t1 >>= k1) (t2 >>= k2).
Proof.
  intros.
  eapply bind_chain_gen; eauto.
  split; eauto.
  now apply H0.
Qed.

Lemma cssim_clo_bind {E F C D: Type -> Type} {X Y X' Y': Type} {L : rel (@label E) (@label F)}
      (R0 : rel X Y)
      (t1 : ctree E C X) (t2: ctree F D Y)
      (k1 : X -> ctree E C X') (k2 : Y -> ctree F D Y'):
  Respects_val L ->
  t1 (⪅update_val_rel L R0) t2 ->
  (forall x y, R0 x y -> k1 x (⪅L) k2 y) ->
  (forall x, exists l t', trans l (k1 x) t') ->
  t1 >>= k1 (⪅L) t2 >>= k2.
Proof.
  intros.
  eapply bind_chain_gen.
  3:eauto.
  eauto using update_val_rel_correct.
  eauto using Respects_val_update_val_rel.
  split; eauto.
  now apply H1.
Qed.

Lemma cssim_clo_bind_eq {E C D: Type -> Type} {X X': Type}
      (t1 : ctree E C X) (t2: ctree E D X)
      (k1 : X -> ctree E C X') (k2 : X -> ctree E D X'):
  t1 ⪅ t2 ->
  (forall x, k1 x ⪅ k2 x) ->
  (forall x, exists l t', trans l (k1 x) t') ->
  t1 >>= k1 ⪅ t2 >>= k2.
Proof.
  intros.
  eapply bind_chain_gen; eauto.
  - apply update_val_rel_eq.
  - apply Respects_val_eq.
  - split; subst; auto.
    apply H0.
Qed.

Ltac __play_cssim := step; cbn; split; [intros ? ? ?TR | etrans].

Ltac __play_cssim_in H :=
  step in H;
  cbn in H; edestruct H as [(? & ? & ?TR & ?EQ & ?HL) ?PROG];
  clear H; [etrans |].

Ltac __eplay_cssim :=
  match goal with
  | h : @cssim ?E ?F ?C ?D ?X ?Y _ _ ?L |- _ =>
      __play_cssim_in h
  end.

#[local] Tactic Notation "play" := __play_cssim.
#[local] Tactic Notation "play" "in" ident(H) := __play_cssim_in H.
#[local] Tactic Notation "eplay" := __eplay_cssim.

Section Proof_Rules.
  Arguments label: clear implicits.
  Context {E C : Type -> Type} {X: Type}.

  Lemma step_css_ret_gen {Y F D}(x : X) (y : Y) (R L : rel _ _) :
    R Stuck Stuck ->
    (Proper (equ eq ==> equ eq ==> impl) R) ->
    L (val x) (val y) ->
    css L R (Ret x : ctree E C X) (Ret y : ctree F D Y).
  Proof.
    intros Rstuck PROP Lval.
    split.
    cbn; intros ? ? TR; inv_trans; subst;
      cbn; eexists; eexists; intuition; etrans;
      now rewrite EQ.
    intros; do 2 eexists; etrans.
  Qed.

  Lemma step_css_ret {Y F D} (x : X) (y : Y) (L : rel _ _)
    {R : Chain (@css E F C D X Y L)} :
    L (val x) (val y) ->
    css L `R (Ret x : ctree E C X) (Ret y : ctree F D Y).
  Proof.
    intros.
    apply step_css_ret_gen.
    - apply (b_chain R).
      split.
      apply is_stuck_ss; apply Stuck_is_stuck.
      intros * abs; apply trans_stuck_inv in abs; easy.
    - typeclasses eauto.
    - apply H.
  Qed.

  Lemma step_css_ret_l_gen {Y F D} (x : X) (y : Y) (u u' : ctree F D Y) (L R : rel _ _) :
    R Stuck Stuck ->
    (Proper (equ eq ==> equ eq ==> impl) R) ->
    L (val x) (val y) ->
    trans (val y) u u' ->
    css L R (Ret x : ctree E C X) u.
  Proof.
    intros.
    apply trans_val_inv in H2 as ?.
    split.
    - cbn. intros.
      inv_trans.
      subst; setoid_rewrite EQ.
      etrans.
    - intros.
      do 2 eexists.
      etrans.
  Qed.

  Lemma step_css_ret_l {Y F D} (x : X) (y : Y) (u u' : ctree F D Y) (L : rel _ _)
    {R : Chain (@css E F C D X Y L)} :
    L (val x) (val y) ->
    trans (val y) u u' ->
    css L ` R (Ret x : ctree E C X) u.
  Proof.
    intros.
    eapply step_css_ret_l_gen; eauto.
    - apply (b_chain R).
      split.
      apply is_stuck_ss; apply Stuck_is_stuck.
      intros * abs; apply trans_stuck_inv in abs; easy.
    - typeclasses eauto.
  Qed.

  Lemma cssim_ret {Y F D} (x : X) (y : Y) (L : rel _ _) :
    L (val x) (val y) ->
    cssim L (Ret x : ctree E C X) (Ret y : ctree F D Y).
  Proof.
    intros. step. now apply step_css_ret.
  Qed.

(*|
 The vis nodes are deterministic from the perspective of the labeled
 transition system, stepping is hence symmetric and we can just recover
 the itree-style rule.
|*)
  Lemma step_css_vis_gen {Y Z Z' F D} (e : E Z) (f: F Z')
    (k : Z -> ctree E C X) (k' : Z' -> ctree F D Y) (R L: rel _ _) :
    inhabited Z ->
    (Proper (equ eq ==> equ eq ==> impl) R) ->
    (forall x, exists y, R (k x) (k' y) /\ L (obs e x) (obs f y)) ->
    css L R (Vis e k) (Vis f k').
  Proof.
    intros.
    split.
    - apply step_ss_vis_gen; auto.
    - intros * tr; inv_trans; subst.
      do 2 eexists. etrans.
      Unshelve.
      apply X0.
  Qed.

  Lemma step_css_vis {Y Z Z' F D} (e : E Z) (f: F Z')
    (k : Z -> ctree E C X) (k' : Z' -> ctree F D Y) (L : rel _ _)
    {R : Chain (@css E F C D X Y L)} :
    inhabited Z ->
    (forall x, exists y, ` R (k x) (k' y) /\ L (obs e x) (obs f y)) ->
    css L ` R (Vis e k) (Vis f k').
  Proof.
    intros * INH EQ.
    apply step_css_vis_gen; auto.
    typeclasses eauto.
  Qed.

  Lemma cssim_vis {Y Z Z' F D} (e : E Z) (f: F Z')
    (k : Z -> ctree E C X) (k' : Z' -> ctree F D Y) (L : rel _ _) :
    inhabited Z ->
    (forall x, exists y, cssim L (k x) (k' y) /\ L (obs e x) (obs f y)) ->
    cssim L (Vis e k) (Vis f k').
  Proof.
    intros. step. apply step_css_vis; auto.
  Qed.

  Lemma step_css_vis_id_gen {Y Z F D} (e : E Z) (f: F Z)
    (k : Z -> ctree E C X) (k' : Z -> ctree F D Y) (R L: rel _ _) :
    (Proper (equ eq ==> equ eq ==> impl) R) ->
    (forall x, R (k x) (k' x) /\ L (obs e x) (obs f x)) ->
    css L R (Vis e k) (Vis f k').
  Proof.
    intros.
    split.
    - apply step_ss_vis_id_gen; auto.
    - intros * tr; inv_trans; subst.
      do 2 eexists. etrans.
      Unshelve. apply x.
  Qed.

  Lemma step_css_vis_id {Y Z F D} (e : E Z) (f: F Z)
        (k : Z -> ctree E C X) (k' : Z -> ctree F D Y) (L : rel _ _)
    {R : Chain (@css E F C D X Y L)} :
    (forall x, ` R (k x) (k' x) /\ L (obs e x) (obs f x)) ->
    css L ` R (Vis e k) (Vis f k').
  Proof.
    intros * EQ.
    apply step_css_vis_id_gen; auto.
    typeclasses eauto.
  Qed.

  Lemma cssim_vis_id {Y Z F D} (e : E Z) (f: F Z)
        (k : Z -> ctree E C X) (k' : Z -> ctree F D Y) (L : rel _ _) :
    (forall x, cssim L (k x) (k' x) /\ L (obs e x) (obs f x)) ->
    cssim L (Vis e k) (Vis f k').
  Proof.
    intros. step. now apply step_css_vis_id.
  Qed.

(*|
  Same goes for visible tau nodes.
|*)
  Lemma step_css_step_gen {Y F D}
        (t : ctree E C X) (t': ctree F D Y) (R L: rel _ _):
    (Proper (equ eq ==> equ eq ==> impl) R) ->
    L τ τ ->
    (R t t') ->
    css L R (Step t) (Step t').
  Proof.
    intros PR ? EQs.
    split.
    - apply step_ss_step_gen; auto.
    - intros * TR; inv_trans; subst; etrans.
  Qed.

  Lemma step_css_step {Y F D}
        (t: ctree E C X) (t': ctree F D Y) (L : rel _ _)
        {R : Chain (@css E F C D X Y L)} :
    (` R t t') ->
    L τ τ ->
    css L ` R (Step t) (Step t').
  Proof.
    intros.
    apply step_css_step_gen; auto.
    typeclasses eauto.
  Qed.

  Lemma cssim_step {Y F D}
        (t: ctree E C X) (t': ctree F D Y) (L : rel _ _) :
    (cssim L t t') ->
    L τ τ ->
    cssim L (Step t) (Step t').
  Proof.
    intros.
    step. apply step_css_step; auto.
  Qed.

(*|
    For invisible nodes, the situation is different: we may kill them, but that execution
    cannot act as going under the guard.
|*)
  Lemma step_css_br_l_gen {Y F D Z} (c : C Z)
        (k : Z -> ctree E C X) (t': ctree F D Y) (R L: rel _ _):
    inhabited Z ->
    (forall x, css L R (k x) t') ->
    css L R (Br c k) t'.
  Proof.
    intros [? _] EQs.
    split.
    - apply step_ss_br_l_gen; auto. apply EQs.
    - intros * TR.
      unshelve edestruct EQs as [_ ?]; eauto.
      apply H in TR.
      destruct TR as (? & ? & ?).
      etrans.
  Qed.

  Lemma step_css_br_l {Y F D Z} (c : C Z)
    (k : Z -> ctree E C X) (t: ctree F D Y) (L: rel _ _)
    {R : Chain (@css E F C D X Y L)} :
    inhabited Z ->
    (forall x,  css L (elem R) (k x) t) ->
    css L ` R (Br c k) t.
  Proof.
    intros [? _] EQs.
    split.
    - apply step_ss_br_l_gen; auto. apply EQs.
    - intros * TR.
      unshelve edestruct EQs as [_ ?]; eauto.
      apply H in TR.
      destruct TR as (? & ? & ?).
      etrans.
  Qed.

  Lemma cssim_br_l {Y F D Z} (c : C Z)
    (k : Z -> ctree E C X) (t: ctree F D Y) (L: rel _ _):
    inhabited Z ->
    (forall x, cssim L (k x) t) ->
    cssim L (Br c k) t.
  Proof.
    intros. step. apply step_css_br_l_gen; auto. intros.
    specialize (H x). step in H. apply H.
  Qed.

  (* This does not hold without assuming explicit progress on the left side.
     Indeed, if [k x] is stuck, [t] would be stuck as well.
     But then [Br c k] could be able to step, contradicting the completeness.
   *)
   Lemma step_css_br_r_gen {Y F D Z} (c : D Z)
    (t : ctree E C X) (k : Z -> ctree F D Y) (R L: rel _ _) z :
    (exists l t', trans l t t') ->
    css L R t (k z) ->
    css L R t (Br c k).
  Proof.
    intros TR [SIM COMP].
    split.
    - eapply step_ss_br_r_gen; eauto.
    - intros; auto.
  Qed.

  Lemma step_css_br_r {Y F D Z} (c : D Z) x
    (k : Z -> ctree F D Y) (t: ctree E C X) (L: rel _ _)
    {R : Chain (@css E F C D X Y L)} :
    (exists l t', trans l t t') ->
    css L (elem R) t (k x) ->
    css L ` R t (Br c k).
  Proof.
    intros TR SIM.
    split.
    - eapply step_ss_br_r_gen; apply SIM.
    - auto.
  Qed.

  Lemma cssim_br_r {Y F D Z} (c : D Z) x
    (k : Z -> ctree F D Y) (t: ctree E C X) (L: rel _ _):
    (exists l t', trans l t t') ->
    cssim L t (k x) ->
    cssim L t (Br c k).
  Proof.
    intros. step.
    apply (@step_css_br_r_gen Y F D Z c t k (cssim L) L x); auto.
    step in H0; auto.
  Qed.

  Lemma step_css_br_gen {Y F D n m} (a: C n) (b: D m)
    (k : n -> ctree E C X) (k' : m -> ctree F D Y) (R L : rel _ _) :
    (exists x l t', trans l (k x) t') ->
    (forall x, exists y, css L R (k x) (k' y)) ->
    css L R (Br a k) (Br b k').
  Proof.
    intros [? PROG] EQs.
    split.
    - apply step_ss_br_gen; auto. intros y. destruct (EQs y).
      exists x0; apply H.
    - intros * TR.
      destruct PROG as (? & ? & TR').
      do 2 eexists; econstructor; apply TR'.
  Qed.

  Lemma step_css_br {Y F D n m} (cn: C n) (cm: D m)
    (k : n -> ctree E C X) (k' : m -> ctree F D Y) (L : rel _ _)
    {R : Chain (@css E F C D X Y L)} :
    (exists x l t', trans l (k x) t') ->
    (forall x, exists y, css L (elem R) (k x) (k' y)) ->
    css L `R (Br cn k) (Br cm k').
  Proof.
    intros.
    apply step_css_br_gen; auto.
  Qed.

  Lemma cssim_br {Y F D n m} (cn: C n) (cm: D m)
    (k : n -> ctree E C X) (k' : m -> ctree F D Y) (L : rel _ _) :
    (exists x l t', trans l (k x) t') ->
    (forall x, exists y, cssim L (k x) (k' y)) ->
    cssim L (Br cn k) (Br cm k').
  Proof.
    intros. step. apply step_css_br; auto.
    intros. destruct (H0 x). step in H1. exists x0. apply H1.
  Qed.

  Lemma step_css_br_id_gen {Y F D Z} (c: C Z) (d: D Z)
        (k : Z -> ctree E C X) (k' : Z -> ctree F D Y)
        (R L : rel _ _) :
    (forall x, css L R (k x) (k' x)) ->
    css L R (Br c k) (Br d k').
  Proof.
    intros EQs.
    split.
    - apply step_ss_br_id_gen; auto. intros y. destruct (EQs y).
      apply H.
    - intros * TR.
      apply trans_br_inv in TR as [x TR].
      apply EQs in TR as (l' & t & TR).
      do 2 eexists; econstructor; apply TR.
  Qed.

  Lemma step_css_br_id {Y F D n} (c: C n) (d: D n)
    (k : n -> ctree E C X) (k': n -> ctree F D Y) (L: rel _ _)
    {R : Chain (@css E F C D X Y L)} :
    (forall x, css L (elem R) (k x) (k' x)) ->
    css L ` R (Br c k) (Br d k').
  Proof.
    intros.
    apply step_css_br_id_gen; eauto.
  Qed.

  Lemma cssim_br_id {Y F D n} (c: C n) (d: D n)
    (k : n -> ctree E C X) (k': n -> ctree F D Y) (L: rel _ _) :
    (forall x, cssim L (k x) (k' x)) ->
    cssim L (Br c k) (Br d k').
  Proof.
    intros. step. apply step_css_br_id; eauto.
    intros. apply (gfp_pfp (css L)). apply H.
  Qed.

  Lemma step_css_guard_gen {Y F D}
        (t: ctree E C X) (t': ctree F D Y) (R L: rel _ _):
    css L R t t' ->
    css L R (Guard t) (Guard t').
  Proof.
    intros EQ.
    split.
    - apply step_ss_guard_gen; apply EQ.
    - intros.
      inv_trans.
      apply EQ in H as (? & ? & ?).
      etrans.
  Qed.

  Lemma step_css_guard_l {Y F D}
    (t: ctree E C X) (t': ctree F D Y) (L: rel _ _)
    {R : Chain (@css E F C D X Y L)} :
    css L `R t t' ->
    css L `R (Guard t) t'.
  Proof.
    intros EQ.
    split.
    - intros ? ? TR; inv_trans; subst.
      apply EQ in TR as (? & ? & TR' & ?).
      eauto.
    - intros.
      apply EQ in H as (? & ? & ?).
      etrans.
  Qed.

  Lemma step_css_guard_r {Y F D}
        (t: ctree E C X) (t': ctree F D Y) (L: rel _ _)
        {R : Chain (@css E F C D X Y L)} :
    css L `R t t' ->
    css L `R t (Guard t').
  Proof.
    intros EQ.
    split.
    - intros ? ? TR; inv_trans; subst.
      apply EQ in TR as (? & ? & TR' & ?).
      do 2 eexists; split; eauto.
      etrans.
    - intros.
      inv_trans.
      apply EQ in H as (? & ? & ?).
      etrans.
  Qed.

  Lemma step_css_guard {Y F D}
        (t: ctree E C X) (t': ctree F D Y) (L: rel _ _)
        {R : Chain (@css E F C D X Y L)} :
    css L `R t t' ->
    css L `R (Guard t) (Guard t').
  Proof.
    intros.
    now apply step_css_guard_gen.
  Qed.

  Lemma cssim_guard_l {Y F D}
        (t: ctree E C X) (t': ctree F D Y) (L: rel _ _):
    cssim L t t' ->
    cssim L (Guard t) t'.
  Proof.
    intros; step; apply step_css_guard_l; step in H; auto.
  Qed.

  Lemma cssim_guard_r {Y F D}
        (t: ctree E C X) (t': ctree F D Y) (L: rel _ _):
    cssim L t t' ->
    cssim L t (Guard t').
  Proof.
    intros; step; apply step_css_guard_r; step in H; auto.
  Qed.

  Lemma cssim_guard {Y F D}
        (t: ctree E C X) (t': ctree F D Y) (L: rel _ _):
    cssim L t t' ->
    cssim L (Guard t) (Guard t').
  Proof.
    intros; step; apply step_css_guard; step in H; auto.
  Qed.

(*|
    When matching visible brs one against another, in general we need to explain how
    we map the branches from the left to the branches to the right.
    A useful special case is the one where the arity coincide and we simply use the identity
    in both directions. We can in this case have [n] rather than [2n] obligations.
|*)
  Lemma step_css_brS_gen {Z Z' Y F D} (c : C Z) (d : D Z')
    (k : Z -> ctree E C X) (k' : Z' -> ctree F D Y) (R L: rel _ _) :
    inhabited Z ->
    (Proper (equ eq ==> equ eq ==> impl) R) ->
    (forall x, exists y, R (k x) (k' y)) ->
    L τ τ ->
    css L R (BrS c k) (BrS d k').
  Proof.
    intros INH HP REL HL.
    eapply step_css_br_gen.
    destruct INH as [z _].
    exists z; etrans.
    intros.
    specialize (REL x) as [y ?].
    exists y.
    eapply step_css_step_gen; auto.
  Qed.

  Lemma step_css_brS {Z Z' Y F D} (c : C Z) (c' : D Z')
    (k : Z -> ctree E C X) (k' : Z' -> ctree F D Y) (L: rel _ _)
    {R : Chain (@css E F C D X Y L)} :
    inhabited Z ->
    (forall x, exists y, `R (k x) (k' y)) ->
    L τ τ ->
    css L `R (BrS c k) (BrS c' k').
  Proof.
    intros INH REL HL.
    destruct INH as [z _].
    eapply step_css_br.
    exists z; etrans.
    intros x; specialize (REL x) as [y ?].
    exists y.
    eapply step_css_step; auto.
  Qed.

  Lemma cssim_brS {Z Z' Y F D} (c : C Z) (c' : D Z')
    (k : Z -> ctree E C X) (k' : Z' -> ctree F D Y) (L: rel _ _) :
    inhabited Z ->
    (forall x, exists y, cssim L (k x) (k' y)) ->
    L τ τ ->
    cssim L (BrS c k) (BrS c' k').
  Proof.
    intros INH REL HL.
    destruct INH as [z _].
    apply cssim_br.
    exists z; etrans.
    intros x; specialize (REL x) as [y ?]; exists y.
    apply cssim_step; auto.
  Qed.

  Lemma step_css_brS_id_gen {Z Y D F} (c : C Z) (d: D Z)
    (k: Z -> ctree E C X) (k': Z -> ctree F D Y) (R L : rel _ _) :
    (Proper (equ eq ==> equ eq ==> impl) R) ->
    (forall x, R (k x) (k' x)) ->
    L τ τ ->
    css L R (BrS c k) (BrS d k').
  Proof.
    intros HP REL HL.
    split; [apply step_ss_brS_id_gen; auto |].
    intros. inv_trans. etrans.
    Unshelve. apply x0.
  Qed.

  Lemma step_css_brS_id {Z Y D F} (c : C Z) (d : D Z)
    (k: Z -> ctree E C X) (k': Z -> ctree F D Y) (L : rel _ _)
    {R : Chain (@css E F C D X Y L)} :
    (forall x, `R (k x) (k' x)) ->
    L τ τ ->
    css L `R (BrS c k) (BrS d k').
  Proof.
    intros REL HL.
    apply step_css_brS_id_gen; auto.
    typeclasses eauto.
  Qed.

  Lemma cssim_brS_id {Z Y D F} (c : C Z) (d : D Z)
        (k: Z -> ctree E C X) (k': Z -> ctree F D Y) (L : rel _ _) :
    (forall x, cssim L (k x) (k' x)) ->
    L τ τ ->
    cssim L (BrS c k) (BrS d k').
  Proof.
    intros. step. apply step_css_brS_id; auto.
  Qed.

End Proof_Rules.

Section WithParams.

  Context {E F C D : Type -> Type}.
  Context (L : rel (@label E) (@label F)).

(*|
Note that with visible schedules, nary-spins are equivalent only
if neither are empty, or if both are empty: they match each other's
tau challenge infinitely often.
With invisible schedules, they are always equivalent: neither of them
produce any challenge for the other.
|*)
  Lemma spinS_gen_nonempty : forall {Z Z' X Y} (c: C X) (c': D Y) (x: X) (y: Y) (L : rel _ _),
    L τ τ ->
    cssim L (@spinS_gen E C Z X c) (@spinS_gen F D Z' Y c').
  Proof.
    intros.
    red. coinduction R CH.
    simpl; split; intros l t' TR; rewrite ctree_eta in TR; cbn in TR;
    apply trans_brS_inv in TR as (_ & EQ & ->);
      do 2 eexists;
      rewrite ctree_eta; cbn; intuition.
    - econstructor; auto.
      constructor; eauto.
    - rewrite EQ; eauto.
    - eapply H.
    - econstructor; auto.
      constructor; eauto.
  Qed.

(*|
Inversion principles
--------------------
|*)
  Lemma cssim_ret_inv X Y (r1 : X) (r2 : Y) :
    (Ret r1 : ctree E C X) (⪅L) (Ret r2 : ctree F D Y) ->
    L (val r1) (val r2).
  Proof.
    intros.
    eplay.
    inv_trans.
    now subst.
  Qed.

  Lemma css_ret_l_inv {X Y R} :
    forall r (u : ctree F D Y),
    css L R (Ret r : ctree E C X) u ->
    exists l' u', trans l' u u' /\ R Stuck u' /\ L (val r) l'.
  Proof.
    intros. apply H; etrans.
  Qed.

  Lemma cssim_ret_l_inv {X Y} :
    forall r (u : ctree F D Y),
    cssim L (Ret r : ctree E C X) u ->
    exists l' u', trans l' u u' /\ L (val r) l'.
  Proof.
    intros. step in H.
    apply css_ret_l_inv in H as (? & ? & ? & ? & ?). etrans.
  Qed.

  Lemma cssim_vis_inv_type {X Y X1 X2}
    (e1 : E X1) (e2 : E X2) (k1 : X1 -> ctree E C X) (k2 : X2 -> ctree E D Y) (x1 : X1):
    cssim eq (Vis e1 k1) (Vis e2 k2) ->
    X1 = X2.
  Proof.
    intros.
    step in H; cbn in H; destruct H as [SIM COMP].
    edestruct SIM as (? & ? & ? & ? & ?).
    etrans.
    inv_trans; subst; auto.
    eapply obs_eq_invT; eauto.
    Unshelve.
    exact x1.
  Qed.

  Lemma cssbt_vis_inv {X Y X1 X2}
    (e1 : E X1) (e2 : F X2) (k1 : X1 -> ctree E C X) (k2 : X2 -> ctree F D Y) (x : X1)
    {R : Chain (@css E F C D X Y L)} :
    css L (elem R) (Vis e1 k1) (Vis e2 k2) ->
    (exists y, L (obs e1 x) (obs e2 y))  /\ (forall x, exists y, ` R (k1 x) (k2 y)).
  Proof.
    intros.
    destruct H as [SIM COMP].
    split; intros; edestruct SIM as (? & ? & ? & ? & ?);
      etrans; subst;
      inv_trans; subst; eexists; auto.
    - now eapply H1.
    - now apply H0.
  Qed.

  Lemma ssim_vis_inv {X Y X1 X2}
    (e1 : E X1) (e2 : F X2) (k1 : X1 -> ctree E C X) (k2 : X2 -> ctree F D Y) (x : X1):
    cssim L (Vis e1 k1) (Vis e2 k2) ->
    (exists y, L (obs e1 x) (obs e2 y)) /\ (forall x, exists y, cssim L (k1 x) (k2 y)).
  Proof.
    intros.
    split.
    - eplay.
      inv_trans; subst; exists x2; eauto.
    - intros y.
      step in H.
      cbn in H.
      edestruct H as [(l' & u' & TR & IN & HL) ?].
      apply trans_vis with (x := y).
      inv_trans.
      eexists.
      apply IN.
  Qed.

  Lemma css_vis_l_inv {X Y Z R} :
    forall (e : E Z) (k : Z -> ctree E C X) (u : ctree F D Y) x,
    css L R (Vis e k) u ->
    exists l' u', trans l' u u' /\ R (k x) u' /\ L (obs e x) l'.
  Proof.
    intros. apply H; etrans.
  Qed.

  Lemma cssim_vis_l_inv {X Y Z} :
    forall (e : E Z) (k : Z -> ctree E C X) (u : ctree F D Y) x,
    cssim L (Vis e k) u ->
    exists l' u', trans l' u u' /\ cssim L (k x) u' /\ L (obs e x) l'.
  Proof.
    intros. step in H.
    now simple apply css_vis_l_inv with (x := x) in H.
  Qed.

  Lemma cssim_brS_inv {X Y}
    n m (cn: C n) (cm: D m) (k1 : n -> ctree E C X) (k2 : m -> ctree F D Y) :
    cssim L (BrS cn k1) (BrS cm k2) ->
    (forall i1, exists i2, cssim L (k1 i1) (k2 i2)).
  Proof.
    intros EQ i1.
    eplay.
    subst; inv_trans.
    eexists; eauto.
  Qed.

  Lemma css_brS_l_inv {X Y Z R} :
    forall (c : C Z) (k : Z -> ctree E C X) (u : ctree F D Y) x,
    css L R (BrS c k) u ->
    exists l' u', trans l' u u' /\ R (k x) u' /\ L τ l'.
  Proof.
    intros. apply H; etrans.
  Qed.

  Lemma cssim_brS_l_inv {X Y Z} :
    forall (c : C Z) (k : Z -> ctree E C X) (u : ctree F D Y) x,
    cssim L (BrS c k) u ->
    exists l' u', trans l' u u' /\ cssim L (k x) u' /\ L τ l'.
  Proof.
    intros. step in H.
    now simple apply css_brS_l_inv with (x := x) in H.
  Qed.

  Lemma css_br_l_inv {X Y}
        n (c: C n) (t : ctree F D Y) (k : n -> ctree E C X) R:
    css L R (Br c k) t ->
    forall x,
      (exists l' t', trans l' (k x) t') ->
      css L R (k x) t.
  Proof.
    cbn. intros [? ?] * PROG; split; intros * TR.
    - eapply trans_br in TR; [| reflexivity].
      apply H in TR as (? & ? & ? & ? & ?); subst.
      eauto.
    - apply PROG.
   Qed.

  Lemma cssim_br_l_inv {X Y}
        n (c: C n) (t : ctree F D Y) (k : n -> ctree E C X):
    cssim L (Br c k) t ->
    forall x,
      (exists l' t', trans l' (k x) t') ->
      cssim L (k x) t.
  Proof.
    intros. step. step in H. eapply css_br_l_inv; eauto.
  Qed.

  (* This one isn't very convenient... *)
  Lemma cssim_br_r_inv {X Y}
        n (c: D n) (t : ctree E C X) (k : n -> ctree F D Y):
    cssim L t (Br c k) ->
    forall l t', trans l t t' ->
    exists l' x t'' , trans l' (k x) t'' /\ L l l' /\ (cssim L t' t'').
  Proof.
    cbn. intros. step in H. apply H in H0 as (? & ? & ? & ? & ?); subst. inv_trans.
    do 3 eexists; eauto.
  Qed.

End WithParams.
