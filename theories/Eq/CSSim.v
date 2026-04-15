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

(*|
Complete strong simulation
==========================

[css L] refines [ss L] (from [Eq.SSim]) with a liveness-preservation
clause: the simulating side must itself be live whenever the simulated
side is:

    css L R t u  ≜  ss L R t u  ∧  (not_stuck u → not_stuck t)

Its greatest fixed point is [cssim L], notated [t (⪅ L) u] (or [t ⪅ u]
with the default [Leq]).

Because of the extra clause, [cssim] is strictly finer than [ssim]:
[cssim_ssim_subrelation] and [cssim_ssim_subrelation_gen] witness the
inclusion. Most structural rules mirror those of [ss]/[ssim] but acquire
a non-stuckness side-condition (typically [Inhabited] on a branching
type, [not_stuck] on a continuation, or a disjunction between the two
sides). Lemmas that would be false under completeness — e.g. "stuck is
simulated by anything" — are therefore absent; their sound analogues
require both sides stuck ([css_is_stuck']).

File organisation mirrors [Eq.SSim]: definition + tactics; homogeneous
theory (Reflexive/Transitive + subrelation into [ss]/[ssim]);
heterogeneous theory with [cssim_mono], [equ_clos] up-to, and
[Seq]/[equ eq] [Proper] instances on both chain elements and [css L r];
up-to bind; structural proof rules and inversion principles, using the
same [_gen] / [`R] / gfp naming convention as in [SSim.v].
|*)

Section CompleteStrongSim.

(*|
[css L R t u]: both [ss L R t u] holds, and [t] is live whenever [u] is.
The second clause is what distinguishes [css] from [ss].
|*)
 
  Program Definition css {E F C D : Type -> Type} {X Y : Type}
    (L : lrel E F X Y) : mon (@S E C X -> @S F D Y -> Prop) :=
    {| body R t u :=
        ss L R t u /\ (not_stuck u -> not_stuck t)
    |}.
  Next Obligation.
    split; eauto. intros.
    edestruct H0 as (? & ? & ? & ? & ?); repeat econstructor; eauto.
  Qed.

  #[global] Instance lequiv_css : forall {E F C D X Y}, Proper (lequiv ==> weq) (@css E F C D X Y).
  Proof.
    cbn. intros * EQ *. split.
    - intros [SIM PROG]; split; auto.
      intros.
      apply SIM in H as (? & ? & ? & ? & ?).
      ex2; split3; eauto.
      now rewrite <- EQ.
    - intros [SIM PROG]; split; auto.
      intros.
      apply SIM in H as (? & ? & ? & ? & ?).
      ex2; split3; eauto.
      now rewrite EQ.
  Qed.

End CompleteStrongSim.

Definition cssim {E F C D X Y} L :=
  (gfp (@css E F C D X Y L) : hrel _ _).

Module CSSimNotations.

  (*| css (complete simulation) notation |*)
  
  Infix "⪅" := (cssim Leq) (at level 70).
  Notation "t (⪅ [ Q ] ) u" := (cssim (Lvrel Q) t u) (at level 79).
  Notation "t (⪅ Q ) u" := (cssim Q t u) (at level 79).

  Notation "t '[⪅]' u" := (css Leq (` _) t u) (at level 90, only printing).
  Notation "t '[⪅' [ R ] ']' u" := (css (Lvrel R) (` _) t u) (at level 90, only printing).
  Notation "t '[⪅' R ']' u" := (css R (` _) t u) (at level 90, only printing).
  
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

Ltac __play_cssim := (try step); cbn; split; [intros ? ? ?TR | etrans].

Ltac __play_cssim_in H :=
  (try step in H);
  cbn in H; edestruct H as [(? & ? & ?TR & ?EQ & ?HL) ?PROG];
  clear H; [etrans |]; fold_cssim.

Ltac __eplay_cssim :=
  match goal with
  | h : cssim ?L ?u ?v |- _ => __play_cssim_in h
  | h : body (css ?L) ?R ?u ?v |- _ => __play_cssim_in h
  end.

Ltac __answer_cssim := ex2; split3; etrans.

#[local] Tactic Notation "play" := __play_cssim.
#[local] Tactic Notation "play" "in" ident(H) := __play_cssim_in H.
#[local] Tactic Notation "eplay" := __eplay_cssim.
#[local] Tactic Notation "answer" := __answer_cssim.
 
(*|
Homogeneous theory: source and target share their signature. In addition
to reflexivity / transitivity (lifted to chain elements), we record
[css_ss_subrelation] and [cssim_ssim_subrelation], making [css]/[cssim]
usable wherever [ss]/[ssim] is expected.
|*)
Section cssim_homogenous_theory.

  Context {E B : Type -> Type} {X : Type}
    {L: lrel E E X X}.

  Notation css   := (@css E E B B X X).
  Notation cssim := (@cssim E E B B X X).

(*|
    Various results on reflexivity and transitivity.
|*)
  #[global] Instance reflexive_css {R}
    (LR: Reflexive L)
    (RR: Reflexive R): Reflexive (css L R).
  Proof.
    cbn; eauto 10.
  Qed.

  #[global] Instance reflexive_chain {LR: Reflexive L} {C: Chain (css L)}: Reflexive `C.
  Proof.
    apply Reflexive_chain; typeclasses eauto.
  Qed.

  #[global] Instance transitive_css {R}
    (LT: Transitive L)
    (RT: Transitive R): Transitive (css L R).
  Proof.
    intros x y z SS1 SS2.
    play.
    - play in SS1.
      play in SS2.
      answer.
    - intros ns.
      now apply SS2,SS1 in ns.
  Qed.
  
  #[global] Instance transitive_chain {LT: Transitive L} {C: Chain (css L)}: Transitive `C.
  Proof.
    apply Transitive_chain; typeclasses eauto.
  Qed.

  #[global] Instance css_ss_subrelation R : subrelation (css L R) (ss L R).
  Proof.
    red.
    intros ?? [? ?]; auto.
  Qed.

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
  Context {E F C D: Type -> Type} {X Y: Type}.

  Notation css := (@css E F C D X Y).
  Notation cssim  := (@cssim E F C D X Y).

  Lemma cssim_mono :
    Proper (sub_lrel ==> leq) cssim.
  Proof.
    cbn; intros * SUB.
    coinduction R cih.
    intros u v CSS.
    remember CSS as TMP; clear HeqTMP;
      step in TMP; destruct TMP as [HSS HPROG].
    split; auto.
    intros l u' TR.
    eplay.
    ex2; split3; etrans.
    eapply sub_lrel_subrel; eauto.
  Qed. 

  Context {L: lrel E F X Y}.
(*|
   Strong simulation up-to [equ] is valid
   ----------------------------------------
|*)

  #[global] Instance equ_chain_goal {c: Chain (css L)} :
    Proper (equ eq ==> equ eq ==> flip impl) `c.
  Proof.
    unfold Proper, respectful,flip,impl.
    apply tower.
    - intros ? INC x y EQ x' y' EQ' ? ? ?; red.
      cbn in INC.
      eapply INC; eauto.
      apply leq_infx in H0.
      now apply H0.
    - intros a b x y EQ x' y' EQ' [SIM LIVE].
      split.
      + intros ?? tr.
        rewrite EQ in tr.
        edestruct SIM as (l' & ? & ? & ? & ?); eauto.
        exists l',x0; intuition.
        rewrite EQ'; auto.
      + intros ns.
        rewrite EQ' in ns.
        edestruct LIVE as (l' & ? & ?); eauto.
        setoid_rewrite EQ. eauto.
   Qed.

  #[global] Instance seq_chain_goal {c: Chain (css L)} :
    Proper (Seq ==> Seq ==> flip impl) `c.
  Proof.
    apply tower.
    - intros ? INC t t' HP' ? ? HP'' ?? HP'''. 
      red.
      eapply INC; eauto.
      apply leq_infx in HP'''.
      now apply HP'''.
    - intros ? INC t t' EQt u u' EQu [HS PROG].
      split.
      now rewrite EQu, EQt.
      intros ns.
      rewrite EQu in ns.
      edestruct PROG as (? & ? & ?); eauto.
      ex2; rewrite EQt; eauto.
  Qed.

  #[global] Instance seq_css_goal {r} :
    Proper (Seq ==> Seq ==> flip impl) (css L r).
  Proof.
    intros t t' tt' u u' uu'; cbn; intros [H1 H2].
    split; intros; auto.
    - edestruct5 H1.
      rewrite <- tt'; eauto.
      ex2; split3; eauto.
      now rewrite uu'.
    - edestruct3 H2.
      rewrite <- uu'; eauto.
      ex2; rewrite tt'; eauto.
  Qed.

  #[global] Instance equ_css_goal {r} :
    Proper (equ eq ==> equ eq ==> flip impl) (css L r).
  Proof.
    intros t t' tt' u u' uu'; cbn.
    intros [? ?]; split.
    - intros.
      rewrite tt' in H1. apply H in H1 as (l' & ? & ? & ? & ?).
      ex2; eauto. rewrite uu'. eauto.
    - now rewrite tt',uu'. 
  Qed.

  #[global] Instance seq_chain_ctx  {c: Chain (css L)} :
    Proper (Seq ==> Seq ==> impl) `c.
  Proof.
    apply tower.
    - intros ? INC t t' HP' ? ? HP'' ?? HP'''. 
      red.
      eapply INC; eauto.
      apply leq_infx in HP'''.
      now apply HP'''.
    - intros ? INC  t t' EQt u u' EQu [HS PROG]; split.
      now rewrite <- EQt, <- EQu.
      intros ns.
      rewrite <- EQu in ns.
      edestruct PROG as (? & ? & ?); eauto.
      ex2; rewrite <- EQt; eauto.
  Qed.

  #[global] Instance equ_chain_ctx  {c: Chain (css L)} :
    Proper (equ eq ==> equ eq ==> impl) `c.
  Proof.
    unfold Proper, respectful,flip,impl.
    apply tower.
    - intros ? INC x y EQ x' y' EQ' ? ? ?; red.
      cbn in INC.
      eapply INC; eauto.
      apply leq_infx in H0.
      now apply H0.
    - intros a b x y EQ x' y' EQ' [SIM LIVE].
      split.
      + intros ?? tr.
        rewrite <- EQ in tr.
        edestruct SIM as (l' & ? & ? & ? & ?); eauto.
        exists l',x0; intuition.
        rewrite <- EQ'; auto.
      + intros ns.
        rewrite <- EQ' in ns.
        edestruct LIVE as (l' & ? & ?); eauto.
        setoid_rewrite <- EQ. eauto.
  Qed.

  #[global] Instance seq_css_ctx {r} :
    Proper (Seq ==> Seq ==> impl) (css L r).
  Proof.
    intros t t' tt' u u' uu'; cbn; intros [H1 H2].
    split; intros; auto.
    - edestruct5 H1.
      rewrite tt'; eauto.
      ex2; split3; eauto.
      now rewrite <- uu'.
    - edestruct3 H2.
      rewrite uu'; eauto.
      ex2; rewrite <- tt'; eauto.
  Qed.

  #[global] Instance equ_css_ctx {r} :
    Proper (equ eq ==> equ eq ==> impl) (css L r).
  Proof.
    intros t t' tt' u u' uu'; cbn; intros [? ?]; split.
    - intros; rewrite <- tt' in H1. apply H in H1 as (l' & ? & ? & ? & ?).
      ex2; eauto. rewrite <- uu'. eauto.
    - now rewrite <- tt', <-uu'.
  Qed.

  Lemma cssim_ssim_subrelation_gen : forall x y, cssim L x y -> ssim L x y.
  Proof.
    red.
    coinduction r cih; intros * SB.
    step in SB; destruct SB as [fwd _].
    intros ?? TR; apply fwd in TR as (? & ? & ? & ? & ?); eauto 10.
  Qed.

End cssim_heterogenous_theory.

#[global] Instance weq_cssim : forall {E F C D X Y},
  Proper (lequiv ==> weq) (@cssim E F C D X Y).
Proof.
  cbn -[css weq]. intros. apply gfp_weq. now apply lequiv_css.
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

(*|
Specialization of [bind_ctx] to a function acting with [cssim] on the bound value,
and with the argument (pointwise) on the continuation.
|*)
  Lemma bind_chain_gen
    {E F C D: Type -> Type} {X X' Y Y': Type}
    (L : lrel E F X' Y')
    (SS: rel X Y)
    {R : Chain (@css E F C D X' Y' L)} :
    forall (t : ctree E C X) (t' : ctree F D Y)
      (k : X -> ctree E C X') (k' : Y -> ctree F D Y'),
      cssim (upd_rel L SS) t t' ->
      (forall x y, SS x y -> ` R (k x) (k' y) /\ not_stuck (k x)) ->
      ` R (bind t k) (bind t' k').
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
        apply trans_bind_inv in STEP as [(?H & ?t' & STEP & EQ) | [(Z & e & EQl & g & STEP & SEQ) | (v & STEPres & STEP)]].
        
        * subst l.
          apply tt in STEP as (? & ? & STEP' & HSIM & HRL).
          invL.
          refine_trans.
          ex2; split3.
          ++ apply trans_bind_l_τ; eauto.
          ++ rewrite EQ; apply H; auto.
             intros.
             edestruct4 kk'; eauto.
             split; eauto.
             step; auto.
          ++ etrans.
             
        * subst l.
          apply tt in STEP as (? & ? & STEP' & HSIM & HRL).
          invL.
          refine_trans.
          exists (ask f); ex; split3; etrans.
          rewrite SEQ.
          step.
          split.
          { intros ?? TR.
            pose proof trans_passive_inv' TR as (a & EQ & ->).
            rewrite EQ in TR.
            assert (TR': trans (rcv e a) (β e g) (g a)) by etrans.
            step in HSIM; apply HSIM in TR' as (l' & u' & TR' & HSIM' & HRL').
            pose proof trans_passive_inv' TR' as (b & EQ' & ->).
            exists (rcv f b); ex; split; eauto; split; cycle 1.
            { invL; etrans. }
            rewrite EQ.
            apply H.
            rewrite EQ' in HSIM'; auto.
            intros.
            edestruct4 kk'; eauto.
            split; eauto.
            now step.
          }
          {
            step in HSIM.
            destruct HSIM as [HSIM' PROD].
            intros (? & ? & TR).
            pose proof trans_passive_inv' TR as (y & EQ & EQ').
            destruct PROD as (?l' & ?t' & ?TR').
            exists (rcv f y); eauto.
            pose proof trans_passive_inv' TR' as (z & EQz & EQz').
            exists (rcv e z).
            etrans.
          }
          
        * apply tt in STEPres as (? & ? & STEP' & HSIM & HRL).
          invL.
          destruct (kk' v y) as [HSIM' HBACK']; [etrans |].
          apply HSIM' in STEP as (l' & u' & STEP'' & HSIM'' & HRL').
          exists l'; eexists; split; eauto.
          eapply trans_bind_r; eauto.
          erewrite <- trans_val_inv'; eauto.
 
      + intros (? & ? & STEP).
        apply trans_bind_inv_l in STEP as (l' & t2' & STEP).
        destruct tt' as (l'' & ? & STEP'); eauto.
        destruct l''.
        refine_trans; ex2; apply trans_bind_l_τ; etrans.
        refine_trans; ex2; eapply trans_bind_l_ask; etrans.
        exfalso; eapply trans_rcv_active_inv; eauto.

        apply trans_val_inv' in STEP' as ?. rewrite H0 in STEP'.
        pose proof STEP' as tmp.
        apply tt in tmp as (? & ? & TR & ? & ?).
        invL.
        specialize (kk' v y).
        destruct kk' as [HSIM' (l'' & ? & TR')]; auto.
        ex2.
        eapply trans_bind_r; etrans.

  Qed.

(*|
Specialization: equality on external calls, equality everywhere
|*)
  Lemma bind_chain E C D X Y X' Y'
    (RR : rel X' Y') (SS : rel X Y)
    {R : Chain (@css E E C D X' Y' (Lvrel RR))} :
    forall (t1 : ctree E C X) (t2: ctree E D Y)
      (k1 : X -> ctree E C X') (k2 : Y -> ctree E D Y'),
      t1 (⪅[SS]) t2 ->
      (forall x y, SS x y -> `R (k1 x) (k2 y) /\ not_stuck (k1 x)) ->
      `R (t1 >>= k1) (t2 >>= k2).
  Proof.
    intros.
    eapply bind_chain_gen; eauto.
  Qed.

  Lemma bind_chain_eq E C X X'
    {R : Chain (@css E E C C X' X' Leq)} :
    forall (t1 t2 : ctree E C X)
      (k1 k2 : X -> ctree E C X'),
      t1 ⪅ t2 ->
      (forall x, `R (k1 x) (k2 x) /\ not_stuck (k1 x)) ->
      `R (t1 >>= k1) (t2 >>= k2).
  Proof.
    intros.
    eapply bind_chain_gen; eauto.
    intros ??<-; auto.
  Qed.

(*|
Specializations to the gfp
|*)
  Lemma cssim_bind_gen E F C D X Y X' Y'
    L (SS : rel X Y) 
    (t1 : ctree E C X) (t2: ctree F D Y)
    (k1 : X -> ctree E C X') (k2 : Y -> ctree F D Y'):
    t1 (⪅ upd_rel L SS) t2 ->
    (forall x y, SS x y -> k1 x (⪅ L) k2 y /\ not_stuck (k1 x)) ->
    t1 >>= k1 (⪅ L) t2 >>= k2.
  Proof.
    intros.
    eapply bind_chain_gen; eauto.
  Qed.

  Lemma cssim_bind E C D X Y X' Y'
    (RR : rel X' Y') (SS : rel X Y) 
    (t1 : ctree E C X) (t2: ctree E D Y)
    (k1 : X -> ctree E C X') (k2 : Y -> ctree E D Y'):
    t1 (⪅ [SS]) t2 ->
    (forall x y, SS x y -> k1 x (⪅ [RR]) k2 y /\ not_stuck (k1 x)) ->
    t1 >>= k1 (⪅ [RR]) t2 >>= k2.
  Proof.
    intros.
    eapply bind_chain_gen; eauto.
  Qed.

  Lemma cssim_bind_eq {E C D: Type -> Type} {X X': Type}
    (t1 : ctree E C X) (t2: ctree E D X)
    (k1 : X -> ctree E C X') (k2 : X -> ctree E D X'):
    t1 ⪅ t2 ->
    (forall x, k1 x ⪅ k2 x /\ not_stuck (k1 x)) ->
    t1 >>= k1 ⪅ t2 >>= k2.
  Proof.
    intros.
    eapply cssim_bind; eauto.
    intros ?? ->; auto.
  Qed.

End bind.

(*|
And in particular, we can justify rewriting [⪅] to the left of a [bind].

NOTE: we shouldn't have to impose [eq] to the right.
|*)
#[global] Instance cssim_bind_chain {E C X Y}
  {R : Chain (@css E E C C Y Y Leq)} :
  Proper ((fun t u => cssim Leq (α t) (α u)) ==>
          (pointwise_relation _ (fun t u => ` R (α t) (α u) /\ not_stuck t)) ==> `R) (@bind E C X Y).
Proof.
  repeat intro; eapply bind_chain_gen; eauto.
  intros ?? <-; auto.
Qed.

(*|
Structural proof rules
======================
Same three-layer shape as in [SSim.v] ([css_*_gen] / [css_*] / [cssim_*]).
Compared to [ss]/[ssim] the rules typically carry an extra non-stuckness
side-condition: [Inhabited] on a [Br]'s index (to witness progress),
[not_stuck] on a branch, or a disjunction between the two sides.
Inversion principles ([cssim_*_inv]) additionally exploit the liveness
clause — e.g. [cssim_stuck_inv] is an *iff*, unlike its [ssim] analogue.
|*)
Section Proof_Rules.

  Context {E F C D: Type -> Type} {X Y : Type}.

(*|
Stuck ctrees can be simulated by anything.
|*)
 
  Lemma css_is_stuck L R : forall (t: @S E C X) (u: @S F D Y),
      css L R t u -> is_stuck t <-> is_stuck u.
  Proof.
    intros * [SIM LIVE]; split; intros IS ? ? TR.
    - destruct LIVE as (? & ? & ?); eauto. now apply IS in H.
    - apply SIM in TR as (? & ? & ? & ? & ?). now apply IS in H.
  Qed.

  Lemma cssim_is_stuck L :  forall (t: @S E C X) (u: @S F D Y),
      t (⪅ L) u -> is_stuck t <-> is_stuck u.
  Proof.
    intros. step in H. eapply css_is_stuck; eauto.
  Qed.

  Lemma css_is_stuck' L R : forall (t : @S E C X) (u: @S F D Y),
      is_stuck t -> is_stuck u -> css L R t u.
  Proof.
    split; intros.
    - cbn. intros. now apply H in H1.
    - edestruct3 H1. now apply H0 in H2.
  Qed.

  Lemma cssim_is_stuck' L : forall (t : @S E C X) (u: @S F D Y),
      is_stuck t -> is_stuck u -> t (⪅ L) u.
  Proof.
    intros. step. now apply css_is_stuck'.
  Qed.
 
(*|
Ret nodes
|*)
  Lemma css_ret_gen (x : X) (y : Y) L R :
    R (α Stuck) (α Stuck) ->
    (Proper (Seq ==> Seq ==> impl) R) ->
    RR L x y ->
    css L R (Ret x : ctree E C X) (Ret y : ctree F D Y).
  Proof.
    intros HS HP HR; split; [intros l u TR |].
    - inv_trans. subst.
      ex2; intuition.
      now rewrite EQ.
    - intros; auto using ret_not_stuck.
  Qed.
  
  Lemma css_ret (x : X) (y : Y) L
    {R : Chain (@css E F C D X Y L)} :
    RR L x y ->
    css L `R (Ret x : ctree E C X) (Ret y : ctree F D Y).
  Proof.
    intros HR; split.
    - apply ss_ret_gen; auto.
      step; eapply css_is_stuck'; apply stuck_is_stuck.
      typeclasses eauto.
    - eauto.
  Qed.
  
  Lemma cssim_ret (x : X) (y : Y) L :
    RR L x y ->
    cssim L (Ret x : ctree E C X) (Ret y : ctree F D Y).
  Proof.
    intros.
    step. now apply css_ret.
  Qed.
    
(*|
 The vis nodes are deterministic from the perspective of the labeled
 transition system, stepping is hence symmetric and we can just recover
 the itree-style rule.
|*)
  Lemma css_vis {Z Z'} `{Inhabited Z} (e : E Z) (f: F Z')
    (k : Z -> ctree E C X) (k' : Z' -> ctree F D Y) L
    {R : Chain (@css E F C D X Y L)}
    (HRask : Rask L e f)
    (HRrcv : forall x, exists y, `R (k x) (k' y) /\ Rrcv L e f x y) :
    css L ` R (Vis e k) (Vis f k').
  Proof.
    split.
    - intros ?? TR; inv_trans.
      ex2; intuition.
      rewrite EQ.
      step.
      split.
      + intros l u TR.
        inv_trans; subst.
        destruct (HRrcv x) as (y & ? & ?).
        ex2; intuition.
        rewrite EQ0; eauto.
        etrans.
      + unshelve eauto.
        exact inhabitant.
    - eauto.
  Qed.

  Lemma cssim_vis {Z Z'} `{Inhabited Z} (e : E Z) (f: F Z')
    (k : Z -> ctree E C X) (k' : Z' -> ctree F D Y) L
    (HRask : Rask L e f)
    (HRrcv : forall x, exists y, cssim L (k x) (k' y) /\ Rrcv L e f x y) :
    cssim L (Vis e k) (Vis f k').
  Proof.
    intros. step. apply css_vis; auto.
  Qed.

  (* Useful special case: over the same type return type,
     we usually pick the identity *)
  Lemma css_vis_id {Z} `{Inhabited Z} (e : E Z) (f: F Z)
    (k : Z -> ctree E C X) (k' : Z -> ctree F D Y) L
    {R : Chain (@css E F C D X Y L)} 
    (HRask : Rask L e f)
    (HRrcv : forall z, ` R (k z) (k' z) /\ Rrcv L e f z z) :
    css L ` R (Vis e k) (Vis f k').
  Proof.
    eapply css_vis; eauto.
  Qed.
  
  Lemma cssim_vis_id {Z} `{Inhabited Z} (e : E Z) (f : F Z)
    (k : Z -> ctree E C X) (k' : Z -> ctree F D Y) L
    (HRask : Rask L e f)
    (HRrcv : forall x, cssim L (k x) (k' x) /\ Rrcv L e f x x) :
    cssim L (Vis e k) (Vis f k').
  Proof.
    intros. step. now apply css_vis_id.
  Qed.


(*|
Invisible nodes
|*)
  (* Here we need a stronger lemma quantifying over arbitrary relations [R] and not just elements of the Chain in order to lift things to cssim as we don't unlock cssim in the structural subterm *)
  Lemma css_br_l_gen {Z} `{Inhabited Z} (c : C Z)
    (k : Z -> ctree E C X) (t': ctree F D Y) R L:
    (forall x, css L R (k x) t') ->
    css L R (Br c k) t'.
  Proof.
    intros EQs.
    split.
    - apply ss_br_l_gen; intros z; destruct (EQs z); auto.
    - intros NS.
      destruct (EQs inhabitant) as [_ PROG].
      edestruct3 PROG; auto.
      eauto.
  Qed.

  Lemma css_br_l {Z} `{Inhabited Z} (c : C Z)
    (k : Z -> ctree E C X) (t: ctree F D Y) L 
    {R : Chain (@css E F C D X Y L)} :
    (forall x,  css L `R (k x) t) ->
    css L `R (Br c k) t.
  Proof.
    intros; now apply css_br_l_gen.
  Qed.

  Lemma cssim_br_l {Z} `{Inhabited Z} (c : C Z)
    (k : Z -> ctree E C X) (t: ctree F D Y) L :
    (forall x, cssim L (k x) t) ->
    cssim L (Br c k) t.
  Proof.
    intros SIM; step; eapply css_br_l.
    now intros z; specialize (SIM z); step in SIM.
  Qed.

  Lemma css_br_r_gen {Z} (c : D Z) x
    (k : Z -> ctree F D Y) (t: ctree E C X) R L:
    (not_stuck t \/ not_stuck (k x)) ->
    css L R t (k x) ->
    css L R t (Br c k).
  Proof.
    cbn. intros NS [SIM PROG]; split.
    - intros; edestruct5 SIM; eauto 10.
    - destruct NS; auto.
  Qed.

  Lemma css_br_r {Z} (c : D Z) x
        (k : Z -> ctree F D Y) (t: ctree E C X) L
        {R : Chain (@css E F C D X Y L)} :
    (not_stuck t \/ not_stuck (k x)) ->
    css L `R t (k x) ->
    css L `R t (Br c k).
  Proof.
    apply css_br_r_gen.
  Qed.

  Lemma cssim_br_r {Z} (c : D Z) x
        (k : Z -> ctree F D Y) (t: ctree E C X) L :
    (not_stuck t \/ not_stuck (k x)) ->
    cssim L t (k x) ->
    cssim L t (Br c k).
  Proof.
    intros. step. apply css_br_r_gen with (x := x); auto.
    now step in H0.
  Qed.

  Lemma css_br_gen {A B} (c: C A) (d: D B)
    (k : A -> ctree E C X) (k' : B -> ctree F D Y) R L :
    (exists x, not_stuck (k x)) ->
    (forall x, exists y, css L R (k x) (k' y)) ->
    css L R (Br c k) (Br d k').
  Proof.
    intros [a NS] EQs.
    split.
    - apply ss_br_l_gen.
      intros x.
      destruct (EQs x) as [x' ?].
      destruct H.
      eapply ss_br_r_gen; eauto.
    - intros NS'.
      destruct NS as (? & ? & TR').
      ex2; eauto.
  Qed.

  Lemma css_br {A B} (c: C A) (d: D B)
    (k : A -> ctree E C X) (k' : B -> ctree F D Y) L 
    {R : Chain (@css E F C D X Y L)} :
    (exists x, not_stuck (k x)) ->
    (forall x, exists y, css L `R (k x) (k' y)) ->
    css L `R (Br c k) (Br d k').
  Proof.
    apply css_br_gen.
  Qed.

  Lemma cssim_br {A B} (c: C A) (d: D B)
    (k : A -> ctree E C X) (k' : B -> ctree F D Y) L :
    (exists x, not_stuck (k x)) ->
    (forall x, exists y, cssim L (k x) (k' y)) ->
    cssim L (Br c k) (Br d k').
  Proof.
    intros NS SIM. step. apply css_br_gen; auto.
    intros. destruct (SIM x). step in H. eauto.
  Qed.

  Lemma css_br_id {A} (c: C A) (d: D A)
    (k : A -> ctree E C X) (k': A -> ctree F D Y) L
    {R : Chain (@css E F C D X Y L)} :
    (exists x, not_stuck (k x)) ->
    (forall x, css L `R (k x) (k' x)) ->
    css L `R (Br c k) (Br d k').
  Proof.
    intros; apply css_br; eauto.
  Qed.

  Lemma cssim_br_id {A} (c: C A) (d: D A)
    (k : A -> ctree E C X) (k': A -> ctree F D Y) L :
    (exists x, not_stuck (k x)) ->
    (forall x, cssim L (k x) (k' x)) ->
    cssim L (Br c k) (Br d k').
  Proof.
    intros. apply cssim_br; eauto.
  Qed.

  Lemma css_guard_l_gen 
    (t: ctree E C X) (t': ctree F D Y) R L:
    css L R t t' ->
    css L R (Guard t) t'.
  Proof.
    intros [SIM PROG]; split.
    - apply ss_guard_l_gen; auto.
    - intros NS; edestruct3 PROG; auto.
      eauto.
  Qed.

  Lemma css_guard_l
    (t: ctree E C X) (t': ctree F D Y) L
    {R : Chain (@css E F C D X Y L)} :
    css L `R t t' ->
    css L `R (Guard t) t'.
  Proof.
    intros; now apply css_guard_l_gen.
  Qed.

  Lemma cssim_guard_l 
    (t: ctree E C X) (t': ctree F D Y) L:
    cssim L t t' ->
    cssim L (Guard t) t'.
  Proof.
    intros; step; apply css_guard_l; step in H; auto.
  Qed.

  Lemma css_guard_r_gen 
    (t: ctree E C X) (t': ctree F D Y) R L :
    css L R t t' ->
    css L R t (Guard t').
  Proof.
    intros [SIM PROG]; split.
    - apply ss_guard_r_gen; auto.
    - intros (? & ? & TR); inv_trans; destruct PROG; eauto.
  Qed.

  Lemma css_guard_r
    (t: ctree E C X) (t': ctree F D Y) L
    {R : Chain (@css E F C D X Y L)} :
    css L `R t t' ->
    css L `R t (Guard t').
  Proof.
    now apply css_guard_r_gen.
  Qed.

  Lemma cssim_guard_r 
    (t: ctree E C X) (t': ctree F D Y) L :
    cssim L t t' ->
    cssim L t (Guard t').
  Proof.
    intros; step; apply css_guard_r; step in H; auto.
  Qed.

  Lemma cssim_guard 
    (t: ctree E C X) (t': ctree F D Y) L :
    cssim L t t' ->
    cssim L (Guard t) (Guard t').
  Proof.
    intros.
    now apply cssim_guard_l, cssim_guard_r.
  Qed.

(*|
Internal transitions
|*)
  Lemma css_step_gen
    (t: ctree E C X) (t': ctree F D Y) L R :
    (Proper (Seq ==> Seq ==> impl) R) ->
    R (α t) (α t') ->
    css L R (Step t) (Step t').
  Proof.
    intros HP HR; split; [intros ???; inv_trans; subst |].
    - ex2; intuition.
      now rewrite EQ.
    - intros; auto using step_not_stuck.
  Qed.

  Lemma css_step 
    (t: ctree E C X) (t': ctree F D Y) L
    {R : Chain (@css E F C D X Y L)} :
    ` R t t' ->
    css L ` R (Step t) (Step t').
  Proof.
    intros HR; split.
    - apply ss_step_gen; auto.
      typeclasses eauto.
    - eauto. 
  Qed.

  Lemma cssim_step
    (t: ctree E C X) (t': ctree F D Y) L :
    cssim L t t' ->
    cssim L (Step t) (Step t').
  Proof.
    now intros; step; apply css_step.
  Qed.

  Lemma css_brS {Z Z'} `{Inhabited Z} (c : C Z) (c' : D Z')
    (k : Z -> ctree E C X) (k' : Z' -> ctree F D Y) L 
    {R : Chain (@css E F C D X Y L)} :
    (forall x, exists y, ` R (k x) (k' y)) ->
    css L ` R (BrS c k) (BrS c' k').
  Proof.
    intros * SIM.
    eapply css_br.
    exists inhabitant; eauto.
    intros x; specialize (SIM x) as [y ?].
    exists y.
    eapply css_step; auto.
  Qed.

  Lemma cssim_brS {Z Z'} `{Inhabited Z} (c : C Z) (c' : D Z')
    (k : Z -> ctree E C X) (k' : Z' -> ctree F D Y) L :
    (forall x, exists y, cssim L (k x) (k' y)) ->
    cssim L (BrS c k) (BrS c' k').
  Proof.
    now intros; step; apply css_brS.
  Qed.

  Lemma css_brS_id {Z} `{Inhabited Z} (c : C Z) (d : D Z)
    (k: Z -> ctree E C X) (k': Z -> ctree F D Y) L 
    {R : Chain (@css E F C D X Y L)} :
    (forall x, `R (k x) (k' x)) ->
    css L ` R (BrS c k) (BrS d k').
  Proof.
    intros; apply css_brS; eauto.
  Qed.

  Lemma cssim_brS_id {Z} `{Inhabited Z} (c : C Z) (d : D Z)
    (k: Z -> ctree E C X) (k': Z -> ctree F D Y) L :
    (forall x, cssim L (k x) (k' x)) ->
    cssim L (BrS c k) (BrS d k').
  Proof.
    intros; apply cssim_brS; eauto.
  Qed.

(*|
    Note that with visible schedules, an nary-spins refines another only
    if it is empty, or if neither are empty.
|*)
  Lemma cssim_spinS_nonempty :
    forall {Z Z'} L (x: Z) (y: Z') (c: C Z) (c': D Z'),
      @cssim E F C D X Y L (spinS_gen c) (spinS_gen c').
  Proof.
    intros until L; intros x y.
    coinduction S CIH.
    split.
    - intros * ?? TR.
      rewrite ctree_eta in TR; cbn in TR.
      inv_trans.
      ex2; split3; subst; etrans.
      rewrite ctree_eta; cbn; etrans.
      now rewrite EQ.
    - intros.
      rewrite ctree_eta; cbn.
      eauto.
  Qed.

(*|
Inversion principles
--------------------
TODO: these principles are mirrored on ssim directly. We should be able to derive additional liveness information from them in some cases.
|*)
  
  Lemma cssim_stuck_inv L (t : ctree E C X) (u : ctree F D Y)
    (CSS :@cssim E F C D X Y  L t u) :
    is_stuck t <-> is_stuck u.
  Proof.
    split.
    - intros IS l u' TR.
      step in CSS.
      destruct CSS as [SS PROG].
      eapply not_stuck_is_stuck.
      apply PROG.
      eauto.
      auto.
    - intros IS l t' TR.
      step in CSS.
      apply CSS in TR.
      edestruct5 TR.
      eapply IS; eauto.
  Qed.

  Lemma cssim_ret_l_inv L :
    forall r (u : ctree F D Y)
      (CSS : @cssim E F C D X Y L (Ret r) u),
      exists r' u', trans (val r') u u' /\ RR L r r'.
  Proof.
    intros. step in CSS.
    destruct CSS as [SIM PROG].
    edestruct5 SIM; etrans.
    invL.
    ex2; split; etrans.
  Qed.
 
  Lemma cssim_ret_inv L (r1 : X) (r2 : Y)
    (CSS : @cssim E F C D X Y L (Ret r1) (Ret r2)) :
    L (val r1) (val r2).
  Proof.
    eplay.
    now inv_trans.
  Qed.

  Lemma cssim_vis_inv {X1 X2} L
    (e : E X1) (f : F X2)
    (k1 : X1 -> ctree E C X) (k2 : X2 -> ctree F D Y)
    (CSS : cssim L (Vis e k1) (Vis f k2)) :
    Rask L e f /\
      (forall x, exists y, Rrcv L e f x y /\ cssim L (k1 x) (k2 y)).
  Proof.
    eplay; inv_trans; invL.
    split; auto.
    intros x.
    unshelve eplay. exact x.
    invL.
    inv_trans.
    exists x1; split; eauto.
    dependent induction EQl; eauto.
  Qed.
  
  Lemma cssim_vis_l_inv {Z L} :
    forall (e : E Z) (k : Z -> ctree E C X) u,
      @cssim E F C D X Y L (Vis e k) u ->
      exists Z' (f : F Z') k',
        trans (ask f) u (β f k') /\
          Rask L e f /\
          forall x, exists y, cssim L (k x) (k' y) /\ Rrcv L e f x y.
  Proof.
    intros.
    eplay; invL; refine_trans.
    ex3; split3; etrans.
    intros z.
    unshelve eplay; [eassumption |]; inv_trans; invL.
    ex; split; etrans.
  Qed.

  Lemma cssim_guard_l_inv L (t1 : ctree E C X) (t2 : ctree F D Y) :
    cssim L (Guard t1) t2 ->
    cssim L t1 t2.
  Proof.
    intros CSS; play.
    - eplay.
      ex2; split3; etrans.
    - intros NS.
      step in CSS; destruct CSS as [_ PROG]; edestruct3 PROG; eauto.
      inv_trans; eauto.
  Qed.

  Lemma cssim_guard_r_inv L (t1 : ctree E C X) (t2 : ctree F D Y) :
    cssim L t1 (Guard t2) ->
    cssim L t1 t2.
  Proof.
    intros CSS; play.
    - eplay; inv_trans.
      ex2; split3; etrans.
    - intros (? & ? & ?).
      step in CSS; destruct CSS as [_ PROG]; edestruct3 PROG; eauto.
  Qed.

  Lemma cssim_guard_inv L (t1 : ctree E C X) (t2 : ctree F D Y) :
    cssim L (Guard t1) (Guard t2) ->
    cssim L t1 t2.
  Proof.
    intros.
    now apply cssim_guard_r_inv, cssim_guard_l_inv.
  Qed.

  Lemma cssim_br_l_inv L Z
    (c: C Z) (t : ctree F D Y) (k : Z -> ctree E C X):
    cssim L (Br c k) t ->
    forall x, not_stuck (k x) -> cssim L (k x) t.
  Proof.
    intros CSS ? NS; play.
    eplay; eauto.
  Qed.

  Lemma cssim_br_r_inv L Z
    (d: D Z) (t : ctree E C X) (k : Z -> ctree F D Y):
    cssim L t (Br d k) ->
    forall l t', trans l t t' ->
    exists x l' u', trans l' (k x) u' /\
               cssim L t' u' /\
               L l l'.
  Proof.
    intros CSS * TR.
    eplay; inv_trans.
    ex3; split3; eauto.
  Qed.

  Lemma cssim_step_inv L (t1 : ctree E C X) (t2 : ctree F D Y) :
    cssim L (Step t1) (Step t2) ->
    cssim L t1 t2.
  Proof.
    intros; eplay; inv_trans; etrans.
  Qed.

  Lemma cssim_step_l_inv L (t1 : ctree E C X) (t2 : ctree F D Y) :
    cssim L (Step t1) t2 ->
    exists t2', trans τ t2 t2' /\ cssim L t1 t2'.
  Proof.
    intros; eplay; invL; refine_trans.
    ex; split; etrans.
  Qed.

  Lemma cssim_brS_inv L
    A B (c: C A) (d: D B) (k1 : A -> ctree E C X) (k2 : B -> ctree F D Y) :
    cssim L (BrS c k1) (BrS d k2) ->
    forall i1, exists i2, cssim L (k1 i1) (k2 i2).
  Proof.
    intros EQ i1.
    eplay; invL; inv_trans; eauto.
  Qed.

  Lemma cssim_brS_l_inv L
    A (c: C A) (k1 : A -> ctree E C X) (t2 : ctree F D Y) :
    cssim L (BrS c k1) t2 ->
    forall i, exists t2', trans τ t2 t2' /\ cssim L (k1 i) t2'.
  Proof.
    intros EQ i1.
    eplay; invL; inv_trans; eauto.
  Qed.

End Proof_Rules.

