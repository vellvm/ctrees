(*| HS
Strong bisimilarity
===================

Companion to [Eq.SSim] / [Eq.CSSim]. [sb L] is the symmetric variant of
strong simulation:

    sb L R t u  ≜  ss L R t u  ∧  ss (flipL L) (flip R) u t

Its greatest fixed point is [sbisim L], notated [t (σ L) u] (or [t ~ u]
with the default [eq] relation on labels).

File organisation mirrors [Eq.SSim]:
- definition of [sb]/[sbisim], notations, folding/step/coinduction/play
  tactics;
- homogeneous theory (Reflexive / Symmetric / Transitive / PreOrder /
  Equivalence, both on [sb L R] and on chain elements);
- heterogeneous theory: [sbisim_mono], [equ_clos]/[sbisim_clos] up-to
  principles, [Proper] instances for rewriting [Seq] and [equ eq] on
  either side, subrelations to [ssim] and [cssim];
- up-to bind;
- structural proof rules and inversion principles, using the same
  [sb_*_gen] / [`R] / [sbisim_*] naming convention as [SSim.v];
- sanity checks ([spinS], [br2], [brS2] laws) and incompatibility
  lemmas;
- interaction with [ss]/[ssim] and [css]/[cssim].

All proofs are [Admitted.] in this draft.
|*)

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
     Eq.SSim
     Eq.CSSim.

From RelationAlgebra Require Export
     rel srel.

Import CoindNotations.
Import CTree.
Set Implicit Arguments.

(*|
Definition
----------
|*)
Section StrongBisim.
  Context {E F C D : Type -> Type} {X Y : Type}.

  Program Definition sb (L : lrel E F X Y) :
    mon (@S E C X -> @S F D Y -> Prop) :=
    {| body R t u := ss L R t u /\ ss (flipL L) (flip R) u t |}.
  Next Obligation.
    split; intros; [edestruct H0 as (? & ? & ?) | edestruct H1 as (? & ? & ?)]; eauto; eexists; eexists; intuition; eauto.
  Qed.

  #[global] Instance lequiv_sb : Proper (lequiv ==> weq) sb.
  Proof.
    cbn -[sb]. intros * EQ *; split.
    - intros [For Bac]; split.
      eapply lequiv_ss in EQ.
      now apply EQ in For.
      eapply lequiv_ss; [| eauto].
      now apply lequiv_flipL.
    - intros [For Bac]; split.
      eapply lequiv_ss; eauto.
      eapply lequiv_ss; [| eauto].
      now apply lequiv_flipL.
  Qed.

End StrongBisim.

Definition sbisim {E F C D X Y} L :=
  (gfp (@sb E F C D X Y L) : hrel _ _).

Module SBisimNotations.

  Notation sbisimeq := (sbisim Leq).
  Infix "≃" := (sbisim Leq) (at level 70).
  Notation "t (≃ [ Q ] ) u" := (sbisim (Lvrel Q) t u) (at level 79).
  Notation "t (≃ L ) u" := (sbisim L t u) (at level 79).

  Notation "t '[≃]' u" := (sb Leq _ t u) (at level 90, only printing).
  Notation "t '[≃' [ R ] ']' u" := (sb (Lvrel R) _ t u) (at level 90, only printing).
  Notation "t '[≃' R ']' u" := (sb R _ t u) (at level 90, only printing).

End SBisimNotations.

Import SBisimNotations.
Import CTreeNotations.
Import EquNotations.

(*|
Hook letting [coq-coinduction]'s symmetric tactic fire on homogeneous
bisimulations.
|*)
#[global] Instance sbisim_sym {E C X L} :
  Symmetric L ->
  Symmetrical converse (@sb E E C C X X (Lvrel L)) (@ss E E C C X X (Lvrel L)).
Proof.
  intros SYM. intros RR u v. split; intros HSIM.
  - destruct HSIM as [F B]. split.
    + apply F.
    + cbn. intros l v' TR.
      apply B in TR as (l' & u' & TR & HR & HR').
      ex2; split3; eauto.
      symmetry.
      pose proof flipL_flip (Lvrel L) l l' as G.
      now apply G.
  - destruct HSIM as [F B]. split.
    + apply F.
    + intros l v' TR.
      apply B in TR as (l' & u' & TR & HR & HR').
      ex2; split3; eauto.
      pose proof flipL_flip (Lvrel L) l l' as G.
      apply G.
      now symmetry.
Qed.

(*|
Tactics
-------
|*)
Ltac fold_sbisim :=
  repeat
    match goal with
    | h: context[gfp (@sb ?E ?F ?C ?D ?X ?Y ?L)] |- _ => fold (@sbisim E F C D X Y L) in h
    | |- context[gfp (@sb ?E ?F ?C ?D ?X ?Y ?L)]      => fold (@sbisim E F C D X Y L)
    end.

Tactic Notation "__step_sbisim" :=
  match goal with
  | |- context[@sbisim ?E ?F ?C ?D ?X ?Y ?L] =>
      unfold sbisim;
      step;
      fold (@sbisim E F C D X Y L)
  end.
#[local] Tactic Notation "step" := __step_sbisim || __step_cssim || __step_ssim || step.

Ltac __step_in_sbisim H :=
  match type of H with
  | context[@sbisim ?E ?F ?C ?D ?X ?Y ?L] =>
      unfold sbisim in H;
      step in H;
      fold (@sbisim E F C D X Y L) in H
  end.
#[local] Tactic Notation "step" "in" ident(H) := __step_in_sbisim H || step in H.

Tactic Notation "__coinduction_sbisim" simple_intropattern(r) simple_intropattern(cih) :=
  first [unfold sbisim at 4 | unfold sbisim at 3 | unfold sbisim at 2 | unfold sbisim at 1]; coinduction r cih.
#[local] Tactic Notation "coinduction" simple_intropattern(r) simple_intropattern(cih) :=
  __coinduction_sbisim r cih || __coinduction_cssim r cih || __coinduction_ssim r cih || coinduction r cih.

Ltac __play_sbisim := (try step); split; cbn; intros ? ? ?TR.

Ltac __playL_sbisim H :=
  (try step in H);
  let Hf := fresh "Hf" in
  destruct H as [Hf _];
  cbn in Hf; edestruct Hf as (? & ? & ?TR & ?EQ & ?);
  clear Hf; [etrans |].

Ltac __playR_sbisim H :=
  (try step in H);
  let Hb := fresh "Hb" in
  destruct H as [_ Hb];
  cbn in Hb; edestruct Hb as (? & ? & ?TR & ?EQ & ?);
  clear Hb; [etrans |].

Ltac __eplayL_sbisim :=
  match goal with
  | h : @sbisim ?E _ ?C _ ?X _ ?RR _ _ |- _ => __playL_sbisim h
  | h : body (sb ?L) ?R _ _ |- _ => __playL_sbisim h
  end.

Ltac __eplayR_sbisim :=
  match goal with
  | h : @sbisim ?E _ ?C _ ?X _ ?RR _ _ |- _ => __playR_sbisim h
  | h : body (sb ?L) ?R _ _ |- _ => __playR_sbisim h
  end.

Ltac __answer_sbisim := ex2; split3; etrans.

#[local] Tactic Notation "play"                 := __play_sbisim.
#[local] Tactic Notation "playL" "in" ident(H)  := __playL_sbisim H.
#[local] Tactic Notation "playR" "in" ident(H)  := __playR_sbisim H.
#[local] Tactic Notation "play"  "in" ident(H)  := first [playL in H; [] | playR in H; []].
#[local] Tactic Notation "eplayL"               := __eplayL_sbisim.
#[local] Tactic Notation "eplayR"               := __eplayR_sbisim.
#[local] Tactic Notation "eplay"                := first [eplayL; [] | eplayR; []].
#[local] Tactic Notation "answer"               := __answer_sbisim.

(*|
Homogeneous theory
------------------
|*)
Section sbisim_homogenous_theory.
  Context {E B : Type -> Type} {X : Type}
          {L : lrel E E X X}.

  Notation sb    := (@sb    E E B B X X).
  Notation sbisim := (@sbisim E E B B X X).

  #[global] Instance reflexive_sb {R}
    (LR : Reflexive L) (RR : Reflexive R) : Reflexive (sb L R).
  Proof.
    split. reflexivity.
    cbn; eauto 10.
  Qed.

  #[global] Instance reflexive_chain {LR : Reflexive L} {C : Chain (sb L)} : Reflexive `C.
  Proof.
    apply Reflexive_chain; typeclasses eauto.
  Qed.

  #[global] Instance symmetric_sb {R}
    (LS : Symmetric L) (RS : Symmetric R) : Symmetric (sb L R).
  Proof.
    intros u v SB.
    play; eplay.
    answer; now apply flipL_flip.
    answer; now apply flipL_flip.
  Qed.

  #[global] Instance symmetric_chain {LS : Symmetric L} {C : Chain (sb L)} : Symmetric `C.
  Proof.
    apply Symmetric_chain; typeclasses eauto.
  Qed.

  #[global] Instance transitive_sb {R}
    (LT : Transitive L) (RT : Transitive R) : Transitive (sb L R).
  Proof.
    intros x y z SS1 SS2.
    play.
    - play in SS1; play in SS2; answer.
    - play in SS2; play in SS1; answer.
      apply (flipL_flip L) in H,H0; apply flipL_flip; cbn in *; eauto.
  Qed.

  #[global] Instance transitive_chain {LT : Transitive L} {C : Chain (sb L)} : Transitive `C.
  Proof.
    apply Transitive_chain; typeclasses eauto.
  Qed.

  #[global] Instance preOrder_sb {R}
    (LE : PreOrder L) (RE : PreOrder R) : PreOrder (sb L R).
  Proof. split; typeclasses eauto. Qed.

  #[global] Instance PreOrder_chain {LPO : PreOrder L} {C : Chain (sb L)} : PreOrder `C.
  Proof. split; typeclasses eauto. Qed.

  #[global] Instance equivalence_sb {R}
    (LE : Equivalence L) (RE : Equivalence R) : Equivalence (sb L R).
  Proof. split; typeclasses eauto. Qed.

  #[global] Instance equivalence_chain {LE : Equivalence L} {C : Chain (sb L)} : Equivalence `C.
  Proof. split; typeclasses eauto. Qed.

End sbisim_homogenous_theory.

(*|
Heterogeneous theory
--------------------
|*)
Section sbisim_heterogenous_theory.
  Arguments label : clear implicits.
  Context {E F C D : Type -> Type} {X Y : Type}.

  Notation sb     := (@sb     E F C D X Y).
  Notation sbisim := (@sbisim E F C D X Y).

  Lemma sbisim_mono : Proper (sub_lrel ==> leq) sbisim.
  Proof. 
    cbn; intros RR SS SUB.
    coinduction R cih.
    intros u v HSB; split.
    - intros ? ? TR; eplay; answer.
      eapply sub_lrel_subrel; eauto.
    - intros ? ? TR; cbn.
      eplay. answer.
      apply lequiv_sub_lrel in SUB.
      eapply sub_lrel_subrel; eauto.
  Qed.

  Context {L : lrel E F X Y}.

  (*| Up-to [equ_clos]. |*)
  (* Lemma equ_clos_chain {c : Chain (sb L)} : *)
  (*   forall x y, equ_clos `c x y -> `c x y. *)
  (* Proof. *)
  (*   apply tower. *)
  (*   - intros ? INC x y [x' y' x'' y'' EQ' EQ''] ??. red. *)
  (*     apply INC; auto. *)
  (*     econstructor; eauto. *)
  (*     apply leq_infx in H. *)
  (*     now apply H. *)
  (*   - clear. *)
  (*     intros c IH x y []; split. *)
  (*     + intros l z x'z. *)
  (*       rewrite Equt in x'z. *)
  (*       apply HR in x'z as (? & ? & ? & ? & ?). *)
  (*       do 2 eexists; intuition; eauto. *)
  (*       rewrite <- Equu; eauto. *)
  (*     + intros l z x'z. *)
  (*       rewrite <- Equu in x'z. *)
  (*       apply HR in x'z as (? & ? & ? & ? & ?). *)
  (*       do 2 eexists; intuition; eauto. *)
  (*       rewrite Equt; eauto. *)
  (* Qed. *)

  #[global] Instance seq_chain_goal {c : Chain (sb L)} :
    Proper (Seq ==> Seq ==> flip impl) `c.
  Proof.
    apply tower.
    - intros ? INC t t' HP' ? ? HP'' ?? HP'''. 
      red.
      eapply INC; eauto.
      apply leq_infx in HP'''.
      now apply HP'''.
    - intros ? INC  t t' EQt u u' EQu HBS; split; intros l v TR.
      + rewrite EQt in TR.
        eplay.
        answer.
        now rewrite EQu.
      + rewrite EQu in TR.
        eplay.
        answer.
        now rewrite EQt.
  Qed.

  #[global] Instance equ_chain_goal {c : Chain (sb L)} :
    Proper (equ eq ==> equ eq ==> flip impl) `c.
  Proof.
    repeat intro; eapply seq_chain_goal; [| |eauto]; eauto.
  Qed.

  #[global] Instance seq_sb_goal {r} :
    Proper (Seq ==> Seq ==> flip impl) (sb L r).
  Proof.  
    intros t t' tt' u u' uu' HBS; split; intros ?? TR.
    - rewrite tt' in TR.
      eplay; answer.
      now rewrite uu'.
    - rewrite uu' in TR.
      eplay; answer.
      now rewrite tt'.
  Qed.  
  
  #[global] Instance equ_sb_goal {r} :
    Proper (equ eq ==> equ eq ==> flip impl) (sb L r).
  Proof.
    repeat intro; eapply seq_sb_goal; [| | eauto]; eauto.
  Qed.
  
  #[global] Instance sbisim_chain_goal {c : Chain (sb L)} :
    Proper (sbisimeq ==> sbisimeq ==> flip impl) `c.
  Proof.
    apply tower.
    - intros ? INC t t' HP' ? ? HP'' ?? HP'''. 
      red.
      eapply INC; eauto.
      apply leq_infx in HP'''.
      now apply HP'''.
    - intros ? INC  t t' Sbisimt u u' Sbisimu [fwd bwd]; split; intros l v TR.
      + step in Sbisimt; apply Sbisimt in TR; destruct TR as (? & ? & TR & Sbis & EQl).
        apply fwd in TR; destruct TR as (? & ? & TR & Sbis' & HL).
        step in Sbisimu; apply Sbisimu in TR; destruct TR as (? & ? & TR & Sbis'' & EQl').
        do 2 eexists; repeat split; eauto.
        eapply INC; eauto.
        (* todo ltac *)
        apply Leq_eq in EQl.
        rewrite flipL_Leq in EQl'.
        apply Leq_eq in EQl'.
        subst; auto.
      + step in Sbisimu; apply Sbisimu in TR; destruct TR as (? & ? & TR & Sbis & EQl).
        apply bwd in TR; destruct TR as (? & ? & TR & Sbis' & HL).
        step in Sbisimt; apply Sbisimt in TR; destruct TR as (? & ? & TR & Sbis'' & EQl').
        do 2 eexists; repeat split; eauto.
        eapply INC; eauto.
        apply Leq_eq in EQl.
        rewrite flipL_Leq in EQl'.
        apply Leq_eq in EQl'.
        subst; auto.
  Qed.
   
  #[global] Instance seq_chain_ctx {c : Chain (sb L)} :
    Proper (Seq ==> Seq ==> impl) `c.
  Proof.
    apply tower.
    - intros ? INC t t' HP' ? ? HP'' ?? HP'''. 
      red.
      eapply INC; eauto.
      apply leq_infx in HP'''.
      now apply HP'''.
    - intros ? INC  t t' EQt u u' EQu HBS; split; intros l v TR.
      + rewrite <- EQt in TR.
        eplay.
        answer.
        now rewrite <- EQu.
      + rewrite <- EQu in TR.
        eplay.
        answer.
        now rewrite <- EQt.
  Qed.

  #[global] Instance equ_chain_ctx {c : Chain (sb L)} :
    Proper (equ eq ==> equ eq ==> impl) `c.
  Proof.
    repeat intro; eapply seq_chain_ctx; [| | eauto]; eauto.
  Qed.

  #[global] Instance seq_sb_ctx {r} :
    Proper (Seq ==> Seq ==> impl) (sb L r).
  Proof.
    intros t t' tt' u u' uu' HBS; split; intros ?? TR.
    - rewrite <- tt' in TR.
      eplay; answer.
      now rewrite <- uu'.
    - rewrite <- uu' in TR.
      eplay; answer.
      now rewrite <- tt'.
  Qed.  

  #[global] Instance equ_sb_ctx {r} :
    Proper (equ eq ==> equ eq ==> impl) (sb L r).
  Proof.
    repeat intro; eapply seq_sb_ctx; [| | eauto]; eauto.
  Qed.
  
  #[global] Instance sbisim_chain_ctx {c : Chain (sb L)} :
    Proper (sbisimeq ==> sbisimeq ==> impl) `c.
  Proof.
    apply tower.
    - intros ? INC t t' HP' ? ? HP'' ?? HP'''. 
      red.
      eapply INC; eauto.
      apply leq_infx in HP'''.
      now apply HP'''.
    - intros ? INC  t t' Sbisimt u u' Sbisimu [fwd bwd]; split; intros l v TR.
      + step in Sbisimt; apply Sbisimt in TR; destruct TR as (? & ? & TR & Sbis & EQl).
        apply fwd in TR; destruct TR as (? & ? & TR & Sbis' & HL).
        step in Sbisimu; apply Sbisimu in TR; destruct TR as (? & ? & TR & Sbis'' & EQl').
        do 2 eexists; repeat split; eauto.
        eapply INC; eauto.
        (* todo ltac *)
        apply Leq_eq in EQl'.
        rewrite flipL_Leq in EQl.
        apply Leq_eq in EQl.
        subst; auto.
      + step in Sbisimu; apply Sbisimu in TR; destruct TR as (? & ? & TR & Sbis & EQl).
        apply bwd in TR; destruct TR as (? & ? & TR & Sbis' & HL).
        step in Sbisimt; apply Sbisimt in TR; destruct TR as (? & ? & TR & Sbis'' & EQl').
        do 2 eexists; repeat split; eauto.
        eapply INC; eauto.
        apply Leq_eq in EQl'.
        rewrite flipL_Leq in EQl.
        apply Leq_eq in EQl.
        subst; auto.
  Qed.
  
  (*| Subrelations. |*)

  Lemma sbisim_cssim_subrelation_gen :
    forall x y, sbisim L x y -> cssim L x y.
  Proof.
    red.
    coinduction r cih; intros * SB.
    step in SB; destruct SB as [fwd bwd].
    split.
    - intros ?? TR; apply fwd in TR as (? & ? & ? & ? & ?); eauto 10.
    - intros (? & ? & TR). apply bwd in TR as (? & ? & ? & ? & ?); eauto 10.
  Qed.

  Lemma sbisim_ssim_subrelation_gen :
    forall x y, sbisim L x y -> ssim L x y.
  Proof. 
    intros. now apply cssim_ssim_subrelation_gen, sbisim_cssim_subrelation_gen.
  Qed.
  
End sbisim_heterogenous_theory.

(* TODO (?) : generalize
Lemma equ_sbisim_subrelation_gen {E B X Y} (RR : rel X Y) :
  forall x y, SeqR RR x y -> @sbisim E E B B X Y (Lvrel RR) x y.
 *)

#[global] Instance equ_sbisim_subrelation {E B X} :
  subrelation (@Seq E B X) sbisimeq.
Proof.
  red; intros * EQ; now rewrite EQ.
Qed.

#[global] Instance sbisim_cssim_subrelation {E C X L} :
  subrelation (@sbisim E E C C X X L) (cssim L).
Proof.
  red; apply sbisim_cssim_subrelation_gen. 
Qed.

#[global] Instance sbisim_ssim_subrelation {E C X L} :
  subrelation (@sbisim E E C C X X L) (ssim L).
Proof.
  red; apply sbisim_ssim_subrelation_gen. 
Qed.

#[global] Instance weq_sbisim : forall {E F C D X Y},
    Proper (lequiv ==> weq) (@sbisim E F C D X Y).
Proof.
    cbn -[weq]. intros. apply gfp_weq. now apply lequiv_sb.
Qed.

#[global] Instance is_stuck_sbisim_iff {E C X L} :
  Proper (@sbisim E E C C X X L ==> iff) is_stuck.
Proof.
  cbn; split; intros IS ?? TR.
  all:step in H; destruct H as [fwd bwd].
  apply bwd in TR as (? & ? & ? & ? & ?); eapply IS; eauto.
  apply fwd in TR as (? & ? & ? & ? & ?); eapply IS; eauto.
Qed.

(*|
Up-to bind
----------
|*)
Section bind.
  Arguments label : clear implicits.
  Obligation Tactic := idtac.

  Lemma bind_chain_gen
    {E F C D : Type -> Type} {X X' Y Y' : Type}
    (L  : lrel E F X' Y')
    (SS : rel X Y)
    {R : Chain (@sb E F C D X' Y' L)} :
    forall (t : ctree E C X) (t' : ctree F D Y)
      (k : X -> ctree E C X') (k' : Y -> ctree F D Y'),
      sbisim (upd_rel L SS) t t' ->
      (forall x y, SS x y -> `R (k x) (k' y)) ->
      `R (bind t k) (bind t' k').
  Proof.
    apply tower.
    - intros ? INC ? ? ? ? tt' kk' ? ?.
      apply INC. apply H. apply tt'.
      intros x x' xx'. apply leq_infx in H. apply H. now apply kk'.
    - intros ? ? ? ? ? ? tt' kk'.
      step in tt'; destruct tt' as [fwd bwd].
      split; cbn; intros * STEP.
      + apply trans_bind_inv in STEP as [(?H & ?t' & STEP & EQ) | [(Z & e & EQl & g & STEP & SEQ) | (v & STEPres & STEP)]].
        * subst l.
          apply fwd in STEP as (? & ? & STEP' & HSIM & HRL).
          inv HRL.
          refine_trans.
          ex2; split3.
          apply trans_bind_l_τ; eauto.
          2: etrans.
          rewrite EQ.
          apply H; auto.
          intros.
          now step; apply kk'.
        * subst l.
          apply fwd in STEP as (? & ? & STEP' & HSIM & HRL).
          invL.
          refine_trans.
          exists (ask f); ex; split3.
          eapply trans_bind_l_ask; eauto.
          2:etrans.
          rewrite SEQ.
          step; split.
          all: intros ? ? STEP''.
          all: pose proof trans_passive_inv' STEP'' as (a & EQ & ->).
          all: rewrite EQ in STEP''.
          assert (TR: trans (rcv e a) (β e g) (g a)) by etrans.
          2:assert (TR: trans (rcv f a) (β f u) (u a)) by etrans.
          all:step in HSIM; apply HSIM in TR as (l' & u' & TR' & HSIM' & HRL').
          all:pose proof trans_passive_inv' TR' as (b & EQ' & ->).
          exists (rcv f b); ex; split; eauto; split; cycle 1; [invL; etrans |].
          2:exists (rcv e b); ex; split; eauto; split; cycle 1; [invL; etrans |].
          all:rewrite EQ.
          all:apply H.
          1,3:rewrite EQ' in HSIM'; auto.
          all:intros; now step; apply kk'.
        * apply fwd in STEPres as (? & ? & STEP' & HSIM & HRL).
          invL.
          apply (kk' v y) in STEP as (l' & u' & STEP'' & HSIM'' & HRL'); etrans.
          exists l'; eexists; split; eauto.
          eapply trans_bind_r; eauto.
          erewrite <- trans_val_inv'; eauto.
       + apply trans_bind_inv in STEP as [(?H & ?t' & STEP & EQ) | [(Z & e & EQl & g & STEP & SEQ) | (v & STEPres & STEP)]].
        * subst l.
          apply bwd in STEP as (? & ? & STEP' & HSIM & HRL).
          inv HRL.
          refine_trans.
          ex2; split3.
          apply trans_bind_l_τ; eauto.
          2: etrans.
          rewrite EQ.
          apply H; auto.
          intros.
          now step; apply kk'.
        * subst l.
          apply bwd in STEP as (? & ? & STEP' & HSIM & HRL).
          invL.
          refine_trans.
          exists (ask f); ex; split3.
          eapply trans_bind_l_ask; eauto.
          2:etrans.
          rewrite SEQ.
          step; split.
          all: intros ? ? STEP''.
          all: pose proof trans_passive_inv' STEP'' as (a & EQ & ->).
          all: rewrite EQ in STEP''.
          assert (TR: trans (rcv f a) (β f u) (u a)) by etrans.
          2:assert (TR: trans (rcv e a) (β e g) (g a)) by etrans.
          all:step in HSIM; apply HSIM in TR as (l' & u' & TR' & HSIM' & HRL').
          all:pose proof trans_passive_inv' TR' as (b & EQ' & ->).
          exists (rcv e b); ex; split; eauto; split; cycle 1; [invL; etrans |].
          2:exists (rcv f b); ex; split; eauto; split; cycle 1; [invL; etrans |].
          all:rewrite EQ.
          all:apply H.
          1,3:rewrite EQ' in HSIM'; auto.
          all:intros; now step; apply kk'.
        * apply bwd in STEPres as (? & ? & STEP' & HSIM & HRL).
          invL.
          eapply (kk' _ _) in STEP as (l' & u' & STEP'' & HSIM'' & HRL'); etrans.
          exists l'; eexists; split; eauto.
          eapply trans_bind_r; eauto.
          erewrite <- trans_val_inv'; eauto.
  Qed.

  Lemma bind_chain {E C D X Y X' Y'}
    (RR : rel X' Y') (SS : rel X Y)
    {R : Chain (@sb E E C D X' Y' (Lvrel RR))} :
    forall (t1 : ctree E C X) (t2 : ctree E D Y) (k1 : X -> ctree E C X') (k2 : Y -> ctree E D Y'),
      t1 (≃[SS]) t2 ->
      (forall x y, SS x y -> `R (k1 x) (k2 y)) ->
      `R (t1 >>= k1) (t2 >>= k2).
  Proof.
    intros.
    eapply bind_chain_gen; eauto.
  Qed.

  Lemma bind_chain_eq {E C X X'}
    {R : Chain (@sb E E C C X' X' Leq)} :
    forall (t1 t2 : ctree E C X)
           (k1 k2 : X -> ctree E C X'),
      t1 ≃ t2 ->
      (forall x, `R (k1 x) (k2 x)) ->
      `R (t1 >>= k1) (t2 >>= k2).
  Proof.
    intros.
    eapply bind_chain_gen; eauto.
    intros ??<-; auto.
  Qed.

  Lemma sbisim_bind_gen {E F C D X Y X' Y'}
    L (SS : rel X Y)
    (t1 : ctree E C X) (t2 : ctree F D Y)
    (k1 : X -> ctree E C X') (k2 : Y -> ctree F D Y') :
    t1 (≃ upd_rel L SS) t2 ->
    (forall x y, SS x y -> k1 x (≃ L) k2 y) ->
    t1 >>= k1 (≃ L) t2 >>= k2.
  Proof.
    intros.
    eapply bind_chain_gen; eauto.
  Qed.

  Lemma sbisim_bind {E C D X Y X' Y'}
    (RR : rel X' Y') (SS : rel X Y)
    (t1 : ctree E C X) (t2 : ctree E D Y)
    (k1 : X -> ctree E C X') (k2 : Y -> ctree E D Y') :
    t1 (≃[SS]) t2 ->
    (forall x y, SS x y -> k1 x (≃[RR]) k2 y) ->
    t1 >>= k1 (≃[RR]) t2 >>= k2.
  Proof.
    intros.
    eapply bind_chain_gen; eauto.
  Qed.

  Lemma sbisim_bind_eq {E C D X X'}
    (t1 : ctree E C X) (t2 : ctree E D X)
    (k1 : X -> ctree E C X') (k2 : X -> ctree E D X') :
    t1 ≃ t2 ->
    (forall x, k1 x ≃ k2 x) ->
    t1 >>= k1 ≃ t2 >>= k2.
  Proof.
    intros.
    eapply sbisim_bind; eauto.
    intros ?? ->; auto.
  Qed.

End bind.

#[global] Instance sbisim_bind_chain {E C X Y}
  {R : Chain (@sb E E C C Y Y Leq)} :
  Proper ((fun t u => sbisim Leq (α t) (α u)) ==>
          (pointwise_relation _ (fun t u => `R (α t) (α u))) ==> `R) (@bind E C X Y).
Proof.
  repeat intro; eapply bind_chain_gen; eauto.
  intros ?? <-; auto.
Qed.

(*|
Structural proof rules
======================
Same three-layer shape as in [SSim.v] / [CSSim.v]:
- [sb_*_gen]: body-level, arbitrary [R], side-conditions explicit;
- [sb_*]: body-level, on a chain element [`R];
- [sbisim_*]: gfp-level.
|*)
Section Proof_rules.

  Context {E F C D : Type -> Type} {X Y : Type}.

  (*|
  Stuck ctrees: under bisimilarity the meaningful statement is biconditional.
  |*)
  Lemma sb_is_stuck L R :
    forall (t : ctree E C X) (u : ctree F D Y),
      sb L R t u -> is_stuck t <-> is_stuck u.
  Proof.
    intros * SB; split; intros IS ?? TR; eplay; eapply IS; eauto.
  Qed.
  
  Lemma sbisim_is_stuck L :
    forall (t : ctree E C X) (u : ctree F D Y),
      t (≃ L) u -> is_stuck t <-> is_stuck u.
  Proof.
    intros * SB; step in SB; eauto using sb_is_stuck.
  Qed.
  
  Lemma is_stuck_sb L R :
    forall (t : ctree E C X) (u : ctree F D Y),
      is_stuck t -> is_stuck u -> sb L R t u.
  Proof.  
    split; repeat intro.
    - now apply H in H1.
    - now apply H0 in H1.
  Qed.
    
  Lemma is_stuck_sbisim L :
    forall (t : ctree E C X) (u : ctree F D Y),
      is_stuck t -> is_stuck u -> t (≃ L) u.
  Proof.
    intros; step; auto using is_stuck_sb.
  Qed.

  Lemma Chain_Stuck L {R : Chain (@sb E F C D X Y L)} :
    ` R Stuck Stuck.
  Proof.
    step. apply is_stuck_sb; auto using stuck_is_stuck.
  Qed.
  
  (*|
  Ret nodes
  |*)
  Lemma sb_ret_gen (x : X) (y : Y) L R :
    R (α Stuck) (α Stuck) ->
    (Proper (Seq ==> Seq ==> impl) R) ->
    RR L x y ->
    sb L R (Ret x : ctree E C X) (Ret y : ctree F D Y).
   Proof.
    intros Rstuck ValRefl PROP.
    split; apply ss_ret_gen; eauto.
    typeclasses eauto.
  Qed.

  Lemma sb_ret (x : X) (y : Y) L
    {R : Chain (@sb E F C D X Y L)} :
    RR L x y ->
    sb L `R (Ret x : ctree E C X) (Ret y : ctree F D Y).
  Proof.
    intros; apply sb_ret_gen; auto.
    apply Chain_Stuck.
    typeclasses eauto.
  Qed. 

  Lemma sbisim_ret (x : X) (y : Y) L :
    RR L x y ->
    (Ret x : ctree E C X) (≃ L) (Ret y : ctree F D Y).
  Proof.
    intros; step; now apply sb_ret.
  Qed.

  (*|
  Vis nodes
  |*)

  Lemma sb_vis_gen {Z Z'} (e : E Z) (f: F Z')
    (k : Z -> ctree E C X) (k' : Z' -> ctree F D Y) (R: rel _ _) (L : lrel E F X Y) :
    R (β (e) k) (β (f) k') ->
    (Proper (Seq ==> Seq ==> impl) R) ->
    L (ask e) (ask f) ->
    sb L R (Vis e k) (Vis f k').
  Proof.
    intros; split; apply ss_vis_gen; try typeclasses eauto; auto.
    now apply flipL_flip.
  Qed.
 
  Lemma sb_vis {Z Z'} (e : E Z) (f : F Z')
    (k : Z -> ctree E C X) (k' : Z' -> ctree F D Y) L
    {R : Chain (@sb E F C D X Y L)}
    (HRask : Rask L e f)
    (HRfwd : forall x, exists y, `R (k x) (k' y) /\ Rrcv L e f x y)
    (HRbwd : forall y, exists x, `R (k x) (k' y) /\ Rrcv L e f x y) :
    sb L `R (Vis e k) (Vis f k').
  Proof.
    apply sb_vis_gen; try typeclasses eauto.
    2: now constructor.
    step; split.
    all: intros l u TR; inv_trans; subst.
    destruct (HRfwd x) as (y & ? & ?).
    2:destruct (HRbwd x) as (y & ? & ?).
    all:ex2; intuition.
    rewrite EQ; eauto.
    etrans.
    rewrite EQ; eauto.
    apply flipL_flip; cbn; etrans.
  Qed.

  Lemma sbisim_vis {Z Z'} (e : E Z) (f : F Z')
    (k : Z -> ctree E C X) (k' : Z' -> ctree F D Y) L
    (HRask : Rask L e f)
    (HRfwd : forall x, exists y, (k x) (≃ L) (k' y) /\ Rrcv L e f x y)
    (HRbwd : forall y, exists x, (k x) (≃ L) (k' y) /\ Rrcv L e f x y) :
    (Vis e k) (≃ L) (Vis f k').
  Proof.
    now step; apply sb_vis.
  Qed.
  
  Lemma sb_vis_id {Z} (e : E Z) (f : F Z)
    (k : Z -> ctree E C X) (k' : Z -> ctree F D Y) L
    {R : Chain (@sb E F C D X Y L)}
    (HRask : Rask L e f)
    (HRrcv : forall z, `R (k z) (k' z) /\ Rrcv L e f z z) :
    sb L `R (Vis e k) (Vis f k').
  Proof.
    apply sb_vis; auto.
    all: intros x; exists x; auto.
  Qed.
  
  Lemma sbisim_vis_id {Z} (e : E Z) (f : F Z)
    (k : Z -> ctree E C X) (k' : Z -> ctree F D Y) L
    (HRask : Rask L e f)
    (HRrcv : forall z, (k z) (≃ L) (k' z) /\ Rrcv L e f z z) :
    (Vis e k) (≃ L) (Vis f k').
  Proof.
    now step; apply sb_vis_id.
  Qed.
  
  (*|
  Invisible branching — [Br]. Unlike [ss], the [_l]/[_r] variants require
  an explicit witness so that the reverse challenge has a branch to take.
  |*)
  
  Lemma sb_br_gen {A B} (c : C A) (d : D B)
    (k : A -> ctree E C X) (k' : B -> ctree F D Y) R L :
    (forall x, exists y, sb L R (k x) (k' y)) ->
    (forall y, exists x, sb L R (k x) (k' y)) ->
    sb L R (Br c k) (Br d k').
  Proof.
    intros EQs1 EQs2.
    split; apply ss_br_gen; intros.
    - destruct (EQs1 x) as [z [FW _]]. eauto.
    - destruct (EQs2 x) as [z [_ BA]]. eauto.
  Qed.
  
  Lemma sb_br_id_gen {A} (c : C A) (d : D A)
    (k : A -> ctree E C X) (k' : A -> ctree F D Y) R L :
    (forall x, sb L R (k x) (k' x)) ->
    sb L R (Br c k) (Br d k').
  Proof.
    intros; apply sb_br_gen; intros x; exists x; auto.
  Qed.

  Lemma sb_br_l_gen {Z} (c : C Z) (x : Z)
    (k : Z -> ctree E C X) (t : ctree F D Y) R L :
    (forall z, sb L R (k z) t) ->
    sb L R (Br c k) t.
  Proof.
    intros EQs.
    split.
    - apply ss_br_l_gen; intros; apply EQs.
    - intros ?? TR.
      eapply ss_br_r_gen with (x := x); eauto.
      apply EQs.
  Qed.

  Lemma sb_br_r_gen {Z} (d : D Z) (y : Z)
    (k : Z -> ctree F D Y) (t : ctree E C X) R L :
    (forall z, sb L R t (k z)) ->
    sb L R t (Br d k).
  Proof.
    intros EQs.
    split.
    - apply ss_br_r_gen with (x := y); intros; apply EQs.
    - apply ss_br_l_gen; intros; apply EQs.
  Qed.

  Lemma sb_br {A B} (c : C A) (d : D B)
    (k : A -> ctree E C X) (k' : B -> ctree F D Y) L
    {R : Chain (@sb E F C D X Y L)} :
    (forall x, exists y, sb L `R (k x) (k' y)) ->
    (forall y, exists x, sb L `R (k x) (k' y)) ->
    sb L `R (Br c k) (Br d k').
  Proof.
    now intros; apply sb_br_gen.
  Qed.
  
  Lemma sb_br_id {A} (c : C A) (d : D A)
    (k : A -> ctree E C X) (k' : A -> ctree F D Y) L
    {R : Chain (@sb E F C D X Y L)} :
    (forall x, sb L `R (k x) (k' x)) ->
    sb L `R (Br c k) (Br d k').
  Proof.
    now intros; apply sb_br_id_gen.
  Qed.

  Lemma sb_br_l {Z} (c : C Z) (x : Z)
    (k : Z -> ctree E C X) (t : ctree F D Y) L
    {R : Chain (@sb E F C D X Y L)} :
    (forall z, sb L `R (k z) t) ->
    sb L `R (Br c k) t.
  Proof.
    now intros; apply sb_br_l_gen.
  Qed.

  Lemma sb_br_r {Z} (d : D Z) (y : Z)
    (k : Z -> ctree F D Y) (t : ctree E C X) L
    {R : Chain (@sb E F C D X Y L)} :
    (forall z, sb L `R t (k z)) ->
    sb L `R t (Br d k).
  Proof.
    now intros; apply sb_br_r_gen.
  Qed.

  Lemma sbisim_br {A B} (c : C A) (d : D B)
    (k : A -> ctree E C X) (k' : B -> ctree F D Y) L :
    (forall x, exists y, (k x) (≃ L) (k' y)) ->
    (forall y, exists x, (k x) (≃ L) (k' y)) ->
    (Br c k) (≃ L) (Br d k').
  Proof.
    intros H1 H2; step; apply sb_br; eauto.
    intros x; destruct (H1 x); eexists; step in H; eauto.
    intros x; destruct (H2 x); eexists; step in H; eauto.
  Qed.

  Lemma sbisim_br_id {A} (c : C A) (d : D A)
    (k : A -> ctree E C X) (k' : A -> ctree F D Y) L :
    (forall x, (k x) (≃ L) (k' x)) ->
    (Br c k) (≃ L) (Br d k').
  Proof.
    intros; step; apply sb_br_id; eauto.
    intros x; specialize (H x); step in H; auto.
  Qed.

  Lemma sbisim_br_l {Z} (c : C Z) (x : Z)
    (k : Z -> ctree E C X) (t : ctree F D Y) L :
    (forall z, (k z) (≃ L) t) ->
    (Br c k) (≃ L) t.
  Proof.
    intros; step; apply sb_br_l; eauto.
    intros y; specialize (H y); step in H; auto.
  Qed.

  Lemma sbisim_br_r {Z} (d : D Z) (y : Z)
    (k : Z -> ctree F D Y) (t : ctree E C X) L :
    (forall z, t (≃ L) (k z)) ->
    t (≃ L) (Br d k).
  Proof.
    intros; step; apply sb_br_r; eauto.
    intros x; specialize (H x); step in H; auto.
  Qed.

  (*|
  Guard — a silent wrapper; absorbed by [≃].
  |*)
  Lemma sb_guard_l_gen (t : ctree E C X) (u : ctree F D Y) R L :
    sb L R t u -> sb L R (Guard t) u.
  Proof.
    intros EQ.
    play; inv_trans; eplay; answer.
  Qed.

  Lemma sb_guard_l (t : ctree E C X) (u : ctree F D Y) L
    {R : Chain (@sb E F C D X Y L)} :
    sb L `R t u -> sb L `R (Guard t) u.
  Proof.
    apply sb_guard_l_gen.
  Qed.
  
  Lemma sbisim_guard_l (t : ctree E C X) (u : ctree F D Y) L :
    t (≃ L) u -> (Guard t) (≃ L) u.
  Proof.
    intros H; step in H; step; apply sb_guard_l_gen; auto.
  Qed.
         
  Lemma sb_guard_r_gen (t : ctree E C X) (u : ctree F D Y) R L :
    sb L R t u -> sb L R t (Guard u).
  Proof.
    intros EQ.
    play; inv_trans; eplay; answer.
  Qed.

  Lemma sb_guard_r (t : ctree E C X) (u : ctree F D Y) L
    {R : Chain (@sb E F C D X Y L)} :
    sb L `R t u -> sb L `R t (Guard u).
  Proof.
    apply sb_guard_r_gen.
  Qed.
 
  Lemma sbisim_guard_r (t : ctree E C X) (u : ctree F D Y) L :
    t (≃ L) u -> t (≃ L) (Guard u).
  Proof.
    intros H; step in H; step; apply sb_guard_r_gen; auto.
  Qed.
         
  Lemma sb_gguard_gen (t : ctree E C X) (u : ctree F D Y) R L :
    sb L R t u -> sb L R (Guard t) (Guard u).
  Proof.
    intros EQ.
    play; inv_trans; eplay; answer.
  Qed.

  Lemma sb_gguard (t : ctree E C X) (u : ctree F D Y) L
    {R : Chain (@sb E F C D X Y L)} :
    sb L `R t u -> sb L `R (Guard t) (Guard u).
  Proof.
    apply sb_gguard_gen.
  Qed.
 
  Lemma sbisim_gguard (t : ctree E C X) (u : ctree F D Y) L :
    t (≃ L) u -> (Guard t) (≃ L) (Guard u).
  Proof.
    intros H; step in H; step; apply sb_gguard_gen; auto.
  Qed.

  (*|
  Internal transitions — [Step].
  |*)
  Lemma sb_step_gen (t : ctree E C X) (u : ctree F D Y) R L :
    Proper (Seq ==> Seq ==> impl) R ->
    Proper (Seq ==> Seq ==> flip impl) R ->
    R (α t) (α u) ->
    sb L R (Step t) (Step u).
  Proof.
    split; apply ss_step_gen; eauto; typeclasses eauto.
  Qed.

  Lemma sb_step (t : ctree E C X) (u : ctree F D Y) L
    {R : Chain (@sb E F C D X Y L)} :
    `R t u ->
    sb L `R (Step t) (Step u).
  Proof.
    intros.
    apply sb_step_gen; eauto; typeclasses eauto.
  Qed.

  Lemma sbisim_step (t : ctree E C X) (u : ctree F D Y) L :
    t (≃ L) u ->
    (Step t) (≃ L) (Step u).
  Proof.
    intros. step. apply sb_step; auto.
  Qed.

  (*|
  Visible branching — [BrS].
  |*)
  Lemma sb_brS_gen {Z Z'} (c : C Z) (d : D Z')
    (k : Z -> ctree E C X) (k' : Z' -> ctree F D Y) R L :
    Proper (Seq ==> Seq ==> impl) R ->
    Proper (Seq ==> Seq ==> flip impl) R ->
    (forall x, exists y, R (α (k x)) (α (k' y))) ->
    (forall y, exists x, R (k x) (k' y)) ->
    sb L R (BrS c k) (BrS d k').
  Proof.
    intros ? ? EQs1 EQs2.
    apply sb_br_gen; intros x.
    - destruct (EQs1 x) as [z ?]; exists z.
      apply sb_step_gen; auto.
    - destruct (EQs2 x) as [z ?]. exists z.
      apply sb_step_gen; eauto.
  Qed.

  Lemma sb_brS_id_gen {X'} (c : C X') (d: D X')
    (k : X' -> ctree E C X) (k' : X' -> ctree F D Y) (R : rel _ _) L:
    Proper (Seq ==> Seq ==> impl) R ->
    Proper (Seq ==> Seq ==> flip impl) R ->
    (forall x, R (k x) (k' x)) ->
    sb L R (BrS c k) (BrS d k').
  Proof.
    intros ?? EQs.
    split; apply sb_br_id_gen; intros; apply sb_step_gen; auto.
  Qed.

  Lemma sb_brS {Z Z'} (c : C Z) (d : D Z')
    (k : Z -> ctree E C X) (k' : Z' -> ctree F D Y) L
    {R : Chain (@sb E F C D X Y L)} :
    (forall x, exists y, `R (k x) (k' y)) ->
    (forall y, exists x, `R (k x) (k' y)) ->
    sb L `R (BrS c k) (BrS d k').
  Proof.
    intros; apply sb_brS_gen; auto; typeclasses eauto.
  Qed.
  
  Lemma sb_brS_id {Z} (c : C Z) (d : D Z)
    (k : Z -> ctree E C X) (k' : Z -> ctree F D Y) L
    {R : Chain (@sb E F C D X Y L)} :
    (forall x, `R (k x) (k' x)) ->
    sb L `R (BrS c k) (BrS d k').
  Proof.
    intros; apply sb_brS_id_gen; auto; typeclasses eauto.
  Qed.

  Lemma sbisim_brS {Z Z'} (c : C Z) (d : D Z')
    (k : Z -> ctree E C X) (k' : Z' -> ctree F D Y) L :
    (forall x, exists y, (k x) (≃ L) (k' y)) ->
    (forall y, exists x, (k x) (≃ L) (k' y)) ->
    (BrS c k) (≃ L) (BrS d k').
  Proof.
    intros; step; apply sb_brS; auto.
  Qed.
  
  Lemma sbisim_brS_id {Z} (c : C Z) (d : D Z)
    (k : Z -> ctree E C X) (k' : Z -> ctree F D Y) L :
    (forall x, (k x) (≃ L) (k' x)) ->
    BrS c k (≃ L ) BrS d k'.
  Proof.
    intros; step; apply sb_brS_id; auto.
  Qed.
 
  (*|
  [spinS] laws.
  |*)
  Lemma spinS_gen_nonempty :
    forall (L : lrel E F X Y) {Z Z'} (c: C Z) (c': D Z') (z: Z) (z': Z'),
      @spinS_gen E C X Z c (≃ L ) @spinS_gen F D Y Z' c'.
  Proof.
    intros * ??.
    coinduction S CIH.
    rewrite (ctree_eta (spinS_gen c)), (ctree_eta (spinS_gen c')); cbn.
    apply sb_brS; intros _; eauto.
  Qed.

  Lemma sbisim_spinS_empty :
    forall L (c : C False) (c' : D False),
      @sbisim E F C D X Y L (spinS_gen c) (spinS_gen c').
  Proof.
    intros.
    eapply is_stuck_sbisim.
    intros ?? TR; rewrite ctree_eta in TR; cbn in TR; now inv_trans.
    intros ?? TR; rewrite ctree_eta in TR; cbn in TR; now inv_trans.
  Qed.

End Proof_rules.

Lemma sbisim_guard {E C X} (t : ctree E C X) :
  Guard t ≃ t.
Proof.
  now apply sbisim_guard_l.
Qed.

Section Inversion_rules.

    Context {E F C D : Type -> Type} {X Y : Type}.

(*|
Inversion principles
--------------------
|*)

  Lemma sbisim_stuck_inv L (t : ctree E C X) (u : ctree F D Y) :
    t (≃ L) u -> is_stuck t <-> is_stuck u.
  Proof.
    intros SB; split; intros IS ?? tr; eplay; eapply IS; eauto.
  Qed.
  
  Lemma sbisim_ret_l_inv L :
    forall r (u : ctree F D Y),
      (Ret r : ctree E C X) (≃ L) u ->
      exists r' u', trans (val r') u u' /\ RR L r r'.
  Proof.
    intros.
    eplayL.
    invL.
    etrans.
  Qed.

  Lemma sbisim_ret_r_inv L :
    forall r' (t : ctree E C X),
      t (≃ L) (Ret r' : ctree F D Y) ->
      exists r t', trans (val r) t t' /\ RR L r r'.
  Proof.
    intros.
    eplayR.
    invL.
    etrans.
  Qed.

  Lemma sbisim_ret_inv L (r : X) (r' : Y) :
    (Ret r : ctree E C X) (≃ L) (Ret r' : ctree F D Y) ->
    RR L r r'.
  Proof.
    intro.
    eplayL.
    invL.
    inv_trans.
    now subst.
  Qed.

  Lemma sbisim_vis_l_inv {Z L} :
    forall (e : E Z) (k : Z -> ctree E C X) (u : ctree F D Y),
      (Vis e k) (≃ L) u ->
      exists Z' (f : F Z') k',
        trans (ask f) u (β f k') /\
        Rask L e f /\
        (forall x, exists y, (k x) (≃ L) (k' y) /\ Rrcv L e f x y) /\
        (forall y, exists x, (k x) (≃ L) (k' y) /\ Rrcv L e f x y).
  Proof.
    intros.
    eplayL; invL.
    refine_trans in TR.
    ex3; split4; eauto.
    - intros x.
      step in EQ.
      edestruct EQ as [(? & ? & ? & ? & ?) _]; unshelve etrans; eauto.
      inv_trans; invL; eauto.
    - intros x.
      step in EQ.
      edestruct EQ as [_ (? & ? & ? & ? & ?)]; unshelve etrans; eauto.
      inv_trans; invL; eauto.
  Qed.
  
  Lemma sbisim_vis_r_inv {Z L} :
    forall (t : ctree E C X) (f : F Z) (k' : Z -> ctree F D Y),
      t (≃ L) (Vis f k') ->
      exists Z' (e : E Z') k,
        trans (ask e) t (β e k) /\
        Rask L e f /\
        (forall x, exists y, (k x) (≃ L) (k' y) /\ Rrcv L e f x y) /\
        (forall y, exists x, (k x) (≃ L) (k' y) /\ Rrcv L e f x y).
  Proof.
    intros.
    eplayR; invL.
    refine_trans in TR.
    ex3; split4; eauto.
    - intros x.
      step in EQ.
      edestruct EQ as [(? & ? & ? & ? & ?) _]; unshelve etrans; eauto.
      inv_trans; invL; eauto.
    - intros x.
      step in EQ.
      edestruct EQ as [_ (? & ? & ? & ? & ?)]; unshelve etrans; eauto.
      inv_trans; invL; eauto.
  Qed.

  Lemma sbisim_vis_inv {Z Z'} L
    (e : E Z) (f : F Z')
    (k : Z -> ctree E C X) (k' : Z' -> ctree F D Y) :
    (Vis e k) (≃ L) (Vis f k') ->
    Rask L e f /\
    (forall x, exists y, Rrcv L e f x y /\ (k x) (≃ L) (k' y)) /\
    (forall y, exists x, Rrcv L e f x y /\ (k x) (≃ L) (k' y)).
  Proof.
    intros.
    eplayL; invL.
    inv_trans.
    dependent destruction EQl.
    split3; auto.
    - intros x.
      step in EQ.
      edestruct EQ as [(? & ? & ? & ? & ?) _]; unshelve etrans; eauto.
      inv_trans; invL; eauto.
    - intros x.
      step in EQ.
      edestruct EQ as [_ (? & ? & ? & ? & ?)]; unshelve etrans; eauto.
      inv_trans; invL; eauto.
  Qed.

  Lemma sbisim_guard_l_inv L (t : ctree E C X) (u : ctree F D Y) :
    (Guard t) (≃ L) u -> t (≃ L) u.
  Proof.
    intros.
    now rewrite sbisim_guard in H.
  Qed.
  
  Lemma sbisim_guard_r_inv L (t : ctree E C X) (u : ctree F D Y) :
    t (≃ L) (Guard u) -> t (≃ L) u.
  Proof.
    intros.
    now rewrite sbisim_guard in H.
  Qed.

  Lemma sbisim_guard_inv L (t : ctree E C X) (u : ctree F D Y) :
    (Guard t) (≃ L) (Guard u) -> t (≃ L) u.
  Proof.
    intros.
    now rewrite !sbisim_guard in H.
  Qed.

  Lemma sbisim_step_inv L (t : ctree E C X) (u : ctree F D Y) :
    (Step t) (≃ L) (Step u) -> t (≃ L) u.
  Proof.
    intros.
    now eplay; inv_trans; invL.
  Qed.
  
  Lemma sbisim_step_l_inv L (t : ctree E C X) (u : ctree F D Y) :
    (Step t) (≃ L) u ->
    exists u', trans τ u u' /\ t (≃ L) u'.
  Proof.
    intros.
    eplayL. invL.
    eexists; split; eauto.
  Qed.

  Lemma sbisim_step_r_inv L (t : ctree E C X) (u : ctree F D Y) :
    t (≃ L) (Step u) ->
    exists t', trans τ t t' /\ t' (≃ L) u.
  Proof.
    intros.
    eplayR. invL.
    eexists; split; eauto.
  Qed.

  Lemma sbisim_brS_inv L
    {A B} (c : C A) (d : D B)
    (k1 : A -> ctree E C X) (k2 : B -> ctree F D Y) :
    (BrS c k1) (≃ L) (BrS d k2) ->
    (forall a, exists b, (k1 a) (≃ L) (k2 b)) /\
    (forall b, exists a, (k1 a) (≃ L) (k2 b)).
  Proof.
    intros.
    split; intros.
    - unshelve eplayL; auto; inv_trans; invL; eauto.
    - unshelve eplayR; auto; inv_trans; invL; eauto.
  Qed.
  
  Lemma sbisim_brS_l_inv L
    {A} (c : C A) (k1 : A -> ctree E C X) (u : ctree F D Y) :
    (BrS c k1) (≃ L) u ->
    forall a, exists u', trans τ u u' /\ (k1 a) (≃ L) u'.
  Proof.
    intros.
    unshelve eplayL; auto; inv_trans; invL; eauto.
  Qed.
  
  Lemma sbisim_brS_r_inv L
    {B} (d : D B) (k2 : B -> ctree F D Y) (t : ctree E C X) :
    t (≃ L) (BrS d k2) ->
    forall b, exists t', trans τ t t' /\ t' (≃ L) (k2 b).
  Proof.
    intros.
    unshelve eplayR; auto; inv_trans; invL; eauto.
  Qed.

End Inversion_rules.

(*|
Sanity checks and structural laws (homogeneous).
|*)
Section WithParams.

  Context {E C : Type -> Type}.
  Context {HasC2 : B2 -< C}.
  Context {HasC3 : B3 -< C}.

  Lemma spin_bisim : forall {D R X Y} (c : C X) (c' : D Y),
      @spin_gen E C R X c ≃ @spin_gen E D R Y c'.
  Proof.
    intros.
    play; exfalso; eapply spin_gen_is_stuck; eauto.
  Qed.
  
  Lemma br2_assoc {X} : forall (t u v : ctree E C X),
      br2 (br2 t u) v ≃ br2 t (br2 u v).
  Proof.
    intros; play; inv_trans; answer.
  Qed.

  Lemma br2_commut {X} : forall (t u : ctree E C X),
      br2 t u ≃ br2 u t.
  Proof.
    intros; play; inv_trans; answer.
  Qed.

  Lemma br2_idem {X} : forall (t : ctree E C X),
      br2 t t ≃ t.
  Proof.
    intros; play; inv_trans; answer.
  Qed.

  Lemma br2_merge {X} : forall (t u v : ctree E C X),
      br2 (br2 t u) v ≃ br3 t u v.
  Proof.
    intros; play; inv_trans; answer.
  Qed.

  Lemma br2_is_stuck {X} : forall (u v : ctree E C X),
      is_stuck u -> br2 u v ≃ v.
  Proof.
    intros; play; inv_trans; answer.
    (* todo: have inv_trans support stuck stepping *)
    exfalso; eapply H; eauto.
  Qed.
  
  Lemma br2_stuck_l {X} : forall (t : ctree E C X),
      br2 Stuck t ≃ t.
  Proof.
    intros; play; inv_trans; answer.
  Qed.

  Lemma br2_stuck_r {X} : forall (t : ctree E C X),
      br2 t Stuck ≃ t.
  Proof.
    intros; play; inv_trans; answer.
  Qed.

  Lemma br2_spin_l {X} : forall (t : ctree E C X),
      br2 spin t ≃ t.
  Proof.
    intros; play; inv_trans; answer.
    (* todo: have inv_trans support stuck stepping *)
    exfalso; eapply spin_is_stuck; eauto.
  Qed.

  Lemma br2_spin_r {X} : forall (t : ctree E C X),
      br2 t spin ≃ t.
  Proof.
    intros; play; inv_trans; answer.
    (* todo: have inv_trans support stuck stepping *)
    exfalso; eapply spin_is_stuck; eauto.
  Qed.

  Lemma brS2_commut {X} : forall (t u : ctree E C X),
      brS2 t u ≃ brS2 u t.
  Proof.
    intros; play;
    apply trans_brS2_inv' in TR as (-> & [EQ | EQ]); setoid_rewrite EQ;
    (ex2; split3; [| eauto |]; etrans).
  Qed.

  Lemma brS2_idem {X} : forall (t : ctree E C X),
      brS2 t t ≃ Step t.
  Proof.
    intros; play.
    - apply trans_brS2_inv' in TR as (-> & [EQ | EQ]); setoid_rewrite EQ;
    ( ex2; split3; [| eauto |]; etrans).
    - inv_trans; setoid_rewrite EQ; answer.
  Qed.
  
  Lemma sb_unfold_forever {X} : forall (k : X -> ctree E C X) (i : X),
      forever k i ≃ r <- k i ;; forever k r.
  Proof.
    intros.
    rewrite unfold_forever.
    apply sbisim_bind_eq; auto.
    intros; now rewrite sbisim_guard.
  Qed.

End WithParams.

(*|
Incompatibility lemmas — constructors of distinct kinds cannot be bisimilar
(with minor inhabitation side-conditions for stuck [Vis] cases).
|*)
Section Incompat.

  Context {E C : Type -> Type}.

  Definition are_bisim_incompat {X} (t u : ctree E C X) : Type :=
    match observe t, observe u with
    | RetF _, RetF _
    | VisF _ _, VisF _ _
    | BrF _ _, _
    | _, BrF _ _
    | GuardF _, _
    | _, GuardF _
    | StepF _, StepF _
    | StuckF, StuckF => False
    | @VisF _ _ _ _ Z _ _, StuckF
    | StuckF, @VisF _ _ _ _ Z _ _ => inhabited Z
    | _, _ => True
    end.

  Lemma sbisim_absurd {X} (t u : ctree E C X) :
    are_bisim_incompat t u -> t ≃ u -> False.
  Proof.
    intros * IC EQ.
    unfold are_bisim_incompat in IC.
    setoid_rewrite ctree_eta in EQ.
    genobs t ot. genobs u ou.
    destruct ot, ou.
    all: inv IC.
    all: try now unshelve (playR in EQ; inv_trans); auto.
    all: try now unshelve (playL in EQ; inv_trans); auto.
  Qed.

  Ltac sb_abs h :=
    eapply sbisim_absurd; [| eassumption]; cbn; try reflexivity.

  Lemma sbisim_ret_vis_inv {X Y} (r : Y) (e : E X) (k : X -> ctree E C Y) :
    (Ret r : ctree E C _) ≃ Vis e k -> False.
  Proof.
    intros * abs. sb_abs abs.
  Qed.

  Lemma sbisim_ret_BrS_inv {X Y} (r : Y) (c : C X) (k : X -> ctree E C Y) :
    (Ret r : ctree E C _) ≃ BrS c k -> False.
  Proof.
    intros EQ; playL in EQ; inv_trans; invL.
  Qed.

  Lemma sbisim_vis_BrS_inv {X Y Z}
    (e : E X) (k1 : X -> ctree E C Z) (c : C Y) (k2 : Y -> ctree E C Z) (y : Y) :
    Vis e k1 ≃ BrS c k2 -> False.
  Proof.
    unshelve (intros EQ; playR in EQ; inv_trans); auto; invL.
  Qed.

  Lemma sbisim_vis_BrS_inv' {X Y Z}
    (e : E X) (k1 : X -> ctree E C Z) (c : C Y) (k2 : Y -> ctree E C Z) (x : X) :
    Vis e k1 ≃ BrS c k2 -> False.
  Proof.
    unshelve (intros EQ; playL in EQ; inv_trans); auto; invL.
  Qed.

End Incompat.

(*|
Interaction with (complete) strong simulation
=============================================
|*)
Section SBisim_vs_SSim.

  Section withParam.
    
    Context {E F C D : Type -> Type} {X Y : Type}
      {L : lrel E F X Y}.

    Notation ss    := (@ss    E F C D X Y).
    Notation ssim  := (@ssim  E F C D X Y).

    #[global] Instance sbisim_ss_chain_goal {c : Chain (ss L)} :
      Proper (sbisimeq ==> sbisimeq ==> flip impl) `c.
    Proof.
      apply tower.
      - intros ? INC x y EQ x' y' EQ' ?? HP; red.
        eapply INC; eauto.
        eapply leq_infx in HP.
        now apply HP.
      - clear.
        intros c IH x y EQ x' y' EQ' SS ?? TR.
        playL in EQ.
        apply SS in TR0; destruct TR0 as (? & ? & TR0 & Sbis' & HL).
        playR in EQ'.
        ex2; split3; eauto.
        eapply IH; eauto.
        rewrite flipL_Leq in H0.
        apply Leq_eq in H,H0; subst; auto.
    Qed.

    #[global] Instance sbisim_ss_chain_ctx {c : Chain (ss L)} :
      Proper (sbisimeq ==> sbisimeq ==> impl) `c.
    Proof.
      apply tower.
      - intros ? INC x y EQ x' y' EQ' ?? HP; red.
        eapply INC; eauto.
        eapply leq_infx in HP.
        now apply HP.
      - clear.
        intros c IH x y EQ x' y' EQ' SS ?? TR.
        playR in EQ.
        apply SS in TR0; destruct TR0 as (? & ? & TR0 & Sbis' & HL).
        playL in EQ'.
        ex2; split3; eauto.
        eapply IH; eauto.
        rewrite flipL_Leq in H.
        apply Leq_eq in H,H0; subst; auto.
    Qed.

    #[global] Instance sbisim_ssim_goal :
      Proper (sbisim Leq ==> sbisim Leq ==> flip impl) (ssim L).
    Proof.
      repeat intro; eapply sbisim_ss_chain_goal; eauto.
    Qed.

    #[global] Instance sbisim_ssim_ctx :
      Proper (sbisim Leq ==> sbisim Leq ==> impl) (ssim L).
    Proof.
      repeat intro; eapply sbisim_ss_chain_ctx; eauto.
    Qed.

    (*|
      "Co-similarity" does not entail bisimilarity as per [ssim_sbisim_nequiv],
      but we can get something weaker:
    |*)
    Lemma ss_sb (R : rel _ _) (t : ctree E C X) (u : ctree F D Y) :
      ss L R t u ->
      SSim.ss (flipL L) (flip R) u t ->
      sb L R t u.
    Proof.
      split; cbn; intros.
      - apply H in H1 as (? & ? & ? & ? & ?); eauto.
      - apply H0 in H1 as (? & ? & ? & ? & ?); eauto.
    Qed.
          
  End withParam.

  (* Bisimilarity entails co-similarity. *)
  Lemma ssim_sbisim {E C X} (t u : ctree E C X) :
    t ≃ u ->
    ssim Leq t u /\ ssim Leq u t.
  Proof.
    intros SB.
    split.
    - coinduction r cih.
      intros ?? TR.
      playL in SB.
      answer.
      now rewrite EQ.
    - coinduction r cih.
      intros ?? TR.
      playR in SB.
      answer.
      now rewrite EQ.
      now simpL.
  Qed.

End SBisim_vs_SSim.

Section Two_ss_is_not_sb.

  (*|
  Two [ssim]s do not always give an [sbisim] (witness below).
  |*)
  Lemma split_sb_eq {E C X} (RR : rel _ _) (t t' : ctree E C X) :
    ss Leq RR t t' ->
    ss Leq (flip RR) t' t ->
    sb Leq RR t t'.
  Proof.
    intros * fwd bwd.
    play.
    apply fwd in TR as (? & ? & ? & ? & ?); answer.
    apply bwd in TR as (? & ? & ? & ? & ?); answer.
    now rewrite flipL_Leq.
  Qed.

  Lemma split_sbisim_eq {E B X} (t u : ctree E B X) :
    t ≃ u <-> ss Leq (sbisim Leq) t u /\ ss Leq (sbisim Leq) u t.
    Proof.
      split; intro.
      - step in H. split; [apply H |].
        symmetry in H. apply H.
      - step. split; [apply H |].
        destruct H as [_ ?].
        (* todo: this should be nicer *)
        eapply lequiv_ss; [apply flipL_Leq |].
        cbn; intros.
        apply H in H0 as (? & ? & ? & ? & ?); answer.
        symmetry; auto.
    Qed.

  (*|
  A concrete counter-example: [Step (Ret tt)] and [brS2 (Ret tt) Stuck]
  are mutually [ssim]-related but not [sbisim]-related.
  |*)
  Lemma ssim_sbisim_nequiv :
    exists (t1 t2 : ctree void1 B2 unit),
      ssim Leq t1 t2 /\ ssim Leq t2 t1 /\ ~ sbisimeq t1 t2.
  Proof.
    exists (Step (Ret tt)), (brS2 (Ret tt) (Stuck)).
    intuition.
    - unfold brS2.
      step.
      intros ?? TR.
      inv_trans; subst.
      exists τ, (α (Ret tt)); split3.
      apply trans_br with true; etrans.
      now rewrite EQ.
      eauto.
    - step; intros ?? TR.
      inv_trans.
      exists τ, (α (Ret tt)); intuition; now rewrite EQ.
      exists τ, (α (Ret tt)). intuition.
      rewrite EQ; apply ssim_stuck.
    - step in H. cbn in H. destruct H as [_ ?].
      specialize (H τ Stuck). lapply H; [| etrans].
      intros. destruct H0 as (? & ? & ? & ? & ?).
      inv_trans. step in H1. cbn in H1. destruct H1 as [? _].
      specialize (H0 (val tt) Stuck). lapply H0.
      2: subst; etrans.
      intro; destruct H1 as (? & ? & ? & ? & ?).
      inv_trans.
  Qed.

End Two_ss_is_not_sb.

Section SBisim_vs_CSSim.

  Section withParam.
    
    Context {E F C D : Type -> Type} {X Y : Type}
      {L : lrel E F X Y}.

    Notation css   := (@css   E F C D X Y).
    Notation cssim := (@cssim E F C D X Y).

    Tactic Notation "dec3" ident(h) "as"
      simple_intropattern(a) simple_intropattern(b) simple_intropattern(c)
      := destruct h as (a & b & c).
    
    #[global] Instance sbisim_css_chain_goal {c : Chain (css L)} :
      Proper (sbisimeq ==> sbisimeq ==> flip impl) `c.
    Proof.
      apply tower.
      - intros ? INC x y EQ x' y' EQ' ?? HP; red.
        eapply INC; eauto.
        eapply leq_infx in HP.
        now apply HP.
      - clear.
        intros c IH x y EQ x' y' EQ'; split.
        + intros ?? TR.
          playL in EQ.
          play in H.
          playR in EQ'.
          answer.
          eapply IH; eauto.
          now simpL.
        + intros (? & ? & TR).
          playL in EQ'.
          destruct H as [_ LIV].
          dec3 LIV as ? ? TR'; eauto.
          playR in EQ.
          eauto.
    Qed.

    #[global] Instance sbisim_css_chain_ctx {c : Chain (css L)} :
      Proper (sbisimeq ==> sbisimeq ==> impl) `c.
    Proof.
      apply tower.
      - intros ? INC x y EQ x' y' EQ' ?? HP; red.
        eapply INC; eauto.
        eapply leq_infx in HP.
        now apply HP.
      - clear.
        intros c IH x y EQ x' y' EQ'; split.
        + intros ?? TR.
          playR in EQ.
          play in H.
          playL in EQ'.
          answer.
          eapply IH; eauto.
          now simpL.
        + intros (? & ? & TR).
          playR in EQ'.
          destruct H as [_ LIV].
          dec3 LIV as ? ? TR'; eauto.
          playL in EQ.
          eauto.
    Qed.

    #[global] Instance sbisim_cssim_goal :
      Proper (sbisim Leq ==> sbisim Leq ==> flip impl) (cssim L).
    Proof.
      repeat intro; eapply sbisim_css_chain_goal; eauto.
    Qed.

    #[global] Instance sbisim_cssim_ctx :
      Proper (sbisim Leq ==> sbisim Leq ==> impl) (cssim L).
    Proof.
      repeat intro; eapply sbisim_css_chain_ctx; eauto.
    Qed.

    Lemma css_sb (R : rel _ _) (t : ctree E C X) (u : ctree F D Y) :
      css L R t u ->
      CSSim.css (flipL L) (flip R) u t ->
      sb L R t u.
    Proof.
      split; cbn; intros.
      - apply H in H1 as (? & ? & ? & ? & ?); eauto.
      - apply H0 in H1 as (? & ? & ? & ? & ?); eauto.
    Qed.

  End withParam.

  (* Bisimilarity entails co-similarity. *)
  Lemma sbisim_cssim {E C X} (t u : ctree E C X) :
    t ≃ u ->
    cssim Leq t u /\ cssim Leq u t.
  Proof.
    intros SB.
    split.
    - coinduction r cih.
      split.
      + intros ?? TR.
        playL in SB.
        answer.
        now rewrite EQ.
      + intros (? & ? & TR).
        playR in SB; eauto.
    - coinduction r cih.
      split.
      + intros ?? TR.
        playR in SB.
        simpL.
        answer.
        now rewrite EQ.
      + intros (? & ? & TR).
        playL in SB; eauto.
  Qed.

End SBisim_vs_CSSim.
