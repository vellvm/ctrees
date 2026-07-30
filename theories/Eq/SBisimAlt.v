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
     Eq.TransAlt
     Eq.Epsilon
     Eq.EstarTheory
     Eq.SSimAlt
     Misc.Pure.

From RelationAlgebra Require Export
     rel srel.

Import CoindNotations.
Import CTree.
Set Implicit Arguments.

Section StrongBisimAlt.
(*|
An alternative definition [sb'] of strong bisimulation.
The simulation challenge does not involve an inductive transition relation,
thus simplifying proofs.
|*)
 
  Program Definition sb' {E F C D : Type -> Type} 
  : mon (bool -> forall X Y : Type, lrel E F X Y -> rel (S E C X) (S F D Y)) 
    := 
    {| body (R : bool -> forall X Y : Type, lrel E F X Y -> rel (S E C X) (S F D Y)) side X Y (L : lrel E F X Y) t u :=
      (side = true -> @ss'_gen E F C D (fun X Y L t' u' => forall side, R side X Y L t' u') (R true) X Y L t u) 
      /\
      (side = false -> @ss'_gen F E D C (fun Y X L t' u' => forall side, R side X Y (flipL L) u' t') 
      (fun Y X (L : lrel F E Y X) u' t' => R false X Y (flipL L) t' u') Y X (flipL L) u t)
    |}.
  Next Obligation.
    split; intro; subst; [specialize (H0 eq_refl); clear H1 | specialize (H1 eq_refl); clear H0]. 
    all: eapply ss'_gen_mon; try eassumption; eauto. 
    all: cbn; intuition.
  Qed.

End StrongBisimAlt.

Section Symmetry.

  Program Definition sb'l {E F C D} :
    mon (bool -> forall X Y, lrel E F X Y -> rel SS SS) :=
    {| body R side X Y L t u := side = true -> @sb' E F C D R side X Y L t u |}.
  Next Obligation. 
  split; intro Hb; try easy.
  eapply (Hbody sb').
  cbn. apply H.  
  apply H0.
   (* dispatch true = true *)
  all: trivial. 
Qed.

(*|
[converse_neg] now swaps type indices and L
|*)
  Program Definition converse_neg {E C : Type -> Type} :
    mon (bool -> forall X Y : Type, lrel E E X Y -> rel (@S E C X) (@S E C Y)) :=
    {| body R b X Y L t u := R (negb b) Y X (flipL L) u t |}.

  #[global] Instance converse_neg_invol {E C} : Involution (@converse_neg E C).
  Proof.
    cbn. intros R b X Y L t u.
    rewrite Bool.negb_involutive, flipL_flipL.
    reflexivity.
  Qed.

  #[global] Instance sbisim'_sym {E C} :
    Symmetrical converse_neg (@sb' E E C C) (@sb'l E E C C).
  Proof.
    cbn -[sb' ss'_gen]. intros R b X Y L t u.
    split.
    - intros [Ht Hf]; split; intro Hb.
      + split; assumption.
      + apply Bool.negb_true_iff in Hb; subst.
        split; [| now intro].
        intros _.
        eapply ss'_gen_mon. 3: now apply Hf.
        * cbn. intros ? ? ? ? ? Hall side. apply Hall.
        * cbn. intros. assumption.
    - intros [Ht Hf]; split; intro Hb; subst.
      + now apply (Ht eq_refl).
      + cbn in Hf. destruct (Hf eq_refl) as [Hf' _]; specialize (Hf' eq_refl).
        eapply ss'_gen_mon. 3: now apply Hf'.
        * cbn. intros ? ? ? ? ? Hall side.
          specialize (Hall (negb side)).
          now rewrite Bool.negb_involutive in Hall.
        * cbn. intros. assumption.
  Qed.

End Symmetry.

Lemma sb'_flip {E F C D X Y} {L : lrel E F X Y}
    side (t: SS) (u: SS) R :
  @sb' F E D C (fun b X Y L t u => R (negb b) Y X (flipL L) u t) (negb side) Y X (flipL L) u t ->
  sb' R side X Y L t u.
Proof.
  intros [Ht Hf].
  split; intros; subst.
  - specialize (Hf eq_refl).
    eapply ss'_gen_mon. 3: now apply Hf.
    + cbn. intros ? ? ? ? ? Hall s.
      specialize (Hall (negb s)). now rewrite Bool.negb_involutive in Hall.
    + cbn. intros. assumption.
  - specialize (Ht eq_refl).
    eapply ss'_gen_mon. 3: now apply Ht.
    + cbn. intros ? ? ? ? ? Hall s.
      specialize (Hall (negb s)). now rewrite Bool.negb_involutive in Hall.
    + cbn. intros. assumption.
Qed.

Definition sbisim' {E F C D X Y} (L : lrel E F X Y) (t : S E C X) (u : S F D Y) :=
  forall side, gfp (@sb' E F C D) side X Y L t u.

Program Definition lift_rel3 {A B} : mon (rel A B) -> mon (bool -> rel A B) :=
    fun f => {| body R side := f (R side) |}.
Next Obligation.
  destruct f. cbn. cbn in H0. eapply Hbody in H0. 2: { cbn. apply H. } apply H0.
Qed.

(* Lemma unary_sym3 {A} (f : A -> A) : compat converse_neg (lift_rel3 (unary_ctx f)). *)
(* Proof. *)
(*   intros R b. apply leq_unary_ctx. *)
(*   intros. now apply in_unary_ctx. *)
(* Qed. *)

(* Lemma binary_sym3 {A} (f : A -> A -> A) : compat converse_neg (lift_rel3 (binary_ctx f)). *)
(* Proof. *)
(*   intros R b. apply leq_binary_ctx. *)
(*   intros. now apply in_binary_ctx. *)
(* Qed. *)

Section sbisim'_theory.
  Arguments label: clear implicits.
  Context {E F C D: Type -> Type} {X Y : Type}
          {L: lrel E F X Y}.

(*|
   Strong bisimulation up-to [Seq] is valid
   ----------------------------------------
|*)
  #[global] Instance Seq_proper_sb'_chain_goal {c: Chain (@sb' E F C D)} :
    forall side, Proper (Seq ==> Seq ==> flip impl) (`c side X Y L).
  Proof.
    tower induction.
    - intros CIH side x y Hseq x' y' Hseq2 [Ht Hf].
      split; intro; subst.
      + destruct (Ht eq_refl) as [Hnonep Hep]; split; intros.
        * rewrite Hseq in H0. destruct (Hnonep _ _ H H0) as
            (l' & u' & Htr & Hc & HL).
          rewrite <- Hseq2 in Htr.
          exists l', u'; split; eauto.
        * rewrite Hseq in H. apply Hep in H as (u' & Htr & Hc).
          rewrite <- Hseq2 in Htr.
          exists u'; split; eauto.
      + destruct (Hf eq_refl) as [Hnonep Hep]; split; intros.
        * rewrite Hseq2 in H0. destruct (Hnonep _ _ H H0) as
            (l' & u' & Htr & Hc & HL).
          rewrite <- Hseq in Htr.
          exists l', u'; split; eauto.
        * rewrite Hseq2 in H. apply Hep in H as (u' & Htr & Hc).
          rewrite <- Hseq in Htr.
          exists u'; split; eauto.
  Qed.

  #[global] Instance Seq_proper_sb'_chain_ctx {c: Chain (@sb' E F C D)} :
    forall side, Proper (Seq ==> Seq ==> impl) (`c side X Y L).
  Proof.
    tower induction.
    - intros CIH side x y Hseq x' y' Hseq2 [Ht Hf].
      split; intro; subst.
      + destruct (Ht eq_refl) as [Hnonep Hep]; split; intros.
        * rewrite <- Hseq in H0. destruct (Hnonep _ _ H H0) as
            (l' & u' & Htr & Hc & HL).
          rewrite Hseq2 in Htr.
          exists l', u'; split; eauto.
        * rewrite <- Hseq in H. apply Hep in H as (u' & Htr & Hc).
          rewrite Hseq2 in Htr.
          exists u'; split; eauto.
      + destruct (Hf eq_refl) as [Hnonep Hep]; split; intros.
        * rewrite <- Hseq2 in H0. destruct (Hnonep _ _ H H0) as
            (l' & u' & Htr & Hc & HL).
          rewrite Hseq in Htr.
          exists l', u'; split; eauto.
        * rewrite <- Hseq2 in H. apply Hep in H as (u' & Htr & Hc).
          rewrite Hseq in Htr.
          exists u'; split; eauto.
  Qed.

  #[global] Instance Seq_proper_sb'_chain_ctx4 {c: Chain (@sb' E F C D)} :
    Proper (eq ==> Seq ==> Seq ==> impl) (fun side => `c side X Y L).
  Proof.
    intros ? side -> ? ? eq1 ? ? eq2 H.
    now rewrite <- eq1, <- eq2.
  Qed.

  #[global] Instance Seq_proper_sb'_gfp_goal :
    forall side, Proper (Seq ==> Seq ==> flip impl) (gfp (@sb' E F C D) side X Y L).
  Proof.
    exact (@Seq_proper_sb'_chain_goal (chain_gfp (@sb' E F C D))).
  Qed.

  #[global] Instance Seq_proper_sb'_gfp_ctx :
    forall side, Proper (Seq ==> Seq ==> impl) (gfp (@sb' E F C D) side X Y L).
  Proof.
    exact (@Seq_proper_sb'_chain_ctx (chain_gfp (@sb' E F C D))).
  Qed.

  #[global] Instance Seq_proper_sbisim'_goal :
    Proper (Seq ==> Seq ==> flip impl) (@sbisim' E F C D X Y L).
  Proof.
    intros x y Hseq x' y' Hseq2 H side.
    now rewrite Hseq, Hseq2.
  Qed.

  #[global] Instance Seq_proper_sbisim'_ctx :
    Proper (Seq ==> Seq ==> impl) (@sbisim' E F C D X Y L).
  Proof.
    intros x y Hseq x' y' Hseq2 H side.
    now rewrite <- Hseq, <- Hseq2.
  Qed.

End sbisim'_theory.

Lemma lequiv_sb'_chain {E F C D} {c : Chain (@sb' E F C D)} :
  forall side X Y (L L' : lrel E F X Y),
    lequiv L L' -> `c side X Y L <= `c side X Y L'.
Proof.
  tower induction. 
  - intros IH side X Y L L' HL t u [Ht Hf].
    split; intro; subst.
    + specialize (Ht eq_refl).
      revert Ht. apply lequiv_ss'_gen.
      * assumption.
      * cbn. intros ? ? H s. eapply IH; [exact HL | apply H].
      * cbn. intros ? ? H. eapply IH; [exact HL | exact H].
    + specialize (Hf eq_refl).
      revert Hf. apply lequiv_ss'_gen.
      * now apply lequiv_flipL.
      * cbn. intros ? ? H s. eapply IH; [exact HL | apply H].
      * cbn. intros ? ? H. eapply IH; [exact HL | exact H].
Qed.

Lemma sb'_chain_flip {E C} {c : Chain (@sb' E E C C)} :
  forall side X Y (L : lrel E E X Y) t u,
    `c (negb side) Y X (flipL L) u t <-> `c side X Y L t u.
Proof.
  intros side X Y L t u.
  exact (invol_chain (i := @converse_neg E C) c side X Y L t u).
Qed.

Ltac fold_sbisim' :=
  repeat
    match goal with
    | h: context[gfp (@sb' ?E ?F ?C ?D) ?side ?X ?Y ?L] |- _ =>
        try fold (@sbisim' E F C D X Y L) in h
    | |- context[gfp (@sb' ?E ?F ?C ?D) ?side ?X ?Y ?L]      =>
        try fold (@sbisim' E F C D X Y L)
    end.

Tactic Notation "__coinduction_sbisim'" simple_intropattern(r) simple_intropattern(cih) :=
  first [unfold sbisim' at 4 | unfold sbisim' at 3 | unfold sbisim' at 2 | unfold sbisim' at 1]; coinduction r cih.

Tactic Notation "__step_sbisim'" :=
  match goal with
  | |- context[@sbisim' ?E ?F ?C ?D ?X ?Y ?LR] =>
      unfold sbisim';
      intro; step
  end.

Ltac __step_sb' :=
  first [ apply (b_chain (b := @sb' _ _ _ _) _)
        | apply (gfp_fp (@sb' _ _ _ _)) ].

Tactic Notation "step" := __step_sbisim' || __step_sb' || step.

Tactic Notation "coinduction" simple_intropattern(R) simple_intropattern(H) :=
  __coinduction_sbisim' R H || coinduction R H.

Ltac __step_in_sbisim' H :=
  match type of H with
  | context[@sbisim' ?E ?F ?C ?D ?X ?Y ?LR] =>
      unfold sbisim' in H;
      let Hl := fresh H "l" in
      let Hr := fresh H "r" in
      pose proof (H true) as Hl;
      pose proof (H false) as Hr;
      step in Hl; step in Hr;
      try fold (@sbisim' E F C D X Y LR) in Hl;
      try fold (@sbisim' E F C D X Y LR) in Hr
  end.

Ltac __step_in_sb' H := apply (gfp_pfp (@sb' _ _ _ _)) in H.

Tactic Notation "step" "in" ident(H) :=
  __step_in_sbisim' H || __step_in_sb' H || step in H.

Import CTreeNotations.
Import EquNotations.
Section sbisim'_homogenous_theory.
  Context {E B: Type -> Type} {X: Type}
          {L: lrel E E X X}.

  Notation sb' := (@sb' E E B B).
  Notation sbisim' := (@sbisim' E E B B X X).

  #[global] Instance refl_sb' {LR: Reflexive L} {C: Chain sb'}
    : forall side, Reflexive (`C side X X L).
  Proof.
    apply tower.
    - cbv. firstorder.
    - intros R IH side x.
      split; intros _; split.
      + intros t' l Hne TR.
        exists l, t'; ssplit.
        * apply estar_l_lift; exact TR.
        * intro; apply IH.
        * apply LR.
      + intros t' TR.
        exists t'; split.
        * apply estar_single; exact TR.
        * apply IH.
      + intros t' l Hne TR.
        exists l, t'; ssplit.
        * apply estar_l_lift; exact TR.
        * intro; apply IH.
        * reflexivity.
      + intros t' TR.
        exists t'; split.
        * apply estar_single; exact TR.
        * apply IH.
  Qed.

  #[global] Instance refl_bsb' {LR: Reflexive L} {C: Chain sb'}
    : forall side, Reflexive (sb' `C side X X L).
  Proof.
    intros ??.
    apply refl_sb'.
  Qed.

  #[global] Instance refl_sbisim' {LR: Reflexive L}
    : Reflexive (sbisim' L).
  Proof.
    intros ??; apply refl_sb'.
  Qed.

  Lemma sym_sb {LT: Symmetric L} {C: Chain sb'} :
    forall side x y, `C (negb side) X X L x y -> `C side X X L y x.
  Proof.
    intros side x y H.
    apply sb'_chain_flip.
    eapply lequiv_sb'_chain; [| exact H].
    symmetry. apply lequiv_flipL_sym.
  Qed.

  Lemma st'_flip `{SL: Symmetric _ L} {C: Chain sb'}:
    forall b t u,
    `C b X X L t u <-> `C (negb b) X X L u t.
  Proof.
    split; intro; apply sym_sb; auto.
    now rewrite Bool.negb_involutive.
  Qed.

  #[global] Instance sbisim_flip `{SL: Symmetric _ L} :
    Symmetric (sbisim' L).
  Proof.
    intros ????.
    eapply st'_flip,H.
  Qed.

End sbisim'_homogenous_theory.

Lemma split_st' : forall {E B X} {L : lrel E E X X} `{SL: Symmetric _ L}
                    (t u : ctree E B X) {C: Chain (@sb' E E B B)},
    (forall side, `C side X X L t u) <->
      `C true X X L t u /\ `C true X X L u t.
Proof.
  intros. split; intros.
  - split; auto.
    apply st'_flip. apply H.
  - destruct side; [apply H |].
    now apply st'_flip.
Qed.

Lemma split_st'_eq : forall {E B X} (t u : ctree E B X) {C: Chain (@sb' E E B B)},
    (forall side, `C side X X Leq t u) <->
      `C true X X Leq t u /\ `C true X X Leq u t.
Proof.
  intros. apply split_st'.
Qed.

Section sbisim'_heterogenous_theory.
  Arguments label: clear implicits.
  Context {E F C D: Type -> Type} {X Y: Type}
          {L: lrel E F X Y}.

  Notation sb' := (@sb' E F C D).
  Notation sbisim'  := (@sbisim' E F C D X Y).

  #[global] Instance Seq_sb'_goal {RR} :
    forall b, Proper (Seq ==> Seq ==> flip impl) (sb' RR b X Y L).
  Proof.
    intros b x x' eq1 y y' eq2 H.
    split; intro; subst.
    - destruct H as [H _]; specialize (H eq_refl).
      now rewrite eq1, eq2.
    - destruct H as [_ H]; specialize (H eq_refl).
      now rewrite eq1, eq2.
  Qed.

  #[global] Instance Seq_sb'_ctx {RR} :
    Proper (eq ==> Seq ==> Seq ==> impl) (fun b => sb' RR b X Y L).
  Proof.
    intros ? b -> ? ? eq1 ? ? eq2 H.
    now rewrite <- eq1, <- eq2.
  Qed.

  Lemma sb'_true_ss' R :
    forall (t : @S E C X) (u : @S F D Y),
    sb' R true X Y L t u <->
      ss'_gen (fun X Y L t u => forall side, R side X Y L t u) (R true) L t u.
  Proof.
    split; intros.
    - now apply H.
    - split; intros; easy.
  Qed.

  Lemma sb'_false_ss' R :
    forall (t : @S E C X) (u : @S F D Y),
    sb' R false X Y L t u <->
      @ss'_gen F E D C (fun Y X L t' u' => forall side, R side X Y (flipL L) u' t')
        (fun Y X (L : lrel F E Y X) u' t' => R false X Y (flipL L) t' u')
        Y X (flipL L) u t.
  Proof.
    split; intros.
    - now apply H.
    - split; intros; try easy.
  Qed.

  Lemma sb'_true_stuck R :
    forall (u : @S F D Y),
    sb' R true X Y L (Stuck : ctree E C X) u.
  Proof.
    intros. apply sb'_true_ss'.
    apply ss'_stuck.
  Qed.

End sbisim'_heterogenous_theory.

Lemma sb'_stuck {E F C D X Y} {L : lrel E F X Y} R :
  forall side,
    sb' R side X Y L (Stuck : ctree E C X) (Stuck : ctree F D Y).
Proof.
  intros. destruct side.
  - apply sb'_true_stuck.
  - apply sb'_flip. cbn -[sb']. apply sb'_true_stuck.
Qed.

(*|
  The [step_ss'_*] rules from SSimAlt require [Seq]-Properness of the
  relations sitting in the answer positions of [ss'_gen]. For [sb'] these
  positions are instantiated with [fun t u => forall side, R side t u],
  [R true] and [flip (R false)]; the following instances discharge
  those side-conditions from a single Properness assumption on [R].
|*)
Notation sb'R E F C D :=
  (bool -> forall X Y : Type, lrel E F X Y -> rel (@S E C X) (@S F D Y)).

Notation sb'Proper R :=
  (forall X Y (L : lrel _ _ X Y),
      Proper (eq ==> Seq ==> Seq ==> impl) (fun b => R b X Y L)).

#[global] Instance Proper_forall_R {E F C D X Y}
  {R : sb'R E F C D} {L : lrel E F X Y}
  {HR: sb'Proper R} :
  Proper (Seq ==> Seq ==> impl) (fun t u => forall side, R side X Y L t u).
Proof.
  intros ? ? eq1 ? ? eq2 H side; eapply HR; eauto.
Qed.

#[global] Instance Proper_forall_R_flip {E F C D X Y}
  {R : sb'R E F C D} {L : lrel E F X Y}
  {HR: sb'Proper R} :
  Proper (Seq ==> Seq ==> impl) (fun u t => forall side, R side X Y L t u).
Proof.
  intros ? ? eq1 ? ? eq2 H side; eapply HR; eauto.
Qed.

#[global] Instance Proper_R_side {E F C D X Y}
  {R : sb'R E F C D} {L : lrel E F X Y}
  {HR: sb'Proper R} side :
  Proper (Seq ==> Seq ==> impl) (R side X Y L).
Proof.
  intros ? ? eq1 ? ? eq2 H; eapply HR; eauto.
Qed.

#[global] Instance Proper_R_side_flip {E F C D X Y}
  {R : sb'R E F C D} {L : lrel E F X Y}
  {HR: sb'Proper R} side :
  Proper (Seq ==> Seq ==> impl) (fun u t => R side X Y L t u).
Proof.
  intros ? ? eq1 ? ? eq2 H; eapply HR; eauto.
Qed.

Section Proof_Rules.

  Arguments label: clear implicits.
  Context {E F C D: Type -> Type}
          {X Y: Type}
          {L : lrel E F X Y}.

  Lemma step_sb'_ret {R : sb'R E F C D} {HR: sb'Proper R}
    (x : X) (y : Y) :
    L (val x) (val y) ->
    (forall side, R side X Y L Stuck Stuck) ->
    forall side, sb' R side X Y L (Ret x : ctree E C X) (Ret y : ctree F D Y).
  Proof.
    intros Lval Rstuck side; split; intro; subst.
    - apply step_ss'_ret; [apply Rstuck | exact Lval].
    - apply step_ss'_ret; [apply Rstuck | now apply flipL_flip].
  Qed.

  Lemma step_sbt'_ret (x : X) (y : Y) {R : Chain (@sb' E F C D)} :
    L (val x) (val y) ->
    forall side, `R side X Y L (Ret x : ctree E C X) (Ret y : ctree F D Y).
  Proof.
    intros HL side.
    apply (b_chain R), step_sb'_ret.
    - exact HL.
    - intro side'; apply (b_chain R), sb'_stuck.
  Qed.

(*|
 The vis nodes are deterministic from the perspective of the labeled
 transition system: both sides step to the corresponding passive states.
|*)
  Lemma step_sb'_vis {R : sb'R E F C D} {HR: sb'Proper R}
    {Z Z'} (e : E Z) (f: F Z')
    (k : Z -> ctree E C X) (k' : Z' -> ctree F D Y) :
    (forall side, R side X Y L (Passive e k) (Passive f k')) ->
    L (ask e) (ask f) ->
    forall side, sb' R side X Y L (Vis e k) (Vis f k').
  Proof.
    intros HRpas Lask side; split; intro; subst.
    - apply step_ss'_vis; [apply HRpas | exact Lask].
    - apply step_ss'_vis; [apply HRpas | now apply flipL_flip].
  Qed.

  Lemma step_sb'_vis_id {R : sb'R E F C D} {HR: sb'Proper R}
    {Z} (e : E Z) (f: F Z)
    (k : Z -> ctree E C X) (k' : Z -> ctree F D Y) :
    (forall side, R side X Y L (Passive e k) (Passive f k')) ->
    L (ask e) (ask f) ->
    forall side, sb' R side X Y L (Vis e k) (Vis f k').
  Proof.
    intros; now apply step_sb'_vis.
  Qed.

  Lemma step_sb'_vis_l {R : sb'R E F C D} {HR: sb'Proper R} {Z} :
    forall (e : E Z) (k : Z -> ctree E C X) (u : @S F D Y),
      (exists l' u', ((trans_alt ε)^* ⋅ trans_alt l') u u'
        /\ (forall side, R side X Y L (Passive e k) u') /\ L (ask e) l') ->
      sb' R true X Y L (Vis e k) u.
  Proof.
    intros e k u (l' & u' & STEP & HRu & Hask).
    split; intro; [| easy].
    apply step_ss'_vis_l.
    exists l', u'; ssplit.
    - exact STEP.
    - exact HRu.
    - exact Hask.
  Qed.

(*|
  With this definition [sb'] of bisimulation, delayed nodes allow to perform a coinductive step.
|*)
  Lemma step_sb'_guard {R : sb'R E F C D} {HR: sb'Proper R}
    (t: ctree E C X) (t': ctree F D Y) side :
      R side X Y L t t' ->
      sb' R side X Y L (Guard t) (Guard t').
  Proof.
    intros HRtt'; split; intro; subst; apply step_ss'_guard; exact HRtt'.
  Qed.

  Lemma step_sb'_true_guard_l
    {R : Chain (@sb' E F C D)}
    (t: ctree E C X) (t': @S F D Y) :
    ` R true X Y L t t' ->
    sb' `R true X Y L (Guard t) t'.
  Proof.
    intros H; split; intro; [| easy].
    apply step_ss'_guard_l; exact H.
  Qed.

  Lemma step_sb'_guard_l
    {R : Chain (@sb' E F C D)}
    (t: ctree E C X) (t': @S F D Y) side :
    sb' (` R) side X Y L t t' ->
    sb' `R side X Y L (Guard t) t'.
  Proof.
    intros H; split; intro; subst.
    - apply step_ss'_guard_l.
      apply (b_chain R); exact H.
    - apply step_ss'_guard_r; now apply H.
  Qed.

  Lemma step_sb'_false_guard_r
    {R : Chain (@sb' E F C D)}
    (t: @S E C X) (t': ctree F D Y) :
    ` R false X Y L t t' ->
    sb' `R false X Y L t (Guard t').
  Proof.
    intros H; split; intro; [easy |].
    apply step_ss'_guard_l; exact H.
  Qed.

  Lemma step_sb'_guard_r
    {R : Chain (@sb' E F C D)}
    (t: @S E C X) (t': ctree F D Y) side :
    sb' (` R) side X Y L t t' ->
    sb' `R side X Y L t (Guard t').
  Proof.
    intros H; split; intro; subst.
    - apply step_ss'_guard_r; now apply H.
    - apply step_ss'_guard_l.
      apply (b_chain R); exact H.
  Qed.

  Lemma step_sb'_br {R : sb'R E F C D} {HR: sb'Proper R}
    {Z Z'} (a: C Z) (b: D Z')
    (k : Z -> ctree E C X) (k' : Z' -> ctree F D Y) side :
    (forall x, exists y, R side X Y L (k x) (k' y)) ->
    (forall y, exists x, R side X Y L (k x) (k' y)) ->
    sb' R side X Y L (Br a k) (Br b k').
  Proof.
    intros H1 H2; split; intro; subst; apply step_ss'_br.
    - intro x; destruct (H1 x) as (y & ?); eauto.
    - intro y; destruct (H2 y) as (x & ?); eauto.
  Qed.

  Lemma step_sb'_br_id {R : sb'R E F C D} {HR: sb'Proper R}
    {Z} (c: C Z) (d: D Z)
    (k : Z -> ctree E C X) (k' : Z -> ctree F D Y) side :
    (forall x, R side X Y L (k x) (k' x)) ->
    sb' R side X Y L (Br c k) (Br d k').
  Proof.
    intros. apply step_sb'_br; eauto.
  Qed.

  Lemma step_sb'_true_br_l {R : Chain (@sb' E F C D)} {Z} :
    forall (c : C Z) (k : Z -> ctree E C X) (u : @S F D Y),
    (forall x, `R true X Y L (k x) u) ->
    sb' `R true X Y L (Br c k) u.
  Proof.
    intros c k u H; split; intro; [| easy].
    apply step_ss'_br_l.
    intro x; apply H.
  Qed.

  Lemma step_sb'_br_l {R : Chain (@sb' E F C D)} {Z} :
    forall (c : C Z) (z : Z) (k : Z -> ctree E C X) (u : @S F D Y) side,
    (forall x, sb' `R side X Y L (k x) u) ->
    sb' `R side X Y L (Br c k) u.
  Proof.
    intros c z k u side H; split; intro; subst.
    - apply step_ss'_br_l.
      intro x; apply (b_chain R), H.
    - apply step_ss'_br_r with (x := z); now apply H.
  Qed.

(*|
  Step
|*)
  Lemma step_sb'_step {R : sb'R E F C D} {HR: sb'Proper R}
    (t : ctree E C X) (t': ctree F D Y) :
    L τ τ ->
    (forall side, R side X Y L t t') ->
    forall side, sb' R side X Y L (Step t) (Step t').
  Proof.
    intros Hτ HRtt' side; split; intro; subst.
    - apply step_ss'_step; [exact Hτ | apply HRtt'].
    - apply step_ss'_step; [now apply flipL_flip | apply HRtt'].
  Qed.

End Proof_Rules.

(*|
    When matching visible brs one against another, in general we need to explain how
    we map the branches from the left to the branches to the right.
    A useful special case is the one where the arity coincide and we simply use the identity
    in both directions. We can in this case have [n] rather than [2n] obligations.
|*)
Lemma step_sb'_brS {E F C D X Y} {L : lrel E F X Y}
  {R : Chain (@sb' E F C D)}
  {Z Z'} (c : C Z) (d : D Z')
  (k : Z -> ctree E C X) (k' : Z' -> ctree F D Y) :
  (forall x, exists y, forall side, `R side X Y L (k x) (k' y)) ->
  (forall y, exists x, forall side, `R side X Y L (k x) (k' y)) ->
  L τ τ ->
  forall side, sb' `R side X Y L (BrS c k) (BrS d k').
Proof.
  intros H1 H2 Hτ side.
  apply step_sb'_br.
  - intro x; destruct (H1 x) as (y & ?); exists y.
    step. now apply step_sb'_step.
  - intro y; destruct (H2 y) as (x & ?); exists x.
    step. now apply step_sb'_step.
Qed.

Lemma step_sb'_brS_id {E F C D X Y} {L : lrel E F X Y}
  {R : Chain (@sb' E F C D)}
  {Z} (c : C Z) (d: D Z)
  (k: Z -> ctree E C X) (k': Z -> ctree F D Y) :
  L τ τ ->
  (forall x side, `R side X Y L (k x) (k' x)) ->
  forall side, sb' `R side X Y L (BrS c k) (BrS d k').
Proof.
  intros Hτ H side.
  apply step_sb'_br_id.
  intro x; apply (b_chain R), step_sb'_step; auto.
Qed.

Lemma step_sb'_true_step_l {E F C D X Y} {L : lrel E F X Y}
  {R : Chain (@sb' E F C D)} :
  forall (t : ctree E C X) (u : @S F D Y),
    (exists l' u', ((trans_alt ε)^* ⋅ trans_alt l') u u'
      /\ (forall side, `R side X Y L t u') /\ L τ l') ->
    sb' `R true X Y L (Step t) u.
Proof.
  intros t u (l' & u' & STEP & HR' & Hτ).
  split; intro; [| easy].
  apply step_ss'_step_l.
  exists l', u'; ssplit.
  - exact STEP.
  - exact HR'.
  - exact Hτ.
Qed.

Lemma step_sb'_true_brS_l {E F C D X Y} {L : lrel E F X Y}
  {R : Chain (@sb' E F C D)}
  {Z} :
  forall (c : C Z) (k : Z -> ctree E C X) (u : @S F D Y),
    (forall x, exists l' u', ((trans_alt ε)^* ⋅ trans_alt l') u u'
      /\ (forall side, `R side X Y L (k x) u') /\ L τ l') ->
    sb' `R true X Y L (BrS c k) u.
Proof.
  intros c k u H.
  apply step_sb'_true_br_l; intro x.
  apply (b_chain R), step_sb'_true_step_l.
  apply H.
Qed.

Section Inversion_Rules.

  Context {E F C D: Type -> Type}
          {X Y: Type}.
  Variable (L : lrel E F X Y).

  (* Lemmas to exploit sb' and sbisim' hypotheses *)

  Lemma estar_vis_inv {G K : Type -> Type} {W Z} (e : G Z) (k : Z -> ctree G K W) (m : @S G K W) :
    (trans_alt ε)^* (Active (Vis e k)) m ->
    (Active (Vis e k) : @S G K W) ⩸ m.
  Proof.
    intros [n STAR]; destruct n.
    - exact STAR.
    - destruct STAR as [mid STEP _].
      apply trans_vis_inv' in STEP as (_ & Habs); easy.
  Qed.

  Lemma sb'_true_vis_l_inv {Z R} :
    forall (e : E Z) (k : Z -> ctree E C X) (u : @S F D Y),
    sb' R true X Y L (Vis e k) u ->
    exists l' u', ((trans_alt ε)^* ⋅ trans_alt l') u u'
      /\ (forall side, R side X Y L (Passive e k) u') /\ L (ask e) l'.
  Proof.
    intros. apply sb'_true_ss' in H.
    now apply ss'_vis_l_inv in H.
  Qed.

  Lemma sb'_true_vis_inv {Z Z' R} :
    forall (e : E Z) (f : F Z') (k : Z -> ctree E C X) (k' : Z' -> ctree F D Y),
    sb'Proper R ->
    sb' R true X Y L (Vis e k) (Vis f k') ->
    (forall side, R side X Y L (Passive e k) (Passive f k')) /\ L (ask e) (ask f).
  Proof.
    intros * HP H.
    apply sb'_true_vis_l_inv in H as (l' & u' & STEP & HR & HL).
    destruct STEP as [m STAR STEPa].
    apply estar_vis_inv in STAR.
    rewrite <- STAR in STEPa.
    apply trans_vis_inv' in STEPa as (EQ & ->).
    split.
    - intro side; rewrite <- EQ; apply HR.
    - exact HL.
  Qed.

  Lemma sb'_true_br_l_inv {Z R} :
    forall (c : C Z) (k : Z -> ctree E C X) (u : @S F D Y),
    sb' R true X Y L (Br c k) u ->
    forall x, exists u', (trans_alt ε)^* u u' /\ R true X Y L (k x) u'.
  Proof.
    intros * H x.
    destruct H as [H _]; specialize (H eq_refl); destruct H as [_ HB].
    destruct (HB _ (trans_br c x k)) as (u' & STAR & HR).
    exists u'; split; [exact STAR | exact HR].
  Qed.

  Lemma sb'_false_br_l_inv {Z R} :
    forall (t : @S E C X) (c : D Z) (k : Z -> ctree F D Y),
    sb' R false X Y L t (Br c k) ->
    forall x, exists t', (trans_alt ε)^* t t' /\ R false X Y L t' (k x).
  Proof.
    intros * H x.
    destruct H as [_ H]; specialize (H eq_refl); destruct H as [_ HB].
    destruct (HB _ (trans_br c x k)) as (t' & STAR & HR).
    exists t'; split; [exact STAR | exact HR].
  Qed.

  Lemma sb'_true_guard_l_inv {R} :
    forall (t : ctree E C X) (u : @S F D Y),
    sb' R true X Y L (Guard t) u ->
    exists u', (trans_alt ε)^* u u' /\ R true X Y L t u'.
  Proof.
    intros * H.
    destruct H as [H _]; specialize (H eq_refl); destruct H as [_ HB].
    destruct (HB _ (trans_guard t)) as (u' & STAR & HR).
    exists u'; split; [exact STAR | exact HR].
  Qed.

  Lemma sb'_false_guard_l_inv {R} :
    forall (t : @S E C X) (u : ctree F D Y),
    sb' R false X Y L t (Guard u) ->
    exists t', (trans_alt ε)^* t t' /\ R false X Y L t' u.
  Proof.
    intros * H.
    destruct H as [_ H]; specialize (H eq_refl); destruct H as [_ HB].
    destruct (HB _ (trans_guard u)) as (t' & STAR & HR).
    exists t'; split; [exact STAR | exact HR].
  Qed.

  Lemma sbisim'_br_l_inv {Z} c x (k : Z -> ctree E C X) (t' : @S F D Y) :
    gfp (@sb' E F C D) true X Y L (Br c k) t' ->
    gfp (@sb' E F C D) true X Y L (k x) t'.
  Proof.
    intros H. step in H.
    eapply sb'_true_br_l_inv with (x := x) in H as (u' & STAR & HR).
    step. split; intro; [| easy].
    eapply step_ss'_epsilon_r; [| exact STAR].
    step in HR. now apply HR.
  Qed.

  Lemma sbisim'_br_r_inv {Z} c x (k : Z -> ctree F D Y) (t : @S E C X) :
    gfp (@sb' E F C D) false X Y L t (Br c k) ->
    gfp (@sb' E F C D) false X Y L t (k x).
  Proof.
    intros H. step in H.
    eapply sb'_false_br_l_inv with (x := x) in H as (t0 & STAR & HR).
    step. split; intro; [easy |].
    eapply step_ss'_epsilon_r; [| exact STAR].
    step in HR. now apply HR.
  Qed.

  Lemma sbisim'_guard_l_inv (t : ctree E C X) (t' : @S F D Y) :
    gfp (@sb' E F C D) true X Y L (Guard t) t' ->
    gfp (@sb' E F C D) true X Y L t t'.
  Proof.
    intros H. step in H.
    apply sb'_true_guard_l_inv in H as (u' & STAR & HR).
    step. split; intro; [| easy].
    eapply step_ss'_epsilon_r; [| exact STAR].
    step in HR. now apply HR.
  Qed.

  Lemma sbisim'_guard_r_inv (t : @S E C X) (t' : ctree F D Y) :
    gfp (@sb' E F C D) false X Y L t (Guard t') ->
    gfp (@sb' E F C D) false X Y L t t'.
  Proof.
    intros H. step in H.
    apply sb'_false_guard_l_inv in H as (t0 & STAR & HR).
    step. split; intro; [easy |].
    eapply step_ss'_epsilon_r; [| exact STAR].
    step in HR. now apply HR.
  Qed.

End Inversion_Rules.

(*|
[eq]-specialized inversions, stated outside the section so [L] can be
instantiated with [eq].
|*)
Lemma sb'_eq_vis_invT {E C X Z Z' R} :
  forall side (e : E Z) (f : E Z') (k : Z -> ctree E C X) (k' : Z' -> ctree E C X),
  sb' R side X X Leq (Vis e k) (Vis f k') ->
  Z = Z'.
Proof.
  intros side e f k k' H.
  destruct side.
  - apply sb'_true_vis_l_inv in H as (l' & u' & STEP & _ & HL).
    destruct STEP as [m STAR STEPa].
    apply estar_vis_inv in STAR; rewrite <- STAR in STEPa.
    apply trans_vis_inv' in STEPa as (_ & ->).
    apply build_rel_ask in HL.
    now dependent destruction HL.
  - apply sb'_false_ss' in H.
    apply ss'_vis_l_inv in H as (l' & u' & STEP & _ & HL).
    destruct STEP as [m STAR STEPa].
    apply estar_vis_inv in STAR; rewrite <- STAR in STEPa.
    apply trans_vis_inv' in STEPa as (_ & ->).
    apply build_rel_ask in HL.
    now dependent destruction HL.
Qed.

Lemma sb'_eq_vis_inv {E C X Z R} :
  forall side (e f : E Z) (k k' : Z -> ctree E C X),
  sb'Proper R ->
  sb' R side X X Leq (Vis e k) (Vis f k') ->
  e = f /\ (forall side, R side X X Leq (Passive e k) (Passive f k')).
Proof.
  intros side e f k k' HP H.
  destruct side.
  - apply sb'_true_vis_inv in H as (HR & Heq); [| exact HP].
    apply build_rel_ask in Heq; dependent destruction Heq.
    auto.
  - apply sb'_false_ss' in H.
    apply ss'_vis_l_inv in H as (l' & u' & STEP & HR & HL).
    destruct STEP as [m STAR STEPa].
    apply estar_vis_inv in STAR; rewrite <- STAR in STEPa.
    apply trans_vis_inv' in STEPa as (EQ & ->).
    apply build_rel_ask in HL; dependent destruction HL.
    split; [reflexivity |].
    intro side'; rewrite <- EQ; apply HR.
Qed.

Definition guard_ctx {E B X} (R : @SS E B X -> Prop)
  (t : @SS E B X) :=
  exists t', t ⩸ (Active (Guard t')) /\ R (Active t').

Lemma epsilon_det_estar {E B X} (t t' : ctree E B X) :
  epsilon_det t t' -> (trans_alt ε)^* (Active t) (Active t').
Proof.
  induction 1.
  - apply estar_seq; constructor; exact H.
  - eapply estar_cons_epsilon.
    + eapply Transguard; [exact H0 | reflexivity].
    + exact IHepsilon_det.
Qed.

Section upto.
  Context {E F C D: Type -> Type}.

  #[local] Obligation Tactic := idtac.

  Program Definition ss_ctx3_l : mon (sb'R E F C D)
    := {| body R b X Y L t u :=
            b = true /\
            ss' (fun X Y L t u => forall side, R side X Y L t u) X Y L t u |}.
  Next Obligation.
    intros R R' HRR' b X Y L t u (-> & Hss); split; [reflexivity |].
    revert Hss; apply ss'_gen_mon;
      cbn; intros ? ? ? ? ? H side; apply HRR', H.
  Qed.

  Lemma ss_st'_l (r : Chain (@sb' E F C D)) :
    forall side X Y L x y, ss_ctx3_l `r side X Y L x y -> `r side X Y L x y.
  Proof.
    intros side X Y L x y (-> & Hss).
    apply (b_chain r); split; intro; [| easy].
    revert Hss; apply ss'_gen_mon.
    - cbn; intros ? ? ? ? ? HH; exact HH.
    - cbn; intros ? ? ? ? ? HH; apply HH.
  Qed.

  (* Up-to guard *)

  Program Definition guard_ctx3_l : mon (sb'R E F C D)
    := {| body R b X Y L t u := guard_ctx (fun t => R b X Y L t u) t |}.
  Next Obligation.
    intros R R' HRR' b X Y L t u (t0 & EQ & HR).
    exists t0; split; [exact EQ | apply HRR', HR].
  Qed.

  Program Definition guard_ctx3_r : mon (sb'R E F C D)
    := {| body R b X Y L t u := guard_ctx (fun u => R b X Y L t u) u |}.
  Next Obligation.
    intros R R' HRR' b X Y L t u (u0 & EQ & HR).
    exists u0; split; [exact EQ | apply HRR', HR].
  Qed.

  Lemma guard_ctx3_l_sbisim' (r : Chain (@sb' E F C D)) :
    forall side X Y L x y, guard_ctx3_l `r side X Y L x y -> `r side X Y L x y.
  Proof.
    apply tower.
    - intros ? INC side X Y L x y (t0 & EQ & HR) ? ?; red.
      apply INC; auto.
      exists t0; split; [exact EQ |].
      apply leq_infx in H.
      apply H, HR.
    - clear.
      intros R IH side X Y L x y (t0 & EQ & HR).
      split; intro; subst.
      + rewrite EQ.
        apply step_ss'_guard_l.
        apply (b_chain R); exact HR.
      + rewrite EQ.
        apply step_ss'_guard_r.
        now apply HR.
  Qed.

  Lemma guard_ctx3_r_sbisim' (r : Chain (@sb' E F C D)) :
    forall side X Y L x y, guard_ctx3_r `r side X Y L x y -> `r side X Y L x y.
  Proof.
    apply tower.
    - intros ? INC side X Y L x y (u0 & EQ & HR) ? ?; red.
      apply INC; auto.
      exists u0; split; [exact EQ |].
      apply leq_infx in H.
      apply H, HR.
    - clear.
      intros R IH side X Y L x y (u0 & EQ & HR).
      split; intro; subst.
      + rewrite EQ.
        apply step_ss'_guard_r.
        now apply HR.
      + rewrite EQ.
        apply step_ss'_guard_l.
        apply (b_chain R); exact HR.
  Qed.

  (* Up-to epsilon *)

  Program Definition epsilon_det_ctx3_l : mon (sb'R E F C D)
    := {| body R b X Y L t u :=
            b = true /\ exists t0 t1, t ⩸ (Active t0) /\ epsilon_det t0 t1
                        /\ R b X Y L (Active t1) u |}.
  Next Obligation.
    intros R R' HRR' b X Y L t u (-> & t0 & t1 & EQ & DET & HR).
    split; auto.
    exists t0, t1; ssplit.
    - exact EQ.
    - exact DET.
    - apply HRR', HR.
  Qed.

  Definition pure_bind_ctx {W X0} (P : X0 -> Prop) (R : @S E C W -> Prop)
    (t : @S E C W) :=
    exists (t0 : ctree E C X0) k0,
      t ⩸ (Active (CTree.bind t0 k0)) /\
      (forall l t', l <> ε -> ((trans_alt ε)^* ⋅ trans_alt l) (Active t0) t' ->
         exists v, l = val v /\ P v) /\
      forall x, P x -> R (Active (k0 x)).

  Program Definition pure_bind_ctx3_l {X0} (P : X0 -> Prop) : mon (sb'R E F C D)
    := {| body R b X Y L t u :=
            b = true /\ pure_bind_ctx P (fun t => R b X Y L t u) t |}.
  Next Obligation.
    intros X0 P R R' HRR' b X Y L t u (-> & t0 & k0 & EQ & HTR & HB).
    split; auto.
    exists t0, k0; ssplit.
    - exact EQ.
    - exact HTR.
    - intros v Pv; apply HRR', HB, Pv.
  Qed.

  Program Definition epsilon_ctx3_r : mon (sb'R E F C D)
    := {| body R b X Y L t u :=
            b = true /\ exists u', (trans_alt ε)^* u u' /\ R b X Y L t u' |}.
  Next Obligation.
    intros R R' HRR' b X Y L t u (-> & u' & STAR & HR).
    split; auto.
    exists u'; split; [exact STAR | apply HRR', HR].
  Qed.

  Lemma epsilon_det_ctx3_l_sbisim' (r : Chain (@sb' E F C D)) :
    forall side X Y L x y, epsilon_det_ctx3_l `r side X Y L x y -> `r side X Y L x y.
  Proof.
    apply tower.
    - intros ? INC side X Y L x y (-> & t0 & t1 & EQ & DET & HR) ? ?; red.
      apply INC; auto.
      split; auto.
      exists t0, t1; ssplit.
      + exact EQ.
      + exact DET.
      + apply leq_infx in H.
        apply H, HR.
    - clear.
      intros R IH side X Y L x y (-> & t0 & t1 & EQ & DET & HR).
      split; intro; [| easy].
      rewrite EQ; clear x EQ.
      revert HR; induction DET as [ta tb EQ01 | ta tb tc DET' IHDET EQg]; intro HR.
      + assert (SQ : (Active ta : @S E C X) ⩸ (Active tb))
          by (constructor; exact EQ01).
        rewrite SQ.
        now apply HR.
      + assert (SQ : (Active tc : @S E C X) ⩸ (Active (Guard ta)))
          by (constructor; exact EQg).
        rewrite SQ.
        apply step_ss'_guard_l.
        apply IH.
        split; auto.
        exists ta, tb; ssplit.
        * reflexivity.
        * exact DET'.
        * apply (b_chain R); exact HR.
  Qed.

  Lemma pure_bind_ctx3_l_sbisim' {X0} (P : X0 -> Prop) (r : Chain (@sb' E F C D)) :
    forall side X Y L x y, pure_bind_ctx3_l P `r side X Y L x y -> `r side X Y L x y.
  Proof.
    apply tower.
    - intros ? INC side X Y L x y (-> & t0 & k0 & EQ & HTR & HB) ? ?; red.
      apply INC; auto.
      split; auto.
      exists t0, k0; ssplit.
      + exact EQ.
      + exact HTR.
      + intros v Pv.
        apply leq_infx in H.
        apply H, HB, Pv.
    - clear.
      intros R IH side X Y L x y (-> & t0 & k0 & EQ & HTR & HB).
      split; intro; [| easy].
      rewrite EQ.
      split.
      + intros s l Hne TR.
        apply trans_bind_inv in TR as
          [ (v & EQt & TRk)
          | [ (-> & t1 & TRt & SQ)
          | [ (-> & _)
          | (Z & e & g & -> & TRt & SQ) ]]].
        * assert (HneV : (val v : @label E X0) <> ε) by easy.
          assert (cV : ((trans_alt ε)^* ⋅ trans_alt (val v))
                         (Active t0) (Active (Stuck : ctree E C X0))).
          { apply trans_star_l; eapply Transval; [exact EQt | reflexivity]. }
          destruct (HTR _ _ HneV cV) as (w & Hvw & Pw).
          apply val_eq_inv in Hvw; subst w.
          specialize (HB v Pw).
          destruct HB as [HB _]; specialize (HB eq_refl).
          destruct HB as [HBA _].
          destruct (HBA _ _ Hne TRk) as (l' & u' & RESP & HR & HL).
          exists l', u'; ssplit.
          -- exact RESP.
          -- exact HR.
          -- exact HL.
        * assert (Hneτ : (τ : @label E X0) <> ε) by easy.
          assert (cT : ((trans_alt ε)^* ⋅ trans_alt τ) (Active t0) (Active t1))
            by (apply trans_star_l; exact TRt).
          destruct (HTR _ _ Hneτ cT) as (w & Habs & _); easy.
        * easy.
        * assert (HneA : (ask e : @label E X0) <> ε) by easy.
          assert (cA : ((trans_alt ε)^* ⋅ trans_alt (ask e))
                         (Active t0) (Passive e g))
            by (apply trans_star_l; exact TRt).
          destruct (HTR _ _ HneA cA) as (w & Habs & _); easy.
      + intros s TR.
        apply trans_bind_inv in TR as
          [ (v & EQt & TRk)
          | [ (Habs & _)
          | [ (_ & t1 & TRt & SQ)
          | (Z & e & g & Habs & _) ]]].
        * assert (HneV : (val v : @label E X0) <> ε) by easy.
          assert (cV : ((trans_alt ε)^* ⋅ trans_alt (val v))
                         (Active t0) (Active (Stuck : ctree E C X0))).
          { apply trans_star_l; eapply Transval; [exact EQt | reflexivity]. }
          destruct (HTR _ _ HneV cV) as (w & Hvw & Pw).
          apply val_eq_inv in Hvw; subst w.
          specialize (HB v Pw).
          destruct HB as [HB _]; specialize (HB eq_refl).
          destruct HB as [_ HBB].
          destruct (HBB _ TRk) as (u' & STAR & HR).
          exists u'; split; [exact STAR | exact HR].
        * easy.
        * exists y; split.
          -- apply trans_star_self.
          -- rewrite SQ.
             apply IH.
             split; auto.
             exists t1, k0; ssplit.
             ++ reflexivity.
             ++ intros l t' Hne cTR.
                eapply (HTR l t'); [exact Hne |].
                eapply estar_cons_label; [exact TRt | exact cTR].
             ++ intros v Pv; apply (b_chain R), HB, Pv.
        * easy.
  Qed.

  Lemma epsilon_ctx3_r_sbisim' (r : Chain (@sb' E F C D)) :
    forall side X Y L x y, epsilon_ctx3_r `r side X Y L x y -> `r side X Y L x y.
  Proof.
    apply tower.
    - intros ? INC side X Y L x y (-> & u' & STAR & HR) ? ?; red.
      apply INC; auto.
      split; auto.
      exists u'; split; [exact STAR |].
      apply leq_infx in H.
      apply H, HR.
    - clear.
      intros R IH side X Y L x y (-> & u' & STAR & HR).
      split; intro; [| easy].
      eapply step_ss'_epsilon_r; [| exact STAR].
      now apply HR.
  Qed.

  #[global] Instance epsilon_det_st' {X Y} {L : lrel E F X Y} :
    forall (R : Chain (@sb' E F C D)),
    Proper (epsilon_det ==> epsilon_det ==> flip impl)
           (fun (t : ctree E C X) (u : ctree F D Y) => ` R true X Y L t u).
  Proof.
    intros R t t' DETt u u' DETu H.
    apply epsilon_det_ctx3_l_sbisim'.
    split; auto.
    exists t, t'; ssplit.
    - reflexivity.
    - exact DETt.
    - apply epsilon_ctx3_r_sbisim'.
      split; auto.
      exists (Active u'); split.
      + apply epsilon_det_estar; exact DETu.
      + exact H.
  Qed.

End upto.

(*|
Epsilon-absorption for the [sb'] game: the left player of the [true] side
(resp. the right player of the [false] side) may be advanced by ε-steps.
|*)
Lemma sbisim'_epsilon_l {E F C D X Y} (L : lrel E F X Y) :
  forall (t t' : @S E C X) (u : @S F D Y),
  gfp (@sb' E F C D) true X Y L t u ->
  (trans_alt ε)^* t t' ->
  gfp (@sb' E F C D) true X Y L t' u.
Proof.
  intros t t' u H STAR. step. split; intro; [| easy].
  eapply ss'_gen_epsilon_l.
  - cbn. intros ? ? H'. step in H'. now apply H'.
  - step in H. now apply H.
  - exact STAR.
Qed.

Lemma sbisim'_epsilon_r {E F C D X Y} (L : lrel E F X Y) :
  forall (t : @S E C X) (u u' : @S F D Y),
  gfp (@sb' E F C D) false X Y L t u ->
  (trans_alt ε)^* u u' ->
  gfp (@sb' E F C D) false X Y L t u'.
Proof.
  intros t u u' H STAR. step. split; intro; [easy |].
  eapply ss'_gen_epsilon_l.
  - cbn. intros ? ? H'. step in H'. now apply H'.
  - step in H. now apply H.
  - exact STAR.
Qed.

(*|
Right-hand inversions for [update_val_rel], complementing the left-hand
ones provided by SSimAlt. Needed for the [false] side of the bind lemma.
|*)
Section uvr_inv_r.

  Context {E F : Type -> Type} {X X' : Type}
          {L : rel (@label E X') (@label F X')} {R0 : rel X X}.

  Lemma update_val_rel_val_r (w : X) (l1 : @label E X) :
    update_val_rel L R0 l1 (val w) ->
    exists v, l1 = val v /\ R0 v w.
  Proof.
    intros H; dependent destruction H; eauto.
  Qed.

  Lemma update_val_rel_τ_r (l1 : @label E X) :
    update_val_rel L R0 l1 τ ->
    l1 = τ /\ L τ τ.
  Proof.
    intros H; dependent destruction H; eauto.
  Qed.

  Lemma update_val_rel_ask_r {Z'} (f : F Z') (l1 : @label E X) :
    update_val_rel L R0 l1 (ask f) ->
    exists Z (e : E Z), l1 = ask e /\ L (ask e) (ask f).
  Proof.
    intros H; dependent destruction H; eauto.
  Qed.

  Lemma update_val_rel_rcv_r {Z'} (f : F Z') (w : Z') (l1 : @label E X) :
    update_val_rel L R0 l1 (rcv f w) ->
    exists Z (e : E Z) (v : Z), l1 = rcv e v /\ L (rcv e v) (rcv f w).
  Proof.
    intros H; dependent destruction H; eauto.
  Qed.

End uvr_inv_r.

Section bind.
  Arguments label: clear implicits.

  Context {E F B : Type -> Type} {X X' : Type}
          (L : rel (@label E X') (@label F X'))
          (R0 : rel X X).

  Notation uvr := (update_val_rel L R0).

(*|
Up-to-bind for [sb']. As in SSimAlt, the continuations must be related at
the [gfp] level (they need to be stepped for the ε-conjunct), while the
prefixes are related by the [gfp] of [sb' uvr] at the same side.
|*)
  Lemma bind_chain_gen {R : Chain (@sb' E F B X' L)} :
    forall (t : ctree E B X) (t' : ctree F B X)
      (k : X -> ctree E B X') (k' : X -> ctree F B X') side,
      gfp (sb' uvr) side (Active t) (Active t') ->
      (forall side x x', R0 x x' -> `R side (Active (k x)) (Active (k' x'))) ->
      ` R side (Active (x <- t;; k x)) (Active (x <- t';; k' x)).
  Proof.
    apply (@tower _ _ _ (fun (P : bool -> rel (@SS E B X') (@SS F B X')) =>
      forall (t : ctree E B X) (t' : ctree F B X)
        (k : X -> ctree E B X') (k' : X -> ctree F B X') side,
        gfp (sb' uvr) side (Active t) (Active t') ->
        (forall side x x', R0 x x' -> P side (Active (k x)) (Active (k' x'))) ->
        P side (Active (x <- t;; k x)) (Active (x <- t';; k' x)))).
    - intros ? INC t t' k k' side tt kk ? ?; red.
      apply INC; auto. intros. apply kk; auto. 
    - clear; intros R IH t t' k k' side tt kk.
      split; intro; subst.
      + (* side = true *)
        split.
        * (* non-ε challenge on x <- t;; k x *)
          intros s l Hne TR.
          apply trans_bind_inv in TR as
            [ (x & EQt & TRk)
            | [ (-> & t1 & TRt & SQ)
            | [ (-> & _)
            | (Z & e & g & -> & TRt & SQ) ]]].
          -- (* the prefix returns; the step happens in k *)
             step in tt.
             destruct tt as [tt _]; specialize (tt eq_refl).
             destruct tt as [ttA _].
             assert (HneV : (val x : @label E X) <> ε) by easy.
             assert (TRv : trans_alt (val x) (Active t) (Active (Stuck : ctree E B X)))
               by (eapply Transval; [exact EQt | reflexivity]).
             destruct (ttA _ _ HneV TRv) as (l2 & n & RESP & _ & HL2).
             apply update_val_rel_val_l in HL2 as (x' & -> & Hx).
             destruct RESP as [m STAR STEPv].
             unfold trans_alt in STEPv; cbn in STEPv; dependent destruction STEPv.
             pose proof (kkT := kk true x x' Hx).
             destruct kkT as [kkT _]; specialize (kkT eq_refl).
             destruct kkT as [kkA _].
             destruct (kkA _ _ Hne TRk) as (l' & u' & RESP2 & Hall & HL').
             exists l', u'; ssplit.
             ++ destruct RESP2 as [m2 STAR2 STEP2].
                exists m2; [| exact STEP2].
                eapply estar_trans.
                ** apply estar_bind; exact STAR.
                ** eapply estar_trans; [| exact STAR2].
                   apply estar_seq; constructor.
                   rewrite H, bind_ret_l; reflexivity.
             ++ intro side'; apply Hall.
             ++ exact HL'.
          -- (* τ step in the prefix *)
             step in tt.
             destruct tt as [tt _]; specialize (tt eq_refl).
             destruct tt as [ttA _].
             assert (Hneτ : (τ : @label E X) <> ε) by easy.
             destruct (ttA _ _ Hneτ TRt) as (l2 & n & RESP & Htt' & HL2).
             apply update_val_rel_τ_l in HL2 as (-> & HLττ).
             destruct RESP as [m STAR STEPτ].
             unfold trans_alt in STEPτ; cbn in STEPτ; dependent destruction STEPτ.
             exists τ, (Active (x <- u;; k' x)); ssplit.
             ++ exists (Active (x <- t0;; k' x)).
                ** apply estar_bind; exact STAR.
                ** apply trans_bind_l_τ; eapply Transstep; eauto.
             ++ intro side'; rewrite SQ.
                apply IH. 
                ** apply Htt'.
                ** intros. step. now apply kk. 
             ++ exact HLττ.
          -- easy.
          -- (* ask step in the prefix: the short trip through passives *)
             step in tt.
             destruct tt as [tt _]; specialize (tt eq_refl).
             destruct tt as [ttA _].
             assert (HneA : (ask e : @label E X) <> ε) by easy.
             destruct (ttA _ _ HneA TRt) as (l2 & n & RESP & Htt' & HL2).
             apply update_val_rel_ask_l in HL2 as (Z' & f & -> & HLaa).
             destruct RESP as [m STAR STEPa].
             unfold trans_alt in STEPa; cbn in STEPa; dependent destruction STEPa.
             exists (ask f), (Passive f (fun z => x <- k0 z;; k' x)); ssplit.
             ++ exists (Active (x <- t0;; k' x)).
                ** apply estar_bind; exact STAR.
                ** apply trans_bind_l_ask; econstructor; exact H.
             ++ intro side'; rewrite SQ.
                apply (b_chain R).
                split; intro; subst.
                ** (* challenges of the E-side passive *)
                   split.
                   --- intros s2 l2 Hne2 TR2.
                       apply trans_passive_inv' in TR2 as (z & SQ2 & ->).
                       pose proof (HttT := Htt' true).
                       step in HttT.
                       destruct HttT as [HttT _]; specialize (HttT eq_refl).
                       destruct HttT as [HttA _].
                       assert (HneR : (rcv e z : @label E X) <> ε) by easy.
                       assert (TRr : trans_alt (rcv e z) (Passive e g) (Active (g z)))
                         by (econstructor; reflexivity).
                       destruct (HttA _ _ HneR TRr) as (l3 & n3 & RESP3 & Hall3 & HL3).
                       apply update_val_rel_rcv_l in HL3 as (Z2 & f2 & w & -> & HLrr).
                       destruct RESP3 as [m3 STAR3 STEP3].
                       apply estar_passive in STAR3.
                       dependent destruction STAR3.
                       apply trans_passive_inv' in STEP3 as (w' & SQ3 & Heq).
                       dependent destruction Heq.
                       dependent destruction SQ3.
                       exists (rcv f w'), (Active (x <- k0 w';; k' x)); ssplit.
                       +++ apply trans_star_l; econstructor; reflexivity.
                       +++ intro side''; rewrite SQ2.
                           assert (SQ5 : (Active (x <- t1;; k' x) : @SS F B X')
                                           ⩸ (Active (x <- k0 w';; k' x))).
                           { constructor; rewrite EQ0, <- (EQ w'); reflexivity. }
                           rewrite <- SQ5; apply IH; [apply Hall3 | intros; step; now apply kk].
                       +++ exact HLrr.
                   --- intros s2 TR2.
                       apply trans_passive_inv' in TR2 as (z & _ & Habs); easy.
                ** (* challenges of the F-side passive *)
                   split.
                   --- intros s2 l2 Hne2 TR2.
                       apply trans_passive_inv' in TR2 as (w & SQ2 & ->).
                       pose proof (HttF := Htt' false).
                       step in HttF.
                       destruct HttF as [_ HttF]; specialize (HttF eq_refl).
                       destruct HttF as [HttA _].
                       assert (HneR : (rcv f w : @label F X) <> ε) by easy.
                       assert (TRr : trans_alt (rcv f w) (Passive f k0) (Active (k0 w)))
                         by (econstructor; reflexivity).
                       destruct (HttA _ _ HneR TRr) as (l3 & n3 & RESP3 & Hall3 & HL3).
                       apply update_val_rel_rcv_r in HL3 as (Z2 & e2 & v & -> & HLrr).
                       destruct RESP3 as [m3 STAR3 STEP3].
                       apply estar_passive in STAR3.
                       dependent destruction STAR3.
                       apply trans_passive_inv' in STEP3 as (v' & SQ3 & Heq).
                       dependent destruction Heq.
                       dependent destruction SQ3.
                       exists (rcv e v'), (Active (x <- g v';; k x)); ssplit.
                       +++ apply trans_star_l; econstructor; reflexivity.
                       +++ intro side''; rewrite SQ2.
                           assert (SQ5 : (Active (x <- t1;; k x) : @SS E B X')
                                           ⩸ (Active (x <- g v';; k x))).
                           { constructor; rewrite EQ0, <- (EQ v'); reflexivity. }
                           rewrite <- SQ5; apply IH; [apply Hall3 | intros; step; now apply kk].
                       +++ exact HLrr.
                   --- intros s2 TR2.
                       apply trans_passive_inv' in TR2 as (w & _ & Habs); easy.
             ++ exact HLaa.
        * (* ε challenge on x <- t;; k x *)
          intros s TR.
          apply trans_bind_inv in TR as
            [ (x & EQt & TRk)
            | [ (Habs & _)
            | [ (_ & t1 & TRt & SQ)
            | (Z & e & g & Habs & _) ]]].
          -- step in tt.
             destruct tt as [tt _]; specialize (tt eq_refl).
             destruct tt as [ttA _].
             assert (HneV : (val x : @label E X) <> ε) by easy.
             assert (TRv : trans_alt (val x) (Active t) (Active (Stuck : ctree E B X)))
               by (eapply Transval; [exact EQt | reflexivity]).
             destruct (ttA _ _ HneV TRv) as (l2 & n & RESP & _ & HL2).
             apply update_val_rel_val_l in HL2 as (x' & -> & Hx).
             destruct RESP as [m STAR STEPv].
             unfold trans_alt in STEPv; cbn in STEPv; dependent destruction STEPv.
             pose proof (kkT := kk true x x' Hx).
             destruct kkT as [kkT _]; specialize (kkT eq_refl).
             destruct kkT as [_ kkB].
             destruct (kkB _ TRk) as (u2 & STARu & Hgfp2).
             exists u2; split.
             ++ eapply estar_trans.
                ** apply estar_bind; exact STAR.
                ** eapply estar_trans; [| exact STARu].
                   apply estar_seq; constructor.
                   rewrite H, bind_ret_l; reflexivity.
             ++ exact Hgfp2.
          -- easy.
          -- exists (Active (x <- t';; k' x)); split.
             ++ apply trans_star_self.
             ++ rewrite SQ; apply IH; [| intros; step; now apply kk].
                eapply sbisim'_epsilon_l; [exact tt | apply estar_single; exact TRt].
          -- easy.
      + (* side = false *)
        split.
        * (* non-ε challenge on x <- t';; k' x *)
          intros s l Hne TR.
          apply trans_bind_inv in TR as
            [ (x' & EQt & TRk)
            | [ (-> & t1 & TRt & SQ)
            | [ (-> & _)
            | (Z & f & g & -> & TRt & SQ) ]]].
          -- (* the prefix returns; the step happens in k' *)
             step in tt.
             destruct tt as [_ tt]; specialize (tt eq_refl).
             destruct tt as [ttA _].
             assert (HneV : (val x' : @label F X) <> ε) by easy.
             assert (TRv : trans_alt (val x') (Active t') (Active (Stuck : ctree F B X)))
               by (eapply Transval; [exact EQt | reflexivity]).
             destruct (ttA _ _ HneV TRv) as (l2 & n & RESP & _ & HL2).
             apply update_val_rel_val_r in HL2 as (x & -> & Hx).
             destruct RESP as [m STAR STEPv].
             unfold trans_alt in STEPv; cbn in STEPv; dependent destruction STEPv.
             pose proof (kkF := kk false x x' Hx).
             destruct kkF as [_ kkF]; specialize (kkF eq_refl).
             destruct kkF as [kkA _].
             destruct (kkA _ _ Hne TRk) as (l' & u' & RESP2 & Hall & HL').
             exists l', u'; ssplit.
             ++ destruct RESP2 as [m2 STAR2 STEP2].
                exists m2; [| exact STEP2].
                eapply estar_trans.
                ** apply estar_bind; exact STAR.
                ** eapply estar_trans; [| exact STAR2].
                   apply estar_seq; constructor.
                   rewrite H, bind_ret_l; reflexivity.
             ++ intro side'; apply Hall.
             ++ exact HL'.
          -- (* τ step in the prefix *)
             step in tt.
             destruct tt as [_ tt]; specialize (tt eq_refl).
             destruct tt as [ttA _].
             assert (Hneτ : (τ : @label F X) <> ε) by easy.
             destruct (ttA _ _ Hneτ TRt) as (l2 & n & RESP & Htt' & HL2).
             apply update_val_rel_τ_r in HL2 as (-> & HLττ).
             destruct RESP as [m STAR STEPτ].
             unfold trans_alt in STEPτ; cbn in STEPτ; dependent destruction STEPτ.
             exists τ, (Active (x <- u;; k x)); ssplit.
             ++ exists (Active (x <- t0;; k x)).
                ** apply estar_bind; exact STAR.
                ** apply trans_bind_l_τ; eapply Transstep; eauto.
             ++ intro side'; rewrite SQ.
                apply IH; [apply Htt' | intros; step; now apply kk].
             ++ exact HLττ.
          -- easy.
          -- (* ask step in the prefix: the short trip, mirrored *)
             step in tt.
             destruct tt as [_ tt]; specialize (tt eq_refl).
             destruct tt as [ttA _].
             assert (HneA : (ask f : @label F X) <> ε) by easy.
             destruct (ttA _ _ HneA TRt) as (l2 & n & RESP & Htt' & HL2).
             apply update_val_rel_ask_r in HL2 as (Z' & e & -> & HLaa).
             destruct RESP as [m STAR STEPa].
             unfold trans_alt in STEPa; cbn in STEPa; dependent destruction STEPa.
             exists (ask e), (Passive e (fun z => x <- k0 z;; k x)); ssplit.
             ++ exists (Active (x <- t0;; k x)).
                ** apply estar_bind; exact STAR.
                ** apply trans_bind_l_ask; econstructor; exact H.
             ++ intro side'; rewrite SQ.
                apply (b_chain R).
                split; intro; subst.
                ** (* challenges of the E-side passive *)
                   split.
                   --- intros s2 l2 Hne2 TR2.
                       apply trans_passive_inv' in TR2 as (z & SQ2 & ->).
                       pose proof (HttT := Htt' true).
                       step in HttT.
                       destruct HttT as [HttT _]; specialize (HttT eq_refl).
                       destruct HttT as [HttA _].
                       assert (HneR : (rcv e z : @label E X) <> ε) by easy.
                       assert (TRr : trans_alt (rcv e z) (Passive e k0) (Active (k0 z)))
                         by (econstructor; reflexivity).
                       destruct (HttA _ _ HneR TRr) as (l3 & n3 & RESP3 & Hall3 & HL3).
                       apply update_val_rel_rcv_l in HL3 as (Z2 & f2 & w & -> & HLrr).
                       destruct RESP3 as [m3 STAR3 STEP3].
                       apply estar_passive in STAR3.
                       dependent destruction STAR3.
                       apply trans_passive_inv' in STEP3 as (w' & SQ3 & Heq).
                       dependent destruction Heq.
                       dependent destruction SQ3.
                       exists (rcv f w'), (Active (x <- g w';; k' x)); ssplit.
                       +++ apply trans_star_l; econstructor; reflexivity.
                       +++ intro side''; rewrite SQ2.
                           assert (SQ5 : (Active (x <- t1;; k' x) : @SS F B X')
                                           ⩸ (Active (x <- g w';; k' x))).
                           { constructor; rewrite EQ0, <- (EQ w'); reflexivity. }
                           rewrite <- SQ5; apply IH; [apply Hall3 | intros; step; now apply kk].
                       +++ exact HLrr.
                   --- intros s2 TR2.
                       apply trans_passive_inv' in TR2 as (z & _ & Habs); easy.
                ** (* challenges of the F-side passive *)
                   split.
                   --- intros s2 l2 Hne2 TR2.
                       apply trans_passive_inv' in TR2 as (w & SQ2 & ->).
                       pose proof (HttF := Htt' false).
                       step in HttF.
                       destruct HttF as [_ HttF]; specialize (HttF eq_refl).
                       destruct HttF as [HttA _].
                       assert (HneR : (rcv f w : @label F X) <> ε) by easy.
                       assert (TRr : trans_alt (rcv f w) (Passive f g) (Active (g w)))
                         by (econstructor; reflexivity).
                       destruct (HttA _ _ HneR TRr) as (l3 & n3 & RESP3 & Hall3 & HL3).
                       apply update_val_rel_rcv_r in HL3 as (Z2 & e2 & v & -> & HLrr).
                       destruct RESP3 as [m3 STAR3 STEP3].
                       apply estar_passive in STAR3.
                       dependent destruction STAR3.
                       apply trans_passive_inv' in STEP3 as (v' & SQ3 & Heq).
                       dependent destruction Heq.
                       dependent destruction SQ3.
                       exists (rcv e v'), (Active (x <- k0 v';; k x)); ssplit.
                       +++ apply trans_star_l; econstructor; reflexivity.
                       +++ intro side''; rewrite SQ2.
                           assert (SQ5 : (Active (x <- t1;; k x) : @SS E B X')
                                           ⩸ (Active (x <- k0 v';; k x))).
                           { constructor; rewrite EQ0, <- (EQ v'); reflexivity. }
                           rewrite <- SQ5; apply IH; [apply Hall3 | intros; step; now apply kk].
                       +++ exact HLrr.
                   --- intros s2 TR2.
                       apply trans_passive_inv' in TR2 as (w & _ & Habs); easy.
             ++ exact HLaa.
        * (* ε challenge on x <- t';; k' x *)
          intros s TR.
          apply trans_bind_inv in TR as
            [ (x' & EQt & TRk)
            | [ (Habs & _)
            | [ (_ & t1 & TRt & SQ)
            | (Z & f & g & Habs & _) ]]].
          -- step in tt.
             destruct tt as [_ tt]; specialize (tt eq_refl).
             destruct tt as [ttA _].
             assert (HneV : (val x' : @label F X) <> ε) by easy.
             assert (TRv : trans_alt (val x') (Active t') (Active (Stuck : ctree F B X)))
               by (eapply Transval; [exact EQt | reflexivity]).
             destruct (ttA _ _ HneV TRv) as (l2 & n & RESP & _ & HL2).
             apply update_val_rel_val_r in HL2 as (x & -> & Hx).
             destruct RESP as [m STAR STEPv].
             unfold trans_alt in STEPv; cbn in STEPv; dependent destruction STEPv.
             pose proof (kkF := kk false x x' Hx).
             destruct kkF as [_ kkF]; specialize (kkF eq_refl).
             destruct kkF as [_ kkB].
             destruct (kkB _ TRk) as (u2 & STARu & Hgfp2).
             exists u2; split.
             ++ eapply estar_trans.
                ** apply estar_bind; exact STAR.
                ** eapply estar_trans; [| exact STARu].
                   apply estar_seq; constructor.
                   rewrite H, bind_ret_l; reflexivity.
             ++ apply Hgfp2.
          -- easy.
          -- exists (Active (x <- t;; k x)); split.
             ++ apply trans_star_self.
             ++ rewrite SQ; apply IH; [| intros; step; now apply kk].
                eapply sbisim'_epsilon_r; [exact tt | apply estar_single; exact TRt].
          -- easy.
  Qed.

End bind.

(*|
Expliciting the reasoning rule provided by the up-to principles.
|*)


(* Note: In this section, I changed the relation between t1 and t2 to 
   be at the gfp.  *)

Lemma st'_clo_bind {E F B: Type -> Type} {X X': Type} {L : rel (@label E X') (@label F X')}
      (R0 : rel X X)
      side
      (t1 : ctree E B X) (t2: ctree F B X)
      (k1 : X -> ctree E B X') (k2 : X -> ctree F B X')
      (R : Chain (@sb' E F B X' L)) :
  gfp (sb' (update_val_rel L R0)) side (Active t1) (Active t2) ->
  (forall x y, R0 x y -> forall b, gfp (sb' L) b (Active (k1 x)) (Active (k2 y))) ->
  `R side (Active (x <- t1;; k1 x)) (Active (x <- t2;; k2 x)).
Proof.
  intros H1 H2.
  eapply bind_chain_gen; [exact H1 |].
  intros b x x' Hxx'; apply H2, Hxx'.
Qed.

Lemma sbisim'_clo_bind {E F B: Type -> Type} {X X': Type} {L : rel (@label E X') (@label F X')}
      (R0 : rel X X)
      side
      (t1 : ctree E B X) (t2: ctree F B X)
      (k1 : X -> ctree E B X') (k2 : X -> ctree F B X') :
  gfp (sb' (update_val_rel L R0)) side (Active t1) (Active t2) ->
  (forall x y, R0 x y -> forall b, gfp (sb' L) b (Active (k1 x)) (Active (k2 y))) ->
  gfp (sb' L) side (Active (x <- t1;; k1 x)) (Active (x <- t2;; k2 x)).
Proof.
  intros H1 H2.
  apply (@st'_clo_bind E F B X X' L R0 side t1 t2 k1 k2 (chain_gfp (sb' L))); assumption.
Qed.

(*|
[eq] as label relation is preserved by [update_val_rel].
|*)
Lemma sbisim_update_val_rel_eq {E B X X'} :
  forall side (t u : @SS E B X),
    gfp (@sb' E E B X eq) side t u ->
    gfp (sb' (@update_val_rel E E X X' eq eq)) side t u.
Proof.
  apply (@tower _ _ _ (fun (P : bool -> rel (@SS E B X) (@SS E B X)) =>
    forall side t u, gfp (@sb' E E B X eq) side t u -> P side t u)).
  - intros ? INC side t u H ? ?; red.
    apply INC; auto.
  - clear; intros R IH side t u H.
    step in H.
    split; intro; subst.
    + destruct H as [H _]; specialize (H eq_refl); destruct H as [HA HB].
      split.
      * intros s l Hne TR.
        destruct (HA _ _ Hne TR) as (l' & u' & RESP & Hall & HL).
        subst l'.
        exists l, u'; ssplit.
        -- exact RESP.
        -- intro side'; apply IH, Hall.
        -- apply update_val_rel_eq_refl; exact Hne.
      * intros s TR.
        destruct (HB _ TR) as (u' & STAR & Hrep).
        exists u'; split; [exact STAR | apply IH, Hrep].
    + destruct H as [_ H]; specialize (H eq_refl); destruct H as [HA HB].
      split.
      * intros s l Hne TR.
        destruct (HA _ _ Hne TR) as (l' & u' & RESP & Hall & HL).
        unfold flip in HL; subst l'.
        exists l, u'; ssplit.
        -- exact RESP.
        -- intro side'; apply IH, Hall.
        -- apply update_val_rel_eq_refl; exact Hne.
      * intros s TR.
        destruct (HB _ TR) as (u' & STAR & Hrep).
        exists u'; split; [exact STAR | apply IH, Hrep].
Qed.

Lemma st'_clo_bind_eq {E B: Type -> Type} {X X': Type}
      side (t1 t2 : ctree E B X)
      (k1 k2 : X -> ctree E B X')
      (R : Chain (@sb' E E B X' eq)) :
  gfp (sb' eq) side (Active t1) (Active t2) ->
  (forall x b, gfp (@sb' E E B X' eq) b (Active (k1 x)) (Active (k2 x))) ->
  ` R side (Active (x <- t1;; k1 x)) (Active (x <- t2;; k2 x)).
Proof.
  intros H1 H2.
  eapply bind_chain_gen with (R0 := eq).
  - apply sbisim_update_val_rel_eq; exact H1.
  - intros b x x' ->; apply H2.
Qed.

Lemma sbisim'_clo_bind_eq {E B: Type -> Type} {X X': Type} :
  forall side (t1 t2 : ctree E B X) (k1 k2 : X -> ctree E B X'),
  gfp (@sb' E E B X eq) side (Active t1) (Active t2) ->
  (forall x b, gfp (@sb' E E B X' eq) b (Active (k1 x)) (Active (k2 x))) ->
  gfp (sb' eq) side (Active (x <- t1;; k1 x)) (Active (x <- t2;; k2 x)).
Proof.
  intros.
  apply (@st'_clo_bind_eq E B X X' side t1 t2 k1 k2 (chain_gfp (sb' eq))); assumption.
Qed.

Lemma step_sb'_guard_l' {E F B X L}
  (t: ctree E B X) (t': @SS F B X)
      (R : Chain (@sb' E F B X L)) :
  (forall side, `R side t t') ->
  forall side, `R side (Guard t) t'.
Proof.
  intros H side.
  apply guard_ctx3_l_sbisim'.
  exists t; split; [reflexivity | apply H].
Qed.

Lemma step_sb'_guard_r' {E F B X L}
  (t: @SS E B X) (t': ctree F B X) (R : Chain (@sb' E F B X L)) :
  (forall side, `R side t t') ->
  forall side, `R side t (Guard t').
Proof.
  intros H side.
  apply guard_ctx3_r_sbisim'.
  exists t'; split; [reflexivity | apply H].
Qed.

(*|
The classic single-shot strong bisimulation over the combined-step LTS,
and its equivalence with [sbisim'].
|*)
#[local] Obligation Tactic := idtac.
Program Definition sb {E F B X} (L : rel (@label E X) (@label F X)) :
  mon (@SS E B X -> @SS F B X -> Prop) :=
  {| body R t u := ss L R t u /\ ss (flip L) (flip R) u t |}.
Next Obligation.
  intros E F B X L R R' HRR' t u (H1 & H2); split.
  - intros t' l Hne TR.
    destruct (H1 _ _ Hne TR) as (l' & u' & STEP & HR & HL).
    exists l', u'; ssplit; auto.
    apply HRR', HR.
  - intros u' l Hne TR.
    destruct (H2 _ _ Hne TR) as (l' & t' & STEP & HR & HL).
    exists l', t'; ssplit; auto.
    apply HRR', HR.
Qed.
#[local] Obligation Tactic := Tactics.program_simpl.

Definition sbisim {E F B X} L := (gfp (@sb E F B X L) : hrel _ _).

Lemma ss_sb'_l_chain {E F B X L} {R : Chain (@sb' E F B X L)} :
  forall (t : @SS E B X) (u : @SS F B X),
  ss L (fun t u => forall b, `R b t u) t u ->
  sb' L `R true t u.
Proof.
  intros t u HSS; split; intro; [| easy].
  split.
  - intros t' l Hne TR.
    assert (cTR : ((trans_alt (B:=B) ε)^* ⋅ trans_alt l) t t')
      by (apply trans_star_l; exact TR).
    destruct (HSS _ _ Hne cTR) as (l' & u' & STEP & HR & HL).
    exists l', u'; ssplit; assumption.
  - intros t' TR.
    exists u; split.
    + apply trans_star_self.
    + apply ss_st'_l.
      split; auto.
      intros t'' l Hne cTR.
      assert (cTR2 : ((trans_alt (B:=B) ε)^* ⋅ trans_alt l) t t'')
        by (eapply estar_cons_label; [exact TR | exact cTR]).
      destruct (HSS _ _ Hne cTR2) as (l' & u' & STEP & HR & HL).
      exists l', u'; ssplit; assumption.
Qed.

(* first half of the theorem *)
Theorem gfp_sb'_ss_sbisim {E F B X} :
  forall L (t : @SS E B X) (u : @SS F B X),
  (ss L (sbisim L) t u -> gfp (sb' L) true t u) /\
  (ss (flip L) (flip (sbisim L)) u t -> gfp (sb' L) false t u).
Proof.
  intros L. coinduction R CH. intros t u.
  split; intro H.
  - apply ss_sb'_l_chain.
    intros t' l Hne cTR.
    destruct (H _ _ Hne cTR) as (l' & u' & STEP & HR & HL).
    exists l', u'; ssplit.
    + assumption.
    + intro b. step in HR. destruct HR as [HR1 HR2].
      destruct b.
      * apply CH; exact HR1.
      * apply CH; exact HR2.
    + assumption.
  - split; intro; [easy |].
    split.
    + intros u1 l Hne TR.
      assert (cTR : ((trans_alt (B:=B) ε)^* ⋅ trans_alt l) u u1)
        by (apply trans_star_l; exact TR).
      destruct (H _ _ Hne cTR) as (l' & t1 & STEP & HR & HL).
      exists l', t1; ssplit.
      * assumption.
      * intro b. step in HR. destruct HR as [HR1 HR2].
        destruct b.
        -- apply CH; exact HR1.
        -- apply CH; exact HR2.
      * assumption.
    + intros u1 TR.
      exists t; split.
      * apply trans_star_self.
      * apply CH.
        intros u2 l Hne cTR.
        apply (H u2 l Hne).
        eapply estar_cons_label; [exact TR | exact cTR].
Qed.

Lemma gfp_sb'_true_ss_sbisim {E F B X} :
  forall L (t : @SS E B X) (u : @SS F B X),
  ss L (sbisim L) t u -> gfp (sb' L) true t u.
Proof.
  intros L t u; apply (gfp_sb'_ss_sbisim L t u).
Qed.

(* main result. both halves are a proof by coinduction; 
   the first half is proved seperately in [gfp_sb'_ss_sbisim]. *)
Theorem sbisim_sbisim' {E F B X} :
  forall L (t : @SS E B X) (t' : @SS F B X), sbisim L t t' <-> sbisim' L t t'.
Proof.
  split; intro H.
  (* immediate from [gfp_sb'_ss_sbisim] *)
  - intro side; destruct side.
    + apply (gfp_sb'_ss_sbisim L t t'). step in H. apply H.
    + apply (gfp_sb'_ss_sbisim L t t'). step in H. apply H.
  - revert t t' H. unfold sbisim. coinduction R CH. intros t t' H.
    split.
    + intros s l Hne cTR.
      destruct cTR as [m STAR STEP].
      pose proof (HT := H true).
      eapply sbisim'_epsilon_l in HT; [| exact STAR].
      step in HT.
      destruct HT as [HT _]; specialize (HT eq_refl); destruct HT as [HTA _].
      destruct (HTA _ _ Hne STEP) as (l' & u' & RESP & Hall & HL).
      exists l', u'; ssplit.
      * assumption.
      * apply CH; exact Hall.
      * assumption.
    + intros s l Hne cTR.
      destruct cTR as [m STAR STEP].
      pose proof (HF := H false).
      eapply sbisim'_epsilon_r in HF; [| exact STAR].
      step in HF.
      destruct HF as [_ HF]; specialize (HF eq_refl); destruct HF as [HFA _].
      destruct (HFA _ _ Hne STEP) as (l' & u' & RESP & Hall & HL).
      exists l', u'; ssplit.
      * assumption.
      * apply CH; exact Hall.
      * assumption.
Qed.

Corollary sbisim_gfp_sb' {E F B X} :
  forall L side (t : @SS E B X) (t' : @SS F B X), sbisim L t t' -> gfp (sb' L) side t t'.
Proof.
  intros. apply sbisim_sbisim' in H. apply H.
Qed.

(* split converse *)
Theorem ss_sbisim_gfp_sb' {E F B X} :
  forall L (t : @SS E B X) (u : @SS F B X),
  (gfp (sb' L) true t u -> ss L (sbisim L) t u) /\
  (gfp (sb' L) false t u -> ss (flip L) (flip (sbisim L)) u t).
Proof.
  intros L t u; split; intro H.
  - intros t1 l Hne cTR.
    destruct cTR as [m STAR STEP].
    eapply sbisim'_epsilon_l in H; [| exact STAR].
    step in H.
    destruct H as [H _]; specialize (H eq_refl); destruct H as [HA _].
    destruct (HA _ _ Hne STEP) as (l' & u' & RESP & Hall & HL).
    exists l', u'; ssplit.
    + assumption.
    + apply sbisim_sbisim'; intro side; apply Hall.
    + assumption.
  - intros u1 l Hne cTR.
    destruct cTR as [m STAR STEP].
    eapply sbisim'_epsilon_r in H; [| exact STAR].
    step in H.
    destruct H as [_ H]; specialize (H eq_refl); destruct H as [HA _].
    destruct (HA _ _ Hne STEP) as (l' & t1 & RESP & Hall & HL).
    exists l', t1; ssplit.
    + assumption.
    + apply sbisim_sbisim'; intro side; apply Hall.
    + assumption.
Qed.

(*
Tactic Notation "__upto_bind_sbisim'" uconstr(R0) := TODO
Tactic Notation "__upto_bind_eq_sbisim'" uconstr(R0) := TODO
*)
