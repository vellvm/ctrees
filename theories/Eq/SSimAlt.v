From Stdlib Require Import
     Lia
     Basics
     Fin
     RelationClasses
     Program.Equality
     Logic.Eqdep.


From ITree Require Import Core.Subevent.

From CTree Require Import
     CTree
     Utils
     Eq.Equ
     Eq.TransAlt
     Eq.EstarTheory
     Eq.Epsilon.

From RelationAlgebra Require Export
     monoid kat kat_tac rel srel.
From Coinduction Require Import all.

Import CoindNotations.
Import CTree.
Set Implicit Arguments.

Ltac ssplit := split; [| split].

Section StrongSimAlt.

    (*|
An alternative definition [ss'] of strong simulation.
The simulation challenge does not involve an inductive transition relation,
thus simplifying proofs.
|*)

Definition ss'_gen {E F C D : Type -> Type} 
(R Reps : (forall [X Y], lrel E F X Y -> @S E C X -> @S F D Y -> Prop)) 
{X Y : Type} (L : lrel E F X Y) (t: @S E C X) (u: @S F D Y) :=
    (forall t' l, l <> ε -> trans_alt (B:=C) l t t'
    -> exists l' u', ((trans_alt (B:=D) ε)^* ⋅ (trans_alt l')) u u' /\ R L t' u' /\ L l l')
    /\
      (forall t', trans_alt (B:=C) ε t t' -> exists u', (trans_alt (B:=D) ε)^* u u' /\ Reps L t' u'). 

(*|
[ss'_gen] is monotone in both of its relational arguments independently.
|*)
#[global] Instance ss'_gen_mon {E F C D} :
  Proper (leq ==> leq ==> leq) (@ss'_gen E F C D).
Proof.
  intros R R' HR Reps Reps' HReps X Y L t u [Hprogress Heps].
  split; intros.
    - destruct (Hprogress _ _ H H0) as (l'' & u'' & Htrans & HRtu & HL').
      cbn in HR. eauto 12.
    - apply Heps in H as (u' & Htrans & HRtu).
      cbn in HReps. eauto 12.
  Qed.

  Definition ss'_ {E F C D : Type -> Type} :
  (forall (X Y : Type),
    lrel E F X Y -> (* L *)
    hrel (@S E C X) (* t *)
         (@S F D Y) (* u *)
    ) ->
  (forall (X Y : Type),
    lrel E F X Y -> (* L *)
    hrel (@S E C X) (* t *)
         (@S F D Y) (* u *)
    ) :=
    fun (R : forall (X Y : Type),
    lrel E F X Y -> (* L *)
    hrel (@S E C X) (* t *)
         (@S F D Y) (* u *)
    ) => @ss'_gen E F C D R R. (* simulation: R and Reps are the same relation *)

#[global] Instance ss'__mon {E F C D} : Proper (leq ==> leq) (@ss'_ E F C D).
Proof.
  intros R R' HR. now apply ss'_gen_mon.
  Qed.


  Program Definition ss' {E F C D : Type -> Type} :
    mon (forall (X Y : Type),
    lrel E F X Y -> (* L *)
    hrel (@S E C X) (* t *)
         (@S F D Y) (* u *)
    ) :=
    {| body R := @ss'_ E F C D R ; Hbody := ss'__mon (* simulation: R and Reps are the same relation *)
    |}.

  #[global] Instance weq_ss' {E F C D} :
    Proper (weq ==> weq) (@ss' E F C D).
  Proof.
    cbn. intros L L' HL R x y; split; intros (HA & HB); split; intros.
    - destruct (HA _ _ H H0) as (l'' & u'' & Htrans & HR & HL').
      do 2 esplit; split; eauto. split; [now apply HL | assumption].
    - apply HB in H as (u' & Htr & HL_).
      exists u'; split; auto. now apply HL. 
    - destruct (HA _ _ H H0) as (l'' & u'' & Htrans & HR & HL').
      do 2 esplit; split; eauto. split; [now apply HL | assumption].
    - apply HB in H as (u' & Htr & HL_).
      exists u'; split; auto. now apply HL.
  Qed.

End StrongSimAlt.

Definition ssim' {E F C D X Y} L :=
  (gfp (@ss' E F C D) X Y L : hrel _ _).

Section ssim'_theory.
  Arguments label: clear implicits.
  Context {E F C D: Type -> Type} {X Y : Type}
          {R: forall X Y, lrel E F X Y -> rel (@S E C X) (@S F D Y)}
          {L: lrel E F X Y}.

(*|
   Strong simulation up-to [equ] is valid. Note Seq is eq lifted to SS
   (active/passive tags).
   ----------------------------------------
|*)

  #[global] Instance Seq_proper_ss'_chain_goal {c: Chain (@ss' E F C D)} :
    Proper (Seq ==> Seq ==> flip impl) (`c X Y L).
  Proof.
    tower induction.   
    - intros CIH x y Hseq x' y' Hseq2 [Hnonep Hep]. 
    split; intros. 
    + rewrite Hseq in H0. destruct (Hnonep _ _ H H0) as 
    (l' & u' & Htr & Hc & HL). rewrite <- Hseq2 in Htr. 
      exists l', u'; split; eauto.
    + rewrite Hseq in H. apply Hep in H as (u' & Htr & Hc).
    rewrite <- Hseq2 in Htr. 
      exists u'; split; eauto.  
  Qed.

  #[global] Instance Seq_proper_ss'_chain_ctx  {c: Chain (@ss' E F C D)} :
    Proper (Seq ==> Seq ==> impl) (`c X Y L).
  Proof.
    tower induction. 
    - intros CIH x y Hseq x' y' Hseq2 [Hnonep Hep]. 
    split; intros. 
    + rewrite <- Hseq in H0. destruct (Hnonep _ _ H H0) as 
    (l' & u' & Htr & Hc & HL). rewrite Hseq2 in Htr. 
      exists l', u'; split; eauto.
    + rewrite <- Hseq in H. apply Hep in H as (u' & Htr & Hc).
    rewrite Hseq2 in Htr. 
      exists u'; split; eauto.  
  Qed.


  #[global] Instance Seq_proper_ssim'_goal : Proper (Seq ==> Seq ==> flip impl) (@ssim' E F C D X Y L).
  Proof.
    exact (@Seq_proper_ss'_chain_goal (chain_gfp (@ss' E F C D))).
  Qed.

  #[global] Instance Seq_proper_ssim'_ctx : Proper (Seq ==> Seq ==> impl) (@ssim' E F C D X Y L).
  Proof.
    exact (@Seq_proper_ss'_chain_ctx (chain_gfp (@ss' E F C D))).
  Qed.

  Lemma ss'_gen_epsilon_star :
    forall (t t' : @S E C X) (u : @S F D Y),
    ss'_gen R R L t u ->
    trans_alt ε t t' ->
    exists u', (trans_alt ε)^* u u' /\ R L t' u'.
  Proof.
    intros * (_ & H); apply H.
  Qed.

End ssim'_theory.

Ltac fold_ssim' :=
  repeat
    match goal with
    | h: context[gfp (@ss' ?E ?F ?C ?D ?X ?Y ?L)] |- _ =>
        fold (@ssim' E F C D X Y L) in h
    | |- context[gfp (@ss' ?E ?F ?C ?D ?X ?Y ?L)]      =>
        fold (@ssim' E F C D X Y L)
    end.

Tactic Notation "__step_ssim'" :=
  match goal with
  | |- context[@ssim' ?E ?F ?C ?D ?X ?Y ?L] =>
      unfold ssim';
        apply (pfp_gfp (@ss' E F C D));
      fold (@ssim' E F C D X Y L)
  end.

Tactic Notation "step" := __step_ssim' || step.

Ltac __step_in_ssim' H :=
  match type of H with
  | context[@ssim' ?E ?F ?C ?D ?X ?Y ?L] =>
      unfold ssim' in H;
      apply (gfp_pfp (@ss' E F C D));
      fold (@ssim' E F C D X Y L) in H
  end.
Tactic Notation "step" "in" ident(H) := __step_in_ssim' H || step in H.

Tactic Notation "__coinduction_ssim'" simple_intropattern(r) simple_intropattern(cih) :=
  first [unfold ssim' at 4 | unfold ssim' at 3 | unfold ssim' at 2 | unfold ssim' at 1]; coinduction r cih.
Tactic Notation "coinduction" simple_intropattern(r) simple_intropattern(cih) := __coinduction_ssim' r cih || coinduction r cih.

Import CTreeNotations.
Import EquNotations.
Section ssim'_homogenous_theory.
  Context {E F C D : Type -> Type} {X Y: Type}
          {L: lrel E E X X}
          {R Reps: forall X Y : Type, lrel E E X Y -> rel (S E C X) (S E C Y)}. 

    (** Theory of chains of ss' *)

  Notation ss' := (@ss' E E C C).
  Notation ssim' := (@ssim' E E C C X X).

  #[global] Instance Reflexive_ss'_gen `{Reflexive _ (R L)} `{Reflexive _ (Reps L)} `{Reflexive _ L}:
    Reflexive (@ss'_gen E E C C R Reps X X L).
  Proof.
    split; intros.
    exists l, t'. split; auto.  
    use_steps O. assumption. 
    exists t'; split; eauto.
    use_steps (1 : nat). econstructor; eauto.  
  Qed.

  #[global] Instance Reflexive_ss'_chain {LR: Reflexive L} {c: Chain (ss')}: Reflexive (`c X X L).
  Proof.
    (* of note: Reflexive_chain fails here because elem has arguments.. we should fix that. *)   
    tower induction.
    split; intros.
    - do 2 eexists. split. use_steps O. apply H1. now split.  
    - exists t'; split; auto.
      use_steps (1 : nat). econstructor; eauto. 
  Qed.

  (* [Transitive `C] should hold? *)
  
End ssim'_homogenous_theory.

(*|
Parametric theory of [ss] with heterogenous [L]
|*)
Section ssim'_heterogenous_theory.
  Arguments label: clear implicits.
  Context {E F C D : Type -> Type} {X Y : Type}
          {L: lrel E F X Y}.


(*|
  stuck ctrees can be simulated by anything.
|*)
  Lemma ss'_stuck R Reps :
    forall (u : @S F D Y),
    ss'_gen R Reps L (Stuck : ctree E C X) u.
  Proof.
    split; intros; exfalso; eapply trans_stuck_inv; eassumption.
  Qed.

  Lemma ssim'_stuck (t : @S F D Y) : ssim' L (Stuck : ctree E C X) t.
  Proof. 
    step. apply ss'_stuck.
  Qed.

End ssim'_heterogenous_theory.

Ltac __play_ssim' := step; cbn; intros ? ? ?TR.

Ltac __play_ssim'_in H :=
  step in H;
  cbn in H; edestruct H as (? & ? & ? & ?TR & ?EPS & ?EQ & ?HL);
  clear H; [etrans |].

Ltac __eplay_ssim' :=
  match goal with
  | h : @ssim' ?E ?F ?B ?X ?L _ _ |- _ =>
      __play_ssim'_in h
  end.

#[local] Tactic Notation "play" := __play_ssim'.
#[local] Tactic Notation "play" "in" ident(H) := __play_ssim'_in H.
#[local] Tactic Notation "eplay" := __eplay_ssim'.

Section Proof_Rules.

  Arguments label: clear implicits.
  Context {E F C D : Type -> Type}
          {X Y : Type}
          {L : lrel E F X Y}
          {R Reps : (forall X Y : Type, lrel E F X Y -> rel (S E C X) (S F D Y))}
          {HR : (Proper (Seq ==> Seq ==> impl) (R X Y L))}
          {HReps : (Proper (Seq ==> Seq ==> impl) (Reps X Y L))}.

  Lemma step_ss'_stuck :
    ss'_gen R Reps L (Stuck : ctree E C X) (Stuck : ctree F D Y).
  Proof.
    split; intros; exfalso; eapply trans_stuck_inv; eassumption.
  Qed.

  Lemma step_ss'_ret (x : X) (y : Y) :
    R L Stuck Stuck ->
    L (val x) (val y) ->
    ss'_gen R Reps L (Ret x : ctree E C X) (Ret y : ctree F D Y).
  Proof.
    intros Rstuck Lval. split.
    - intros t' l Hl TR. apply trans_ret_inv' in TR as (EQ & ->).
      exists (val y), (Active Stuck). split; [| split].
      + apply estar_l_lift, trans_ret.
      + rewrite EQ. apply Rstuck.
      + assumption.
    - intros t' TR. apply trans_ret_inv' in TR as (_ & abs). discriminate.
  Qed.

  Lemma step_ss'_ret_l (x : X) (y : Y) (u u' : @S F D Y) :
    R L Stuck Stuck ->
    L (val x) (val y) ->
    trans_alt (val y) u u' ->
    ss'_gen R Reps L (Ret x : ctree E C X) u.
  Proof.
    intros Rstuck Lval TR. split.
    - intros t' l Hl TRl. apply trans_ret_inv' in TRl as (EQ & ->).
      pose proof (trans_val_inv' TR) as EQ'.
      exists (val y), u'. split; [| split].
      + apply estar_l_lift, TR.
      + rewrite EQ, EQ'. apply Rstuck.
      + assumption.
    - intros t' TRl. apply trans_ret_inv' in TRl as (_ & abs). discriminate.
  Qed.

(*|
 The vis nodes are deterministic from the perspective of the labeled
 transition system, stepping is hence symmetric and we can just recover
 the itree-style rule.
|*)
  Lemma step_ss'_vis {Z Z'} (e : E Z) (f: F Z')
        (k : Z -> ctree E C X) (k' : Z' -> ctree F D Y) :
    R L (Passive e k) (Passive f k') ->
    L (ask e) (ask f) ->
    ss'_gen R Reps L (Vis e k) (Vis f k').
  Proof.
    intros HRpas Lask. split.
    - intros t' l Hl TR. apply trans_vis_inv' in TR as (EQ & ->).
      exists (ask f), (Passive f k'). split; [| split].
      + apply estar_l_lift, trans_ask.
      + rewrite EQ. apply HRpas.
      + assumption.
    - intros t' TR. apply trans_vis_inv' in TR as (_ & abs). discriminate.
  Qed.

  Lemma step_ss'_vis_id {Z} (e : E Z) (f: F Z)
        (k : Z -> ctree E C X) (k' : Z -> ctree F D Y) :
    R L (Passive e k) (Passive f k') ->
    L (ask e) (ask f) ->
    ss'_gen R Reps L (Vis e k) (Vis f k').
  Proof.
    intros; apply step_ss'_vis; auto.
  Qed.

  Lemma step_ss'_vis_l {Z} :
    forall (e : E Z) (k : Z -> ctree E C X) (u : @S F D Y),
    (exists l' u', ((trans_alt ε)^* ⋅ trans_alt l') u u' /\ R L (Passive e k) u' /\ L (ask e) l') ->
    ss'_gen R Reps L (Vis e k) u.
  Proof.
    intros e k u (l' & u' & STEP & HRu & Lask). split.
    - intros t' l Hl TR. apply trans_vis_inv' in TR as (EQ & ->).
      exists l', u'. split; [| split].
      + assumption.
      + rewrite EQ. assumption.
      + assumption.
    - intros t' TR. apply trans_vis_inv' in TR as (_ & abs). discriminate.
  Qed.

(*|
    With this definition [ss'] of simulation, delayed nodes allow to perform a coinductive step.
|*)
  Lemma trans_alt_br_inv {G B : Type -> Type} {Z} (c : B Z) (k : Z -> ctree G B X) l u :
    trans_alt l (Br c k) u -> l = ε /\ exists x, u ⩸ (Active (k x)).
  Proof.
    intros TR; unfold trans_alt in TR; cbn in TR.
    dependent induction TR; inv_equ.
    split; auto.
    eexists; constructor.
    rewrite H0; first [ now apply EQ | now symmetry; apply EQ
                      | now rewrite EQ | now rewrite <- EQ ].
  Qed.

  Lemma trans_alt_guard_inv {G B : Type -> Type} (t : ctree G B X) l u :
    trans_alt l (Guard t) u -> l = ε /\ u ⩸ (Active t).
  Proof.
    intros TR; unfold trans_alt in TR; cbn in TR.
    dependent induction TR; inv_equ.
    split; auto.
    constructor.
    first [ now rewrite H0, <- H | now rewrite H0, H
          | now (rewrite H0; symmetry) ].
  Qed.

  Lemma step_ss'_br_l {Z} (c : C Z)
        (k : Z -> ctree E C X) (u : @S F D Y):
    (forall x, Reps L (Active (k x)) u) ->
    ss'_gen R Reps L (Br c k) u.
  Proof.
    intros HReps'. split.
    - intros t' l Hl TR. apply trans_alt_br_inv in TR as (-> & _). easy.
    - intros t' TR. apply trans_alt_br_inv in TR as (_ & x & EQ).
      exists u; split.
      + apply (str_refl (trans_alt ε)); cbn; reflexivity.
      + rewrite EQ. apply HReps'.
  Qed.
  
  Lemma step_ss'_br_r {Z} (c : D Z) x
        (k : Z -> ctree F D Y) (t: @S E C X):
    ss'_gen R Reps L t (k x) ->
    ss'_gen R Reps L t (Br c k).
  Proof.
    intros (HA & HB); split.
    - intros t' l Hl TR. apply HA in TR as (l' & u' & STEP & HRtu & HL); auto.
      exists l', u'; split; [| split; assumption].
      eapply estar_cons_label; [ apply trans_br | exact STEP ].
    - intros t' TR. apply HB in TR as (u' & STEP & HRep).
      exists u'; split; [| assumption].
      eapply estar_cons_epsilon; [ apply trans_br | exact STEP ].
  Qed.

  Lemma step_ss'_br {Z Z'} (a: C Z) (b: D Z')
    (k : Z -> ctree E C X) (k' : Z' -> ctree F D Y) :
    (forall x, exists y, Reps L (k x) (k' y)) ->
    ss'_gen R Reps L (Br a k) (Br b k').
  Proof.
    intros HRep; split.
    - intros t' l Hl TR. apply trans_alt_br_inv in TR as (-> & _); easy.
    - intros t' TR. apply trans_alt_br_inv in TR as (_ & x & EQ).
      destruct (HRep x) as (y & HR').
      exists (Active (k' y)); split.
      + apply estar_single, trans_br.
      + rewrite EQ. apply HR'.
  Qed.

  Lemma step_ss'_br_id {Z} (c: C Z) (d: D Z)
        (k : Z -> ctree E C X) (k' : Z -> ctree F D Y) :
    (forall x, Reps L (k x) (k' x)) ->
    ss'_gen R Reps L (Br c k) (Br d k').
  Proof.
   intros. apply step_ss'_br; eauto.
  Qed.

  Lemma step_ss'_guard_l
        (t: ctree E C X) (u: @S F D Y) :
    Reps L t u ->
    ss'_gen R Reps L (Guard t) u.
  Proof.
    intros HRep; split.
    - intros t' l Hl TR. apply trans_alt_guard_inv in TR as (-> & _); easy.
    - intros t' TR. apply trans_alt_guard_inv in TR as (_ & EQ).
      exists u; split; [ apply trans_star_self | rewrite EQ; apply HRep ].
  Qed.

  Lemma step_ss'_guard_r
    (t: @S E C X) (t': ctree F D Y) :
    ss'_gen R Reps L t t' ->
    ss'_gen R Reps L t (Guard t').
  Proof.
    intros (HA & HB); split.
    - intros s l Hl TR. apply HA in TR as (l' & u' & STEP & HRtu & HL); auto.
      exists l', u'; split; [| split; assumption].
      eapply estar_cons_label; [ apply trans_guard | exact STEP ].
    - intros s TR. apply HB in TR as (u' & STEP & HRep).
      exists u'; split; [| assumption].
      eapply estar_cons_epsilon; [ apply trans_guard | exact STEP ].
  Qed.

  Lemma step_ss'_guard
        (t: ctree E C X) (t': ctree F D Y) :
    Reps L t t' ->
    ss'_gen R Reps L (Guard t) (Guard t').
  Proof.
    intros HRep; split.
    - intros s l Hl TR. apply trans_alt_guard_inv in TR as (-> & _); easy.
    - intros s TR. apply trans_alt_guard_inv in TR as (_ & EQ).
      exists (Active t'); split.
      + apply estar_single, trans_guard.
      + rewrite EQ. apply HRep.
  Qed.

  Lemma step_ss'_epsilon_r :
    forall (t : @S E C X) (u u' : @S F D Y),
      ss'_gen R Reps L t u' -> (trans_alt ε)^* u u' -> ss'_gen R Reps L t u.
  Proof.
    intros t u u' (HA & HB) STAR; split.
    - intros s l Hl TR. apply HA in TR as (l' & u'' & STEP & HRtu & HL); auto.
      exists l', u''; split; [| split; assumption].
      eapply estar_app; eassumption.
    - intros s TR. apply HB in TR as (u'' & STEP & HRep).
      exists u''; split; [| assumption].
      eapply estar_trans; eassumption.
  Qed.

  Lemma ss'_gen_epsilon_l :
    forall (t t' : @S E C X) (u : @S F D Y),
    (Reps L) <= ss'_gen R Reps L ->
    ss'_gen R Reps L t u ->
    (trans_alt ε)^* t t' ->
    ss'_gen R Reps L t' u.
  Proof.
    intros t t' u HRle HSS STAR.
    destruct STAR as [n STAR]. revert t t' u HRle HSS STAR.
    induction n; intros t t' u HRle HSS STAR.
    - cbn in STAR.
      destruct HSS as (HA & HB); split.
      + intros s l Hne TR. rewrite <- STAR in TR. exact (HA _ _ Hne TR).
      + intros s TR. rewrite <- STAR in TR. exact (HB _ TR).
    - destruct STAR as [m STEP REST].
      destruct HSS as (HA & HB).
      apply HB in STEP as (u' & STARu & HRep).
      apply HRle in HRep.
      eapply step_ss'_epsilon_r in HRep; [| exact STARu].
      eapply IHn; [ exact HRle | exact HRep | exact REST ].
  Qed.

  (*|
    Same goes for visible τ nodes.
    |*)
  Lemma step_ss'_step
        (t : ctree E C X) (t': ctree F D Y) :
    L τ τ ->
    R L t t' ->
    ss'_gen R Reps L (Step t) (Step t').
  Proof.
    intros Ltau HRtt; split.
    - intros s l Hl TR. apply trans_step_inv' in TR as (EQ & ->).
      exists τ, (Active t'). split; [| split].
      + apply estar_l_lift, trans_step.
      + rewrite EQ. apply HRtt.
      + assumption.
    - intros s TR. apply trans_step_inv' in TR as (_ & abs). discriminate.
  Qed.

  Lemma step_ss'_step_l :
    forall (t : ctree E C X) (u : @S F D Y),
    (exists l' u', ((trans_alt ε)^* ⋅ trans_alt l') u u' /\ R L t u' /\ L τ l') ->
    ss'_gen R Reps L (Step t) u.
  Proof.
    intros t u (l' & u' & STEP & HRtu & Ltau). split.
    - intros s l Hl TR. apply trans_step_inv' in TR as (EQ & ->).
      exists l', u'. split; [| split].
      + assumption.
      + rewrite EQ. assumption.
      + assumption.
    - intros s TR. apply trans_step_inv' in TR as (_ & abs). discriminate.
  Qed.

(*|
    When matching visible brs one against another, in general we need to explain how
    we map the branches from the left to the branches to the right.
    A useful special case is the one where the arity coincide and we simply use the identity
    in both directions. We can in this case have [n] rather than [2n] obligations.
|*)

End Proof_Rules.

(* Specialized proof rules *)

Lemma ssim'_stuck' {E F B X}
  (L : lrel _ _ _ _) :
  ssim' L (Stuck : ctree E B X) (Stuck : ctree F B X).
Proof.
  step. apply step_ss'_stuck.
Qed.

Lemma step_ssbt'_ret {E F C D X Y}
  (x : X) (y : Y) (L : lrel _ _ _ _)
  {R : Chain (@ss' E F C D)} :
  L (val x) (val y) ->
  ss' `R X Y L (Ret x : ctree E C X) (Ret y : ctree F D Y).
Proof.
  intros.
  unshelve eapply step_ss'_ret; eauto.
  apply (b_chain R). apply ss'_stuck.
Qed.

Lemma ssim'_ret {E F B X}
  (x : X) (y : X) (L : lrel _ _ _ _) :
  L (val x) (val y) ->
  ssim' L (Ret x : ctree E B X) (Ret y : ctree F B X).
Proof.
  now intros; step; apply step_ssbt'_ret.
Qed.

Lemma ssim'_step {E F B X}
  (t : ctree E B X) (u : ctree F B X) (L : lrel _ _ _ _) :
  L τ τ  ->
  ssim' L t u ->
  ssim' L (Step t) (Step u).
Proof.
  now intros; step; apply step_ss'_step.
Qed.

Lemma ssim'_guard {E F B X}
  (t : ctree E B X) (u : ctree F B X) (L : lrel _ _ _ _) :
  ssim' L t u ->
  ssim' L (Guard t) (Guard u).
Proof.
  now intros; step; apply step_ss'_guard.
Qed.

Lemma ssim'_br {E F B X Z Z'} {L}
  (c: B Z) (d: B Z')
  (k : Z -> ctree E B X) (k' : Z' -> ctree F B X) :
  (forall x, exists y, ssim' L (k x) (k' y)) ->
  ssim' L (Br c k) (Br d k').
Proof.
  now intros; step; apply step_ss'_br.
Qed.

Lemma ssim'_br_id {E F B X Z} {L}
  (c: B Z) (d: B Z)
  (k : Z -> ctree E B X) (k' : Z -> ctree F B X) :
  (forall x, ssim' L (k x) (k' x)) ->
  ssim' L (Br c k) (Br d k').
Proof.
  now intros; step; apply step_ss'_br_id.
Qed.

Lemma step_ssbt'_brS {E F C D X Y Z Z'}
  {L : lrel _ _ _ _}
  {R : Chain (@ss' E F C D)}
  (c: C Z) (d: D Z')
  (k : Z -> ctree E C X) (k' : Z' -> ctree F D Y) :
  L τ τ  ->
  (forall x, exists y, `R X Y L (k x) (k' y)) ->
  ss' `R X Y L (BrS c k) (BrS d k').
Proof.
  intros.
  apply step_ss'_br; auto.
  intros x; destruct (H0 x) as (y & ?); exists y.
  apply (b_chain R), step_ss'_step; auto.
Qed.

Lemma ssim'_brS {E F C D X Y Z Z'}
  {L : lrel _ _ _ _}
  {R : Chain (@ss' E F C D)}
  (c: C Z) (d: D Z')
  (k : Z -> ctree E C X) (k' : Z' -> ctree F D Y) :
  L τ τ  ->
  (forall x, exists y, ssim' L (k x) (k' y)) ->
  ssim' L (BrS c k) (BrS d k').
Proof.
  intros; step; now apply step_ssbt'_brS.
Qed.

Lemma step_ssbt'_brS_id {E F C D X Y Z}
  {L : lrel _ _ _ _}
  {R : Chain (@ss' E F C D)}
  (c: C Z) (d: D Z)
  (k : Z -> ctree E C X) (k' : Z -> ctree F D Y) :
  L τ τ  ->
  (forall x, ` R X Y L (k x) (k' x)) ->
  ss' `R X Y L (BrS c k) (BrS d k').
Proof.
  intros.
  apply step_ss'_br_id; auto.
  intros; apply (b_chain R), step_ss'_step; auto.
Qed.

Lemma ssim'_brS_id {E F C D X Y Z} {L : lrel _ _ _ _}
  (c: C Z) (d: D Z)
  (k : Z -> ctree E C X) (k' : Z -> ctree F D Y) :
  L τ τ  ->
  (forall x, ssim' L (k x) (k' x)) ->
  ssim' L (BrS c k) (BrS d k').
Proof.
  now intros; step; apply step_ssbt'_brS_id.
Qed.

Lemma ssim'_vis
  {E F C D X Y Z Z'} {L : lrel _ _ _ _}
  (e: E Z) (f: F Z')
  (k : Z -> ctree E C X) (k' : Z' -> ctree F D Y) :
  ssim' L (Passive e k) (Passive f k') ->
  L (ask e) (ask f) ->
  ssim' L (Vis e k) (Vis f k').
Proof.
  intros Hpas Hask; step; apply step_ss'_vis; [exact Hpas | exact Hask].
Qed.

Lemma ssim'_vis_id
  {E F C D X Y Z} {L : lrel _ _ _ _}
  (e: E Z) (f: F Z)
  (k : Z -> ctree E C X) (k' : Z -> ctree F D Y) :
  ssim' L (Passive e k) (Passive f k') ->
  L (ask e) (ask f) ->
  ssim' L (Vis e k) (Vis f k').
Proof.
  intros Hpas Hask; step; apply step_ss'_vis_id; [exact Hpas | exact Hask].
Qed.

Lemma ssim'_vis_l
  {E F C D X Y Z} {L : lrel _ _ _ _}
  (e: E Z)
  (k : Z -> ctree E C X) (u : @S F D Y) :
  (exists l' u', ((trans_alt ε)^* ⋅ trans_alt l') u u' /\ ssim' L (Passive e k) u' /\ L (ask e) l') ->
  ssim' L (Vis e k) u.
Proof.
  intros H; step; apply step_ss'_vis_l; exact H.
Qed.

Lemma ssim'_epsilon_l {E F C D X Y} {L : lrel _ _ _ _} :
  forall (t t' : @S E C X) (u : @S F D Y),
  ssim' L t u ->
  (trans_alt ε)^* t t' ->
  ssim' L t' u.
Proof.
  intros. step. eapply ss'_gen_epsilon_l.
  (* blessed postfixpoint *)
  - exact (gfp_pfp (@ss' E F C D) X Y L).
  - step in H. apply H.
  - apply H0.
Qed.

Section Inversion_Rules.

  Context {E F C D : Type -> Type}
          {X Y : Type}
          {L : lrel E F X Y}
          {R Reps : forall X Y : Type, lrel E F X Y -> rel (@S E C X) (@S F D Y)}.

  Lemma ss'_vis_l_inv {Z} :
    forall (e : E Z) (k : Z -> ctree E C X) (u : @S F D Y),
    ss'_gen R Reps L (Vis e k) u ->
    exists l' u', ((trans_alt ε)^* ⋅ trans_alt l') u u' /\ R L (Passive e k) u' /\ L (ask e) l'.
  Proof.
    intros e k u (HA & _).
    apply (HA (Passive e k) (ask e)); [ discriminate | apply trans_ask ].
  Qed.

  Lemma ss'_step_l_inv :
    forall (t : ctree E C X) (u : @S F D Y),
    ss'_gen R Reps L (Step t) u ->
    exists l' u', ((trans_alt ε)^* ⋅ trans_alt l') u u' /\ R L t u' /\ L τ l'.
  Proof.
    intros t u (HA & _).
    apply (HA (Active t) τ); [ discriminate | apply trans_step ].
  Qed.

End Inversion_Rules.

Definition epsilon_ctx {E B X} (R : ctree E B X -> Prop)
  (t : ctree E B X) :=
  exists t', epsilon t t' /\ R t'.

Definition epsilon_det_ctx {E B X} (R : ctree E B X -> Prop)
  (t : ctree E B X) :=
  exists t', epsilon_det t t' /\ R t'.

Section upto.

  Context {E F C D : Type -> Type}.

  (* Up-to epsilon *)

  #[local] Obligation Tactic := idtac.
  Program Definition epsilon_ctx_r :
    mon (forall X Y, lrel E F X Y -> hrel (@S E C X) (@S F D Y))
    := {| body R := fun X Y L t u => exists u', (trans_alt ε)^* u u' /\ R X Y L t u' |}.
  Next Obligation.
    intros R R' HR X Y L t u (u' & STAR & HRtu).
    exists u'; split; [ exact STAR | now apply HR ].
  Qed.

  Lemma epsilon_ctx_r_sst' {c: Chain (@ss' E F C D)}:
    forall X Y L x y, epsilon_ctx_r `c X Y L x y -> `c X Y L x y.
  Proof.
    apply tower.
    - intros ? INC X Y L x y (? & ? & ?) ??; red.
      apply INC; auto.
      eexists; split; eauto.
      apply H0, H1. 
    - clear.
      intros R IH X Y L t u (u' & STAR & HSS).
      eapply step_ss'_epsilon_r; [ exact HSS | exact STAR ].
  Qed.

End upto.


#[local] Example ssim'_spin {E F B X} (L : lrel E F X X) :
  forall (u : @SS F B X), ssim' L (Active (@spin E B X)) u.
Proof.
  unfold ssim'; coinduction R CH; intros u.
  assert (SQ : (Active (@spin E B X) : @SS E B X) ⩸ (Active (Guard spin)))
    by (constructor; apply unfold_spin).
  split.
  - intros t' l Hne TR.
    rewrite SQ in TR.
    eapply trans_alt_guard_inv in TR as (-> & _); easy.
    Unshelve. exact E. exact F. all: auto.
  - intros t' TR.
    rewrite SQ in TR.
    eapply trans_alt_guard_inv in TR as (_ & EQ).
    exists u; split.
    + apply trans_star_self.
    + rewrite EQ; apply CH.
    Unshelve. exact E. exact F. all: auto.
Qed.

Section Sbind. 

Definition Sbind {E B X Y} (s : @S E B X) (k : X -> ctree E B Y) : @S E B Y :=
  match s with
  | Active t => Active (x <- t;; k x)
  | Passive e g => Passive e (fun z => x <- g z;; k x)
  end.

(* theory of Sbind, from which we derive bind *)

Lemma Sbind_Seq {E B X Y} (s u : @S E B X) (k : X -> ctree E B Y) :
  s ⩸ u -> (Sbind s k) ⩸ (Sbind u k).
Proof.
  intros EQ; destruct EQ; cbn; constructor.
  - now rewrite EQ.
  - intros; now rewrite EQ.
Qed.

Lemma estar_Sbind {E B X Y} (s u : @S E B X) (k : X -> ctree E B Y) :
  (trans_alt ε)^* s u -> (trans_alt ε)^* (Sbind s k) (Sbind u k).
Proof.
  destruct s as [t | Z e g]; intros STAR.
  - destruct (estar_active STAR) as [u0 EQ].
    assert (STAR2 : (trans_alt ε)^* (Active t) (Active u0))
      by (eapply estar_trans; [ exact STAR | apply estar_seq, EQ ]).
    eapply (estar_trans (b := Sbind (Active u0 : @S E B X) k)).
    + cbn. apply estar_bind; exact STAR2.
    + apply estar_seq. apply Sbind_Seq. now symmetry.
  - apply estar_passive in STAR. now apply estar_seq, Sbind_Seq.
Qed.

Lemma trans_Sbind_τ {E B X Y} (s u : @S E B X) (k : X -> ctree E B Y) :
  trans_alt τ s u -> trans_alt τ (Sbind s k) (Sbind u k).
Proof.
  intros TR; destruct s as [t | Z e g].
  - unfold trans_alt in TR; cbn in TR; dependent destruction TR; cbn.
    apply trans_bind_l_τ; eapply Transstep; eauto.
  - apply trans_passive_inv' in TR as (z & _ & Habs); easy.
Qed.

Lemma trans_Sbind_ask {E B X Y Z} (s u : @S E B X) (k : X -> ctree E B Y) (e : E Z) :
  trans_alt (ask e) s u -> trans_alt (ask e) (Sbind s k) (Sbind u k).
Proof.
  intros TR; destruct s as [t | Z0 e0 g].
  - unfold trans_alt in TR; cbn in TR; dependent destruction TR; cbn.
    apply trans_bind_l_ask; econstructor; eauto.
  - apply trans_passive_inv' in TR as (z & _ & Habs); easy.
Qed.

Lemma trans_Sbind_rcv {E B X Y Z} (s u : @S E B X) (k : X -> ctree E B Y) (e : E Z) (w : Z) :
  trans_alt (rcv e w) s u -> trans_alt (rcv e w) (Sbind s k) (Sbind u k).
Proof.
  intros TR; destruct s as [t | Z0 e0 g].
  - unfold trans_alt in TR; cbn in TR; dependent destruction TR.
  - apply trans_passive_inv' in TR as (z & EQ & Heq).
    dependent destruction Heq; cbn.
    assert (HS : (Sbind u k) ⩸ (Active (x <- g z;; k x))).
    { transitivity (Sbind (Active (g z)) k); [ now apply Sbind_Seq | reflexivity ]. }
    rewrite HS. econstructor; reflexivity.
Qed.

End Sbind. 

Section bind_restore.

  Context {E F C D : Type -> Type} {X Y X' Y' : Type}.

  Lemma sbind_chain_gen (L : lrel E F X' Y') {R : Chain (@ss' E F C D)} :
    forall (s : @S E C X) (s' : @S F D Y)
      (k : X -> ctree E C X') (k' : Y -> ctree F D Y')
      (SS : rel X Y),
      ` R X Y (upd_rel L SS) s s' ->
      (forall x x', SS x x' -> ` R X' Y' L (Active (k x)) (Active (k' x'))) ->
      ` R X' Y' L (Sbind s k) (Sbind s' k').
  Proof.
    tower induction.
    - intros IH s s' k k' SS tt kk.
      destruct s as [t | Zs es gs].
      + split.
        * intros succ l Hne TR.
          apply trans_bind_inv in TR as
            [ (x & EQt & TRk)
            | [ (-> & t1 & TRt & SQ)
            | [ (Heps & _)
            | (Z & e & g & -> & TRt & SQ) ]]].
          -- assert (cV : trans_alt (val x)
                            (Active t) (Active (Stuck : ctree E C X))) by now constructor.
             destruct tt as [tt_ne tt_ep].
             destruct (tt_ne _ (val x) (ltac:(easy)) cV) as (l2 & resp & RESP & _ & HL2).
             destruct RESP as [m STAR STEPv].
             unfold trans_alt in STEPv; cbn in STEPv.
             dependent destruction STEPv; inversion HL2; subst.
             specialize (kk x r ltac:(assumption)).
             destruct kk as (kkA & _).
             destruct (kkA _ _ Hne TRk) as (l' & u' & RESP2 & Hgfp & HL').
             exists l', u'; ssplit.
             ++ destruct RESP2 as [m2 STAR2 STEP2].
                exists m2; [| exact STEP2].
                eapply estar_trans.
                ** apply estar_Sbind; exact STAR.
                ** eapply estar_trans; [| exact STAR2].
                   apply estar_seq; cbn; constructor.
                   rewrite H, bind_ret_l; reflexivity.
             ++ exact Hgfp.
             ++ exact HL'.
          -- destruct tt as [tt_ne tt_ep].
             destruct (tt_ne _ τ (ltac:(easy)) TRt) as (l2 & resp & RESP & Hpre & HL2).
             inversion HL2; subst.
             destruct RESP as [m STAR STEPτ].
             exists τ, (Sbind resp k'); ssplit.
             ++ exists (Sbind m k').
                ** apply estar_Sbind; exact STAR.
                ** apply trans_Sbind_τ; exact STEPτ.
             ++ rewrite SQ. apply (IH (Active t1) resp k k' SS); [ exact Hpre | intros ? ? ?; apply (b_chain R); now apply kk ].
             ++ constructor.
          -- easy.
          -- destruct tt as [tt_ne tt_ep].
             destruct (tt_ne _ (ask e) (ltac:(easy)) TRt) as (l2 & resp & RESP & Hpre & HL2).
             dependent destruction HL2.
             destruct RESP as [m STAR STEPa].
             exists (ask f), (Sbind resp k'); ssplit.
             ++ exists (Sbind m k').
                ** apply estar_Sbind; exact STAR.
                ** apply trans_Sbind_ask; exact STEPa.
             ++ rewrite SQ. apply (IH (Passive e g) resp k k' SS); [ exact Hpre | intros ? ? ?; apply (b_chain R); now apply kk ].
             ++ now constructor.
        * intros succ TR.
          apply trans_bind_inv in TR as
            [ (x & EQt & TRk)
            | [ (Habs & _)
            | [ (_ & t1 & TRt & SQ)
            | (Z & e & g & Habs & _) ]]].
          -- assert (cV : trans_alt (val x) (Active t) (Active (Stuck : ctree E C X)))
               by (eapply Transval; [ exact EQt | reflexivity ]).
             destruct tt as [tt_ne tt_ep].
             destruct (tt_ne _ (val x) (ltac:(easy)) cV) as (l2 & resp & RESP & _ & HL2).
             destruct RESP as [m STAR STEPv].
             unfold trans_alt in STEPv; cbn in STEPv.
             dependent destruction STEPv; inversion HL2; subst.
             specialize (kk x r ltac:(assumption)).
             destruct kk as (_ & kkB).
             destruct (kkB _ TRk) as (u2 & STARu & Hgfp2).
             exists u2; split.
             ++ eapply estar_trans.
                ** apply estar_Sbind; exact STAR.
                ** eapply estar_trans; [| exact STARu].
                   apply estar_seq; cbn; constructor.
                   rewrite H, bind_ret_l; reflexivity.
             ++ exact Hgfp2.
          -- easy.
          -- destruct tt as [tt_ne tt_ep].
             destruct (tt_ep _ TRt) as (resp & STARr & Hpre).
             exists (Sbind resp k'); split.
             ++ apply estar_Sbind; exact STARr.
             ++ rewrite SQ. apply (IH (Active t1) resp k k' SS); [ exact Hpre | intros ? ? ?; apply (b_chain R); now apply kk ].
          -- easy.
      + split.
        * intros succ l Hne TR.
          apply trans_passive_inv' in TR as (z & SQ & ->).
          assert (TRrcv : trans_alt (rcv es z) (Passive es gs) (Active (gs z)))
            by (econstructor; reflexivity).
          destruct tt as [tt_ne tt_ep].
          destruct (tt_ne _ (rcv es z) (ltac:(easy)) TRrcv) as (l2 & resp & RESP & Hpre & HL2).
          dependent destruction HL2.
          destruct RESP as [m STAR STEPr].
          exists (rcv f y), (Sbind resp k'); ssplit.
          -- exists (Sbind m k').
             ++ apply estar_Sbind; exact STAR.
             ++ apply trans_Sbind_rcv; exact STEPr.
          -- rewrite SQ. apply (IH (Active (gs z)) resp k k' SS); [ exact Hpre | intros ? ? ?; apply (b_chain R); now apply kk ].
          -- now constructor.
        * intros succ TR.
          apply trans_passive_inv' in TR as (z & _ & Habs); easy.
  Qed.

  Lemma bind_chain_gen (L : lrel E F X' Y') {R : Chain (@ss' E F C D)} :
    forall (t : ctree E C X) (t' : ctree F D Y)
      (k : X -> ctree E C X') (k' : Y -> ctree F D Y')
      (SS : rel X Y),
      ` R X Y (upd_rel L SS) (Active t) (Active t') ->
      (forall x x', SS x x' -> ` R X' Y' L (Active (k x)) (Active (k' x'))) ->
      ` R X' Y' L (Active (x <- t;; k x)) (Active (x <- t';; k' x)).
  Proof.
    intros t t' k k' SS.
    exact (sbind_chain_gen L (Active t) (Active t') k k' SS).
  Qed.

  Lemma ssim'_clo_bind (L : lrel E F X' Y') :
    forall (t : ctree E C X) (t' : ctree F D Y)
      (k : X -> ctree E C X') (k' : Y -> ctree F D Y') (SS : rel X Y),
      ssim' (upd_rel L SS) (Active t) (Active t') ->
      (forall x x', SS x x' -> ssim' L (Active (k x)) (Active (k' x'))) ->
      ssim' L (Active (x <- t;; k x)) (Active (x <- t';; k' x)).
  Proof.
    intros t t' k k' SS tt kk.
    exact (@bind_chain_gen L (chain_gfp (@ss' E F C D)) t t' k k' SS tt kk).
  Qed.

End bind_restore.

(** Finally, up-to bind closure for trees of the same type. *)
Lemma ssim'_clo_bind_eq {E B X X'} :
  forall (t t' : ctree E B X) (k k' : X -> ctree E B X'),
    ssim' (upd_rel (@Leq E X') eq) (Active t) (Active t') ->
    (forall x, ssim' (@Leq E X') (Active (k x)) (Active (k' x))) ->
    ssim' (@Leq E X') (Active (x <- t;; k x)) (Active (x <- t';; k' x)).
Proof.
  intros t t' k k' tt kk.
  eapply ssim'_clo_bind; [ exact tt |].
  intros x x' ->; apply kk.
Qed.
