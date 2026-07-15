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
(R Reps : (forall X Y, lrel E F X Y -> @S E C X -> @S F D Y -> Prop)) 
(X Y : Type) (L : lrel E F X Y) (t: @S E C X) (u: @S F D Y) :=
    (forall t' l, l <> ε -> trans_alt (B:=C) l t t'
    -> exists l' u', ((trans_alt (B:=D) ε)^* ⋅ (trans_alt l')) u u' /\ R X Y L t' u' /\ L l l')
    /\
      (forall t', trans_alt (B:=C) ε t t' -> exists u', (trans_alt (B:=D) ε)^* u u' /\ Reps X Y L t' u'). 

  Program Definition ss' {E F C D : Type -> Type} :
    mon (forall (X Y : Type), 
    lrel E F X Y -> (* L *)
    @S E C X -> (* t *)
    @S F D Y -> (* u *)
    Prop) :=
    {| body R := ss'_gen R R
    |}. 
Next Obligation.
Proof.  
  split; intros; destruct H0. 
    - destruct (H0 _ _ H1 H2) as (l'' & u'' & Htrans & HRtu & HL').
      eauto 12. 
    - apply H2 in H1 as (u' & Htrans & HRtu). eauto. 
  Qed.

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


(* TODO: remove this and rewrite using simple proper instances *)
Variant Seq_clos_body {E F B X} (R : rel (@S E B X) (@S F B X)) : rel (@S E B X) (@S F B X) :=
  | Seq_clos_intro : forall t t' u' u
                       (Seqt : t ⩸ t')
                       (HR : R t' u')
                       (Sequ : u' ⩸ u),
      Seq_clos_body R t u.

Program Definition Seq_clos {E F B X} : mon (rel (@S E B X) (@S F B X)) :=
  {| body := @Seq_clos_body E F B X |}.
Next Obligation.
  match goal with h : Seq_clos_body _ _ _ |- _ => inv h end.
  econstructor; eauto.
Qed.

Section ssim'_theory.
  Arguments label: clear implicits.
  Context {E F B: Type -> Type} {X : Type}
          {L: rel (@label E X) (@label F X)}.

(*|
   Strong simulation up-to [equ] is valid
   ----------------------------------------
|*)
  #[global] Instance Seq_ss'_gen_goal {R Reps} :
    Proper (Seq ==> Seq ==> flip impl) (@ss'_gen E F B X L R Reps).
  Proof.
    intros t t' EQt u u' EQu (HA & HB); split.
    - intros t'' l Hl TR. rewrite EQt in TR.
      apply HA in TR as (l' & u'' & STEP & HRtu & HL); auto.
      exists l', u''; split; [| split; assumption].
      now rewrite EQu.
    - intros t'' TR. rewrite EQt in TR.
      apply HB in TR as (u'' & STEP & HRtu).
      exists u''; split; [| assumption].
      now rewrite EQu.
  Qed.

  #[global] Instance Seq_ss'_gen_ctx {R Reps} :
    Proper (Seq ==> Seq ==> impl) (@ss'_gen E F B X L R Reps).
  Proof.
    intros t t' EQt u u' EQu H. now rewrite <- EQt, <- EQu.
  Qed.

  Lemma Seq_clos_sst' {c: Chain (@ss' E F B X L)}:
    forall x y, Seq_clos `c x y -> `c x y.
  Proof.
    apply tower.
    - intros ? INC x y [t t' u' u EQt HR EQu] ??. red.
      apply INC; auto.
      econstructor; eauto.
      apply leq_infx in H.
      now apply H.
    - intros R IH x y [t t' u' u EQt HR EQu].
      eapply Seq_ss'_gen_goal; [ exact EQt | symmetry; exact EQu | exact HR ].
  Qed.

  #[global] Instance Seq_clos_sst_goal {c: Chain (@ss' E F B X L)} :
    Proper (Seq ==> Seq ==> flip impl) `c.
  Proof.
    cbn; intros ? ? eq1 ? ? eq2 H.
    apply Seq_clos_sst'; econstructor; [eauto | | symmetry; eauto]; assumption.
  Qed.

  #[global] Instance Seq_clos_sst'_ctx  {c: Chain (@ss' E F B X L)} :
    Proper (Seq ==> Seq ==> impl) `c.
  Proof.
    cbn; intros ? ? eq1 ? ? eq2 H.
    apply Seq_clos_sst'; econstructor; [symmetry; eauto | | eauto]; assumption.
  Qed.

  #[global] Instance Seq_clos_ssim'_goal : Proper (Seq ==> Seq ==> flip impl) (@ssim' E F B X L).
  Proof.
    cbn; intros ? ? eq1 ? ? eq2 H.
    apply Seq_clos_sst'; econstructor; eauto; now symmetry.
  Qed.

  #[global] Instance Seq_clos_ssim'_ctx : Proper (Seq ==> Seq ==> impl) (@ssim' E F B X L).
  Proof.
    cbn; intros ? ? eq1 ? ? eq2 H.
    now rewrite <- eq1, <- eq2.
  Qed.

  Lemma ss'_gen_epsilon_star {R : rel (@S E B X) (@S F B X)} :
    forall (t t' : @S E B X) (u : @S F B X),
    ss'_gen L R R t u ->
    trans_alt ε t t' ->
    exists u', (trans_alt ε)^* u u' /\ R t' u'.
  Proof.
    intros * (_ & H); apply H.
  Qed.

  Lemma trans_alt_estar_l {G : Type -> Type} :
    forall (t t' : @S G B X) l,
    trans_alt l t t' ->
    ((trans_alt ε)^* ⋅ trans_alt l) t t'.
  Proof.
    intros. use_steps O. assumption.
  Qed.

End ssim'_theory.

Ltac fold_ssim' :=
  repeat
    match goal with
    | h: context[gfp (@ss' ?E ?F ?B ?X ?L)] |- _ =>
        fold (@ssim' E F B X L) in h
    | |- context[gfp (@ss' ?E ?F ?B ?X ?L)]      =>
        fold (@ssim' E F B X L)
    end.

Tactic Notation "__step_ssim'" :=
  match goal with
  | |- context[@ssim' ?E ?F ?B ?X ?L] =>
      unfold ssim';
      step;
      fold (@ssim' E F B X L)
  end.

Tactic Notation "step" := __step_ssim' || step.

Ltac __step_in_ssim' H :=
  match type of H with
  | context[@ssim' ?E ?F ?B ?X ?L] =>
      unfold ssim' in H;
      step in H;
      fold (@ssim' E F B X L) in H
  end.
Tactic Notation "step" "in" ident(H) := __step_in_ssim' H || step in H.

Tactic Notation "__coinduction_ssim'" simple_intropattern(r) simple_intropattern(cih) :=
  first [unfold ssim' at 4 | unfold ssim' at 3 | unfold ssim' at 2 | unfold ssim' at 1]; coinduction r cih.
Tactic Notation "coinduction" simple_intropattern(r) simple_intropattern(cih) := __coinduction_ssim' r cih || coinduction r cih.

Import CTreeNotations.
Import EquNotations.
Section ssim'_homogenous_theory.
  Context {E B: Type -> Type} {X: Type}
          {L: relation (@label E X)}.

  Notation ss' := (@ss' E E B X).
  Notation ssim' := (@ssim' E E B X).

  #[global] Instance Reflexive_ss' R Reps `{Reflexive _ R} `{Reflexive _ L} `{Reflexive _ Reps}:
    Reflexive (@ss'_gen E E B X L R Reps).
  Proof.
    split; intros.
    exists l, t'. split; auto.  
    use_steps O. assumption. 
    exists t'; split; eauto.
    use_steps (1 : nat). econstructor; eauto.  
  Qed.

  #[global] Instance refl_ss' {LR: Reflexive L} {C: Chain (ss' L)}: Reflexive `C.
  Proof.
    apply Reflexive_chain.
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
  Context {E F B: Type -> Type} {X: Type}
          {L: rel (@label E X) (@label F X)}.

  Notation ss' := (@ss' E F B X).
  Notation ssim'  := (@ssim' E F B X).

(*|
  stuck ctrees can be simulated by anything.
|*)
  Lemma ss'_stuck R Reps :
    forall (u : @S F B X),
    ss'_gen L R Reps (Stuck : ctree E B X) u.
  Proof.
    split; intros; exfalso; eapply trans_stuck_inv; eassumption.
  Qed.

  Lemma ssim'_stuck (t : @S F B X) : ssim' L (Stuck : ctree E B X) t.
  Proof.
    intros. step. apply ss'_stuck.
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
  Context {E F B : Type -> Type}
          {X : Type}
          {L : rel (@label E X) (@label F X)}
          {R Reps : rel (@S E B X) (@S F B X)}
          {HR : (Proper (Seq ==> Seq ==> impl) R)}
          {HReps : (Proper (Seq ==> Seq ==> impl) Reps)}.

  Lemma step_ss'_stuck :
    ss'_gen L R Reps (Stuck : ctree E B X) (Stuck : ctree F B X).
  Proof.
    split; intros; exfalso; eapply trans_stuck_inv; eassumption.
  Qed.

  Lemma step_ss'_ret (x : X) (y : X) :
    R Stuck Stuck ->
    L (val x) (val y) ->
    ss'_gen L R Reps (Ret x : ctree E B X) (Ret y : ctree F B X).
  Proof.
    intros Rstuck Lval. split.
    - intros t' l Hl TR. apply trans_ret_inv' in TR as (EQ & ->).
      exists (val y), (Active Stuck). split; [| split].
      + apply trans_alt_estar_l, trans_ret.
      + rewrite EQ. apply Rstuck.
      + assumption.
    - intros t' TR. apply trans_ret_inv' in TR as (_ & abs). discriminate.
  Qed.

  Lemma step_ss'_ret_l (x : X) (y : X) (u u' : @S F B X) :
    R Stuck Stuck ->
    L (val x) (val y) ->
    trans_alt (val y) u u' ->
    ss'_gen L R Reps (Ret x : ctree E B X) u.
  Proof.
    intros Rstuck Lval TR. split.
    - intros t' l Hl TRl. apply trans_ret_inv' in TRl as (EQ & ->).
      pose proof (trans_val_inv' TR) as EQ'.
      exists (val y), u'. split; [| split].
      + apply trans_alt_estar_l, TR.
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
        (k : Z -> ctree E B X) (k' : Z' -> ctree F B X) :
    R (Passive e k) (Passive f k') ->
    L (ask e) (ask f) ->
    ss'_gen L R Reps (Vis e k) (Vis f k').
  Proof.
    intros HRpas Lask. split.
    - intros t' l Hl TR. apply trans_vis_inv' in TR as (EQ & ->).
      exists (ask f), (Passive f k'). split; [| split].
      + apply trans_alt_estar_l, trans_ask.
      + rewrite EQ. apply HRpas.
      + assumption.
    - intros t' TR. apply trans_vis_inv' in TR as (_ & abs). discriminate.
  Qed.

  Lemma step_ss'_vis_id {Z} (e : E Z) (f: F Z)
        (k : Z -> ctree E B X) (k' : Z -> ctree F B X) :
    R (Passive e k) (Passive f k') ->
    L (ask e) (ask f) ->
    ss'_gen L R Reps (Vis e k) (Vis f k').
  Proof.
    intros; apply step_ss'_vis; auto.
  Qed.

  Lemma step_ss'_vis_l {Z} :
    forall (e : E Z) (k : Z -> ctree E B X) (u : @S F B X),
    (exists l' u', ((trans_alt ε)^* ⋅ trans_alt l') u u' /\ R (Passive e k) u' /\ L (ask e) l') ->
    ss'_gen L R Reps (Vis e k) u.
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
  Lemma trans_alt_br_inv {G : Type -> Type} {Z} (c : B Z) (k : Z -> ctree G B X) l u :
    trans_alt l (Br c k) u -> l = ε /\ exists x, u ⩸ (Active (k x)).
  Proof.
    intros TR; unfold trans_alt in TR; cbn in TR.
    dependent induction TR; inv_equ.
    split; auto.
    eexists; constructor.
    rewrite H0; first [ now apply EQ | now symmetry; apply EQ
                      | now rewrite EQ | now rewrite <- EQ ].
  Qed.

  Lemma trans_alt_guard_inv {G : Type -> Type} (t : ctree G B X) l u :
    trans_alt l (Guard t) u -> l = ε /\ u ⩸ (Active t).
  Proof.
    intros TR; unfold trans_alt in TR; cbn in TR.
    dependent induction TR; inv_equ.
    split; auto.
    constructor.
    first [ now rewrite H0, <- H | now rewrite H0, H
          | now (rewrite H0; symmetry) ].
  Qed.

  Lemma step_ss'_br_l {Z} (c : B Z)
        (k : Z -> ctree E B X) (u : @S F B X):
    (forall x, Reps (Active (k x)) u) ->
    ss'_gen L R Reps (Br c k) u.
  Proof.
    intros HReps'. split.
    - intros t' l Hl TR. apply trans_alt_br_inv in TR as (-> & _). easy.
    - intros t' TR. apply trans_alt_br_inv in TR as (_ & x & EQ).
      exists u; split.
      + apply (str_refl (trans_alt ε)); cbn; reflexivity.
      + rewrite EQ. apply HReps'.
  Qed.

  Lemma estar_trans {G : Type -> Type} (a b c : @S G B X) :
    (trans_alt ε)^* a b -> (trans_alt ε)^* b c -> (trans_alt ε)^* a c.
  Proof.
    intros S1 S2.
    assert (H : (@trans_alt G B X ε)^* ⋅ (trans_alt ε)^* ≦ (trans_alt ε)^*) by ka.
    apply H; eexists; eassumption.
  Qed.

  Lemma estar_cons0 {G : Type -> Type} (a b c : @S G B X) :
    trans_alt ε a b -> (trans_alt ε)^* b c -> (trans_alt ε)^* a c.
  Proof.
    intros S1 S2.
    assert (H : @trans_alt G B X ε ⋅ (trans_alt ε)^* ≦ (trans_alt ε)^*) by ka.
    apply H; eexists; eassumption.
  Qed.

  Lemma estar_single' {G : Type -> Type} :
    (@trans_alt G B X ε) ≦ (trans_alt ε)^*.
  Proof.
    ka.
  Qed.

  Lemma estar_single {G : Type -> Type} (a b : @S G B X) :
    trans_alt ε a b -> (trans_alt ε)^* a b.
  Proof.
    apply estar_single'.
  Qed.

  Lemma estar_cons {G : Type -> Type} (a b c : @S G B X) l :
    trans_alt ε a b -> ((trans_alt ε)^* ⋅ trans_alt l) b c ->
    ((trans_alt ε)^* ⋅ trans_alt l) a c.
  Proof.
    intros S1 S2.
    assert (H : @trans_alt G B X ε ⋅ ((trans_alt ε)^* ⋅ trans_alt l)
                ≦ (trans_alt ε)^* ⋅ trans_alt l) by ka.
    apply H; eexists; eassumption.
  Qed.

  Lemma estar_app {G : Type -> Type} (a b c : @S G B X) l :
    (trans_alt ε)^* a b -> ((trans_alt ε)^* ⋅ trans_alt l) b c ->
    ((trans_alt ε)^* ⋅ trans_alt l) a c.
  Proof.
    intros S1 S2.
    assert (H : (@trans_alt G B X ε)^* ⋅ ((trans_alt ε)^* ⋅ trans_alt l)
                ≦ (trans_alt ε)^* ⋅ trans_alt l) by ka.
    apply H; eexists; eassumption.
  Qed.

  Lemma step_ss'_br_r {Z} (c : B Z) x
        (k : Z -> ctree F B X) (t: @S E B X):
    ss'_gen L R Reps t (k x) ->
    ss'_gen L R Reps t (Br c k).
  Proof.
    intros (HA & HB); split.
    - intros t' l Hl TR. apply HA in TR as (l' & u' & STEP & HRtu & HL); auto.
      exists l', u'; split; [| split; assumption].
      eapply estar_cons; [ apply trans_br | exact STEP ].
    - intros t' TR. apply HB in TR as (u' & STEP & HRep).
      exists u'; split; [| assumption].
      eapply estar_cons0; [ apply trans_br | exact STEP ].
  Qed.

  Lemma step_ss'_br {Z Z'} (a: B Z) (b: B Z')
    (k : Z -> ctree E B X) (k' : Z' -> ctree F B X) :
    (forall x, exists y, Reps (k x) (k' y)) ->
    ss'_gen L R Reps (Br a k) (Br b k').
  Proof.
    intros HRep; split.
    - intros t' l Hl TR. apply trans_alt_br_inv in TR as (-> & _); easy.
    - intros t' TR. apply trans_alt_br_inv in TR as (_ & x & EQ).
      destruct (HRep x) as (y & HR').
      exists (Active (k' y)); split.
      + apply estar_single, trans_br.
      + rewrite EQ. apply HR'.
  Qed.

  Lemma step_ss'_br_id {Z} (c: B Z) (d: B Z)
        (k : Z -> ctree E B X) (k' : Z -> ctree F B X) :
    (forall x, Reps (k x) (k' x)) ->
    ss'_gen L R Reps (Br c k) (Br d k').
  Proof.
   intros. apply step_ss'_br; eauto.
  Qed.

  Lemma step_ss'_guard_l
        (t: ctree E B X) (u: @S F B X) :
    Reps t u ->
    ss'_gen L R Reps (Guard t) u.
  Proof.
    intros HRep; split.
    - intros t' l Hl TR. apply trans_alt_guard_inv in TR as (-> & _); easy.
    - intros t' TR. apply trans_alt_guard_inv in TR as (_ & EQ).
      exists u; split; [ apply trans_star_self | rewrite EQ; apply HRep ].
  Qed.

  Lemma step_ss'_guard_r
    (t: @S E B X) (t': ctree F B X) :
    ss'_gen L R Reps t t' ->
    ss'_gen L R Reps t (Guard t').
  Proof.
    intros (HA & HB); split.
    - intros s l Hl TR. apply HA in TR as (l' & u' & STEP & HRtu & HL); auto.
      exists l', u'; split; [| split; assumption].
      eapply estar_cons; [ apply trans_guard | exact STEP ].
    - intros s TR. apply HB in TR as (u' & STEP & HRep).
      exists u'; split; [| assumption].
      eapply estar_cons0; [ apply trans_guard | exact STEP ].
  Qed.

  Lemma step_ss'_guard
        (t: ctree E B X) (t': ctree F B X) :
    Reps t t' ->
    ss'_gen L R Reps (Guard t) (Guard t').
  Proof.
    intros HRep; split.
    - intros s l Hl TR. apply trans_alt_guard_inv in TR as (-> & _); easy.
    - intros s TR. apply trans_alt_guard_inv in TR as (_ & EQ).
      exists (Active t'); split.
      + apply estar_single, trans_guard.
      + rewrite EQ. apply HRep.
  Qed.

  Lemma step_ss'_epsilon_r :
    forall (t : @S E B X) (u u' : @S F B X),
      ss'_gen L R Reps t u' -> (trans_alt ε)^* u u' -> ss'_gen L R Reps t u.
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
    forall (t t' : @S E B X) (u : @S F B X),
    Reps <= ss'_gen L R Reps ->
    ss'_gen L R Reps t u ->
    (trans_alt ε)^* t t' ->
    ss'_gen L R Reps t' u.
  Proof.
    intros t t' u HRle HSS STAR.
    destruct STAR as [n STAR]. revert t t' u HRle HSS STAR.
    induction n; intros t t' u HRle HSS STAR.
    - cbn in STAR. now rewrite STAR in HSS.
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
        (t : ctree E B X) (t': ctree F B X) :
    L τ τ ->
    R t t' ->
    ss'_gen L R Reps (Step t) (Step t').
  Proof.
    intros Ltau HRtt; split.
    - intros s l Hl TR. apply trans_step_inv' in TR as (EQ & ->).
      exists τ, (Active t'). split; [| split].
      + apply trans_alt_estar_l, trans_step.
      + rewrite EQ. apply HRtt.
      + assumption.
    - intros s TR. apply trans_step_inv' in TR as (_ & abs). discriminate.
  Qed.

  Lemma step_ss'_step_l :
    forall (t : ctree E B X) (u : @S F B X),
    (exists l' u', ((trans_alt ε)^* ⋅ trans_alt l') u u' /\ R t u' /\ L τ l') ->
    ss'_gen L R Reps (Step t) u.
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
  (L : rel _ _) :
  ssim' L (Stuck : ctree E B X) (Stuck : ctree F B X).
Proof.
  step. apply step_ss'_stuck.
Qed.

Lemma step_ssbt'_ret {E F B X}
  (x : X) (y : X) (L : rel _ _)
  {R : Chain (@ss' E F B X L)} :
  L (val x) (val y) ->
  ss' L `R (Ret x : ctree E B X) (Ret y : ctree F B X).
Proof.
  intros.
  unshelve eapply step_ss'_ret; eauto.
  apply (b_chain R). apply ss'_stuck.
Qed.

Lemma ssim'_ret {E F B X}
  (x : X) (y : X) (L : rel _ _) :
  L (val x) (val y) ->
  ssim' L (Ret x : ctree E B X) (Ret y : ctree F B X).
Proof.
  now intros; step; apply step_ssbt'_ret.
Qed.

Lemma ssim'_step {E F B X}
  (t : ctree E B X) (u : ctree F B X) (L : rel _ _) :
  L τ τ  ->
  ssim' L t u ->
  ssim' L (Step t) (Step u).
Proof.
  now intros; step; apply step_ss'_step.
Qed.

Lemma ssim'_guard {E F B X}
  (t : ctree E B X) (u : ctree F B X) (L : rel _ _) :
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

Lemma step_ssbt'_brS {E F B X Z Z'} {L}
  {R : Chain (@ss' E F B X L)}
  (c: B Z) (d: B Z')
  (k : Z -> ctree E B X) (k' : Z' -> ctree F B X) :
  L τ τ  ->
  (forall x, exists y, `R (k x) (k' y)) ->
  ss' L `R (BrS c k) (BrS d k').
Proof.
  intros.
  apply step_ss'_br; auto.
  intros x; destruct (H0 x) as (y & ?); exists y.
  apply (b_chain R), step_ss'_step; auto.
Qed.

Lemma ssim'_brS {E F B X Z Z'} {L}
  (c: B Z) (d: B Z')
  (k : Z -> ctree E B X) (k' : Z' -> ctree F B X) :
  L τ τ  ->
  (forall x, exists y, ssim' L (k x) (k' y)) ->
  ssim' L (BrS c k) (BrS d k').
Proof.
  now intros; step; apply step_ssbt'_brS.
Qed.

Lemma step_ssbt'_brS_id {E F B X Z} {L}
  {R : Chain (@ss' E F B X L)}
  (c: B Z) (d: B Z)
  (k : Z -> ctree E B X) (k' : Z -> ctree F B X) :
  L τ τ  ->
  (forall x, ` R (k x) (k' x)) ->
  ss' L `R (BrS c k) (BrS d k').
Proof.
  intros.
  apply step_ss'_br_id; auto.
  intros; apply (b_chain R), step_ss'_step; auto.
Qed.

Lemma ssim'_brS_id {E F B X Z} {L}
  (c: B Z) (d: B Z)
  (k : Z -> ctree E B X) (k' : Z -> ctree F B X) :
  L τ τ  ->
  (forall x, ssim' L (k x) (k' x)) ->
  ssim' L (BrS c k) (BrS d k').
Proof.
  now intros; step; apply step_ssbt'_brS_id.
Qed.

Lemma ssim'_vis
  {E F B X Z Z'} {L}
  (e: E Z) (f: F Z')
  (k : Z -> ctree E B X) (k' : Z' -> ctree F B X) :
  ssim' L (Passive e k) (Passive f k') ->
  L (ask e) (ask f) ->
  ssim' L (Vis e k) (Vis f k').
Proof.
  intros Hpas Hask; step; apply step_ss'_vis; [exact Hpas | exact Hask].
Qed.

Lemma ssim'_vis_id
  {E F B X Z} {L}
  (e: E Z) (f: F Z)
  (k : Z -> ctree E B X) (k' : Z -> ctree F B X) :
  ssim' L (Passive e k) (Passive f k') ->
  L (ask e) (ask f) ->
  ssim' L (Vis e k) (Vis f k').
Proof.
  intros Hpas Hask; step; apply step_ss'_vis_id; [exact Hpas | exact Hask].
Qed.

Lemma ssim'_vis_l
  {E F B X Z} {L}
  (e: E Z)
  (k : Z -> ctree E B X) (u : @S F B X) :
  (exists l' u', ((trans_alt ε)^* ⋅ trans_alt l') u u' /\ ssim' L (Passive e k) u' /\ L (ask e) l') ->
  ssim' L (Vis e k) u.
Proof.
  intros H; step; apply step_ss'_vis_l; exact H.
Qed.

Lemma ssim'_epsilon_l {E F B X} {L} :
  forall (t t' : @S E B X) (u : @S F B X),
  ssim' L t u ->
  (trans_alt ε)^* t t' ->
  ssim' L t' u.
Proof.
  intros. step. eapply ss'_gen_epsilon_l.
  (* blessed postfixpoint *)
  - exact (gfp_pfp (ss' L)).
  - step in H. apply H.
  - apply H0.
Qed.

Section Inversion_Rules.

  Context {E F B : Type -> Type}
          {X : Type}
          {L : rel (@label E X) (@label F X)}
          {R Reps : rel (@S E B X) (@S F B X)}.

  Lemma ss'_vis_l_inv {Z} :
    forall (e : E Z) (k : Z -> ctree E B X) (u : @S F B X),
    ss'_gen L R Reps (Vis e k) u ->
    exists l' u', ((trans_alt ε)^* ⋅ trans_alt l') u u' /\ R (Passive e k) u' /\ L (ask e) l'.
  Proof.
    intros e k u (HA & _).
    apply (HA (Passive e k) (ask e)); [ discriminate | apply trans_ask ].
  Qed.

  Lemma ss'_step_l_inv :
    forall (t : ctree E B X) (u : @S F B X),
    ss'_gen L R Reps (Step t) u ->
    exists l' u', ((trans_alt ε)^* ⋅ trans_alt l') u u' /\ R t u' /\ L τ l'.
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

  Context {E F B : Type -> Type} {X : Type}
          (L : rel (@label E X) (@label F X)).

  (* Up-to epsilon *)

  #[local] Obligation Tactic := idtac.
  Program Definition epsilon_ctx_r : mon (rel (@S E B X) (@S F B X))
    := {| body R t u := exists u', (trans_alt ε)^* u u' /\ R t u' |}.
  Next Obligation.
    intros R R' HR t u (u' & STAR & HRtu).
    exists u'; split; [ exact STAR | now apply HR ].
  Qed.

  Lemma epsilon_ctx_r_sst' {c: Chain (@ss' E F B X L)}:
    forall x y, epsilon_ctx_r `c x y -> `c x y.
  Proof.
    apply tower.
    - intros ? INC x y (? & ? & ?) ??; red.
      apply INC; auto.
      eexists; split; eauto.
      apply leq_infx in H1.
      now apply H1.
    - clear.
      intros R IH t u (u' & STAR & HSS).
      eapply step_ss'_epsilon_r; [ exact HSS | exact STAR ].
  Qed.

End upto.


#[local] Example ssim'_spin {E F B X} (L : rel (@label E X) (@label F X)) :
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

Variant update_val_rel {E F X X'}
  (L : rel (@label E X') (@label F X')) (R0 : rel X X)
  : rel (@label E X) (@label F X) :=
| uvr_τ :
    L τ τ ->
    update_val_rel L R0 τ τ
| uvr_ask {Z Z'} (e : E Z) (f : F Z') :
    L (ask e) (ask f) ->
    update_val_rel L R0 (ask e) (ask f)
| uvr_rcv {Z Z'} (e : E Z) (v : Z) (f : F Z') (w : Z') :
    L (rcv e v) (rcv f w) ->
    update_val_rel L R0 (rcv e v) (rcv f w)
| uvr_val (v w : X) :
    R0 v w ->
    update_val_rel L R0 (val v) (val w).

Section uvr_inv.

  Context {E F : Type -> Type} {X X' : Type}
          {L : rel (@label E X') (@label F X')} {R0 : rel X X}.

  Lemma update_val_rel_val_l (v : X) (l2 : @label F X) :
    update_val_rel L R0 (val v) l2 ->
    exists w, l2 = val w /\ R0 v w.
  Proof.
    intros H; dependent destruction H; eauto.
  Qed.

  Lemma update_val_rel_τ_l (l2 : @label F X) :
    update_val_rel L R0 τ l2 ->
    l2 = τ /\ L τ τ.
  Proof.
    intros H; dependent destruction H; eauto.
  Qed.

  Lemma update_val_rel_ask_l {Z} (e : E Z) (l2 : @label F X) :
    update_val_rel L R0 (ask e) l2 ->
    exists Z' (f : F Z'), l2 = ask f /\ L (ask e) (ask f).
  Proof.
    intros H; dependent destruction H; eauto.
  Qed.

  Lemma update_val_rel_rcv_l {Z} (e : E Z) (v : Z) (l2 : @label F X) :
    update_val_rel L R0 (rcv e v) l2 ->
    exists Z' (f : F Z') (w : Z'), l2 = rcv f w /\ L (rcv e v) (rcv f w).
  Proof.
    intros H; dependent destruction H; eauto.
  Qed.

End uvr_inv.

Lemma estar_seq {E B X} (a b : @SS E B X) :
  a ⩸ b -> (trans_alt ε)^* a b.
Proof.
  intros H; exists O; exact H.
Qed.

Lemma estar_passive {E B X Z} (e : E Z) (g : Z -> ctree E B X) (m : @SS E B X) :
  (trans_alt ε)^* (Passive e g) m ->
  (Passive e g : @SS E B X) ⩸ m.
Proof.
  intros [n STAR]; destruct n.
  - exact STAR.
  - destruct STAR as [mid STEP _].
    apply trans_passive_inv' in STEP as (z & _ & Habs); easy.
Qed.

Lemma estar_bind {E B X Y} (t u : ctree E B X) (k : X -> ctree E B Y) :
  (trans_alt ε)^* (Active t) (Active u) ->
  (trans_alt ε)^* (Active (x <- t;; k x)) (Active (x <- u;; k x)).
Proof.
  intros [n STAR]; revert t STAR; induction n; intros t STAR.
  - cbn in STAR; dependent destruction STAR.
    apply estar_seq; constructor.
    now rewrite EQ.
  - destruct STAR as [mid STEP REST].
    unfold trans_alt in STEP; cbn in STEP; dependent destruction STEP.
    + eapply estar_cons0.
      * apply trans_bind_l_ε; eapply Transbr; eauto.
      * apply IHn; exact REST.
    + eapply estar_cons0.
      * apply trans_bind_l_ε; eapply Transguard; eauto.
      * apply IHn; exact REST.
Qed.


Section bind_restore.

  Context {E F B : Type -> Type} {X X' : Type}
          (L : rel (@label E X') (@label F X'))
          (R0 : rel X X).

  Notation uvr := (update_val_rel L R0).

  Lemma bind_chain_gen {R : Chain (@ss' E F B X' L)} :
    forall (t : ctree E B X) (t' : ctree F B X)
      (k : X -> ctree E B X') (k' : X -> ctree F B X'),
      ssim' uvr (Active t) (Active t') ->
      (forall x x', R0 x x' -> ` R (Active (k x)) (Active (k' x'))) ->
      ` R (Active (x <- t;; k x)) (Active (x <- t';; k' x)).
  Proof.
    apply tower.
    - intros ? INC t t' k k' tt kk ? ?; red.
      apply INC; auto.
      intros. now apply kk. 
    - clear; intros R IH t t' k k' tt kk.
      split.
      + intros s l Hne TR.
        apply trans_bind_inv in TR as
          [ (x & EQt & TRk)
          | [ (-> & t1 & TRt & SQ)
          | [ (Heps & _)
          | (Z & e & g & -> & TRt & SQ) ]]].
          (* t ≅ Ret, show t' steps to Stuck as well *)
        * assert (cV : trans_alt (val x)
                         (Active t) (Active (Stuck : ctree E B X))) by now constructor. 
          step in tt; repeat red in tt; destruct tt as [tt_nonep tt_ep].
          (* know cV reduced  *)
          assert (HneV : (val x : @label E X) <> ε) by easy.
          (* take the nonep branch *)
          destruct (tt_nonep _ _ HneV cV) as (l2 & n & RESP & _ & HL2).
          apply update_val_rel_val_l in HL2 as (x' & -> & Hx).
          destruct RESP as [m STAR STEPv].
          unfold trans_alt in STEPv; cbn in STEPv; dependent destruction STEPv.
          specialize (kk x x' Hx).
          destruct kk as (kkA & _).
          destruct (kkA _ _ Hne TRk) as (l' & u' & RESP2 & Hgfp & HL').
          exists l', u'; ssplit.
          -- destruct RESP2 as [m2 STAR2 STEP2].
             exists m2; [| exact STEP2].
             eapply estar_trans.
             ++ apply estar_bind; exact STAR.
             ++ eapply estar_trans; [| exact STAR2].
                apply estar_seq; constructor.
                rewrite H, bind_ret_l; reflexivity.
          -- exact Hgfp.
          -- exact HL'.
        * assert (cT : ((trans_alt ε)^* ⋅ trans_alt τ) (Active t) (Active t1))
            by (apply trans_star_l; exact TRt).
          step in tt.
          assert (Hneτ : (τ : @label E X) <> ε) by discriminate.
          destruct (tt _ _ Hneτ cT) as (l2 & n & RESP & Htt' & HL2).
          apply update_val_rel_τ_l in HL2 as (-> & HLττ).
          destruct RESP as [m STAR STEPτ].
          unfold trans_alt in STEPτ; cbn in STEPτ; dependent destruction STEPτ.
          exists τ, (Active (x <- u;; k' x)); ssplit.
          -- exists (Active (x <- t0;; k' x)).
             ++ apply estar_bind; exact STAR.
             ++ apply trans_bind_l_τ; eapply Transstep; eauto.
          -- rewrite SQ; apply IH; [exact Htt' | intros; step; now apply kk].
          -- exact HLττ.
        * easy.
        (* a short trip is needed: active -> passive -> active 
           via ask/rcv. not hard but a bit tedious. if this 
           logic appears again it should be factored out into a lemma.  *)
        * assert (cA : ((trans_alt ε)^* ⋅ trans_alt (ask e))
                         (Active t) (Passive e g))
            by (apply trans_star_l; exact TRt).
          step in tt.
          assert (HneA : (ask e : @label E X) <> ε) by discriminate.
          destruct (tt _ _ HneA cA) as (l2 & n & RESP & Htt' & HL2).
          apply update_val_rel_ask_l in HL2 as (Z' & f & -> & HLaa).
          destruct RESP as [m STAR STEPa].
          unfold trans_alt in STEPa; cbn in STEPa; dependent destruction STEPa.
          exists (ask f), (Passive f (fun z => x <- k0 z;; k' x)); ssplit.
          -- exists (Active (x <- t0;; k' x)).
             ++ apply estar_bind; exact STAR.
             ++ apply trans_bind_l_ask; econstructor; exact H.
          -- rewrite SQ; apply (b_chain R); split.
             ++ intros s2 l2 Hne2 TR2.
                apply trans_passive_inv' in TR2 as (z & SQ2 & ->).
                step in Htt'.
                assert (cR : ((trans_alt ε)^* ⋅ trans_alt (rcv e z))
                               (Passive e g) (Active (g z))).
                { apply trans_star_l; econstructor; reflexivity. }
                assert (HneR : (rcv e z : @label E X) <> ε) by discriminate.
                destruct (Htt' _ _ HneR cR) as (l3 & n3 & RESP3 & Htt2 & HL3).
                apply update_val_rel_rcv_l in HL3 as (Z2 & f2 & w & -> & HLrr).
                destruct RESP3 as [m3 STAR3 STEP3].
                apply estar_passive in STAR3.
                dependent destruction STAR3.
                apply trans_passive_inv' in STEP3 as (w' & SQ3 & Heq).
                dependent destruction Heq.
                dependent destruction SQ3.
                exists (rcv f w'), (Active (x <- k0 w';; k' x)); ssplit.
                ** apply trans_star_l; econstructor; reflexivity.
                ** rewrite SQ2.
                   assert (SQ5 : (Active (x <- t1;; k' x) : @SS F B X')
                                   ⩸ (Active (x <- k0 w';; k' x))).
                   { constructor; rewrite EQ0, <- (EQ w'); reflexivity. }
                   rewrite <- SQ5; apply IH; [exact Htt2 | intros; step; now apply kk].
                ** exact HLrr.
             ++ intros s2 TR2.
                apply trans_passive_inv' in TR2 as (z & _ & Habs); easy.
          -- exact HLaa.
      + intros s TR.
        apply trans_bind_inv in TR as
          [ (x & EQt & TRk)
          | [ (Habs & _)
          | [ (_ & t1 & TRt & SQ)
          | (Z & e & g & Habs & _) ]]].
        * assert (cV : ((trans_alt ε)^* ⋅ trans_alt (val x))
                         (Active t) (Active (Stuck : ctree E B X))).
          { apply trans_star_l; eapply Transval; [exact EQt | reflexivity]. }
          step in tt.
          assert (HneV : (val x : @label E X) <> ε) by discriminate.
          destruct (tt _ _ HneV cV) as (l2 & n & RESP & _ & HL2).
          apply update_val_rel_val_l in HL2 as (x' & -> & Hx).
          destruct RESP as [m STAR STEPv].
          unfold trans_alt in STEPv; cbn in STEPv; dependent destruction STEPv.
          specialize (kk x x' Hx).
          destruct kk as (_ & kkB).
          destruct (kkB _ TRk) as (u2 & STARu & Hgfp2).
          exists u2; split.
          -- eapply estar_trans.
             ++ apply estar_bind; exact STAR.
             ++ eapply estar_trans; [| exact STARu].
                apply estar_seq; constructor.
                rewrite H, bind_ret_l; reflexivity.
          -- exact Hgfp2.
        * easy.
        * exists (Active (x <- t';; k' x)); split.
          -- apply trans_star_self.
          -- rewrite SQ; apply IH; [| intros; step; now apply kk].
             eapply ssim_eps_l; [exact tt | exact TRt].
        * easy.
  Qed.

  Lemma ssim'_clo_bind :
    forall (t : ctree E B X) (t' : ctree F B X)
      (k : X -> ctree E B X') (k' : X -> ctree F B X'),
      ssim uvr (Active t) (Active t') ->
      (forall x x', R0 x x' -> ssim' L (Active (k x)) (Active (k' x'))) ->
      ssim' L (Active (x <- t;; k x)) (Active (x <- t';; k' x)).
  Proof.
    intros t t' k k' tt kk.
    apply (@bind_chain_gen (chain_gfp (ss' L))); assumption.
  Qed.

End bind_restore.

Lemma update_val_rel_eq_refl {E X X'} :
  forall (l : @label E X),
    l <> ε -> @update_val_rel E E X X' eq eq l l.
Proof.
  destruct l; intro Hne. 
  all: easy || now constructor. 
Qed.

Lemma ssim_update_val_rel_eq {E B X X'} :
  forall (t u : @SS E B X),
    ssim eq t u -> ssim (@update_val_rel E E X X' eq eq) t u.
Proof.
  unfold ssim at 2; coinduction R CH; intros t u H.
  intros t' l Hne TR.
  step in H.
  destruct (H _ _ Hne TR) as (l' & u' & RESP & HR & HL).
  exists l', u'; ssplit.
  - assumption.
  - apply CH, HR.
  - subst l'; apply update_val_rel_eq_refl; assumption.
Qed.

Lemma ss'_clo_bind_eq {E B X X'} {R : Chain (@ss' E E B X' eq)} :
  forall (t t' : ctree E B X) (k k' : X -> ctree E B X'),
    ssim eq (Active t) (Active t') ->
    (forall x, ssim' eq (Active (k x)) (Active (k' x))) ->
    ` R (Active (x <- t;; k x)) (Active (x <- t';; k' x)).
Proof.
  intros t t' k k' tt kk.
  apply bind_chain_gen with (R0 := eq).
  - apply ssim_update_val_rel_eq; exact tt.
  - intros x x' ->; apply kk.
Qed.

Lemma ssim'_clo_bind_eq {E B X X'} :
  forall (t t' : ctree E B X) (k k' : X -> ctree E B X'),
    ssim eq (Active t) (Active t') ->
    (forall x, ssim' eq (Active (k x)) (Active (k' x))) ->
    ssim' eq (Active (x <- t;; k x)) (Active (x <- t';; k' x)).
Proof.
  intros t t' k k' tt kk.
  apply (@ss'_clo_bind_eq E B X X' (chain_gfp (ss' eq))); assumption.
Qed.
