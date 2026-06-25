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
     Eq.Epsilon.

From RelationAlgebra Require Export
     monoid kat kat_tac rel srel.

Import CoindNotations.
Import CTree.
Set Implicit Arguments.

(* TODO: Decide where to set this *)
Arguments trans_alt : simpl never.

Ltac ssplit := split; [| split].

Section StrongSimAlt.

  (* finition ss'_gen {E F C D : Type -> Type} {X : Type}
    (L : rel (@label E X) (@label F X))
    (R Reps : rel (ctree E C X) (ctree F D X))
    (t : ctree E C X) (u : ctree F D Y) :=

    (productive t ->
    (* t and u step together under labels related by L, assuming 
    t is "productive"; that is, not a Br *)
      forall l t', trans l t t' ->
             exists l' u', trans l' u u' /\ R t' u' /\ L l l')
    (* if t branches, u ϵ-steps to u'  *)
    /\ (forall Z (c : C Z) k,
          t ≅ Br c k ->
          forall x, exists u', epsilon u u' /\ Reps (k x) u')
    /\ (forall t',
          t ≅ Guard t' ->
          exists u', epsilon u u' /\ Reps t' u').
 *)
Locate dot. 
  Definition ss'_gen {E F B : Type -> Type} {X : Type}
    (L : rel (@label E X) (@label F X))
    (R Reps : rel SS SS)
    (t : SS) (u : SS) :=

    (forall t' l, l <> ε -> trans_alt (B:=B) l t t'
    -> exists l' u', ((trans_alt (B:=B) ε)^* ⋅ (trans_alt l')) u u' /\ R t' u' /\ L l l')
    /\
      (forall t', trans_alt (B:=B) ε t t' -> exists u', (trans_alt (B:=B) ε)^* u u' /\ Reps t' u').

  #[global] Instance weq_ss'_gen {E F B X} :
    Proper (weq ==> eq ==> weq) (@ss'_gen E F B X).
  Proof.
    cbn. intros L L' HL R ? <- x y; split; intros (HA & HB); split; intros.
    - destruct (HA _ _ H H0) as (l'' & u'' & Htrans & HR & HL').
      do 2 esplit; split; [eassumption | split; [eassumption |]]; now apply HL.
    - now apply HB in H.
    - destruct (HA _ _ H H0) as (l'' & u'' & Htrans & HR & HL').
      do 2 esplit; split; [eassumption | split; [eassumption |]]; now apply HL.
    - now apply HB in H.
  Qed.

  #[global] Instance ss'_gen_mon {E F B X}
    (L : rel (@label E X) (@label F X)) :
    Proper (Coinduction.lattice.leq ==> Coinduction.lattice.leq ==> Coinduction.lattice.leq)
     (@ss'_gen E F B X L).
  Proof.
    cbn. intros R R' HR Reps1 Reps2 HReps s1 s2 [Hl Hep]; split; intros.
    - destruct (Hl _ _ H H0) as (l'' & u'' & Htrans & HRtu & HL').
      do 2 esplit; split; [eassumption | split; [now apply HR | assumption]].
    - apply Hep in H as (u' & Htrans & HRtu). exists u'; split; [assumption | now apply HReps].
  Qed.

(*|
An alternative definition [ss'] of strong simulation.
The simulation challenge does not involve an inductive transition relation,
thus simplifying proofs.
|*)
  Program Definition ss' {E F B : Type -> Type} {X : Type}
    (L : rel (@label E X) (@label F X)) :
    mon (SS -> SS -> Prop) :=
    {| body R t u :=
      @ss'_gen E F B X L R R t u  
    |}.
      Next Obligation.
    epose proof (@ss'_gen_mon E F B X). eapply H1.
    3: apply H0.
    all: auto.
  Qed.


End StrongSimAlt.

Definition ssim' {E F B X} L :=
  (gfp (@ss' E F B X L): hrel _ _).

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


  #[global] Instance Reflexive_ss' R Reps
    `{Reflexive _ R} `{Reflexive _ L} `{Reflexive _ Reps}:
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

  Lemma estar_single {G : Type -> Type} (a b : @S G B X) :
    trans_alt ε a b -> (trans_alt ε)^* a b.
  Proof.
    intro S; eapply estar_cons0; [ exact S | apply trans_star_self ].
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
  - apply (gfp_pfp (ss' L)).
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

  Context {E F C D: Type -> Type} {X Y: Type}
          (L : hrel (@label E) (@label F)).

  (* Up-to epsilon *)

  Program Definition epsilon_ctx_r : mon (rel (ctree E B X) (ctree F B X))
    := {| body R t u := epsilon_ctx (fun u => R t u) u |}.
  Next Obligation.
    destruct H0 as (? & ? & ?). red. eauto.
  Qed.

  Lemma epsilon_ctx_r_sst' {c: Chain (ss' L)}:
    forall x y, epsilon_ctx_r `c x y -> `c x y.
  Proof.
    apply tower.
    - intros ? INC x y (? & ? & ?) ??; red.
      apply INC; auto.
      eexists; split; eauto.
      apply leq_infx in H1.
      now apply H1.
    - clear.
      intros R IH t u (u' & Heps & (HA & HB & HC)).
      ssplit.
      + intros HP l t' TR.
        eapply HA in TR as (l'' & u'' & TR' & ? & ?); auto.
        do 2 eexists; ssplit.
        eapply epsilon_trans; eauto.
        all: auto.
      + intros * EQ ?.
        eapply HB in EQ as (? & ? & ?).
        eexists; split; [| eauto].
        etransitivity; eauto.
      + intros * EQ.
        eapply HC in EQ as (? & ? & ?).
        eexists; split; [| eauto].
        etransitivity; eauto.
  Qed.

  (* Up-to ss. *)
  (* This principle holds because an ss step always corresponds
     to one or more ss' steps. *)
  Lemma ss_sst' {c : Chain (ss' L)} :
    forall x y, @ss E F C D X Y L ` c x y -> `c x y.
  Proof.
    apply tower.
    - intros ? INC x y HSS ??; red.
      apply INC; auto.
      intros ?? TR; apply HSS in TR as (?& ?& ? &? &?).
      do 2 eexists; ssplit; eauto.
      apply leq_infx in H.
      now apply H.
    - clear.
      intros R IH t u HSS.
      ssplit.
      + intros HP l t' TR.
        apply HSS in TR as (l'' & u'' & TR' & ? & ?).
        do 2 eexists; ssplit; eauto.
        now apply (b_chain R).
      + intros * EQ ?.
        eexists; split; eauto.
        apply IH.
        intros ?? TR.
        edestruct HSS as (l'' & u'' & TR' & ? & ?).
        rewrite EQ; econstructor; apply TR.
        do 2 eexists; ssplit; eauto.
        now apply (b_chain R).
      + intros * EQ.
        eexists; split; eauto.
        apply IH.
        intros ?? TR.
        edestruct HSS as (l'' & u'' & TR' & ? & ?).
        rewrite EQ; econstructor; apply TR.
        do 2 eexists; ssplit; eauto.
        now apply (b_chain R).
  Qed.

End upto.

Arguments ss_sst' {E F B X} L.

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
    The resulting enhancing function gives a valid up-to technique
|*)

  Lemma bind_chain_gen L0
    (ISVR : is_update_val_rel L R0 L0)
    {R : Chain (@ss' E F C D X' Y' L)} :
    forall (t : ctree E B X) (t' : ctree F B X) (k : X -> ctree E B X') (k' : Y -> ctree F B X'),
      ssim L0 t t' ->
      (forall x x', R0 x x' -> elem R (k x) (k' x')) ->
      ` R (bind t k) (bind t' k').
  Proof.
    apply tower.
    - intros ? INC ? ? ? ? tt' kk' ? ?.
      apply INC. apply H. apply tt'.
      intros x x' xx'. apply leq_infx in H. apply H. now apply kk'.
    - clear R; intros R IH ? ? ? ? tt kk.
      step in tt. ssplit.
      + simpl; intros PROD l u STEP.
        apply trans_bind_inv in STEP as [(?H & ?t' & STEP & EQ) | (v & STEPres & STEP)].
        apply tt in STEP as (l' & u' & STEP & EQ' & ?).
        do 2 eexists. ssplit.
        apply trans_bind_l; eauto.
        * intro Hl. destruct Hl.
          apply ISVR in H0; etrans.
          inversion H0; subst. apply H. constructor. apply H2.
          constructor.
        * rewrite EQ; apply IH.
          eauto.
          intros.
          apply (b_chain R); auto.
        * apply ISVR in H0; etrans.
          destruct H0. exfalso. apply H. constructor. apply H2.
        * assert (t ≅ Ret v).
          { apply productive_bind in PROD. apply trans_val_epsilon in STEPres as [? _].
            now apply productive_epsilon. } subs.
          apply tt in STEPres as (l' & u' & STEPres & EQ' & ?).
          apply ISVR in H; etrans.
          dependent destruction H. 2: { exfalso. apply H. constructor. }
                                 pose proof (trans_val_inv STEPres) as EQ.
          rewrite EQ in STEPres.
          specialize (kk v v2 H).
          rewrite bind_ret_l in PROD.
          apply kk in STEP as (? & u''' & STEP & EQ'' & ?); auto.
          do 2 eexists; split.
          eapply trans_bind_r; eauto.
          split; auto.
      + intros * EQ ?.
        apply br_equ_bind in EQ as EQ'.
        destruct EQ' as [(v & EQ' & EQ'') | (?k0 & EQ' & EQ'')].
        * subs.
          edestruct tt as (l & t'' & STEPres & _ & ?). etrans.
          apply ISVR in H; etrans.
          apply update_val_rel_val_l in H as (v' & -> & EQ').
          rewrite bind_ret_l in EQ.
          specialize (kk v v' EQ').
          apply kk with (x := x) in EQ. destruct EQ as (u' & EPS & EQ).
          exists u'.
          apply trans_val_epsilon in STEPres as [? _]. split; eauto.
          eapply epsilon_bind; eassumption.
        * subs. eexists. split; [now constructor |].
          rewrite EQ''.
          apply IH.
          eapply ssim_br_l_inv. step. apply tt.
          intros.
          apply (b_chain R); eauto.
      + intros * EQ.
        apply guard_equ_bind in EQ as EQ'.
        destruct EQ' as [(v & EQ' & EQ'') | (?k0 & EQ' & EQ'')].
        * subs.
          edestruct tt as (l & t'' & STEPres & _ & ?). etrans.
          apply ISVR in H; etrans.
          apply update_val_rel_val_l in H as (v' & -> & EQ').
          rewrite bind_ret_l in EQ.
          specialize (kk v v' EQ').
          apply kk in EQ. destruct EQ as (u' & EPS & EQ).
          exists u'.
          apply trans_val_epsilon in STEPres as [? _]. split; eauto.
          eapply epsilon_bind; eassumption.
        * subs. eexists. split; [now constructor |].
          rewrite <- EQ''.
          apply IH.
          eapply ssim_guard_l_inv. step. apply tt.
          intros.
          apply (b_chain R); eauto.
  Qed.

End bind.

(*|
Expliciting the reasoning rule provided by the up-to principles.
|*)
Lemma ss'_clo_bind_gen {E F C D: Type -> Type} {X Y X' Y': Type}  {L : rel (@label E) (@label F)}
      (R0 : rel X Y) L0
      (HL0 : is_update_val_rel L R0 L0)
      (t1 : ctree E B X) (t2: ctree F B X)
      (k1 : X -> ctree E B X') (k2 : Y -> ctree F B X'):
  ssim L0 t1 t2 ->
  (forall x y, R0 x y -> ssim' L (k1 x) (k2 y)) ->
  ssim' L (t1 >>= k1) (t2 >>= k2).
Proof.
  intros.
  eapply bind_chain_gen; eauto.
Qed.

Lemma ss'_clo_bind {E F C D: Type -> Type} {X Y X' Y': Type} {L : rel (@label E) (@label F)}
  (R0 : rel X Y)
  {R : Chain (@ss' E F C D X' Y' L)} :
  forall (t : ctree E B X) (t' : ctree F B X) (k : X -> ctree E B X') (k' : Y -> ctree F B X'),
    t (≲update_val_rel L R0) t' ->
    (forall x x', R0 x x' -> elem R (k x) (k' x')) ->
    ` R (bind t k) (bind t' k').
Proof.
  intros.
  eapply bind_chain_gen; eauto using update_val_rel_correct.
Qed.

Lemma ssim'_clo_bind {E F C D: Type -> Type} {X Y X' Y': Type} {L : rel (@label E) (@label F)}
      (R0 : rel X Y)
      (t1 : ctree E B X) (t2: ctree F B X)
      (k1 : X -> ctree E B X') (k2 : Y -> ctree F B X'):
  t1 (≲update_val_rel L R0) t2 ->
  (forall x y, R0 x y -> ssim' L (k1 x) (k2 y)) ->
  ssim' L (t1 >>= k1) (t2 >>= k2).
Proof.
  intros. eapply ss'_clo_bind; eauto.
Qed.

Lemma ss'_clo_bind_eq {E C D: Type -> Type} {X X': Type}
  {R : Chain (@ss' E E C D X' X' eq)} :
  forall (t : ctree E B X) (t' : ctree E D X) (k : X -> ctree E B X') (k' : X -> ctree E D X'),
    t ≲ t' ->
    (forall x, elem R (k x) (k' x)) ->
    ` R (bind t k) (bind t' k').
Proof.
  intros.
  eapply bind_chain_gen; eauto.
  - apply update_val_rel_eq.
  - intros; subst. apply H0.
Qed.

Lemma ssim'_clo_bind_eq {E C D: Type -> Type} {X X': Type}
      (t1 : ctree E B X) (t2: ctree E D X)
      (k1 : X -> ctree E B X') (k2 : X -> ctree E D X'):
  t1 ≲ t2 ->
  (forall x, ssim' eq (k1 x) (k2 x)) ->
  ssim' eq (t1 >>= k1) (t2 >>= k2).
Proof.
  apply ss'_clo_bind_eq.
Qed.

Lemma ss_ss'_chain {E F B X L} {R : Chain (ss' L)} :
  forall (t : ctree E B X) (u : ctree F B X),
  ss L `R t u ->
  ss' L `R t u.
Proof.
  - intros.
    ssplit; intros.
    + apply H in H1 as (? & ? & ? & ? & ?). eauto 6.
    + subs. apply ss_br_l_inv with (x := x) in H.
      apply ss_sst' in H. eauto.
    + subs. apply ss_guard_l_inv in H. apply ss_sst' in H.
      eauto.
Qed.

(* This alternative notion of simulation is equivalent to [ssim] *)
Theorem ssim_ssim' {E F B X} :
  forall L (t : ctree E B X) (t' : ctree F B X), ssim L t t' <-> ssim' L t t'.
Proof.
  split; intros.
  - red. revert t t' H. coinduction R CH. intros.
    ssplit; intros.
    + step in H. apply H in H1 as (? & ? & ? & ? & ?). eauto 6.
    + subs. apply ssim_br_l_inv with (x := x) in H. eauto.
    + subs. apply ssim_guard_l_inv in H. eauto.
  - revert t t' H. coinduction R CH.
    intros * HSS ?? TR.
    apply trans_epsilon in TR as (? & ? & ? & ?).
    apply ssim'_epsilon_l with (t' := x) in HSS; auto.
    step in HSS. apply (proj1 HSS) in H1 as (? & ? & ? & ? & ?); auto.
    eauto 6.
Qed.

#[local] Example ssim'_spin {E B X} : forall (t : ctree E B X), (spin : ctree E B X) ≲ t.
Proof.
  intros.
  apply ssim_ssim'.
  coinduction R CH.
  rewrite unfold_spin.
  apply step_ss'_guard_l.
  apply CH.
Qed.
