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
     Eq
     Eq.Epsilon.

From RelationAlgebra Require Export
     rel srel.

Import CoindNotations.
Import CTree.
Set Implicit Arguments.

(* TODO: Decide where to set this *)
Arguments trans : simpl never.

Ltac ssplit := split; [| split].

Section StrongSimAlt.

  Definition ss'_gen {E F C D : Type -> Type} {X Y : Type}
    (L : rel (@label E) (@label F))
    (R Reps : rel (ctree E C X) (ctree F D Y))
    (t : ctree E C X) (u : ctree F D Y) :=
    (productive t ->
     forall l t', trans l t t' ->
             exists l' u', trans l' u u' /\ R t' u' /\ L l l')
    /\ (forall Z (c : C Z) k,
          t ≅ Br c k ->
          forall x, exists u', epsilon u u' /\ Reps (k x) u')
    /\ (forall t',
          t ≅ Guard t' ->
          exists u', epsilon u u' /\ Reps t' u').

  #[global] Instance weq_ss'_gen {E F C D X Y} :
    Proper (weq ==> weq) (@ss'_gen E F C D X Y).
  Proof.
    cbn. intros; split; (split; [| split]); intros.
    all: try now (eapply H0 in H1 as (? & ? & ?); eauto).
    all: apply H0 in H2 as (? & ? & ? & ? & ?); auto; edestruct H; eauto 6 with trans.
  Qed.

  #[global] Instance ss'_gen_mon {E F C D : Type -> Type} {X Y : Type}
    (L : rel (@label E) (@label F)) :
    Proper (leq ==> leq ==> leq) (@ss'_gen E F C D X Y L).
  Proof.
    cbn. intros.
    destruct H1 as (? & ? & ?).
    split; [| split].
    - intros.
      edestruct H1 as (? & ? & ? & ?); eauto.
      eexists _, x2; intuition; eauto.
    - intros. edestruct H2 as (? & ? & ?); eauto.
    - intros. edestruct H3 as (? & ? & ?); eauto.
  Qed.

(*|
An alternative definition [ss'] of strong simulation.
The simulation challenge does not involve an inductive transition relation,
thus simplifying proofs.
|*)
  Program Definition ss' {E F C D : Type -> Type} {X Y : Type}
    (L : rel (@label E) (@label F)) :
    mon (ctree E C X -> ctree F D Y -> Prop) :=
    {| body R t u :=
      ss'_gen L R R t u
    |}.
  Next Obligation.
    epose proof (@ss'_gen_mon E F C D X Y). eapply H1.
    3: apply H0.
    all: auto.
  Qed.

End StrongSimAlt.

Definition ssim' {E F C D X Y} L :=
  (gfp (@ss' E F C D X Y L): hrel _ _).

Section ssim'_theory.
  Arguments label: clear implicits.
  Context {E F C D: Type -> Type} {X Y: Type}
          {L: rel (@label E) (@label F)}.

(*|
   Strong simulation up-to [equ] is valid
   ----------------------------------------
|*)
  #[global] Instance equ_ss'_gen_goal {R Reps} :
    Proper (equ eq ==> equ eq ==> flip impl) (@ss'_gen E F C D X Y L R Reps).
  Proof.
    split; [| split]; intros; subs; destruct H1 as (HA & HB & HC).
    - apply HA in H3; auto.
      destruct H3 as (? & ? & ? & ? & ?). eexists _, _. subs. etrans.
    - symmetry in H. eapply HB in H. destruct H as (? & ? & ?).
      eexists. subs. etrans.
    - symmetry in H. eapply HC in H. destruct H as (? & ? & ?).
      eexists. subs. etrans.
   Qed.

  #[global] Instance equ_ss'_gen_ctx {R Reps} :
    Proper (equ eq ==> equ eq ==> impl) (@ss'_gen E F C D X Y L R Reps).
  Proof.
    do 4 red. intros. now rewrite <- H, <- H0.
  Qed.

  Lemma equ_clos_sst' {c: Chain (ss' L)}:
    forall x y, @equ_clos E F C D X Y `c x y -> `c x y.
  Proof.
    apply tower.
    - intros ? INC x y [x' y' x'' y'' EQ' EQ''] ??. red.
      apply INC; auto.
      econstructor; eauto.
      apply leq_infx in H.
      now apply H.
    - intros R IH x y [x' y' x'' y'' EQ' EQ''].
      now subs.
  Qed.

  #[global] Instance equ_clos_sst_goal {c: Chain (@ss' E F C D X Y L)} :
    Proper (equ eq ==> equ eq ==> flip impl) `c.
  Proof.
    cbn; intros ? ? eq1 ? ? eq2 H.
    apply equ_clos_sst'; econstructor; [eauto | | symmetry; eauto]; assumption.
  Qed.

  #[global] Instance equ_clos_sst'_ctx  {c: Chain (@ss' E F C D X Y L)} :
    Proper (equ eq ==> equ eq ==> impl) `c.
  Proof.
    cbn; intros ? ? eq1 ? ? eq2 H.
    apply equ_clos_sst'; econstructor; [symmetry; eauto | | eauto]; assumption.
  Qed.

  #[global] Instance equ_clos_ssim'_goal : Proper (equ eq ==> equ eq ==> flip impl) (@ssim' E F C D X Y L).
  Proof.
    cbn; intros ? ? eq1 ? ? eq2 H.
    apply equ_clos_sst'; econstructor; eauto; now symmetry.
  Qed.

  #[global] Instance equ_clos_ssim'_ctx : Proper (equ eq ==> equ eq ==> impl) (@ssim' E F C D X Y L).
  Proof.
    cbn; intros ? ? eq1 ? ? eq2 H.
    now rewrite <- eq1, <- eq2.
  Qed.

  Lemma ss'_gen_br : forall {Z} (c : C Z) (k : Z -> ctree E C X) (u : ctree F D Y)
    (R Reps : rel _ _),
    ss'_gen L R Reps (Br c k) u ->
    forall x, exists u', epsilon u u' /\ Reps (k x) u'.
  Proof.
    intros. destruct H as (_ & H & _); eapply H; reflexivity.
  Qed.

  Lemma ss'_gen_guard : forall (t : ctree E C X) (u : ctree F D Y)
    (R Reps : rel _ _),
    ss'_gen L R Reps (Guard t) u ->
    exists u', epsilon u u' /\ Reps t u'.
  Proof.
    intros. destruct H as (_ & _ & H); eapply H; reflexivity.
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
  | |- context[@ssim' ?E ?F ?C ?D ?X ?Y ?LR] =>
      unfold ssim';
      step;
      fold (@ssim' E F C D X Y L)
  end.

Tactic Notation "step" := __step_ssim' || step.

Ltac __step_in_ssim' H :=
  match type of H with
  | context[@ssim' ?E ?F ?C ?D ?X ?Y ?LR] =>
      unfold ssim' in H;
      step in H;
      fold (@ssim' E F C D X Y L) in H
  end.

Tactic Notation "step" "in" ident(H) := __step_in_ssim' H || step in H.

Tactic Notation "__coinduction_ssim'" simple_intropattern(r) simple_intropattern(cih) :=
  first [unfold ssim' at 4 | unfold ssim' at 3 | unfold ssim' at 2 | unfold ssim' at 1]; coinduction r cih.
Tactic Notation "coinduction" simple_intropattern(r) simple_intropattern(cih) := __coinduction_ssim' r cih || coinduction r cih.

Import CTreeNotations.
Import EquNotations.
Section ssim'_homogenous_theory.
  Context {E B: Type -> Type} {X: Type}
          {L: relation (@label E)}.

  Notation ss' := (@ss' E E B B X X).
  Notation ssim' := (@ssim' E E B B X X).

  #[global] Instance Reflexive_ss' R Reps
    `{Reflexive _ R} `{Reflexive _ Reps} `{Reflexive _ L}:
    Reflexive (@ss'_gen E E B B X X L R Reps).
  Proof.
    split; [| split]; intros; eauto.
    exists (k x0). subs. split; auto. now eapply epsilon_br.
    exists t'; split; eauto.
    rewrite H2; now apply epsilon_guard.
  Qed.

  #[global] Instance refl_ss' {LR: Reflexive L} {C: Chain (ss' L)}: Reflexive `C.
  Proof.
    apply Reflexive_chain.
    split; [| split]; cbn; intros; eauto.
    - exists (k x0); split; auto.
      rewrite H0; eapply epsilon_br, epsilon_id; reflexivity.
    - exists t'; split; auto.
      rewrite H0; eapply epsilon_guard, epsilon_id; reflexivity.
  Qed.

End ssim'_homogenous_theory.

(*|
Parametric theory of [ss] with heterogenous [L]
|*)
Section ssim'_heterogenous_theory.
  Arguments label: clear implicits.
  Context {E F C D: Type -> Type} {X Y: Type}
          {L: rel (@label E) (@label F)}.

  Notation ss' := (@ss' E F C D X Y).
  Notation ssim'  := (@ssim' E F C D X Y).

(*|
  stuck ctrees can be simulated by anything.
|*)
  Lemma ss'_stuck R Reps :
    forall (u : ctree F D Y),
    ss'_gen (E := E) (C := C) (X := X) L R Reps Stuck u.
  Proof.
    split; [| split]; intros; inv_equ.
    inv_trans.
  Qed.

  Lemma ssim'_stuck (t : ctree F D Y) : ssim' L Stuck t.
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
  | h : @ssim' ?E ?F ?C ?D ?X ?Y ?L _ _ |- _ =>
      __play_ssim'_in h
  end.

#[local] Tactic Notation "play" := __play_ssim'.
#[local] Tactic Notation "play" "in" ident(H) := __play_ssim'_in H.
#[local] Tactic Notation "eplay" := __eplay_ssim'.

Section Proof_Rules.

  Arguments label: clear implicits.
  Context {E F C D : Type -> Type}
          {X Y : Type}
          {L : rel (@label E) (@label F)}
          {R Reps : rel (ctree E C X) (ctree F D Y)}
          {HR : (Proper (equ eq ==> equ eq ==> impl) R)}
          {HReps : (Proper (equ eq ==> equ eq ==> impl) Reps)}.

  Lemma step_ss'_stuck :
    ss'_gen L R Reps Stuck Stuck.
  Proof.
    ssplit; intros; inv_equ.
    exfalso; eapply productive_stuck; eauto.
  Qed.

  Lemma step_ss'_ret (x : X) (y : Y) :
    R Stuck Stuck ->
    L (val x) (val y) ->
    ss'_gen L R Reps (Ret x : ctree E C X) (Ret y : ctree F D Y).
  Proof.
    intros Rstuck Lval. split; [| split]; intros.
    2,3: inv_equ.
    inv_trans; subst.
    do 3 eexists; intuition; etrans. now subs.
  Qed.

  Lemma step_ss'_ret_l (x : X) (y : Y) (u u' : ctree F D Y) :
    R Stuck Stuck ->
    L (val x) (val y) ->
    trans (val y) u u' ->
    ss'_gen L R Reps (Ret x : ctree E C X) u.
  Proof.
    intros. cbn. intros.
    apply trans_val_inv in H1 as ?. subs.
    split; [| split]; intros; inv_equ.
    inv_trans. subst. rewrite <- EQ in H. etrans.
  Qed.

(*|
 The vis nodes are deterministic from the perspective of the labeled
 transition system, stepping is hence symmetric and we can just recover
 the itree-style rule.
|*)
  Lemma step_ss'_vis {Z Z'} (e : E Z) (f: F Z')
        (k : Z -> ctree E C X) (k' : Z' -> ctree F D Y) :
    (forall x, exists y, R (k x) (k' y) /\ L (obs e x) (obs f y)) ->
    ss'_gen L R Reps (Vis e k) (Vis f k').
  Proof.
    intros. split; [| split]; intros; inv_equ.
    cbn; inv_trans; subst;
      destruct (H x) as (x' & RR & LL);
      cbn; do 3 eexists; intuition.
    - rewrite EQ; eauto.
    - assumption.
  Qed.

  Lemma step_ss'_vis_id {Z} (e : E Z) (f: F Z)
        (k : Z -> ctree E C X) (k' : Z -> ctree F D Y) :
    (forall x, R (k x) (k' x) /\ L (obs e x) (obs f x)) ->
    ss'_gen L R Reps (Vis e k) (Vis f k').
  Proof.
    intros. apply step_ss'_vis.
    eauto.
  Qed.

  Lemma step_ss'_vis_l {Z} :
    forall (e : E Z) (k : Z -> ctree E C X) (u : ctree F D Y),
    (forall x, exists l' u', trans l' u u' /\ R (k x) u' /\ L (obs e x) l') ->
    ss'_gen L R Reps (Vis e k) u.
  Proof.
    intros. split; [| split]; intros; inv_equ.
    inv_trans. subst. destruct (H x) as (? & ? & ? & ? & ?).
    eexists _, _. rewrite <- EQ in H2. etrans.
  Qed.

(*|
    With this definition [ss'] of simulation, delayed nodes allow to perform a coinductive step.
|*)
  Lemma step_ss'_br_l {Z} (c : C Z)
        (k : Z -> ctree E C X) (t': ctree F D Y):
    (forall x, Reps (k x) t') ->
    ss'_gen L R Reps (Br c k) t'.
  Proof.
    ssplit; intros.
    now apply productive_br in H0.
    inv_equ. exists t'; split; eauto; rewrite <- EQ; auto.
    inv_equ.
  Qed.

  Lemma step_ss'_br_r {Z} (c : D Z) x
        (k : Z -> ctree F D Y) (t: ctree E C X):
    ss'_gen L R Reps t (k x) ->
    ss'_gen L R Reps t (Br c k).
  Proof.
    intros (HA & HB & HC); ssplit; intros.
    - apply HA in H0 as (? & ? & ? & ? & ?).
      exists x0, x1; etrans. auto.
    - eapply HB in H as (? & ? & ?). eapply epsilon_br in H. etrans.
    - eapply HC in H as (? & ? & ?).
      eexists; split; [| eauto].
      eapply epsilon_br, H.
  Qed.

  Lemma step_ss'_br {Z Z'} (a: C Z) (b: D Z')
    (k : Z -> ctree E C X) (k' : Z' -> ctree F D Y) :
    (forall x, exists y, Reps (k x) (k' y)) ->
    ss'_gen L R Reps (Br a k) (Br b k').
  Proof.
    ssplit; intros. { now apply productive_br in H0. }
    2: inv_equ.
    inv_equ.
    setoid_rewrite EQ in H. destruct (H x).
    eexists. split; [| eassumption].
    econstructor 2.
    econstructor.
    reflexivity.
  Qed.

  Lemma step_ss'_br_id {Z} (c: C Z) (d: D Z)
        (k : Z -> ctree E C X) (k' : Z -> ctree F D Y) :
    (forall x, Reps (k x) (k' x)) ->
    ss'_gen L R Reps (Br c k) (Br d k').
  Proof.
   intros. apply step_ss'_br; eauto.
  Qed.

  Lemma step_ss'_guard_l
        (t: ctree E C X) (t': ctree F D Y) :
    Reps t t' ->
    ss'_gen L R Reps (Guard t) t'.
  Proof.
    ssplit; intros.
    now apply productive_guard in H0.
    inv_equ.
    inv_equ.
    eexists t'; split.
    reflexivity.
    rewrite <- H0; auto.
  Qed.

  Lemma step_ss'_guard_r
    (t: ctree E C X) (t': ctree F D Y) :
    ss'_gen L R Reps t t' ->
    ss'_gen L R Reps t (Guard t').
  Proof.
    intros (HA & HB & HC); ssplit; intros.
    - apply HA in H0 as (? & ? & ? & ? & ?).
      do 2 eexists; etrans.
      auto.
    - eapply HB in H as (? & ? & ?).
      eexists; split; [| eauto].
      eapply epsilon_guard, H.
    - eapply HC in H as (? & ? & ?).
      eexists; split; [| eauto].
      eapply epsilon_guard, H.
  Qed.

  Lemma step_ss'_guard
        (t: ctree E C X) (t': ctree F D Y) :
    Reps t t' ->
    ss'_gen L R Reps (Guard t) (Guard t').
  Proof.
    ssplit; intros. { now apply productive_guard in H0. }
    inv_equ.
    inv_equ.
    setoid_rewrite H0 in H.
    eexists. split; [| eassumption].
    now econstructor 3.
  Qed.

  Lemma step_ss'_epsilon_r :
    forall (t : ctree E C X) (u u' : ctree F D Y),
      ss'_gen L R Reps t u' -> epsilon u u' -> ss'_gen L R Reps t u.
  Proof.
    intros. red in H0. rewrite (ctree_eta u). rewrite (ctree_eta u') in H.
    genobs u ou. genobs u' ou'. clear u Heqou u' Heqou'.
    revert t H. induction H0; intros.
    - now subs.
    - eapply step_ss'_br_r, IHepsilon_; eauto.
    - eapply step_ss'_guard_r, IHepsilon_; eauto.
  Qed.

  Lemma ss'_gen_epsilon_l :
    forall (t t' : ctree E C X) (u : ctree F D Y),
    Reps <= ss'_gen L R Reps ->
    ss'_gen L R Reps t u ->
    epsilon t t' ->
    ss'_gen L R Reps t' u.
  Proof.
    intros. red in H1. rewrite (ctree_eta t'). rewrite (ctree_eta t) in H0.
    genobs t ot. genobs t' ot'. clear t Heqot t' Heqot'.
    revert u H0. induction H1; intros.
    - now subs.
    - apply IHepsilon_. rewrite <- ctree_eta.
      eapply ss'_gen_br in H0 as (? & ? & ?).
      apply H in H2. eapply step_ss'_epsilon_r in H2; eauto.
    - apply IHepsilon_. rewrite <- ctree_eta.
      eapply ss'_gen_guard in H0 as (? & ? & ?).
      apply H in H2. eapply step_ss'_epsilon_r in H2; eauto.
   Qed.


  (*|
    Same goes for visible τ nodes.
    |*)
  Lemma step_ss'_step
        (t : ctree E C X) (t': ctree F D Y) :
    L τ τ ->
    R t t' ->
    ss'_gen L R Reps (Step t) (Step t').
  Proof.
    split; [| split]; intros; inv_equ.
    inv_trans; subst.
    cbn; do 3 eexists; intuition; subs; eauto.
  Qed.

  Lemma step_ss'_step_l :
    forall (t : ctree E C X) (u : ctree F D Y),
    (exists l' u', trans l' u u' /\ R t u' /\ L τ l') ->
    ss'_gen L R Reps (Step t) u.
  Proof.
    intros. ssplit; intros; inv_equ.
    inv_trans. subst. destruct H as (? & ? & ? & ? & ?).
    eexists _, _. rewrite <- EQ in H1. etrans.
  Qed.

(*|
    When matching visible brs one against another, in general we need to explain how
    we map the branches from the left to the branches to the right.
    A useful special case is the one where the arity coincide and we simply use the identity
    in both directions. We can in this case have [n] rather than [2n] obligations.
|*)

End Proof_Rules.

(* Specialized proof rules *)

Lemma ssim'_stuck' {E F C D X Y}
  (L : rel _ _) :
  ssim' L (Stuck : ctree E C X) (Stuck : ctree F D Y).
Proof.
  step. apply step_ss'_stuck.
Qed.

Lemma step_ssbt'_ret {E F C D X Y}
  (x : X) (y : Y) (L : rel _ _)
  {R : Chain (@ss' E F C D X Y L)} :
  L (val x) (val y) ->
  ss' L `R (Ret x : ctree E C X) (Ret y : ctree F D Y).
Proof.
  intros.
  unshelve eapply step_ss'_ret; eauto.
  apply (b_chain R). apply ss'_stuck.
Qed.

Lemma ssim'_ret {E F C D X Y}
  (x : X) (y : Y) (L : rel _ _) :
  L (val x) (val y) ->
  ssim' L (Ret x : ctree E C X) (Ret y : ctree F D Y).
Proof.
  now intros; step; apply step_ssbt'_ret.
Qed.

Lemma ssim'_step {E F C D X Y}
  (t : ctree E C X) (u : ctree F D Y) (L : rel _ _) :
  L τ τ  ->
  ssim' L t u ->
  ssim' L (Step t) (Step u).
Proof.
  now intros; step; apply step_ss'_step.
Qed.

Lemma ssim'_guard {E F C D X Y}
  (t : ctree E C X) (u : ctree F D Y) (L : rel _ _) :
  ssim' L t u ->
  ssim' L (Guard t) (Guard u).
Proof.
  now intros; step; apply step_ss'_guard.
Qed.

Lemma ssim'_br {E F C D X Y Z Z'} {L}
  (c: C Z) (d: D Z')
  (k : Z -> ctree E C X) (k' : Z' -> ctree F D Y) :
  (forall x, exists y, ssim' L (k x) (k' y)) ->
  ssim' L (Br c k) (Br d k').
Proof.
  now intros; step; apply step_ss'_br.
Qed.

Lemma ssim'_br_id {E F C D X Y Z} {L}
  (c: C Z) (d: D Z)
  (k : Z -> ctree E C X) (k' : Z -> ctree F D Y) :
  (forall x, ssim' L (k x) (k' x)) ->
  ssim' L (Br c k) (Br d k').
Proof.
  now intros; step; apply step_ss'_br_id.
Qed.

Lemma step_ssbt'_brS {E F C D X Y Z Z'} {L}
  {R : Chain (@ss' E F C D X Y L)}
  (c: C Z) (d: D Z')
  (k : Z -> ctree E C X) (k' : Z' -> ctree F D Y) :
  L τ τ  ->
  (forall x, exists y, `R (k x) (k' y)) ->
  ss' L `R (BrS c k) (BrS d k').
Proof.
  intros.
  apply step_ss'_br; auto.
  intros x; destruct (H0 x) as (y & ?); exists y.
  apply (b_chain R), step_ss'_step; auto.
Qed.

Lemma ssim'_brS {E F C D X Y Z Z'} {L}
  (c: C Z) (d: D Z')
  (k : Z -> ctree E C X) (k' : Z' -> ctree F D Y) :
  L τ τ  ->
  (forall x, exists y, ssim' L (k x) (k' y)) ->
  ssim' L (BrS c k) (BrS d k').
Proof.
  now intros; step; apply step_ssbt'_brS.
Qed.

Lemma step_ssbt'_brS_id {E F C D X Y Z} {L}
  {R : Chain (@ss' E F C D X Y L)}
  (c: C Z) (d: D Z)
  (k : Z -> ctree E C X) (k' : Z -> ctree F D Y) :
  L τ τ  ->
  (forall x, ` R (k x) (k' x)) ->
  ss' L `R (BrS c k) (BrS d k').
Proof.
  intros.
  apply step_ss'_br_id; auto.
  intros; apply (b_chain R), step_ss'_step; auto.
Qed.

Lemma ssim'_brS_id {E F C D X Y Z} {L}
  (c: C Z) (d: D Z)
  (k : Z -> ctree E C X) (k' : Z -> ctree F D Y) :
  L τ τ  ->
  (forall x, ssim' L (k x) (k' x)) ->
  ssim' L (BrS c k) (BrS d k').
Proof.
  now intros; step; apply step_ssbt'_brS_id.
Qed.

Lemma ssim'_vis
  {E F C D X Y Z Z'} {L}
  (e: E Z) (f: F Z')
  (k : Z -> ctree E C X) (k' : Z' -> ctree F D Y) :
  (forall x, exists y, ssim' L (k x) (k' y) /\ L (obs e x) (obs f y)) ->
  ssim' L (Vis e k) (Vis f k').
Proof.
  now intros; step; apply step_ss'_vis.
Qed.

Lemma ssim'_vis_id
  {E F C D X Y Z} {L}
  (e: E Z) (f: F Z)
  (k : Z -> ctree E C X) (k' : Z -> ctree F D Y) :
  (forall x, ssim' L (k x) (k' x) /\ L (obs e x) (obs f x)) ->
  ssim' L (Vis e k) (Vis f k').
Proof.
  now intros; step; apply step_ss'_vis_id.
Qed.

Lemma ssim'_vis_l
  {E F C D X Y Z} {L}
  (e: E Z)
  (k : Z -> ctree E C X) (u : ctree F D Y) :
  (forall x, exists l' u', trans l' u u' /\ ssim' L (k x) u' /\ L (obs e x) l') ->
  ssim' L (Vis e k) u.
Proof.
  now intros; step; apply step_ss'_vis_l.
Qed.

Lemma ssim'_epsilon_l {E F C D X Y} {L} :
  forall (t t' : ctree E C X) (u : ctree F D Y),
  ssim' L t u ->
  epsilon t t' ->
  ssim' L t' u.
Proof.
  intros. step. eapply ss'_gen_epsilon_l.
  - apply (gfp_pfp (ss' L)).
  - step in H. apply H.
  - apply H0.
Qed.

Section Inversion_Rules.

  Context {E F C D : Type -> Type}
          {X Y : Type}
          {L : rel (@label E) (@label F)}
          {R Reps : rel (ctree E C X) (ctree F D Y)}.

  Lemma ss'_vis_l_inv {Z} :
    forall (e : E Z) (k : Z -> ctree E C X) (u : ctree F D Y) x,
    ss'_gen L R Reps (Vis e k) u ->
    exists l' u', trans l' u u' /\ R (k x) u' /\ L (obs e x) l'.
  Proof.
    intros. apply H; etrans.
  Qed.

  Lemma ss'_step_l_inv :
    forall (t : ctree E C X) (u : ctree F D Y),
    ss'_gen L R Reps (Step t) u ->
    exists l' u', trans l' u u' /\ R t u' /\ L τ l'.
  Proof.
    intros * (HA & HB & HC).
    apply HA; etrans.
  Qed.

End Inversion_Rules.

Definition epsilon_ctx {E C X} (R : ctree E C X -> Prop)
  (t : ctree E C X) :=
  exists t', epsilon t t' /\ R t'.

Definition epsilon_det_ctx {E C X} (R : ctree E C X -> Prop)
  (t : ctree E C X) :=
  exists t', epsilon_det t t' /\ R t'.

Section upto.

  Context {E F C D: Type -> Type} {X Y: Type}
          (L : hrel (@label E) (@label F)).

  (* Up-to epsilon *)

  Program Definition epsilon_ctx_r : mon (rel (ctree E C X) (ctree F D Y))
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

Arguments ss_sst' {E F C D X Y} L.

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
    forall (t : ctree E C X) (t' : ctree F D Y) (k : X -> ctree E C X') (k' : Y -> ctree F D Y'),
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
      (t1 : ctree E C X) (t2: ctree F D Y)
      (k1 : X -> ctree E C X') (k2 : Y -> ctree F D Y'):
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
  forall (t : ctree E C X) (t' : ctree F D Y) (k : X -> ctree E C X') (k' : Y -> ctree F D Y'),
    t (≲update_val_rel L R0) t' ->
    (forall x x', R0 x x' -> elem R (k x) (k' x')) ->
    ` R (bind t k) (bind t' k').
Proof.
  intros.
  eapply bind_chain_gen; eauto using update_val_rel_correct.
Qed.

Lemma ssim'_clo_bind {E F C D: Type -> Type} {X Y X' Y': Type} {L : rel (@label E) (@label F)}
      (R0 : rel X Y)
      (t1 : ctree E C X) (t2: ctree F D Y)
      (k1 : X -> ctree E C X') (k2 : Y -> ctree F D Y'):
  t1 (≲update_val_rel L R0) t2 ->
  (forall x y, R0 x y -> ssim' L (k1 x) (k2 y)) ->
  ssim' L (t1 >>= k1) (t2 >>= k2).
Proof.
  intros. eapply ss'_clo_bind; eauto.
Qed.

Lemma ss'_clo_bind_eq {E C D: Type -> Type} {X X': Type}
  {R : Chain (@ss' E E C D X' X' eq)} :
  forall (t : ctree E C X) (t' : ctree E D X) (k : X -> ctree E C X') (k' : X -> ctree E D X'),
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
      (t1 : ctree E C X) (t2: ctree E D X)
      (k1 : X -> ctree E C X') (k2 : X -> ctree E D X'):
  t1 ≲ t2 ->
  (forall x, ssim' eq (k1 x) (k2 x)) ->
  ssim' eq (t1 >>= k1) (t2 >>= k2).
Proof.
  apply ss'_clo_bind_eq.
Qed.

Lemma ss_ss'_chain {E F C D X Y L} {R : Chain (ss' L)} :
  forall (t : ctree E C X) (u : ctree F D Y),
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
Theorem ssim_ssim' {E F C D X Y} :
  forall L (t : ctree E C X) (t' : ctree F D Y), ssim L t t' <-> ssim' L t t'.
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
