From Coq Require Import
     Lia
     Basics
     Fin
     RelationClasses
     Program.Equality
     Logic.Eqdep.

From Coinduction Require Import
     coinduction rel tactics.

From ITree Require Import Core.Subevent.

From CTree Require Import
     CTree
     Utils
     Eq
     Eq.Epsilon.

From RelationAlgebra Require Export
     rel srel.

Import CTree.
Set Implicit Arguments.

(* TODO: Decide where to set this *)
Arguments trans : simpl never.

Section StrongSimAlt.
  Definition ss'_gen {E F C D : Type -> Type} {X Y : Type}
    `{HasStuck : B0 -< C} `{HasStuck' : B0 -< D}
    (L : rel (@label E) (@label F))
    (R Reps : rel (ctree E C X) (ctree F D Y))
    (t : ctree E C X) (u : ctree F D Y) :=
    (productive t -> forall l t', trans l t t' -> exists l' u', trans l' u u' /\ R t' u' /\ L l l') /\
    (forall {Z} (c : C Z) k, t ≅ BrD c k -> forall x, exists u', epsilon u u' /\ Reps (k x) u').

  #[global] Instance weq_ss'_gen {E F C D X Y} `{HasB0: B0 -< C} `{HasB0': B0 -< D} :
    Proper (weq ==> weq) (@ss'_gen E F C D X Y _ _).
  Proof.
    cbn. intros. split; split; intros.
    - apply H0 in H2 as (? & ? & ? & ? & ?); auto. edestruct H. eauto 6 with trans.
    - intros. eapply H0 in H1 as (? & ? & ?). etrans.
    - apply H0 in H2 as (? & ? & ? & ? & ?); auto. edestruct H. eauto 6 with trans.
    - intros. eapply H0 in H1 as (? & ? & ?). etrans.
  Qed.

  #[global] Instance ss'_gen_mon {E F C D : Type -> Type} {X Y : Type}
    `{HasStuck : B0 -< C} `{HasStuck' : B0 -< D}
    (L : rel (@label E) (@label F)) :
    Proper (leq ==> leq ==> leq) (@ss'_gen E F C D X Y _ _ L).
  Proof.
    cbn. intros.
    split.
    - intros.
      edestruct (proj1 H1) as (? & ? & ? & ?); eauto.
      eexists _, x2; intuition; eauto.
    - intros. edestruct (proj2 H1) as (? & ? & ?); eauto.
  Qed.

(*|
An alternative definition [ss'] of strong simulation.
The simulation challenge does not involve an inductive transition relation,
thus simplifying proofs.
|*)
  Program Definition ss' {E F C D : Type -> Type} {X Y : Type}
    `{HasStuck : B0 -< C} `{HasStuck' : B0 -< D}
    (L : rel (@label E) (@label F)) :
    mon (ctree E C X -> ctree F D Y -> Prop) :=
    {| body R t u :=
      ss'_gen L R R t u
    |}.
  Next Obligation.
    epose proof (@ss'_gen_mon E F C D X Y _ _). eapply H1.
    3: apply H0.
    all: auto.
  Qed.

End StrongSimAlt.

Definition ssim' {E F C D X Y} `{HasStuck : B0 -< C} `{HasStuck' : B0 -< D} L :=
  (gfp (@ss' E F C D X Y _ _ L): hrel _ _).

Section ssim'_theory.
  Arguments label: clear implicits.
  Context {E F C D: Type -> Type} {X Y: Type}
          {L: rel (@label E) (@label F)}
          {HasStuck1: B0 -< C} {HasStuck2: B0 -< D}.

(*|
   Strong simulation up-to [equ] is valid
   ----------------------------------------
|*)
  #[global] Instance equ_ss'_gen_goal {R Reps} :
    Proper (equ eq ==> equ eq ==> flip impl) (@ss'_gen E F C D X Y _ _ L R Reps).
  Proof.
    split; intros; subs.
    - destruct H1 as [? _]. apply H in H3; auto.
      destruct H3 as (? & ? & ? & ? & ?). eexists _, _. subs. etrans.
    - destruct H1 as [_ ?]. symmetry in H. eapply H1 in H. destruct H as (? & ? & ?).
      eexists. subs. etrans.
  Qed.

  #[global] Instance equ_ss'_gen_ctx {R Reps} :
    Proper (equ eq ==> equ eq ==> impl) (@ss'_gen E F C D X Y _ _ L R Reps).
  Proof.
    do 4 red. intros. now rewrite <- H, <- H0.
  Qed.

  Lemma equ_clos_sst' : equ_clos <= (t (@ss' E F C D X Y _ _ L)).
  Proof.
    apply leq_t; cbn.
    intros R x y [x' y' x'' y'' EQ' EQ''].
    subs. eapply ss'_gen_mon. 3: apply EQ''.
    all: econstructor; eauto.
  Qed.

  #[global] Instance equ_clos_ssim'_goal : Proper (equ eq ==> equ eq ==> flip impl) (@ssim' E F C D X Y _ _ L).
  Proof.
    cbn; intros ? ? eq1 ? ? eq2 H.
    apply (ft_t equ_clos_sst'); econstructor; [eauto | | symmetry; eauto]; assumption.
  Qed.

  #[global] Instance equ_clos_ssim'_ctx : Proper (equ eq ==> equ eq ==> impl) (@ssim' E F C D X Y _ _ L).
  Proof.
    cbn; intros ? ? eq1 ? ? eq2 H.
    now rewrite <- eq1, <- eq2.
  Qed.

  Lemma ss'_gen_brD : forall {Z} (c : C Z) (k : Z -> ctree E C X) (u : ctree F D Y)
    (R Reps : rel _ _),
    ss'_gen L R Reps (BrD c k) u ->
    forall x, exists u', epsilon u u' /\ Reps (k x) u'.
  Proof.
    intros. eapply H. reflexivity.
  Qed.

End ssim'_theory.

Module SSim'Notations.

  (*| ss (simulation) notation |*)
  Notation sst' L := (t (ss' L)).
  Notation ssbt' L := (bt (ss' L)).
  Notation ssT' L := (T (ss' L)).
  Notation ssbT' L := (bT (ss' L)).

End SSim'Notations.

Import SSim'Notations.

Ltac fold_ssim' :=
  repeat
    match goal with
    | h: context[gfp (@ss' ?E ?F ?C ?D ?X ?Y _ _ ?L)] |- _ => fold (@ssim' E F C D X Y _ _ L) in h
    | |- context[gfp (@ss' ?E ?F ?C ?D ?X ?Y _ _ ?L)]      => fold (@ssim' E F C D X Y _ _ L)
    end.

Ltac __coinduction_ssim' R H :=
  (try unfold ssim');
  apply_coinduction; fold_ssim'; intros R H.

Tactic Notation "__step_ssim'" :=
  match goal with
  | |- context[@ssim' ?E ?F ?C ?D ?X ?Y _ _ ?LR] =>
      unfold ssim';
      step;
      fold (@ssim' E F C D X Y _ _ L)
  end.

#[local] Tactic Notation "step" := __step_ssim' || step.

#[local] Tactic Notation "coinduction" simple_intropattern(R) simple_intropattern(H) :=
  __coinduction_ssim' R H || coinduction R H.

Ltac __step_in_ssim' H :=
  match type of H with
  | context[@ssim' ?E ?F ?C ?D ?X ?Y _ _ ?LR] =>
      unfold ssim' in H;
      step in H;
      fold (@ssim' E F C D X Y _ _ L) in H
  end.

#[local] Tactic Notation "step" "in" ident(H) := __step_in_ssim' H || step in H.

Import CTreeNotations.
Import EquNotations.
Section ssim'_homogenous_theory.
  Context {E C: Type -> Type} {X: Type}
          {L: relation (@label E)}
          {HasStuck1: B0 -< C}.

  Notation ss' := (@ss' E E C C X X _ _).
  Notation ssim' := (@ssim' E E C C X X _ _).
  Notation sst' L := (coinduction.t (ss' L)).
  Notation ssbt' L := (coinduction.bt (ss' L)).
  Notation ssT' L := (coinduction.T (ss' L)).

  (*|
    Various results on reflexivity and transitivity.
  |*)
  #[global] Instance Reflexive_ss' R Reps
    `{Reflexive _ R} `{Reflexive _ Reps} `{Reflexive _ L}:
    Reflexive (@ss'_gen E E C C X X _ _ L R Reps).
  Proof.
    split; intros; eauto.
    exists (k x0). subs. split; auto. now eapply epsilon_br.
  Qed.

  Lemma refl_sst' `{Reflexive _ L}: const seq <= (sst' L).
  Proof.
    apply leq_t. cbn.
    intros. unfold seq in H0. subst. reflexivity.
  Qed.

  (*| Reflexivity |*)
  #[global] Instance Reflexive_sst' R `{Reflexive _ L}: Reflexive (sst' L R).
  Proof. apply build_reflexive; apply ft_t; apply (refl_sst'). Qed.

  Corollary Reflexive_ssim' `{Reflexive _ L}: Reflexive (ssim' L).
  Proof. now apply Reflexive_sst'. Qed.

  #[global] Instance Reflexive_ssbt' R `{Reflexive _ L}: Reflexive (ssbt' L R).
  Proof. apply build_reflexive; apply fbt_bt; apply refl_sst'. Qed.

  #[global] Instance Reflexive_ssT' f R `{Reflexive _ L}: Reflexive (ssT' L f R).
  Proof. apply build_reflexive; apply fT_T; apply refl_sst'. Qed.

End ssim'_homogenous_theory.

(*|
Parametric theory of [ss] with heterogenous [L]
|*)
Section ssim'_heterogenous_theory.
  Arguments label: clear implicits.
  Context {E F C D: Type -> Type} {X Y: Type}
          {L: rel (@label E) (@label F)}
          {HasStuck1: B0 -< C} {HasStuck2: B0 -< D}.

  Notation ss' := (@ss' E F C D X Y _ _).
  Notation ssim'  := (@ssim' E F C D X Y _ _).
  Notation sst' L := (coinduction.t (ss' L)).
  Notation ssbt' L := (coinduction.bt (ss' L)).
  Notation ssT' L := (coinduction.T (ss' L)).

  #[global] Instance equ_clos_sst'_goal {RR} :
    Proper (equ eq ==> equ eq ==> flip impl) (sst' L RR).
  Proof.
    cbn; intros ? ? eq1 ? ? eq2 H.
    apply (ft_t equ_clos_sst'); econstructor; [eauto | | symmetry; eauto]; assumption.
  Qed.

  #[global] Instance equ_clos_sst'_ctx {RR} :
    Proper (equ eq ==> equ eq ==> impl) (sst' L RR).
  Proof.
    cbn; intros ? ? eq1 ? ? eq2 H.
    apply (ft_t equ_clos_sst'); econstructor; [symmetry; eauto | | eauto]; assumption.
  Qed.

  #[global] Instance equ_ssbt'_closed_goal {r} :
    Proper (equ eq ==> equ eq ==> flip impl) (ssbt' L r).
  Proof.
    cbn. intros.
    apply (fbt_bt equ_clos_sst'); econstructor; eauto.
    now symmetry.
  Qed.

  #[global] Instance equ_ssbt'_closed_ctx {r} :
    Proper (equ eq ==> equ eq ==> impl) (ssbt' L r).
  Proof.
    cbn; intros.
    now rewrite H, H0 in H1.
  Qed.

  #[global] Instance equ_clos_ssT'_goal RR f :
    Proper (equ eq ==> equ eq ==> flip impl) (ssT' L f RR).
  Proof.
    cbn; intros ? ? eq1 ? ? eq2 H.
    apply (fT_T equ_clos_sst'); econstructor; [eauto | | symmetry; eauto]; assumption.
  Qed.

  #[global] Instance equ_clos_ssT'_ctx RR f :
    Proper (equ eq ==> equ eq ==> impl) (ssT' L f RR).
  Proof.
    cbn; intros ? ? eq1 ? ? eq2 H.
    apply (fT_T equ_clos_sst'); econstructor; [symmetry; eauto | | eauto]; assumption.
  Qed.

(*|
  stuck ctrees can be simulated by anything.
|*)
  Lemma ss'_stuck R Reps :
    forall b (u : ctree F D Y) k,
    ss'_gen L R Reps (go (@BrF E C X _ b void (subevent _ branch0) k)) u.
  Proof.
    split; intros.
    - destruct b; inv_trans; destruct x.
    - destruct b; inv_equ. destruct x.
  Qed.

  Lemma ssim'_stuck (t : ctree F D Y) : ssim' L stuckD t.
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
  | h : @ssim' ?E ?F ?C ?D ?X ?Y _ _ ?L _ _ |- _ =>
      __play_ssim'_in h
  end.

#[local] Tactic Notation "play" := __play_ssim'.
#[local] Tactic Notation "play" "in" ident(H) := __play_ssim'_in H.
#[local] Tactic Notation "eplay" := __eplay_ssim'.

Section Proof_Rules.

  Arguments label: clear implicits.
  Context {E F C D : Type -> Type}
          {X Y : Type}
          {HasStuck: B0 -< C}
          {HasStuck': B0 -< D}
          {L : rel (@label E) (@label F)}
          {R Reps : rel (ctree E C X) (ctree F D Y)}
          {HR : (Proper (equ eq ==> equ eq ==> impl) R)}
          {HReps : (Proper (equ eq ==> equ eq ==> impl) Reps)}.

  Lemma step_ss'_ret (x : X) (y : Y) :
    R stuckD stuckD ->
    L (val x) (val y) ->
    ss'_gen L R Reps (Ret x : ctree E C X) (Ret y : ctree F D Y).
  Proof.
    intros Rstuck Lval. split; intros.
    2: inv_equ.
    inv_trans; subst.
    do 3 eexists; intuition; etrans. now subs.
  Qed.

  Lemma step_ss'_ret_l (x : X) (y : Y) (u u' : ctree F D Y) :
    R stuckD stuckD ->
    L (val x) (val y) ->
    trans (val y) u u' ->
    ss'_gen L R Reps (Ret x : ctree E C X) u.
  Proof.
    intros. cbn. intros.
    apply trans_val_inv in H1 as ?. subs.
    split; intros.
    - inv_trans. subst. rewrite <- EQ in H. etrans.
    - inv_equ.
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
    intros. split; intros; inv_equ.
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
    intros. split; intros; [| inv_equ].
    inv_trans. subst. destruct (H x) as (? & ? & ? & ? & ?).
    eexists _, _. rewrite <- EQ in H2. etrans.
  Qed.

  (*|
    Same goes for visible tau nodes.
    |*)
  Lemma step_ss'_step `{HasTau: B1 -< C} `{HasTau': B1 -< D}
        (t : ctree E C X) (t': ctree F D Y) :
    L tau tau ->
    R t t' ->
    ss'_gen L R Reps (Step t) (Step t').
  Proof.
    split; intros; inv_equ.
    inv_trans; subst.
    cbn; do 3 eexists; intuition; subs; eauto.
  Qed.

  (*|
    When matching visible brs one against another, in general we need to explain how
    we map the branches from the left to the branches to the right.
    A useful special case is the one where the arity coincide and we simply use the identity
    in both directions. We can in this case have [n] rather than [2n] obligations.
    |*)
  Lemma step_ss'_brS {Z Z'} (c : C Z) (d : D Z')
        (k : Z -> ctree E C X) (k' : Z' -> ctree F D Y) :
    (forall x, exists y, R (k x) (k' y)) ->
    L tau tau ->
    ss'_gen L R Reps (BrS c k) (BrS d k').
  Proof.
    split; intros; inv_equ. inv_trans. subst.
    destruct (H x).
    cbn; do 3 eexists; intuition; subs; eauto.
  Qed.

  Lemma step_ss'_brS_id {Z} (c : C Z) (d: D Z)
        (k: Z -> ctree E C X) (k': Z -> ctree F D Y) :
    (forall x, R (k x) (k' x)) ->
    L tau tau ->
    ss'_gen L R Reps (BrS c k) (BrS d k').
  Proof.
    intros; apply step_ss'_brS; eauto.
  Qed.

  Lemma step_ss'_brS_l {Z} :
    forall (c : C Z) (k : Z -> ctree E C X) (u : ctree F D Y),
    (forall x, exists l' u', trans l' u u' /\ R (k x) u' /\ L tau l') ->
    ss'_gen L R Reps (BrS c k) u.
  Proof.
    intros. split; intros; [| inv_equ].
    inv_trans. subst. destruct (H x) as (? & ? & ? & ? & ?).
    eexists _, _. rewrite <- EQ in H2. etrans.
  Qed.

  (*|
    With this definition [ss'] of simulation, delayed nodes allow to perform a coinductive step.
    |*)
  Lemma step_ss'_brD_l {Z} (c : C Z)
        (k : Z -> ctree E C X) (t': ctree F D Y):
    (forall x, Reps (k x) t') ->
    ss'_gen L R Reps (BrD c k) t'.
  Proof.
    split; intros. { now apply productive_brD in H0. }
    inv_equ. setoid_rewrite EQ in H. eauto.
  Qed.

  Lemma step_ss'_brD_r {Z} (c : D Z) x
        (k : Z -> ctree F D Y) (t: ctree E C X):
    ss'_gen L R Reps t (k x) ->
    ss'_gen L R Reps t (BrD c k).
  Proof.
    cbn. split; intros.
    apply H in H1 as (? & ? & ? & ? & ?).
    exists x0, x1; etrans. auto.
    eapply (proj2 H) in H0 as (? & ? & ?). eapply EpsilonBr in H0. etrans.
  Qed.

  Lemma step_ss'_epsilon_r :
    forall (t : ctree E C X) (u u' : ctree F D Y),
    ss'_gen L R Reps t u' -> epsilon u u' -> ss'_gen L R Reps t u.
  Proof.
    intros. red in H0. rewrite (ctree_eta u). rewrite (ctree_eta u') in H.
    genobs u ou. genobs u' ou'. clear u Heqou u' Heqou'.
    revert t H. induction H0; intros.
    - now subs.
    - apply IHepsilon_ in H. rewrite <- ctree_eta in H.
      eapply step_ss'_brD_r. apply H.
  Qed.

  Lemma step_ss'_brD {Z Z'} (a: C Z) (b: D Z')
    (k : Z -> ctree E C X) (k' : Z' -> ctree F D Y) :
    (forall x, exists y, Reps (k x) (k' y)) ->
    ss'_gen L R Reps (BrD a k) (BrD b k').
  Proof.
    split; intros. { now apply productive_brD in H0. }
    inv_equ. setoid_rewrite EQ in H. destruct (H x).
    eexists. split; [| eassumption]. eright. eleft. reflexivity.
  Qed.

  Lemma step_ss'_brD_id {Z} (c: C Z) (d: D Z)
        (k : Z -> ctree E C X) (k' : Z -> ctree F D Y) :
    (forall x, Reps (k x) (k' x)) ->
    ss'_gen L R Reps (BrD c k) (BrD d k').
  Proof.
   intros. apply step_ss'_brD; eauto.
  Qed.

  Lemma step_ss'_guard_l `{HasTau: B1 -< C}
        (t: ctree E C X) (t': ctree F D Y) :
    Reps t t' ->
    ss'_gen L R Reps (Guard t) t'.
  Proof.
    intros. apply step_ss'_brD_l; auto.
  Qed.

  Lemma step_ss'_guard `{HasTau: B1 -< C} `{HasTau': B1 -< D}
        (t: ctree E C X) (t': ctree F D Y) :
    Reps t t' ->
    ss'_gen L R Reps (Guard t) (Guard t').
  Proof.
    intros. apply step_ss'_brD_id; auto.
  Qed.

  Lemma step_ss'_guard_r `{HasB1: B1 -< D} :
    forall t u,
    ss'_gen L R Reps t u ->
    ss'_gen L R Reps t (Guard u).
  Proof.
    intros. eapply step_ss'_epsilon_r.
    - apply H.
    - apply epsilon_br; auto.
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
      eapply ss'_gen_brD in H0 as (? & ? & ?).
      apply H in H2. eapply step_ss'_epsilon_r in H2; eauto.
  Qed.

End Proof_Rules.

(* Specialized proof rules *)

Lemma step_ssbt'_ret {E F C D X Y} `{HasB0: B0 -< C} `{HasB0': B0 -< D}
  (x : X) (y : Y) (L R : rel _ _) :
  L (val x) (val y) ->
  ssbt' L R (Ret x : ctree E C X) (Ret y : ctree F D Y).
Proof.
  intros.
  apply step_ss'_ret.
  - step. intros. red. red. cbn.
    apply ss'_stuck.
  - apply H.
Qed.

Lemma step_ssbt'_br {E F C D X Y Z Z'} `{HasB0: B0 -< C} `{HasB0': B0 -< D} {L R}
  (vis : bool) (c: C Z) (d: D Z')
  (k : Z -> ctree E C X) (k' : Z' -> ctree F D Y) :
  (forall x, exists y, sst' L R (k x) (k' y)) ->
  L tau tau ->
  ssbt' L R (Br vis c k) (Br vis d k').
Proof.
  intros.
  destruct vis; [apply step_ss'_brS | apply step_ss'_brD];
    eauto; typeclasses eauto.
Qed.

Lemma step_ssbt'_br_id {E F C D X Y Z} `{HasB0: B0 -< C} `{HasB0': B0 -< D} {L R}
  (vis : bool) (c: C Z) (d: D Z)
  (k : Z -> ctree E C X) (k': Z -> ctree F D Y) :
  (forall x, sst' L R (k x) (k' x)) ->
  L tau tau ->
  ssbt' L R (Br vis c k) (Br vis d k').
Proof.
  intros. apply step_ssbt'_br; eauto.
Qed.

Lemma ssim'_epsilon_l {E F C D X Y} `{HasB0: B0 -< C} `{HasB0': B0 -< D} {L} :
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
          {HasStuck: B0 -< C}
          {HasStuck': B0 -< D}
          {L : rel (@label E) (@label F)}
          {R Reps : rel (ctree E C X) (ctree F D Y)}.

  Lemma ss'_vis_l_inv {Z} :
    forall (e : E Z) (k : Z -> ctree E C X) (u : ctree F D Y) x,
    ss'_gen L R Reps (Vis e k) u ->
    exists l' u', trans l' u u' /\ R (k x) u' /\ L (obs e x) l'.
  Proof.
    intros. apply H; etrans.
  Qed.

  Lemma ss'_brS_l_inv {Z} :
    forall (c : C Z) (k : Z -> ctree E C X) (u : ctree F D Y) x,
    ss'_gen L R Reps (BrS c k) u ->
    exists l' u', trans l' u u' /\ R (k x) u' /\ L tau l'.
  Proof.
    intros. apply H; etrans.
  Qed.

End Inversion_Rules.

Definition epsilon_ctx {E C X} `{HasB1: B1 -< C} (R : ctree E C X -> Prop)
  (t : ctree E C X) :=
  exists t', epsilon t t' /\ R t'.

Definition epsilon_det_ctx {E C X} `{HasB1: B1 -< C} (R : ctree E C X -> Prop)
  (t : ctree E C X) :=
  exists t', epsilon_det t t' /\ R t'.

Section upto.

  Context {E F C D: Type -> Type} {X Y: Type}
          `{HasB0 : B0 -< C} `{HasB0' : B0 -< D}
          `{HasB1 : B1 -< C} `{HasB1' : B1 -< D}
          (L : hrel (@label E) (@label F)).

  (* Up-to epsilon *)

  Program Definition epsilon_ctx_r : mon (rel (ctree E C X) (ctree F D Y))
    := {| body R t u := epsilon_ctx (fun u => R t u) u |}.
  Next Obligation.
    destruct H0 as (? & ? & ?). red. eauto.
  Qed.

  Lemma epsilon_ctx_r_ssim' :
      epsilon_ctx_r <= t (@ss' E F C D X Y _ _ L).
  Proof.
    apply Coinduction. cbn -[ss']. intros.
    destruct H as (? & ? & ?).
    eapply step_ss'_epsilon_r in H0.
    eapply (Hbody (ss' L)). 2: apply H0; auto. 2: auto.
    intros ???. apply (id_T (ss' L)). apply H1.
  Qed.

  (* Up-to ss. *)
  (* This principle holds because an ss step always corresponds
     to one or more ss' steps. *)
  Lemma ss_sst' : @ss E F C D X Y _ _ L <= t (ss' L).
  Proof.
    intro. apply Coinduction. cbn. intros. split; intros.
    - apply H in H1 as (? & ? & ? & ? & ?).
      exists x, x0. split; auto. split; auto.
      intros. apply (b_T (ss' L)). apply H2.
    - exists a2. split; auto.
      apply (fTf_Tf (ss' L)). cbn. intros.
      eapply trans_brD in H1; auto. rewrite <- H0 in H1.
      apply H in H1 as (? & ? & ? & ? & ?).
      exists x0, x1. split; auto. split; auto.
      apply (b_T (ss' L)). apply H2.
  Qed.

End upto.

Arguments ss_sst' {E F C D X Y HasB0 HasB0'} L.

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
          `{HasStuck : B0 -< C} `{HasStuck' : B0 -< D}
          (L : hrel (@label E) (@label F)) (R0 : rel X Y).

(*|
    The resulting enhancing function gives a valid up-to technique
|*)
  Lemma bind_ctx_ssim'_t L0 (*{RV: Respects_val L}*):
    is_update_val_rel L R0 L0 -> @bind_ctx_ssim E F C D X X' Y Y' _ _ R0 L0 <= (t (ss' L)).
  Proof.
    intro HL0. apply Coinduction.
    intros R. apply (leq_bind_ctx _).
    intros t1 t2 tt k1 k2 kk.
    step in tt. split.
    - simpl; intros PROD l u STEP.
      apply trans_bind_inv in STEP as [(H & t' & STEP & EQ) | (v & STEPres & STEP)].
      apply tt in STEP as (l' & u' & STEP & EQ' & ?).
      do 2 eexists. split; [| split].
      apply trans_bind_l; eauto.
      + intro Hl. destruct Hl.
        apply HL0 in H0; etrans.
        inversion H0; subst. apply H. constructor. apply H2. constructor.
      + apply (fT_T equ_clos_sst').
        econstructor; [exact EQ | | reflexivity].
        apply (fTf_Tf (ss' L)).
        apply in_bind_ctx; [apply EQ' |].
        intros ? ? ?.
        apply (b_T (ss' L)).
        red in kk; cbn; apply kk. eassumption.
      + apply HL0 in H0; etrans.
        destruct H0. exfalso. apply H. constructor. apply H2.
      + assert (t1 ≅ Ret v).
        { apply productive_bind in PROD. apply trans_val_epsilon in STEPres as [? _].
          now apply productive_epsilon. } subs.
        apply tt in STEPres as (l' & u' & STEPres & EQ' & ?).
        apply HL0 in H; etrans.
        dependent destruction H. 2: { exfalso. apply H. constructor. }
        pose proof (trans_val_inv STEPres) as EQ.
        rewrite EQ in STEPres.
        specialize (kk v v2 H).
        rewrite bind_ret_l in PROD.
        apply kk in STEP as (? & u''' & STEP & EQ'' & ?); auto.
        do 2 eexists; split.
        eapply trans_bind_r; eauto.
        split; auto.
        eapply (id_T (ss' L)); auto.
    - intros Z c k EQ z.
      apply br_equ_bind in EQ as EQ'. destruct EQ' as [(v & EQ') | (k0 & EQ' & EQ'')].
      + subs.
        edestruct tt as (l & t'' & STEPres & _ & ?). etrans.
        apply HL0 in H; etrans.
        apply update_val_rel_val_l in H as (v' & -> & EQ').
        rewrite bind_ret_l in EQ.
        specialize (kk v v' EQ'). apply kk with (x := z) in EQ. destruct EQ as (u' & EPS & EQ).
        exists u'.
        apply trans_val_epsilon in STEPres as [? _]. split.
        * eapply epsilon_bind; eassumption.
        * now apply (id_T (ss' L)).
      + subs. eexists. split; [now left |].
        rewrite EQ''.
        apply (fTf_Tf (ss' L)). apply in_bind_ctx.
        eapply ssim_brD_l_inv. step. apply tt.
        red. intros. apply (b_T (ss' L)). now apply kk.
  Qed.

End bind.

(*|
Expliciting the reasoning rule provided by the up-to principles.
|*)
Lemma sst'_clo_bind_gen {E F C D: Type -> Type} {X Y X' Y': Type} {L : rel (@label E) (@label F)}
      `{HasStuck: B0 -< C} `{HasStuck': B0 -< D}
      (R0 : rel X Y) L0
      (HL0 : is_update_val_rel L R0 L0)
      (t1 : ctree E C X) (t2: ctree F D Y)
      (k1 : X -> ctree E C X') (k2 : Y -> ctree F D Y') RR:
  ssim L0 t1 t2 ->
  (forall x y, R0 x y -> (sst' L RR) (k1 x) (k2 y)) ->
  sst' L RR (t1 >>= k1) (t2 >>= k2).
Proof.
  intros ? ?.
  apply (ft_t (@bind_ctx_ssim'_t E F C D X X' Y Y' _ _ L R0 L0 HL0)).
  apply in_bind_ctx; eauto.
Qed.

Lemma sst'_clo_bind {E F C D: Type -> Type} {X Y X' Y': Type} {L : rel (@label E) (@label F)}
      `{HasStuck: B0 -< C} `{HasStuck': B0 -< D}
      (R0 : rel X Y)
      (t1 : ctree E C X) (t2: ctree F D Y)
      (k1 : X -> ctree E C X') (k2 : Y -> ctree F D Y') RR:
  t1 (≲update_val_rel L R0) t2 ->
  (forall x y, R0 x y -> (sst' L RR) (k1 x) (k2 y)) ->
  sst' L RR (t1 >>= k1) (t2 >>= k2).
Proof.
  intros ? ?.
  eapply sst'_clo_bind_gen; eauto. apply update_val_rel_correct.
Qed.

Lemma sst'_clo_bind_eq {E C D: Type -> Type} {X X': Type}
      `{HasStuck: B0 -< C} `{HasStuck': B0 -< D}
      (t1 : ctree E C X) (t2: ctree E D X)
      (k1 : X -> ctree E C X') (k2 : X -> ctree E D X') RR:
  t1 ≲ t2 ->
  (forall x, sst' eq RR (k1 x) (k2 x)) ->
  sst' eq RR (t1 >>= k1) (t2 >>= k2).
Proof.
  intros ? ?.
  eapply sst'_clo_bind_gen.
  - apply update_val_rel_eq.
  - apply H.
  - intros. now subst.
Qed.

Lemma ssbt'_clo_bind_gen {E F C D: Type -> Type} {X Y X' Y': Type} {L : rel (@label E) (@label F)}
      `{HasStuck: B0 -< C} `{HasStuck': B0 -< D}
      (R0 : rel X Y) L0
      (HL0 : is_update_val_rel L R0 L0)
      (t1 : ctree E C X) (t2: ctree F D Y)
      (k1 : X -> ctree E C X') (k2 : Y -> ctree F D Y') RR:
  ssim L0 t1 t2 ->
  (forall x y, R0 x y -> (ssbt' L RR) (k1 x) (k2 y)) ->
  ssbt' L RR (t1 >>= k1) (t2 >>= k2).
Proof.
  intros ? ?.
  apply (fbt_bt (@bind_ctx_ssim'_t E F C D X X' Y Y' _ _ L R0 L0 HL0)).
  apply in_bind_ctx; eauto.
Qed.

Lemma ssbt'_clo_bind {E F C D: Type -> Type} {X Y X' Y': Type} {L : rel (@label E) (@label F)}
      `{HasStuck: B0 -< C} `{HasStuck': B0 -< D}
      (R0 : rel X Y)
      (t1 : ctree E C X) (t2: ctree F D Y)
      (k1 : X -> ctree E C X') (k2 : Y -> ctree F D Y') RR:
  t1 (≲update_val_rel L R0) t2 ->
  (forall x y, R0 x y -> (ssbt' L RR) (k1 x) (k2 y)) ->
  ssbt' L RR (t1 >>= k1) (t2 >>= k2).
Proof.
  intros ? ?.
  eapply ssbt'_clo_bind_gen; eauto. apply update_val_rel_correct.
Qed.

Lemma ssbt'_clo_bind_eq {E C D: Type -> Type} {X X': Type}
      `{HasStuck: B0 -< C} `{HasStuck': B0 -< D}
      (t1 : ctree E C X) (t2: ctree E D X)
      (k1 : X -> ctree E C X') (k2 : X -> ctree E D X') RR:
  t1 ≲ t2 ->
  (forall x, ssbt' eq RR (k1 x) (k2 x)) ->
  ssbt' eq RR (t1 >>= k1) (t2 >>= k2).
Proof.
  intros ? ?.
  eapply ssbt'_clo_bind_gen.
  - apply update_val_rel_eq.
  - apply H.
  - intros. now subst.
Qed.

Tactic Notation "__upto_bind_ssim'" uconstr(R0) :=
  match goal with
  | |- body (t (@ss' ?E ?F ?C ?D ?X ?Y _ _ ?L)) ?R (CTree.bind (T := ?T) _ _) (CTree.bind (T := ?T') _ _) =>
      apply (ft_t (@bind_ctx_ssim'_t E F C D T X T' Y _ _ L R0
        (update_val_rel L R0) (update_val_rel_correct L R0))), in_bind_ctx
  | |- body (bt (@ss' ?E ?F ?C ?D ?X ?Y _ _ ?L)) ?R (CTree.bind (T := ?T) _ _) (CTree.bind (T := ?T') _ _) =>
      apply (fbt_bt (@bind_ctx_ssim'_t E F C D T X T' Y _ _ L R0
        (update_val_rel L R0) (update_val_rel_correct L R0))), in_bind_ctx
  end.

Tactic Notation "__upto_bind_eq_ssim'" uconstr(R0) :=
  match goal with
  | _ => __upto_bind_ssim' R0; [reflexivity | intros ? ? ?EQl]
   end.

(* This alternative notion of simulation is equivalent to [ssim] *)
Theorem ssim_ssim' {E F C D X Y} `{HasStuck: B0 -< C} `{HasStuck': B0 -< D} :
  forall L (t : ctree E C X) (t' : ctree F D Y), ssim L t t' <-> ssim' L t t'.
Proof.
  split; intro.
  - red. revert t t' H. coinduction R CH. intros.
    split; intros.
    + step in H. apply H in H1 as (? & ? & ? & ? & ?). eauto 6.
    + subs. apply ssim_brD_l_inv with (x := x) in H. eauto.
  - revert t t' H. coinduction R CH.
    do 3 red. cbn. intros.
    apply trans_epsilon in H0 as (? & ? & ? & ?).
    apply ssim'_epsilon_l with (t' := x) in H; auto.
    step in H. apply (proj1 H) in H2 as (? & ? & ? & ? & ?); auto.
    eauto 6.
Qed.
