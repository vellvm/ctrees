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
      (productive t -> forall l t', trans l t t' -> exists l' u' u'', trans l' u u' /\ epsilon u' u'' /\ R t' u'' /\ L l l') /\
      (forall {Z} (c : C Z) k, t ≅ BrD c k -> forall x, exists u', epsilon u u' /\ R (k x) u')
    |}.
  Next Obligation.
    split.
    - intros.
      edestruct H0 as (? & ? & ? & ?); eauto.
      eexists _, x1, x2; intuition; eauto.
    - intros. edestruct H1 as (? & ? & ?); eauto.
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
  Lemma equ_clos_sst : equ_clos <= (t (@ss' E F C D X Y _ _ L)).
  Proof.
    apply Coinduction; cbn.
    intros R x y [x' y' x'' y'' EQ' EQ'']. split.
    - intros prod l z x'z.
      rewrite EQ' in x'z, prod.
      destruct ((proj1 EQ'') prod _ _ x'z) as (l' & ? & ? & ? & ? & ? & ?).
      exists l', x0, x1.
      split.
      + rewrite <- Equu; auto.
      + split; auto. split; auto.
        eapply (f_Tf (ss' L)).
        econstructor; auto; auto.
    - intros Z c k EQx' z.
      rewrite EQ' in EQx'.
      destruct (proj2 EQ'' _ _ _ EQx' z) as (? & ? & ?). exists x0.
      split.
      + now rewrite <- Equu.
      + eapply (f_Tf (ss' L)). econstructor. 2: apply H0. all: auto.
  Qed.

  #[global] Instance ssim'_foo : Proper (equ eq ==> equ eq ==> flip impl) (@ssim' E F C D X Y _ _ L).
  Proof.
    cbn; intros ? ? eq1 ? ? eq2 H.
    apply (ft_t equ_clos_sst); econstructor; [eauto | | symmetry; eauto]; assumption.
  Qed.

  #[global] Instance ssim'_foo' : Proper (equ eq ==> equ eq ==> impl) (@ssim' E F C D X Y _ _ L).
  Proof.
    cbn; intros ? ? eq1 ? ? eq2 H.
    now rewrite <- eq1, <- eq2.
  Qed.

  End ssim'_theory.

Notation go t := ({| _observe := t |}).

Lemma ssim'_brD_r : forall {E F C D X Y Z} `{HasB0: B0 -< C} `{HasB0': B0 -< D}
  L (t : ctree E C X) (c : D Z) x (k : Z -> ctree F D Y),
  ssim' L t (k x) -> ssim' L t (BrD c k).
Proof.
  intros.
  step in H. step. split; intros.
    + apply H in H1; auto. destruct H1 as (? & ? & ? & ? & ? & ? & ?).
      eauto 8 with trans.
    + eapply H in H0. destruct H0 as (? & ? & ?).
      eapply EpsilonBr in H0.
      exists x1. split. 2: apply H1. apply H0.
Qed.

Lemma ssim'_epsilon_r : forall {E F C D X Y} `{HasB0: B0 -< C} `{HasB0': B0 -< D}
  L (t : ctree E C X) (u u' : ctree F D Y),
  ssim' L t u' -> epsilon u u' -> ssim' L t u.
Proof.
  intros. red in H0. rewrite (ctree_eta u') in H. rewrite (ctree_eta u).
  genobs u ou. clear u Heqou. genobs u' ou'. clear u' Heqou'.
  revert t H. induction H0; intros.
  - now subs.
  - apply IHepsilon_ in H. rewrite <- ctree_eta in H.
    eapply ssim'_brD_r. apply H.
Qed.

Theorem ssim_ssim' {E F C D X Y} `{HasStuck: B0 -< C} `{HasStuck': B0 -< D} :
  forall L (t : ctree E C X) (t' : ctree F D Y), ssim L t t' <-> ssim' L t t'.
Proof.
  split; intro.
  - red. revert t t' H. coinduction R CH. intros.
    do 3 red. cbn. split; intros.
    + subst. subs.
      step in H. apply H in H1. destruct H1 as (? & ? & ? & ? & ?).
      eexists _, _, _. split; [apply H1 |]. split; [left; reflexivity |]. split; [| apply H3].
      now apply CH.
    + subs. apply ssim_brD_l_inv with (x := x) in H. exists t'. split; [now left |]. now apply CH.
  - revert t t' H. coinduction R CH. intros.
    do 3 red. cbn. intros.
    apply trans_epsilon in H0 as (? & ? & ? & ?).
    red in H0. rewrite ctree_eta in H.
    genobs t ot. clear t Heqot.
    rewrite (ctree_eta x) in H1, H2. genobs x ox. clear x Heqox.
    revert t' H. induction H0; intros.
    + subs. rewrite <- ctree_eta in H1, H2, H0.
      step in H0. apply (proj1 H0) in H2; auto.
      destruct H2 as (? & ? & ? & ? & ? & ? & ?).
      exists x, x0. split. auto. split; auto. apply CH.
      eapply ssim'_epsilon_r; eauto.
    + step in H. destruct H as [_ ?].
      edestruct H as (? & ? & ?); auto.
      setoid_rewrite <- ctree_eta in IHepsilon_.
      eapply IHepsilon_ in H4; auto.
      destruct H4 as (? & ? & ? & ? & ?).
      eauto 6 with trans.
Qed.


Module SSim'Notations.

  (*| ss (simulation) notation |*)
  Notation sst' L := (t (ss' L)).
  Notation ssbt' L := (bt (ss' L)).
  Notation ssT' L := (T (ss' L)).
  Notation ssbT' L := (bT (ss' L)).

  (*Notation "t (≲ L ) u" := (ssim L t u) (at level 70).
  Notation "t ≲ u" := (ssim eq t u) (at level 70).
  Notation "t [≲ L ] u" := (ss L _ t u) (at level 79).
  Notation "t [≲] u" := (ss eq _ t u) (at level 79).
  Notation "t {≲ L } u" := (sst L _ t u) (at level 79).
  Notation "t {≲} u" := (sst eq _ t u) (at level 79).
  Notation "t {{≲ L }} u" := (ssbt L _ t u) (at level 79).
     Notation "t {{≲}} u" := (ssbt eq _ t u) (at level 79).*)

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
  Lemma refl_sst' `{Reflexive _ L}: const seq <= (sst' L).
  Proof.
    apply leq_t. cbn.
    intros. unfold seq in H0. subst. split; intros.
    - eexists _, _, _. eauto.
    - eexists. split; [| auto]. subs. eright. now left.
  Qed.

  (*Lemma square_sst' `{Transitive _ L}: square <= (sst' L).
  Proof.
    apply Coinduction; cbn.
    intros R x z [y [xy1 xy2] [yz1 yz2]]. split.
    - intros prod l x' xx'.
      destruct (xy1 prod _ _ xx') as (l' & y' & y'' & yy' & y'y'' & ? & ?).
      destruct (ctree_case_productive y) as [prod' | ?].
      + destruct (yz1 prod' _ _ yy') as (l'' & z' & z'' & zz' & z'z'' & ? & ?).
        exists l'', z', z''.
        split; [assumption |]. split; [assumption |].
        split.
        * apply (f_Tf (ss' L)). now exists y''.
    exists l'', z'.
    split.
    assumption.
    split.
    apply (f_Tf (ss L)).
    exists y'; eauto.
    transitivity l'; auto.
     Qed.*)

  (*| Reflexivity |*)
  #[global] Instance Reflexive_sst' R `{Reflexive _ L}: Reflexive (sst' L R).
  Proof. apply build_reflexive; apply ft_t; apply (refl_sst'). Qed.

  Corollary Reflexive_ssim' `{Reflexive _ L}: Reflexive (ssim' L).
  Proof. now apply Reflexive_sst'. Qed.

  #[global] Instance Reflexive_ssbt' R `{Reflexive _ L}: Reflexive (ssbt' L R).
  Proof. apply build_reflexive; apply fbt_bt; apply refl_sst'. Qed.

  #[global] Instance Reflexive_ssT' f R `{Reflexive _ L}: Reflexive (ssT' L f R).
  Proof. apply build_reflexive; apply fT_T; apply refl_sst'. Qed.

  (*| Transitivity |*)
  (*#[global] Instance Transitive_sst R `{Transitive _ L}: Transitive (sst L R).
  Proof. apply build_transitive; apply ft_t; apply (square_sst). Qed.

  Corollary Transitive_ssim `{Transitive _ L}: Transitive (ssim L).
  Proof. now apply Transitive_sst. Qed.

  #[global] Instance Transitive_ssbt R `{Transitive _ L}: Transitive (ssbt L R).
  Proof. apply build_transitive; apply fbt_bt; apply square_sst. Qed.

  #[global] Instance Transitive_ssT f R `{Transitive _ L}: Transitive (ssT L f R).
  Proof. apply build_transitive; apply fT_T; apply square_sst. Qed.

  (*| PreOrder |*)
  #[global] Instance PreOrder_sst R `{PreOrder _ L}: PreOrder (sst L R).
  Proof. split; typeclasses eauto. Qed.

  Corollary PreOrder_ssim `{PreOrder _ L}: PreOrder (ssim L).
  Proof. split; typeclasses eauto. Qed.

  #[global] Instance PreOrder_ssbt R `{PreOrder _ L}: PreOrder (ssbt L R).
  Proof. split; typeclasses eauto. Qed.

  #[global] Instance PreOrder_ssT f R `{PreOrder _ L}: PreOrder (ssT L f R).
     Proof. split; typeclasses eauto. Qed.*)

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

(*|
   Strong simulation up-to [equ] is valid
   ----------------------------------------
|*)
  Lemma equ_clos_sst' : equ_clos <= sst' L.
  Proof.
    apply Coinduction; cbn.
    intros R x y [x' y' x'' y'' EQ' EQ'']. split.
    - intros prod l z x'z.
      rewrite EQ' in x'z, prod.
      destruct ((proj1 EQ'') prod _ _ x'z) as (l' & ? & ? & ? & ? & ? & ?).
      exists l', x0, x1.
      split.
      + rewrite <- Equu; auto.
      + split; auto. split; auto.
        eapply (f_Tf (ss' L)).
        econstructor; auto; auto.
    - intros Z c k EQx' z.
      rewrite EQ' in EQx'.
      destruct (proj2 EQ'' _ _ _ EQx' z) as (? & ? & ?). exists x0.
      split.
      + now rewrite <- Equu.
      + eapply (f_Tf (ss' L)). econstructor. 2: apply H0. all: auto.
  Qed.

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

  #[global] Instance equ_clos_ssim'_goal :
    Proper (equ eq ==> equ eq ==> flip impl) (ssim' L).
  Proof.
    cbn; intros ? ? eq1 ? ? eq2 H.
    apply (ft_t equ_clos_sst'); econstructor; [eauto | | symmetry; eauto]; assumption.
  Qed.

  #[global] Instance equ_clos_ssim'_ctx :
    Proper (equ eq ==> equ eq ==> impl) (ssim' L).
  Proof.
    cbn; intros ? ? eq1 ? ? eq2 H.
    apply (ft_t equ_clos_sst'); econstructor; [symmetry; eauto | | eauto]; assumption.
  Qed.

(*|
  stuck ctrees can be simulated by anything.
|*)
  (*Lemma is_stuck_ss (R : rel _ _) (t : ctree E C X) (t': ctree F D Y):
    is_stuck t -> ss' L R t t'.
  Proof.
    repeat intro. split; intros.
    - now apply H in H1.
    - subs.
  Qed.

  Lemma is_stuck_ssim (t: ctree E C X) (t': ctree F D Y):
    is_stuck t -> ssim L t t'.
  Proof.
    intros. step. now apply is_stuck_ss.
     Qed.*)

  Lemma ss'_stuck (R : rel _ _) (t : ctree F D Y) b : ss' L R (stuck b) t.
  Proof.
    split; intros.
    - destruct b; inv_trans.
    - destruct b; inv_equ.
      step in H. inv H. invert. destruct x.
  Qed.

  Lemma ssim'_stuck (t : ctree F D Y) : ssim' L stuckD t.
  Proof.
    intros. step. apply ss'_stuck.
  Qed.

  (*Lemma spinD_ss (R : rel _ _) (t : ctree F D Y) `{HasTau: B1 -< C}: ss L R spinD t.
  Proof.
    repeat intro. now apply spinD_is_stuck in H.
  Qed.

  Lemma spinD_ssim : forall (t' : ctree F D Y) `{HasTau: B1 -< C},
      ssim L spinD t'.
  Proof.
    intros. step. apply spinD_ss.
     Qed.*)

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
  Context {E C: Type -> Type}
          {X : Type}
          {HasStuck: B0 -< C}.

  Lemma step_ss'_ret_gen {Y F D} `{HasStuck': B0 -< D}(x : X) (y : Y) (R L : rel _ _) :
    R stuckD stuckD ->
    (Proper (equ eq ==> equ eq ==> impl) R) ->
    L (val x) (val y) ->
    ss' L R (Ret x : ctree E C X) (Ret y : ctree F D Y).
  Proof.
    intros Rstuck PROP Lval. split; intros.
    2: inv_equ.
    inv_trans; subst.
    do 3 eexists; intuition; etrans. now subs.
  Qed.

  Lemma step_ss'_ret {Y F D} `{HasStuck': B0 -< D} (x : X) (y : Y) (R L : rel _ _) :
    L (val x) (val y) ->
    ssbt' L R (Ret x : ctree E C X) (Ret y : ctree F D Y).
  Proof.
    intros.
    apply step_ss'_ret_gen.
    - step. intros. red. red. cbn.
      apply ss'_stuck.
    - typeclasses eauto.
    - apply H.
  Qed.

(*|
 The vis nodes are deterministic from the perspective of the labeled
 transition system, stepping is hence symmetric and we can just recover
 the itree-style rule.
|*)
  Lemma step_ss'_vis_gen {Y Z Z' F D} `{HasStuck': B0 -< D} (e : E Z) (f: F Z')
        (k : Z -> ctree E C X) (k' : Z' -> ctree F D Y) (R L: rel _ _) :
    (Proper (equ eq ==> equ eq ==> impl) R) ->
    (forall x, exists y, R (k x) (k' y) /\ L (obs e x) (obs f y)) ->
    ss' L R (Vis e k) (Vis f k').
  Proof.
    intros. split; intros; inv_equ.
    cbn; inv_trans; subst;
      destruct (H0 x) as (x' & RR & LL);
      cbn; do 3 eexists; intuition.
    - rewrite EQ; eauto.
    - assumption.
  Qed.

  Lemma step_ss'_vis {Y Z Z' F D} `{HasStuck': B0 -< D} (e : E Z) (f: F Z')
        (k : Z -> ctree E C X) (k' : Z' -> ctree F D Y) (R L : rel _ _) :
    (forall x, exists y, sst' L R (k x) (k' y) /\ L (obs e x) (obs f y)) ->
    ssbt' L R (Vis e k) (Vis f k').
  Proof.
    intros * EQ.
    apply step_ss'_vis_gen; auto.
    typeclasses eauto.
  Qed.

  Lemma step_ss'_vis_id_gen {Y Z F D} `{HasStuck': B0 -< D} (e : E Z) (f: F Z)
        (k : Z -> ctree E C X) (k' : Z -> ctree F D Y) (R L: rel _ _) :
    (Proper (equ eq ==> equ eq ==> impl) R) ->
    (forall x, R (k x) (k' x) /\ L (obs e x) (obs f x)) ->
    ss' L R (Vis e k) (Vis f k').
  Proof.
    intros. apply step_ss'_vis_gen. { typeclasses eauto. }
    eauto.
  Qed.

  Lemma step_ss'_vis_id {Y Z F D} `{HasStuck': B0 -< D} (e : E Z) (f: F Z)
        (k : Z -> ctree E C X) (k' : Z -> ctree F D Y) (R L : rel _ _) :
    (forall x, sst' L R (k x) (k' x) /\ L (obs e x) (obs f x)) ->
    ssbt' L R (Vis e k) (Vis f k').
  Proof.
    intros * EQ.
    apply step_ss'_vis_id_gen; auto.
    typeclasses eauto.
  Qed.

  (*|
    Same goes for visible tau nodes.
    |*)
  Lemma step_ss'_step_gen {Y F D} `{HasTau: B1 -< C} `{HasStuck': B0 -< D} `{HasTau': B1 -< D}
        (t : ctree E C X) (t': ctree F D Y) (R L: rel _ _):
    (Proper (equ eq ==> equ eq ==> impl) R) ->
    L tau tau ->
    (R t t') ->
    ss' L R (Step t) (Step t').
  Proof.
    split; intros; inv_equ.
    inv_trans; subst.
    cbn; do 3 eexists; intuition; subs; eauto.
  Qed.

  Lemma step_ss'_step {Y F D} `{HasStuck': B0 -< D} `{HasTau: B1 -< C} `{HasTau': B1 -< D}
        (t: ctree E C X) (t': ctree F D Y) (R L : rel _ _) :
    (sst' L R t t') ->
    L tau tau ->
    ssbt' L R (Step t) (Step t').
  Proof.
    intros. apply step_ss'_step_gen; auto.
    typeclasses eauto.
  Qed.

  (*|
    When matching visible brs one against another, in general we need to explain how
    we map the branches from the left to the branches to the right.
    A useful special case is the one where the arity coincide and we simply use the identity
    in both directions. We can in this case have [n] rather than [2n] obligations.
    |*)
  Lemma step_ss'_brS_gen {Z Z' Y F D} `{HasStuck': B0 -< D} (c : C Z) (d : D Z')
        (k : Z -> ctree E C X) (k' : Z' -> ctree F D Y) (R L: rel _ _) :
    (Proper (equ eq ==> equ eq ==> impl) R) ->
    (forall x, exists y, R (k x) (k' y)) ->
    L tau tau ->
    ss' L R (BrS c k) (BrS d k').
  Proof.
    split; intros; inv_equ. inv_trans. subst.
    destruct (H0 x) as [y HR].
    cbn; do 3 eexists; intuition; subs; eauto.
  Qed.

  Lemma step_ss'_brS {Z Z' Y F D} `{HasStuck' : B0 -< D} (c : C Z) (c' : D Z')
        (k : Z -> ctree E C X) (k' : Z' -> ctree F D Y) (R L: rel _ _) :
    (forall x, exists y, sst' L R (k x) (k' y)) ->
    L tau tau ->
    ssbt' L R (BrS c k) (BrS c' k').
  Proof.
    intros.
    apply step_ss'_brS_gen; auto.
    typeclasses eauto.
  Qed.

  Lemma step_ss'_brS_id_gen {Z Y D F} `{HasStuck': B0 -< D} (c : C Z) (d: D Z)
        (k: Z -> ctree E C X) (k': Z -> ctree F D Y) (R L : rel _ _) :
    (Proper (equ eq ==> equ eq ==> impl) R) ->
    (forall x, exists y, R (k x) (k' y)) ->
    L tau tau ->
    ss' L R (BrS c k) (BrS d k').
  Proof.
    intros; apply step_ss'_brS_gen; eauto.
  Qed.

  Lemma step_ss'_brS_id {Z Y D F} `{HasStuck': B0 -< D} (c : C Z) (d : D Z)
        (k: Z -> ctree E C X) (k': Z -> ctree F D Y) (R L : rel _ _) :
    (forall x, exists y, sst' L R (k x) (k' y)) ->
    L tau tau ->
    ssbt' L R (BrS c k) (BrS d k').
  Proof.
    intros.
    apply step_ss'_brS_id_gen; eauto.
    typeclasses eauto.
  Qed.

  (*|
    With this definition [ss'] of simulation, delayed nodes allow to perform a coinductive step.
    |*)
  Lemma step_ss'_brD_l_gen {Y F D Z} `{HasStuck': B0 -< D} (c : C Z)
        (k : Z -> ctree E C X) (t': ctree F D Y) (R L: rel _ _):
    (Proper (equ eq ==> equ eq ==> impl) R) ->
    (forall x, R (k x) t') ->
    ss' L R (BrD c k) t'.
  Proof.
    split; intros. { now apply productive_brD in H1. }
    inv_equ. setoid_rewrite EQ in H0. eauto.
  Qed.

  Lemma step_ss'_brD_l {Y F D Z} `{HasStuck': B0 -< D} (c : C Z)
        (k : Z -> ctree E C X) (t: ctree F D Y) (R L: rel _ _):
    (forall x, sst' L R (k x) t) ->
    ssbt' L R (BrD c k) t.
  Proof.
    apply step_ss'_brD_l_gen. typeclasses eauto.
  Qed.

  Lemma step_ss'_brD_r_gen {Y F D Z} `{HasStuck': B0 -< D} (c : D Z) x
        (k : Z -> ctree F D Y) (t: ctree E C X) (R L: rel _ _):
    ss' L R t (k x) ->
    ss' L R t (BrD c k).
  Proof.
    cbn. split; intros.
    apply H in H1 as (? & ? & ? & ? & ? & ? & ?).
    exists x0, x1, x2; etrans. auto.
    eapply (proj2 H) in H0 as (? & ? & ?). eapply EpsilonBr in H0. etrans.
  Qed.

  Lemma step_ss'_brD_r {Y F D Z} `{HasStuck': B0 -< D} (c : D Z) x
        (k : Z -> ctree F D Y) (t: ctree E C X) (R L: rel _ _):
    ssbt' L R t (k x) ->
    ssbt' L R t (BrD c k).
  Proof.
    intros. eapply step_ss'_brD_r_gen. apply H.
  Qed.

  Lemma step_ss'_brD_gen {Y F D n m} `{HasStuck': B0 -< D} (a: C n) (b: D m)
    (k : n -> ctree E C X) (k' : m -> ctree F D Y) (R L : rel _ _) :
    (Proper (equ eq ==> equ eq ==> impl) R) ->
    (forall x, exists y, R (k x) (k' y)) ->
    ss' L R (BrD a k) (BrD b k').
  Proof.
    split; intros. { now apply productive_brD in H1. }
    inv_equ. setoid_rewrite EQ in H0. destruct (H0 x).
    eexists. split; [| eassumption]. eright. eleft. reflexivity.
  Qed.

  Lemma step_ss'_brD {Y F D n m} `{HasStuck': B0 -< D} (cn: C n) (cm: D m)
    (k : n -> ctree E C X) (k' : m -> ctree F D Y) (L R : rel _ _) :
    (forall x, exists y, sst' L R (k x) (k' y)) ->
    ssbt' L R (BrD cn k) (BrD cm k').
  Proof.
    apply step_ss'_brD_gen. typeclasses eauto.
  Qed.

  Lemma step_ss'_brD_id_gen {F D Y Z} `{HasStuck': B0 -< D} (c: C Z) (d: D Z)
        (k : Z -> ctree E C X) (k' : Z -> ctree F D Y)
        (R L : rel _ _) :
    (Proper (equ eq ==> equ eq ==> impl) R) ->
    (forall x, R (k x) (k' x)) ->
    ss' L R (BrD c k) (BrD d k').
  Proof.
   intros. apply step_ss'_brD_gen; eauto.
  Qed.

  Lemma step_ss'_brD_id {F D Y Z} `{HasStuck': B0 -< D} (c: C Z) (d: D Z)
    (k : Z -> ctree E C X) (k': Z -> ctree F D Y) (R L: rel _ _) :
    (forall x, sst' L R (k x) (k' x)) ->
    ssbt' L R (BrD c k) (BrD d k').
  Proof.
    apply step_ss'_brD_id_gen. typeclasses eauto.
  Qed.

  Lemma step_ss'_guard_gen {Y F D} `{HasStuck': B0 -< D} `{HasTau: B1 -< C} `{HasTau': B1 -< D}
        (t: ctree E C X) (t': ctree F D Y) (R L: rel _ _):
    (Proper (equ eq ==> equ eq ==> impl) R) ->
    R t t' ->
    ss' L R (Guard t) (Guard t').
  Proof.
    intros. apply step_ss'_brD_id_gen; auto.
  Qed.

  Lemma step_ss'_guard {Y F D} `{HasStuck': B0 -< D} `{HasTau: B1 -< C} `{HasTau': B1 -< D}
        (t: ctree E C X) (t': ctree F D Y) (R L: rel _ _):
    sst' L R t t' ->
    ssbt' L R (Guard t) (Guard t').
  Proof.
    apply step_ss'_guard_gen. typeclasses eauto.
  Qed.


  (*Lemma ssbt_vis_inv {F D Y X1 X2} {L: rel (label E) (label F)} `{HasStuck': B0 -< D}
    (e1 : E X1) (e2 : F X2) (k1 : X1 -> ctree E C X) (k2 : X2 -> ctree F D Y) (x : X1) R:
    ssbt L R (Vis e1 k1) (Vis e2 k2) ->
    (exists y, L (obs e1 x) (obs e2 y))  /\ (forall x, exists y, sst L R (k1 x) (k2 y)).
  Proof.
    intros.
    split; intros; edestruct H as (? & ? & ? & ? & ?);
      etrans; subst;
      inv_trans; subst; eexists; auto.
    - now eapply H2.
    - now apply H1.
  Qed.

  Lemma ss_brD_l_inv {F D Y} {L: rel (label E) (label F)} `{HasStuck': B0 -< D}
        n (c: C n) (t : ctree F D Y) (k : n -> ctree E C X) R:
    ss L R (BrD c k) t ->
    forall x, ss L R (k x) t.
  Proof.
    cbn. intros.
    eapply trans_brD in H0; [| reflexivity].
    apply H in H0 as (? & ? & ? & ? & ?); subst.
    eauto.
     Qed.*)

End Proof_Rules.

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
Specialization of [bind_ctx] to a function acting with [ssim] on the bound value,
and with the argument (pointwise) on the continuation.
|*)
  Program Definition bind_ctx_ssim' L0 : mon (rel (ctree E C X') (ctree F D Y')) :=
    {|body := fun R => @bind_ctx E F C D X Y X' Y' (ssim' L0) (pointwise R0 R) |}.
  Next Obligation.
    intros ?? ? H. apply leq_bind_ctx. intros ?? H' ?? H''.
    apply in_bind_ctx. apply H'. intros t t' HS. apply H, H'', HS.
  Qed.

(*|
    The resulting enhancing function gives a valid up-to technique
|*)
  Lemma bind_ctx_ssim'_t L0 (*{RV: Respects_val L}*):
    is_update_val_rel L R0 L0 -> bind_ctx_ssim' L0 <= (t (ss' L)).
  Proof.
    intro HL0. apply Coinduction.
    intros R. apply (leq_bind_ctx _).
    intros t1 t2 tt k1 k2 kk.
    step in tt. split.
    - simpl; intros PROD l u STEP.
      apply trans_bind_inv in STEP as [(H & t' & STEP & EQ) | (v & STEPres & STEP)].
      apply tt in STEP as (l' & u' & u'' & STEP & EPS & EQ' & ?).
      2: { now apply productive_bind in PROD. }
      do 3 eexists. split; [| split; [| split]].
      apply trans_bind_l; eauto.
      + intro Hl. destruct Hl.
        apply HL0 in H0.
        2: now apply wf_val_nonval.
        2: now apply wf_val_trans in STEP.
        inversion H0; subst. apply H. constructor. apply H2. constructor.
      + apply epsilon_bind_l. apply EPS.
      + apply (fT_T equ_clos_sst').
          econstructor; [exact EQ | | reflexivity].
          apply (fTf_Tf (ss' L)).
          apply in_bind_ctx; [apply EQ' |].
          intros ? ? ?.
          apply (b_T (ss' L)).
          red in kk; cbn; apply kk. eassumption.
      + apply HL0 in H0.
        2: now apply wf_val_nonval.
        2: now apply wf_val_trans in STEP.
        destruct H0. exfalso. apply H. constructor. apply H2.
      + assert (t1 ≅ Ret v).
        { apply productive_bind in PROD. apply trans_val_epsilon in STEPres as [? _].
          now apply productive_epsilon. } subs.
        apply tt in STEPres as (l' & u' & u'' & STEPres & EPS & EQ' & ?).
        2: { now apply productive_bind in PROD. }
        apply HL0 in H.
        2: apply wf_val_val.
        2: now apply wf_val_trans in STEPres.
        dependent destruction H. 2: { exfalso. apply H. constructor. }
        pose proof (trans_val_inv STEPres) as EQ.
        rewrite EQ in STEPres.
        specialize (kk v v2 H).
        rewrite bind_ret_l in PROD.
        apply kk in STEP as (? & u''' & ? & STEP & EPS' & EQ'' & ?); auto.
        do 3 eexists; split.
        eapply trans_bind_r; eauto.
        split; [eassumption |]. split; auto.
        eapply (id_T (ss' L)); auto.
    - intros Z c k EQ z.
      apply br_equ_bind in EQ as EQ'. destruct EQ' as [(v & EQ') | (k0 & EQ' & EQ'')].
      + subs. destruct tt as [tt _].
        edestruct tt as (l & t'' & _ & STEPres & _ & _ & ?).
        now eapply prod_ret. etrans.
        apply HL0 in H. 2: apply wf_val_val. 2: now apply wf_val_trans in STEPres.
        apply update_val_rel_val_l in H as (v' & -> & EQ').
        rewrite bind_ret_l in EQ.
        specialize (kk v v' EQ'). apply kk with (x := z) in EQ. destruct EQ as (u' & EPS & EQ).
        exists u'.
        apply trans_val_epsilon in STEPres as [? _]. split.
        * eapply epsilon_bind; eassumption.
        * now apply (id_T (ss' L)).
      + subs. destruct tt as [_ tt].
        specialize (tt Z c k0). lapply tt; [clear tt; intros tt | reflexivity].
        destruct (tt z) as (u' & EPS & tt').
        exists (u' >>= k2). split.
        * now apply epsilon_bind_l.
        * rewrite EQ''.
          apply (fTf_Tf (ss' L)). apply in_bind_ctx. apply tt'.
          red. intros. apply (b_T (ss' L)). now apply kk.
  Qed.

End bind.

(*|
Expliciting the reasoning rule provided by the up-to principles.
|*)
Lemma sst'_clo_bind {E F C D: Type -> Type} {X Y X' Y': Type} {L : rel (@label E) (@label F)}
      `{HasStuck: B0 -< C} `{HasStuck': B0 -< D}
      (R0 : rel X Y) L0
      (t1 : ctree E C X) (t2: ctree F D Y)
      (HL0 : is_update_val_rel L R0 L0)
      (k1 : X -> ctree E C X') (k2 : Y -> ctree F D Y') RR:
  ssim' L0 t1 t2 ->
  (forall x y, R0 x y -> (sst' L RR) (k1 x) (k2 y)) ->
  sst' L RR (t1 >>= k1) (t2 >>= k2).
Proof.
  intros ? ?.
  apply (ft_t (@bind_ctx_ssim'_t E F C D X X' Y Y' _ _ L R0 L0 HL0)).
  apply in_bind_ctx; eauto.
Qed.

(*|
And in particular, we can justify rewriting [≲] to the left of a [bind].
|*)
(*Lemma bind_ssim_cong_gen {E C X X'} RR {HasStuck: B0 -< C}
      {L: relation (@label E)} (R0 : relation X):
  Proper (ssim L ==> (fun f g => forall x y, sst L RR (f x) (g y)) ==> sst L RR) (@bind E C X X').
Proof.
  do 4 red; intros.
  eapply sst_clo_bind; auto.
Qed.*)

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
