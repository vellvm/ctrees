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
     Eq.Epsilon
     Eq.SSimAlt.

From RelationAlgebra Require Export
     rel srel.

Import CTree.
Set Implicit Arguments.

(* TODO: Decide where to set this *)
Arguments trans : simpl never.

Section StrongBisimAlt.
(*|
An alternative definition [sb'] of strong bisimulation.
The simulation challenge does not involve an inductive transition relation,
thus simplifying proofs.
|*)
  Program Definition sb' {E F C D : Type -> Type} {X Y : Type}
    `{HasStuck : B0 -< C} `{HasStuck' : B0 -< D}
    (L : rel (@label E) (@label F)) :
    mon (bool -> ctree E C X -> ctree F D Y -> Prop) :=
    {| body R side t u :=
      (side = true -> ss'_gen L (fun t u => forall side, R side t u) (R true) t u) /\
      (side = false -> ss'_gen (flip L) (fun u t => forall side, R side t u) (flip (R false)) u t)
    |}.
  Next Obligation.
    split; intro; subst; [specialize (H0 eq_refl); clear H1 | specialize (H1 eq_refl); clear H0].
    all: eapply ss'_gen_mon; try eassumption; eauto.
    all: cbn; intuition.
  Qed.

End StrongBisimAlt.

Lemma sb'_flip {E F C D X Y L} `{HasB0: B0 -< C} `{HasB0': B0 -< D}
    side (t: ctree E C X) (u: ctree F D Y) R :
  sb' (flip L) (fun b => flip (R (negb b))) (negb side) u t ->
  sb' L R side t u.
Proof.
  split; intros; subst; destruct H; cbn in H.
  - specialize (H0 eq_refl).
    split; intros.
    + apply H0 in H2 as (? & ? & ? & ? & ?); auto. eexists _, _.
      split; eauto. split; auto. intros. specialize (H3 (negb side)).
      now rewrite Bool.negb_involutive in H3.
    + eapply (proj2 H0) in H1 as (? & ? & ?). eauto.
  - specialize (H eq_refl).
    split; intros.
    + apply H in H2 as (? & ? & ? & ? & ?); auto. eexists _, _.
      split; eauto. split; auto. intros. specialize (H3 (negb side)).
      now rewrite Bool.negb_involutive in H3.
    + eapply (proj2 H) in H1 as (? & ? & ?). eauto.
Qed.

Definition sbisim' {E F C D X Y} `{HasStuck : B0 -< C} `{HasStuck' : B0 -< D} L t u :=
  forall side, gfp (@sb' E F C D X Y _ _ L) side t u.

Section sbisim'_theory.
  Arguments label: clear implicits.
  Context {E F C D: Type -> Type} {X Y: Type}
          {L: rel (@label E) (@label F)}
          {HasStuck1: B0 -< C} {HasStuck2: B0 -< D}.

(*|
   Strong simulation up-to [equ] is valid
   ----------------------------------------
|*)
  Program Definition lift_rel3 : mon (rel (ctree E C X) (ctree F D Y)) -> mon (bool -> rel (ctree E C X) (ctree F D Y)) :=
      fun f => {| body R side t u := f (R side) t u |}.
  Next Obligation.
    destruct f. cbn. cbn in H0. eapply Hbody in H0. 2: { cbn. apply H. } apply H0.
  Qed.

  Lemma equ_clos_st' : lift_rel3 equ_clos <= (t (@sb' E F C D X Y _ _ L)).
  Proof.
    apply Coinduction; cbn.
    intros R side x y [x' y' x'' y'' EQ' EQ''].
    split; [destruct EQ'' as [EQ'' _] | destruct EQ'' as [_ EQ'']];
        intros; subst; specialize (EQ'' eq_refl); split.
    - intros prod l z x'z.
      rewrite EQ' in x'z, prod.
      destruct ((proj1 EQ'') prod _ _ x'z) as (l' & ? & ? & ? & ?).
      exists l', x0.
      split.
      + rewrite <- Equu; auto.
      + split; auto.
        intro. eapply (f_Tf (sb' L)); econstructor; auto; apply H0.
    - intros Z c k EQx' z.
      rewrite EQ' in EQx'.
      destruct (proj2 EQ'' _ _ _ EQx' z) as (? & ? & ?). exists x0.
      split.
      + now rewrite <- Equu.
      + eapply (f_Tf (sb' L)). econstructor. 2: apply H0. all: auto.
    - intros prod l z x'z.
      rewrite <- Equu in x'z, prod.
      destruct ((proj1 EQ'') prod _ _ x'z) as (l' & ? & ? & ? & ?).
      exists l', x0.
      split.
      + rewrite EQ'; auto.
      + split; auto.
        intro. eapply (f_Tf (sb' L)); econstructor; auto; apply H0.
    - intros Z c k EQx' z.
      rewrite <- Equu in EQx'.
      destruct (proj2 EQ'' _ _ _ EQx' z) as (? & ? & ?). exists x0.
      split.
      + now rewrite EQ'.
      + eapply (f_Tf (sb' L)). econstructor. 2: apply H0. all: auto.
  Qed.

  #[global] Instance equ_clos_gfp_sb'_goal : forall side, Proper (equ eq ==> equ eq ==> flip impl) (gfp (@sb' E F C D X Y _ _ L) side).
  Proof.
    cbn; intros ? ? ? eq1 ? ? eq2 H.
    apply (ft_t equ_clos_st'); econstructor; try eassumption.
    now symmetry.
  Qed.

  #[global] Instance equ_clos_gfp_sb'_ctx : forall side, Proper (equ eq ==> equ eq ==> impl) (gfp (@sb' E F C D X Y _ _ L) side).
  Proof.
    cbn; intros ? ? ? eq1 ? ? eq2 H. now subs.
  Qed.

  #[global] Instance equ_clos_sbisim'_goal : Proper (equ eq ==> equ eq ==> flip impl) (@sbisim' E F C D X Y _ _ L).
  Proof.
    cbn; intros ? ? eq1 ? ? eq2 H.
    intro. now subs.
  Qed.

  #[global] Instance equ_clos_sbisim'_ctx : Proper (equ eq ==> equ eq ==> impl) (@sbisim' E F C D X Y _ _ L).
  Proof.
    cbn; intros ? ? eq1 ? ? eq2 H. now subs.
  Qed.

  End sbisim'_theory.

Notation go t := ({| _observe := t |}).

(*Lemma ssim'_brD_r : forall {E F C D X Y Z} `{HasB0: B0 -< C} `{HasB0': B0 -< D}
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
   Qed.*)

(* TODO symmetry *)
Theorem sbisim_sbisim' {E F C D X Y} `{HasStuck: B0 -< C} `{HasStuck': B0 -< D} :
  forall L (t : ctree E C X) (t' : ctree F D Y), sbisim L t t' <-> sbisim' L t t'.
Proof.
  split; intro.
  - revert t t' H.
    assert (
      forall (t : ctree E C X) (u : ctree F D Y),
        (ss L (sbisim L) t u -> gfp (sb' L) true t u) /\
        (ss (flip L) (flip (sbisim L)) u t -> gfp (sb' L) false t u)).
    2: {
      intros. step in H0. destruct H0.
      apply H in H0, H1. intros []; auto.
    }
    coinduction R CH. intros. split; [| admit]. intro. split.
    2: { intro. discriminate. }
    intros _.
    cbn. split; intros.
    + subst. subs.
      apply H in H1. destruct H1 as (? & ? & ? & ? & ?).
      eexists _, _. split; [apply H1 |]. split; [| apply H3].
      step in H2. destruct side; apply CH; apply H2.
    + subs. apply ss_brD_l_inv with (x := x) in H. exists u. split; [now left |]. now apply CH.
  - revert t t' H.
    coinduction R CH. intros. split; intros. 2: admit.
    cbn. intros. apply trans_epsilon in H0 as (? & ? & ? & ?).
    red in H0. rewrite ctree_eta in H.
    genobs t ot. clear t Heqot.
    rewrite (ctree_eta x) in H1, H2. genobs x ox. clear x Heqox.
    specialize (H true).
    revert t' H. induction H0; intros.
    + subs. rewrite <- ctree_eta in H1, H2, H0.
      step in H0. apply (proj1 H0) in H2; auto.
      destruct H2 as (? & ? & ? & ? & ?).
      exists x, x0. auto.
    + step in H.
      destruct H as [H _]. specialize (H eq_refl).
      destruct H as [_ H].
      edestruct H as (? & ? & ?); auto.
      setoid_rewrite <- ctree_eta in IHepsilon_.
      eapply IHepsilon_ in H4 as ?; auto.
      destruct H5 as (? & ? & ? & ? & ?). eexists _, _. etrans.
Admitted.


Module SBisim'Notations.

  (*| ss (simulation) notation |*)
  Notation st' L := (t (sb' L)).
  Notation sbt' L := (bt (sb' L)).
  Notation sT' L := (T (sb' L)).
  Notation sbT' L := (bT (sb' L)).

  (*Notation "t (≲ L ) u" := (ssim L t u) (at level 70).
  Notation "t ≲ u" := (ssim eq t u) (at level 70).
  Notation "t [≲ L ] u" := (ss L _ t u) (at level 79).
  Notation "t [≲] u" := (ss eq _ t u) (at level 79).
  Notation "t {≲ L } u" := (sst L _ t u) (at level 79).
  Notation "t {≲} u" := (sst eq _ t u) (at level 79).
  Notation "t {{≲ L }} u" := (ssbt L _ t u) (at level 79).
     Notation "t {{≲}} u" := (ssbt eq _ t u) (at level 79).*)

End SBisim'Notations.

Import SBisim'Notations.

(* TODO check *)
Ltac fold_sbisim' :=
  repeat
    match goal with
    | h: context[gfp (@sb' ?E ?F ?C ?D ?X ?Y _ _ ?L)] |- _ => try fold (@sbisim' E F C D X Y _ _ L) in h
    | |- context[gfp (@sb' ?E ?F ?C ?D ?X ?Y _ _ ?L)]      => try fold (@sbisim' E F C D X Y _ _ L)
    end.

Ltac __coinduction_sbisim' R H :=
  (try unfold sbisim');
  apply_coinduction; fold_sbisim'; intros R H.

Tactic Notation "__step_sbisim'" :=
  match goal with
  | |- context[@sbisim' ?E ?F ?C ?D ?X ?Y _ _ ?LR] =>
      unfold sbisim';
      intro; step
  end.

#[local] Tactic Notation "step" := __step_sbisim' || step.

#[local] Tactic Notation "coinduction" simple_intropattern(R) simple_intropattern(H) :=
  __coinduction_sbisim' R H || coinduction R H.

Ltac __step_in_sbisim' H :=
  match type of H with
  | context[@sbisim' ?E ?F ?C ?D ?X ?Y _ _ ?LR] =>
      unfold sbisim' in H;
      let Hl := fresh H "l" in
      let Hr := fresh H "r" in
      pose proof (Hl : H true);
      pose proof (Hr : H false);
      step in Hl; step in Hr;
      try fold (@sbisim' E F C D X Y _ _ L) in Hl;
      try fold (@sbisim' E F C D X Y _ _ L) in Hr
  end.

#[local] Tactic Notation "step" "in" ident(H) := __step_in_sbisim' H || step in H.

Import CTreeNotations.
Import EquNotations.
Section sbisim'_homogenous_theory.
  Context {E C: Type -> Type} {X: Type}
          {L: relation (@label E)}
          {HasStuck1: B0 -< C}.

  Notation sb' := (@sb' E E C C X X _ _).
  Notation sbisim' := (@sbisim' E E C C X X _ _).
  Notation st' L := (coinduction.t (sb' L)).
  Notation sbt' L := (coinduction.bt (sb' L)).
  Notation sT' L := (coinduction.T (sb' L)).

  (*|
    Various results on reflexivity and transitivity.
  |*)
  Lemma refl_st' `{Reflexive _ L}: lift_rel3 (const seq) <= (st' L).
  Proof.
    apply leq_t. cbn.
    intros. unfold seq in H0. subst. split; intros; subst; split; intros.
    - eexists _, _. eauto.
    - eexists. split; [| auto]. subs. eright. now left.
    - eexists _, _. cbn. eauto.
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
  #[global] Instance Reflexive_st' R `{Reflexive _ L}: forall b, Reflexive (st' L R b).
  Proof.
    intros. apply build_reflexive.
    cbn. intros.
    pose proof (ft_t refl_st'). cbn in H1. auto.
  Qed.

  Corollary Reflexive_sbisim' `{Reflexive _ L}: Reflexive (sbisim' L).
  Proof. cbn. intros ? ?. now apply Reflexive_st'. Qed.

  #[global] Instance Reflexive_sbt' R `{Reflexive _ L}:
    forall b, Reflexive (sbt' L R b).
  Proof.
    intros. apply build_reflexive.
    cbn. intros.
    pose proof (fbt_bt refl_st'). cbn in H1. auto.
  Qed.

  #[global] Instance Reflexive_sT' f R `{Reflexive _ L}:
    forall b, Reflexive (sT' L f R b).
  Proof.
    intros. apply build_reflexive.
    cbn. intros.
    pose proof (fT_T refl_st'). cbn in H1. auto.
  Qed.

End sbisim'_homogenous_theory.

Section sbisim'_heterogenous_theory.
  Arguments label: clear implicits.
  Context {E F C D: Type -> Type} {X Y: Type}
          {L: rel (@label E) (@label F)}
          {HasStuck1: B0 -< C} {HasStuck2: B0 -< D}.

  Notation sb' := (@sb' E F C D X Y _ _).
  Notation sbisim'  := (@sbisim' E F C D X Y _ _).
  Notation st' L := (coinduction.t (sb' L)).
  Notation sbt' L := (coinduction.bt (sb' L)).
  Notation sT' L := (coinduction.T (sb' L)).

  #[global] Instance equ_sb'_goal {RR} :
    forall b, Proper (equ eq ==> equ eq ==> flip impl) (sb' L RR b).
  Proof.
    intros. split; intros; subst.
    - subs. now apply H1.
    - subs. now apply H1.
  Qed.

  #[global] Instance equ_sb'_ctx {RR} :
    Proper (eq ==> equ eq ==> equ eq ==> impl) (sb' L RR).
  Proof.
    do 6 red. intros. subst. now rewrite <- H0, <- H1.
  Qed.

  #[global] Instance equ_clos_st'_goal {RR} :
    Proper (eq ==> equ eq ==> equ eq ==> flip impl) (st' L RR).
  Proof.
    cbn; intros ? ? ? ? ? eq1 ? ? eq2 H. subst.
    apply (ft_t equ_clos_st'); econstructor; [eauto | | symmetry; eauto]; assumption.
  Qed.

  #[global] Instance equ_clos_st'_ctx {RR} :
    Proper (eq ==> equ eq ==> equ eq ==> impl) (st' L RR).
  Proof.
    cbn; intros ? ? ? ? ? eq1 ? ? eq2 H. subst.
    now rewrite <- eq1, <- eq2.
  Qed.

  #[global] Instance equ_sbt'_closed_goal {r} :
    Proper (eq ==> equ eq ==> equ eq ==> flip impl) (sbt' L r).
  Proof.
    cbn. intros. subst.
    apply (fbt_bt equ_clos_st'); econstructor; eauto.
    now symmetry.
  Qed.

  #[global] Instance equ_sbt'_closed_ctx {r} :
    Proper (eq ==> equ eq ==> equ eq ==> impl) (sbt' L r).
  Proof.
    cbn; intros. subst.
    now rewrite H0, H1 in H2.
  Qed.

  #[global] Instance equ_clos_sT'_goal RR f :
    Proper (eq ==> equ eq ==> equ eq ==> flip impl) (sT' L f RR).
  Proof.
    cbn; intros ? ? ? ? ? eq1 ? ? eq2 H. subst.
    apply (fT_T equ_clos_st'); econstructor; [eauto | | symmetry; eauto]; assumption.
  Qed.

  #[global] Instance equ_clos_sT'_ctx RR f :
    Proper (eq ==> equ eq ==> equ eq ==> impl) (sT' L f RR).
  Proof.
    cbn; intros ? ? ? ? ? eq1 ? ? eq2 H. subst.
    now rewrite <- eq1, <- eq2.
  Qed.

End sbisim'_heterogenous_theory.


Section Proof_Rules.

  Arguments label: clear implicits.
  Context {E F C D: Type -> Type}
          {X Y: Type}
          {HasStuck: B0 -< C}
          {HasStuck': B0 -< D}.
  Variable (L : rel (@label E) (@label F)).

  Lemma step_sb'_ret_gen (x : X) (y : Y) (R : bool -> rel (ctree E C X) (ctree F D Y)) :
    (forall side, R side stuckD stuckD) ->
    (Proper (eq ==> equ eq ==> equ eq ==> impl) R) ->
    L (val x) (val y) ->
    forall side, sb' L R side (Ret x : ctree E C X) (Ret y : ctree F D Y).
  Proof.
    intros Rstuck PROP Lval. split; intros; subst.
    - apply step_ss'_ret_gen; auto. cbn. intros. rewrite <- H. specialize (H1 side). now subs.
    - apply step_ss'_ret_gen; auto. cbn. intros. specialize (H1 side). now subs.
  Qed.

  Lemma step_sb'_ret (x : X) (y : Y) (R : bool -> rel _ _) :
    L (val x) (val y) ->
    forall side, sbt' L R side (Ret x : ctree E C X) (Ret y : ctree F D Y).
  Proof.
    intros. unfold bt. red. red. eapply step_sb'_ret_gen; auto.
    - intro. step. red. red. cbn.
      destruct side0; split; intuition; apply ss'_stuck.
    - typeclasses eauto.
  Qed.

(*|
 The vis nodes are deterministic from the perspective of the labeled
 transition system, stepping is hence symmetric and we can just recover
 the itree-style rule.
|*)
  Lemma step_sb'_vis_gen {Z Z'} (e : E Z) (f: F Z')
        (k : Z -> ctree E C X) (k' : Z' -> ctree F D Y) R :
    (Proper (eq ==> equ eq ==> equ eq ==> impl) R) ->
    (forall x, exists y, (forall side, R side (k x) (k' y)) /\ L (obs e x) (obs f y)) ->
    (forall y, exists x, (forall side, R side (k x) (k' y)) /\ L (obs e x) (obs f y)) ->
    forall side, sb' L R side (Vis e k) (Vis f k').
  Proof.
    intros. split; intro; subst; apply step_ss'_vis_gen; auto.
    - cbn. intros. specialize (H4 side). now subs.
    - cbn. intros. specialize (H4 side). now subs.
  Qed.

  Lemma step_sb'_vis {Z Z'} (e : E Z) (f: F Z')
        (k : Z -> ctree E C X) (k' : Z' -> ctree F D Y) R :
    (forall x, exists y, (forall side, st' L R side (k x) (k' y)) /\ L (obs e x) (obs f y)) ->
    (forall y, exists x, (forall side, st' L R side (k x) (k' y)) /\ L (obs e x) (obs f y)) ->
    forall side, sbt' L R side (Vis e k) (Vis f k').
  Proof.
    intros * EQ.
    apply step_sb'_vis_gen; auto.
    typeclasses eauto.
  Qed.

  Lemma step_sb'_vis_id_gen {Z} (e : E Z) (f: F Z)
        (k : Z -> ctree E C X) (k' : Z -> ctree F D Y) R :
    (Proper (eq ==> equ eq ==> equ eq ==> impl) R) ->
    (forall x, (forall side, R side (k x) (k' x)) /\ L (obs e x) (obs f x)) ->
    forall side, sb' L R side (Vis e k) (Vis f k').
  Proof.
    intros. apply step_sb'_vis_gen; eauto.
  Qed.

  Lemma step_sb'_vis_id {Z} (e : E Z) (f: F Z)
        (k : Z -> ctree E C X) (k' : Z -> ctree F D Y) R :
    (forall x, (forall side, st' L R side (k x) (k' x)) /\ L (obs e x) (obs f x)) ->
    forall side, sbt' L R side (Vis e k) (Vis f k').
  Proof.
    intros * EQ.
    apply step_sb'_vis_id_gen; auto.
    typeclasses eauto.
  Qed.

  (*|
    When matching visible brs one against another, in general we need to explain how
    we map the branches from the left to the branches to the right.
    A useful special case is the one where the arity coincide and we simply use the identity
    in both directions. We can in this case have [n] rather than [2n] obligations.
    |*)
  Lemma step_sb'_brS_gen {Z Z'} (c : C Z) (d : D Z')
        (k : Z -> ctree E C X) (k' : Z' -> ctree F D Y) R :
    (Proper (eq ==> equ eq ==> equ eq ==> impl) R) ->
    (forall x, exists y, forall side, R side (k x) (k' y)) ->
    (forall y, exists x, forall side, R side (k x) (k' y)) ->
    L tau tau ->
    forall side, sb' L R side (BrS c k) (BrS d k').
  Proof.
    split; intros; subst; apply step_ss'_brS_gen; auto.
    all: cbn; intros; specialize (H5 side); now subs.
  Qed.

  Lemma step_sb'_brS {Z Z'} (c : C Z) (c' : D Z')
        (k : Z -> ctree E C X) (k' : Z' -> ctree F D Y) R :
    (forall x, exists y, forall side, st' L R side (k x) (k' y)) ->
    (forall y, exists x, forall side, st' L R side (k x) (k' y)) ->
    L tau tau ->
    forall side, sbt' L R side (BrS c k) (BrS c' k').
  Proof.
    intros.
    apply step_sb'_brS_gen; auto.
    typeclasses eauto.
  Qed.

  Lemma step_sb'_brS_id_gen {Z} (c : C Z) (d: D Z)
        (k: Z -> ctree E C X) (k': Z -> ctree F D Y) R :
    (Proper (eq ==> equ eq ==> equ eq ==> impl) R) ->
    (forall x side, R side (k x) (k' x)) ->
    L tau tau ->
    forall side, sb' L R side (BrS c k) (BrS d k').
  Proof.
    intros; apply step_sb'_brS_gen; eauto.
  Qed.

  Lemma step_sb'_brS_id {Z} (c : C Z) (d : D Z)
        (k: Z -> ctree E C X) (k': Z -> ctree F D Y) R :
    (forall x side, st' L R side (k x) (k' x)) ->
    L tau tau ->
    forall side, sbt' L R side (BrS c k) (BrS d k').
  Proof.
    intros.
    apply step_sb'_brS_id_gen; eauto.
    typeclasses eauto.
  Qed.

  (*|
    Same goes for visible tau nodes.
    |*)
  Lemma step_sb'_step_gen `{HasTau: B1 -< C} `{HasTau': B1 -< D}
        (t : ctree E C X) (t': ctree F D Y) R :
    (Proper (eq ==> equ eq ==> equ eq ==> impl) R) ->
    L tau tau ->
    (forall side, R side t t') ->
    forall side, sb' L R side (Step t) (Step t').
  Proof.
    split; intros; subst; apply step_ss'_step_gen; auto.
    all: cbn; intros; specialize (H4 side); now subs.
  Qed.

  Lemma step_sb'_step `{HasTau: B1 -< C} `{HasTau': B1 -< D}
        (t: ctree E C X) (t': ctree F D Y) R :
    (forall side, st' L R side t t') ->
    L tau tau ->
    forall side, sbt' L R side (Step t) (Step t').
  Proof.
    intros. apply step_sb'_step_gen; auto.
    typeclasses eauto.
  Qed.

  (*|
    With this definition [sb'] of bisimulation, delayed nodes allow to perform a coinductive step.
    |*)
  Lemma step_sb'_brD_gen {Z Z'} (a: C Z) (b: D Z')
    (k : Z -> ctree E C X) (k' : Z' -> ctree F D Y) R :
    (Proper (eq ==> equ eq ==> equ eq ==> impl) R) ->
    (forall x, exists y, forall side, R side (k x) (k' y)) ->
    (forall y, exists x, forall side, R side (k x) (k' y)) ->
    forall side, sb' L R side (BrD a k) (BrD b k').
  Proof.
    split; intros; apply step_ss'_brD_gen.
    - typeclasses eauto.
    - intros. destruct (H0 x). eauto.
    - typeclasses eauto.
    - intros. destruct (H1 x). cbn. eauto.
  Qed.

  Lemma step_sb'_brD {Z Z'} (cn: C Z) (cm: D Z')
    (k : Z -> ctree E C X) (k' : Z' -> ctree F D Y) R :
    (forall x, exists y, forall side, st' L R side (k x) (k' y)) ->
    (forall y, exists x, forall side, st' L R side (k x) (k' y)) ->
    forall side, sbt' L R side (BrD cn k) (BrD cm k').
  Proof.
    apply step_sb'_brD_gen. typeclasses eauto.
  Qed.

  Lemma step_sb'_brD_id_gen {Z} (c: C Z) (d: D Z)
        (k : Z -> ctree E C X) (k' : Z -> ctree F D Y) R :
    (Proper (eq ==> equ eq ==> equ eq ==> impl) R) ->
    (forall x side, R side (k x) (k' x)) ->
    forall side, sb' L R side (BrD c k) (BrD d k').
  Proof.
   intros. apply step_sb'_brD_gen; eauto.
  Qed.

  Lemma step_sb'_brD_id {Z} (c: C Z) (d: D Z)
    (k : Z -> ctree E C X) (k': Z -> ctree F D Y) R :
    (forall x side, st' L R side (k x) (k' x)) ->
    forall side, sbt' L R side (BrD c k) (BrD d k').
  Proof.
    apply step_sb'_brD_id_gen. typeclasses eauto.
  Qed.

  Lemma step_sb'_guard_gen `{HasTau: B1 -< C} `{HasTau': B1 -< D}
        (t: ctree E C X) (t': ctree F D Y) R :
    (Proper (eq ==> equ eq ==> equ eq ==> impl) R) ->
    (forall side, R side t t') ->
    forall side, sb' L R side (Guard t) (Guard t').
  Proof.
    intros. apply step_sb'_brD_id_gen; auto.
  Qed.

  Lemma step_sb'_guard `{HasTau: B1 -< C} `{HasTau': B1 -< D}
        (t: ctree E C X) (t': ctree F D Y) R :
    (forall side, st' L R side t t') ->
    forall side, sbt' L R side (Guard t) (Guard t').
  Proof.
    apply step_sb'_guard_gen. typeclasses eauto.
  Qed.

  Lemma step_sb'_guard_l `{HasTau: B1 -< C}
        (t: ctree E C X) (t': ctree F D Y) R :
    (forall side, sbt' L R side t t') ->
    forall side, sbt' L R side (Guard t) t'.
  Proof.
    split; intros; subst.
    - apply step_ss'_guard_l_gen. typeclasses eauto. step. apply H.
    - apply step_ss'_brD_r_gen; auto. now apply (H false).
  Qed.

  Lemma step_sb'_guard_r `{HasTau': B1 -< D}
        (t: ctree E C X) (t': ctree F D Y) R :
    (forall side, sbt' L R side t t') ->
    forall side, sbt' L R side t (Guard t').
  Proof.
    split; intros; subst.
    - apply step_ss'_brD_r_gen; auto. now apply (H true).
    - apply step_ss'_guard_l_gen. typeclasses eauto. step. apply H.
  Qed.

End Proof_Rules.


Lemma sbisim'_brD_l_inv {E F C D X Y Z L} `{HasB0 : B0 -< C} `{HasB0' : B0 -< D} (c : C Z) x
  (k : Z -> ctree E C X) (t' : ctree F D Y) :
  gfp (sb' L) true (BrD c k) t' ->
  gfp (sb' L) true (k x) t'.
Proof.
  intros. step. split; [| intros; discriminate].
  intros _.
  step in H. destruct H as [? _]. specialize (H eq_refl).
  destruct H as [_ ?].
  specialize (H Z c k). lapply H; auto. clear H. intro.
  destruct (H x) as (? & ? & ?).
  eapply step_ss'_epsilon_r_gen; [| apply H0].
  step in H1. now apply H1.
Qed.

Lemma sbisim'_brD_r_inv {E F C D X Y Z L} `{HasB0 : B0 -< C} `{HasB0' : B0 -< D} (c : D Z) x
  (k : Z -> ctree F D Y) (t : ctree E C X) :
  gfp (sb' L) false t (BrD c k) ->
  gfp (sb' L) false t (k x).
Proof.
  intros. step. split; [intros; discriminate |].
  intros _.
  step in H. destruct H as [_ ?]. specialize (H eq_refl).
  destruct H as [_ ?].
  specialize (H Z c k). lapply H; auto. clear H. intro.
  destruct (H x) as (? & ? & ?).
  eapply step_ss'_epsilon_r_gen; [| apply H0].
  step in H1. now apply H1.
Qed.


Section bind.
  Arguments label: clear implicits.
  Obligation Tactic := idtac.

  Context {E F C D: Type -> Type} {X X' Y Y': Type}
          `{HasStuck : B0 -< C} `{HasStuck' : B0 -< D}
          (L : hrel (@label E) (@label F)) (R0 : rel X X').

(*|
Specialization of [bind_ctx] to a function acting with [sbisim'] on the bound value,
and with the argument (pointwise) on the continuation.
|*)

  Definition bind_ctx3
             (R: bool -> rel (ctree E C X) (ctree F D X'))
             (S: rel (X -> ctree E C Y) (X' -> ctree F D Y')):
    bool -> rel (ctree E C Y) (ctree F D Y') := fun b => bind_ctx (R b) S.

  Lemma leq_bind_ctx3 :
    forall R S S', bind_ctx3 R S <= S' <->
    (forall b x x', R b x x' -> forall k k', S k k' -> S' b (bind x k) (bind x' k')).
  Proof.
    split; intros.
    - apply H. now apply in_bind_ctx.
    - intro. apply leq_bind_ctx. auto.
  Qed.

  Program Definition bind_ctx_sbisim' L0 : mon (bool -> rel (ctree E C Y) (ctree F D Y')) :=
    {| body := fun R => bind_ctx3 (gfp (sb' L0)) (pointwise R0 (fun x y => forall b, R b x y)) |}.
  Next Obligation.
    intros ?? ? H. apply leq_bind_ctx3. intros.
    apply in_bind_ctx; auto. red. intros. apply H. now apply H1.
  Qed.

(*|
    The resulting enhancing function gives a valid up-to technique
|*)
  Lemma bind_ctx_sbisim'_t L0 :
    is_update_val_rel L R0 L0 -> bind_ctx_sbisim' L0 <= t (sb' L).
  Proof.
    intro HL0. apply Coinduction.
    red. red. red. intros.
    apply leq_bind_ctx3.
    intros b t1 t2 tt k1 k2 kk.
    split; intros; subst; split.
    - simpl; intros PROD l u STEP.
      apply trans_bind_inv in STEP as [(H & t' & STEP & EQ) | (v & STEPres & STEP)].
      step in tt.
      apply tt in STEP as (l' & u' & STEP & EQ' & ?); auto.
      2: { now apply productive_bind in PROD. }
      do 2 eexists. split; [| split].
      apply trans_bind_l; eauto.
      + intro Hl. destruct Hl.
        apply HL0 in H0; etrans.
        inversion H0; subst. apply H. constructor. apply H2. constructor.
      + intro. apply (fT_T equ_clos_st').
          econstructor; [exact EQ | | reflexivity].
          apply (fTf_Tf (sb' L)). Opaque bind_ctx. cbn.
          apply in_bind_ctx; auto.
          intros ? ? ? ?.
          apply (b_T (sb' L)).
          red in kk; apply kk. eassumption.
      + apply HL0 in H0; etrans.
        destruct H0. exfalso. apply H. constructor. apply H2.
      + assert (t1 ≅ Ret v).
        { apply productive_bind in PROD. apply trans_val_epsilon in STEPres as [? _].
          now apply productive_epsilon. } subs.
        step in tt.
        apply tt in STEPres as (l' & u' & STEPres & EQ' & ?); auto.
        2: now eapply prod_ret.
        apply HL0 in H; etrans.
        dependent destruction H. 2: { exfalso. apply H. constructor. }
        pose proof (trans_val_inv STEPres) as EQ.
        rewrite EQ in STEPres.
        specialize (kk v v2 H true).
        rewrite bind_ret_l in PROD.
        apply kk in STEP as (? & u''' & STEP & EQ'' & ?); auto.
        do 2 eexists; split.
        eapply trans_bind_r; eauto.
        split; auto.
        intros. eapply (id_T (sb' L)). apply EQ''.
    - intros Z c k EQ z.
      apply br_equ_bind in EQ as EQ'. destruct EQ' as [(v & EQ') | (k0 & EQ' & EQ'')].
      + subs. step in tt. destruct tt as [tt _]. specialize (tt eq_refl). destruct tt as [tt _].
        edestruct tt as (l & t'' & STEPres & _ & ?); etrans.
        apply HL0 in H; etrans.
        apply update_val_rel_val_l in H as (v' & -> & EQ').
        rewrite bind_ret_l in EQ.
        specialize (kk v v' EQ' true).
        apply kk with (x := z) in EQ; auto. destruct EQ as (u' & EPS & EQ).
        exists u'.
        apply trans_val_epsilon in STEPres as [? _]. split.
        * eapply epsilon_bind; eassumption.
        * now apply (id_T (sb' L)).
      + subs. setoid_rewrite EQ''. clear k EQ EQ''.
        eexists. split. reflexivity.
        apply (fTf_Tf (sb' L)). apply in_bind_ctx.
        step. split; [| intros; discriminate].
        intros _. simple apply sbisim'_brD_l_inv with (x := z) in tt.
        step in tt. now apply tt.
        red. intros. apply (b_T (sb' L)). now apply kk.
    - simpl; intros PROD l u STEP.
      apply trans_bind_inv in STEP as [(H & t' & STEP & EQ) | (v & STEPres & STEP)].
      step in tt.
      apply tt in STEP as (l' & u' & STEP & EQ' & ?); auto.
      2: { now apply productive_bind in PROD. }
      do 2 eexists. split; [| split].
      apply trans_bind_l; eauto.
      + intro Hl. destruct Hl.
        apply HL0 in H0; etrans.
        inversion H0; subst. apply H. constructor. apply H1. constructor.
      + intro. apply (fT_T equ_clos_st').
          econstructor; [reflexivity | | now rewrite EQ].
          apply (fTf_Tf (sb' L)). Opaque bind_ctx. cbn.
          apply in_bind_ctx; auto.
          intros ? ? ? ?.
          apply (b_T (sb' L)).
          red in kk; apply kk. eassumption.
      + apply HL0 in H0; etrans.
        destruct H0. exfalso. apply H. constructor. apply H2.
      + assert (t2 ≅ Ret v).
        { apply productive_bind in PROD. apply trans_val_epsilon in STEPres as [? _].
          now apply productive_epsilon. } subs.
        step in tt.
        apply tt in STEPres as (l' & u' & STEPres & EQ' & ?); auto.
        2: now eapply prod_ret.
        apply HL0 in H; etrans.
        dependent destruction H. 2: { exfalso. apply H0. constructor. }
        pose proof (trans_val_inv STEPres) as EQ.
        rewrite EQ in STEPres.
        specialize (kk v1 v H false).
        rewrite bind_ret_l in PROD.
        apply kk in STEP as (? & u''' & STEP & EQ'' & ?); auto.
        do 2 eexists; split.
        eapply trans_bind_r; eauto.
        split; auto.
        intros. eapply (id_T (sb' L)). apply EQ''.
    - intros Z c k EQ z.
      apply br_equ_bind in EQ as EQ'. destruct EQ' as [(v & EQ') | (k0 & EQ' & EQ'')].
      + subs. step in tt. destruct tt as [_ tt]. specialize (tt eq_refl). destruct tt as [tt _].
        edestruct tt as (l & t'' & STEPres & _ & ?); etrans.
        apply HL0 in H; etrans.
        apply update_val_rel_val_r in H as (v' & -> & EQ').
        rewrite bind_ret_l in EQ.
        specialize (kk v' v EQ' false).
        apply kk with (x := z) in EQ; auto. destruct EQ as (u' & EPS & EQ).
        exists u'.
        apply trans_val_epsilon in STEPres as [? _]. split.
        * eapply epsilon_bind; eassumption.
        * now apply (id_T (sb' L)).
      + subs. setoid_rewrite EQ''. clear k EQ EQ''.
        eexists. split. reflexivity.
        apply (fTf_Tf (sb' L)). apply in_bind_ctx.
        step. split; [intros; discriminate |].
        intros _. apply sbisim'_brD_r_inv with (x := z) in tt.
        step in tt. now apply tt.
        red. intros. apply (b_T (sb' L)). now apply kk.
  Qed.

End bind.

(*|
Expliciting the reasoning rule provided by the up-to principles.
|*)
Lemma st'_clo_bind {E F C D: Type -> Type} {X Y X' Y': Type} {L : rel (@label E) (@label F)}
      `{HasStuck: B0 -< C} `{HasStuck': B0 -< D}
      R0 L0 b
      (t1 : ctree E C X) (t2: ctree F D X')
      (HL0 : is_update_val_rel L R0 L0)
      (k1 : X -> ctree E C Y) (k2 : X' -> ctree F D Y') RR:
  gfp (sb' L0) b t1 t2 ->
  (forall x y, R0 x y -> forall b, (st' L RR) b (k1 x) (k2 y)) ->
  st' L RR b (t1 >>= k1) (t2 >>= k2).
Proof.
  intros ? ?.
  apply (ft_t (@bind_ctx_sbisim'_t E F C D X X' Y Y' _ _ L R0 L0 HL0)).
  apply in_bind_ctx; eauto.
Qed.

Lemma sbt'_clo_bind {E F C D: Type -> Type} {X Y X' Y': Type} {L : rel (@label E) (@label F)}
      `{HasStuck: B0 -< C} `{HasStuck': B0 -< D}
      R0 L0 b
      (t1 : ctree E C X) (t2: ctree F D X')
      (HL0 : is_update_val_rel L R0 L0)
      (k1 : X -> ctree E C Y) (k2 : X' -> ctree F D Y') RR:
  gfp (sb' L0) b t1 t2 ->
  (forall x y, R0 x y -> forall b, (sbt' L RR) b (k1 x) (k2 y)) ->
  sbt' L RR b (t1 >>= k1) (t2 >>= k2).
Proof.
  intros ? ?.
  apply (fbt_bt (@bind_ctx_sbisim'_t E F C D X X' Y Y' _ _ L R0 L0 HL0)).
  apply in_bind_ctx; eauto.
Qed.

Lemma step_sb'_guard_l' {E F C D X Y L}
  `{HasB0: B0 -< C} `{HasB0': B0 -< D} `{HasB1: B1 -< C}
  (t: ctree E C X) (t': ctree F D Y) R :
  (forall side, st' L R side t t') ->
  forall side, st' L R side (Guard t) t'.
Proof.
  intros.
  assert (st' L R side (Guard (Ret tt);; t) (Ret tt;; t')).
  - eapply st'_clo_bind with (R0 := fun _ _ => True).
    + apply update_val_rel_correct.
    + step. apply step_sb'_guard_l. intro. apply step_sb'_ret. now constructor.
    + intros. apply H.
  - rewrite bind_guard in H0.
    unfold Guard in H0. setoid_rewrite bind_ret_l in H0. apply H0.
Qed.

Lemma step_sb'_guard_r' {E F C D X Y L}
  `{HasB0: B0 -< C} `{HasB0': B0 -< D} `{HasB1: B1 -< D}
  (t: ctree E C X) (t': ctree F D Y) R :
  (forall side, st' L R side t t') ->
  forall side, st' L R side t (Guard t').
Proof.
  intros.
  assert (st' L R side (Ret tt;; t) (Guard (Ret tt);; t')).
  - eapply st'_clo_bind with (R0 := fun _ _ => True).
    + apply update_val_rel_correct.
    + step. apply step_sb'_guard_r. intro. apply step_sb'_ret. now constructor.
    + intros. apply H.
  - rewrite bind_guard in H0.
    unfold Guard in H0. setoid_rewrite bind_ret_l in H0. apply H0.
Qed.

(*
Tactic Notation "__upto_bind_sbisim'" uconstr(R0) := TODO
Tactic Notation "__upto_bind_eq_sbisim'" uconstr(R0) := TODO
*)
