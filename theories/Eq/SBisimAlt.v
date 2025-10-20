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
     Eq.Epsilon
     Eq.SSimAlt
     Misc.Pure.

From RelationAlgebra Require Export
     rel srel.

Import CoindNotations.
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

Section Symmetry.

  Program Definition sb'l {E F C D X Y} L :
    mon (bool -> rel (ctree E C X) (ctree F D Y)) :=
    {| body R side t u := side = true -> sb' L R side t u |}.
  Next Obligation.
      eapply (Hbody (sb' L)).
      2: { specialize (H0 eq_refl). apply H0. }
      cbn. apply H.
  Qed.

  Program Definition converse_neg {A : Type} : mon (bool -> relation A) :=
  {| body := fun (R : bool -> rel A A) b (x y : A) => R (negb b) y x |}.

  #[global] Instance converse_neg_invol {A} : Involution (@converse_neg A).
  Proof.
    cbn. intros.
    now rewrite Bool.negb_involutive.
  Qed.

  #[global] Instance sbisim'_sym {E C X L} :
    `{Symmetric L} ->
    Symmetrical converse_neg (@sb' E E C C X X L) (sb'l L).
  Proof.
    intros SYM.
    assert (HL: L == flip L). { cbn. intuition. }
    eapply weq_ss'_gen in HL.
    cbn -[sb']. split; intros.
    - split; cbn -[sb']; intro.
      + apply H.
      + intros. apply Bool.negb_true_iff in H0. subst.
        destruct H as [_ ?].
        specialize (H eq_refl).
        apply HL in H.
        split; intros; subst; try discriminate.
        eapply ss'_gen_mon. 3: now apply H.
        * cbn. intros. apply H1.
        * cbn. intros. apply H1.
    - split; intros; subst.
      + now apply H.
      + intros.
        apply HL.
        eapply ss'_gen_mon. 3: now apply H.
        * cbn. intros.
          specialize (H0 (negb side)).
          rewrite Bool.negb_involutive in H0. apply H0.
        * cbn. intros. apply H0.
  Qed.

End Symmetry.

Lemma sb'_flip {E F C D X Y L}
    side (t: ctree E C X) (u: ctree F D Y) R :
  sb' (flip L) (fun b => flip (R (negb b))) (negb side) u t ->
  sb' L R side t u.
Proof.
  split; intros; subst; destruct H; cbn in H.
  - specialize (H0 eq_refl).
    cbn -[ss'_gen] in H0. unfold flip in H0.
    eapply (ss'_gen_mon (x := fun t u => forall side, R (negb side) t u)).
    { cbn. intros. specialize (H1 (negb side)). rewrite Bool.negb_involutive in H1. apply H1. }
    { cbn. intros. apply H1. }
    apply H0.
  - specialize (H eq_refl).
    cbn -[ss'_gen] in H.
    eapply (ss'_gen_mon (x := fun t u => forall side, R (negb side) u t)).
      { cbn. intros. specialize (H1 (negb side)). rewrite Bool.negb_involutive in H1. apply H1. }
      { cbn. intros. apply H1. }
      apply H.
Qed.

Definition sbisim' {E F C D X Y} L t u :=
  forall side, gfp (@sb' E F C D X Y L) side t u.

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
  Context {E F C D: Type -> Type} {X Y: Type}
          {L: rel (@label E) (@label F)}.

(*|
   Strong bisimulation up-to [equ] is valid
   ----------------------------------------
|*)
  #[global] Instance equ_clos3_equ (R : bool -> rel (ctree E C X) (ctree F D Y)) :
  Proper (eq ==> equ eq ==> equ eq ==> impl) (lift_rel3 equ_clos R).
  Proof.
    cbn. intros. destruct H2.
    (* Can this be faster? *)
    econstructor; subs. 2: subst; eassumption.
    now rewrite H0. assumption.
  Qed.

  Lemma equ_clos_sb' {c: Chain (@sb' E F C D X Y L)}:
    forall b x y, lift_rel3 equ_clos `c b x y -> `c b x y.
  Proof.
    apply tower.
    - intros ? INC side x y [x' y' x'' y'' EQ' EQ''] ??. red.
      apply INC; auto.
      econstructor; eauto.
      apply leq_infx in H.
      now apply H.
    - clear.
      intros R IH side x y [x' y' x'' y'' EQ' EQ''].
      split; [destruct EQ'' as [EQ'' _] | destruct EQ'' as [_ EQ'']];
        intros; subst; specialize (EQ'' eq_refl); subs.
      + eapply ss'_gen_mon. 3: apply EQ''.
        all: auto.
      + eapply ss'_gen_mon. 3: apply EQ''.
        all: eauto.
  Qed.

  #[global] Instance equ_clos_gfp_sb'_goal : forall side, Proper (equ eq ==> equ eq ==> flip impl) (gfp (@sb' E F C D X Y L) side).
  Proof.
    cbn; intros ? ? ? eq1 ? ? eq2 H.
    apply equ_clos_sb'; econstructor; eauto.
    now symmetry.
  Qed.

  #[global] Instance equ_clos_gfp_sb'_ctx : forall side, Proper (equ eq ==> equ eq ==> impl) (gfp (@sb' E F C D X Y L) side).
  Proof.
    cbn; intros ? ? ? eq1 ? ? eq2 H. now subs.
  Qed.

  #[global] Instance equ_clos_sbisim'_goal : Proper (equ eq ==> equ eq ==> flip impl) (@sbisim' E F C D X Y L).
  Proof.
    cbn; intros ? ? eq1 ? ? eq2 H.
    intro. now subs.
  Qed.

  #[global] Instance equ_clos_sbisim'_ctx : Proper (equ eq ==> equ eq ==> impl) (@sbisim' E F C D X Y L).
  Proof.
    cbn; intros ? ? eq1 ? ? eq2 H. now subs.
  Qed.

End sbisim'_theory.

(* TODO check *)
Ltac fold_sbisim' :=
  repeat
    match goal with
    | h: context[gfp (@sb' ?E ?F ?C ?D ?X ?Y ?L)] |- _ => try fold (@sbisim' E F C D X Y L) in h
    | |- context[gfp (@sb' ?E ?F ?C ?D ?X ?Y ?L)]      => try fold (@sbisim' E F C D X Y L)
    end.

Tactic Notation "__coinduction_sbisim'" simple_intropattern(r) simple_intropattern(cih) :=
  first [unfold sbisim' at 4 | unfold sbisim' at 3 | unfold sbisim' at 2 | unfold sbisim' at 1]; coinduction r cih.

Tactic Notation "__step_sbisim'" :=
  match goal with
  | |- context[@sbisim' ?E ?F ?C ?D ?X ?Y ?LR] =>
      unfold sbisim';
      intro; step
  end.

Tactic Notation "step" := __step_sbisim' || step.

Tactic Notation "coinduction" simple_intropattern(R) simple_intropattern(H) :=
  __coinduction_sbisim' R H || coinduction R H.

Ltac __step_in_sbisim' H :=
  match type of H with
  | context[@sbisim' ?E ?F ?C ?D ?X ?Y ?LR] =>
      unfold sbisim' in H;
      let Hl := fresh H "l" in
      let Hr := fresh H "r" in
      pose proof (Hl : H true);
      pose proof (Hr : H false);
      step in Hl; step in Hr;
      try fold (@sbisim' E F C D X Y L) in Hl;
      try fold (@sbisim' E F C D X Y L) in Hr
  end.

Tactic Notation "step" "in" ident(H) := __step_in_sbisim' H || step in H.

Import CTreeNotations.
Import EquNotations.
Section sbisim'_homogenous_theory.
  Context {E B: Type -> Type} {X: Type}
          {L: relation (@label E)}.

  Notation sb' := (@sb' E E B B X X).
  Notation sbisim' := (@sbisim' E E B B X X).

  #[global] Instance refl_sb' {LR: Reflexive L} {C: Chain (sb' L)}
    : forall side, Reflexive (`C side).
  Proof.
    apply tower.
    - cbv. firstorder.
    - intros R IH ? x.
      split; (intros; subst; split; [| split]; intros).
      1,4: eexists _, _; eauto.
      1,3:eexists; split; subs; [| reflexivity]; eapply epsilon_br; eauto.
      all:eexists; split; subs; [| reflexivity]; eapply epsilon_guard; eauto.
  Qed.

  #[global] Instance refl_bsb' {LR: Reflexive L} {C: Chain (sb' L)}
    : forall side, Reflexive (sb' L `C side).
  Proof.
    intros ??.
    apply refl_sb'.
  Qed.

  #[global] Instance refl_sbisim' {LR: Reflexive L}
    : Reflexive (sbisim' L).
  Proof.
    intros ??; apply refl_sb'.
  Qed.

  Lemma sym_sb {LT: Symmetric L} {C: Chain (sb' L)} :
    forall side x y, `C (negb side) x y -> `C side y x.
  Proof.
    apply tower.
    - cbv. firstorder.
    - clear C.
      intros R IH ? x y EQC.
      split; intros EQ.
      + subst.
        destruct EQC as [_ EQC]; specialize (EQC eq_refl).
        eapply (weq_ss'_gen (x := L)) in EQC. 2: { split; apply LT. }
        eapply ss'_gen_mon.
        3:apply EQC.
        { cbn. intros. apply IH; auto. }
        { cbn. intros. apply IH, H. }
      + subst.
        destruct EQC as [EQC _]; specialize (EQC eq_refl).
        eapply (weq_ss'_gen (x := flip L)) in EQC. 2: { split; apply LT. }
        eapply ss'_gen_mon.
        3:apply EQC.
        { cbn. intros. apply IH, H. }
        { cbn. intros. apply IH, H. }
  Qed.

  Lemma st'_flip `{SL: Symmetric _ L} {C: Chain (sb' L)}:
    forall b t u,
    `C b t u <-> `C (negb b) u t.
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

Lemma split_st' : forall {E B X L} `{SL: Symmetric _ L} (t u : ctree E B X)
                    {C: Chain (sb' L)},
    (forall side, `C side t u) <->
      `C true t u /\ `C true u t.
Proof.
  intros. split; intros.
  - split; auto.
    apply st'_flip. apply H.
  - destruct side; [apply H |].
    now apply st'_flip.
Qed.

Lemma split_st'_eq : forall {E B X} (t u : ctree E B X) {C: Chain (sb' eq)},
    (forall side, `C side t u) <->
      `C true t u /\ `C true u t.
Proof.
  intros. apply split_st'.
Qed.

Section sbisim'_heterogenous_theory.
  Arguments label: clear implicits.
  Context {E F B D: Type -> Type} {X Y: Type}
          {L: rel (@label E) (@label F)}.

  Notation sb' := (@sb' E F B D X Y).
  Notation sbisim'  := (@sbisim' E F B D X Y).

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

  #[global] Instance equ_clos_st'_goal {RR} {C : Chain (sb' RR)}:
    Proper (eq ==> equ eq ==> equ eq ==> flip impl) `C.
  Proof.
    cbn; intros ? ? ? ? ? eq1 ? ? eq2 H. subst.
    apply equ_clos_sb'; econstructor; [eauto | | symmetry; eauto]; assumption.
  Qed.

  #[global] Instance equ_clos_st'_ctx {RR} {C : Chain (sb' RR)}:
    Proper (eq ==> equ eq ==> equ eq ==> impl) `C.
  Proof.
    cbn; intros ? ? ? ? ? eq1 ? ? eq2 H. subst.
    now rewrite <- eq1, <- eq2.
  Qed.

  Lemma sb'_true_ss' R :
    forall (t : ctree E B X) (u : ctree F D Y),
    sb' L R true t u <-> ss'_gen L (fun t u => forall side, R side t u) (R true) t u.
  Proof.
    split; intros.
    - now apply H.
    - split; intros; try discriminate. apply H.
  Qed.

  Lemma sb'_false_ss' R :
    forall (t : ctree E B X) (u : ctree F D Y),
    sb' L R false t u <-> ss'_gen (flip L) (fun u t => forall side, R side t u) (flip (R false)) u t.
  Proof.
    split; intros.
    - now apply H.
    - split; intros; try discriminate. apply H.
  Qed.

  Lemma sb'_true_stuck R :
    forall (u : ctree F D Y),
    sb' L R true Stuck u.
  Proof.
    intros. apply sb'_true_ss'.
    apply ss'_stuck.
  Qed.

End sbisim'_heterogenous_theory.

Lemma sb'_stuck {E F C D X Y L}   R :
  forall side,
    sb' L R side (Stuck : ctree E C X) (Stuck : ctree F D Y).
Proof.
  intros. destruct side.
  - apply sb'_true_stuck.
  - apply sb'_flip. cbn -[sb']. apply sb'_true_stuck.
Qed.

Section Proof_Rules.

  Arguments label: clear implicits.
  Context {E F C D: Type -> Type}
          {X Y: Type}
          {L : rel (@label E) (@label F)}.

  Lemma step_sb'_ret :
    forall {R : _ -> rel _ _} {HR: Proper (eq ==> equ eq ==> equ eq ==> impl) R}
      x y,
      L (val x) (val y) ->
      (forall side, R side Stuck Stuck) ->
      forall side, sb' L R side (Ret x : ctree E C X) (Ret y : ctree F D Y).
  Proof.
    intros R HR x y Rstuck PROP Lval. split; intros; subst.
    - unshelve eapply step_ss'_ret; auto.
      cbn. intros. rewrite <- H. specialize (H1 side). now subs.
    - unshelve eapply step_ss'_ret; auto.
      cbn. intros. specialize (H1 side). now subs.
  Qed.

  Lemma step_sbt'_ret x y {R : Chain (sb' L)} :
    L (val x) (val y) ->
    forall side, `R side (Ret x : ctree E C X) (Ret y : ctree F D Y).
  Proof.
    intros. step; apply step_sb'_ret.
    - exact H.
    - intros. step; apply sb'_stuck.
  Qed.

(*|
 The vis nodes are deterministic from the perspective of the labeled
 transition system, stepping is hence symmetric and we can just recover
 the itree-style rule.
|*)
  Lemma step_sb'_vis
    {R : _ -> rel _ _} {HR: Proper (eq ==> equ eq ==> equ eq ==> impl) R}
    {Z Z'} (e : E Z) (f: F Z')
        (k : Z -> ctree E C X) (k' : Z' -> ctree F D Y) :
    (forall x, exists y, (forall side, R side (k x) (k' y)) /\ L (obs e x) (obs f y)) ->
    (forall y, exists x, (forall side, R side (k x) (k' y)) /\ L (obs e x) (obs f y)) ->
    forall side, sb' L R side (Vis e k) (Vis f k').
  Proof.
    intros. split; intro; subst; unshelve eapply step_ss'_vis; auto.
    - cbn. intros. specialize (H3 side). now subs.
    - cbn. intros. specialize (H3 side). now subs.
  Qed.

  Lemma step_sb'_vis_id
    {R : _ -> rel _ _} {HR: Proper (eq ==> equ eq ==> equ eq ==> impl) R}
    {Z} (e : E Z) (f: F Z)
        (k : Z -> ctree E C X) (k' : Z -> ctree F D Y) :
    (forall x, (forall side, R side (k x) (k' x)) /\ L (obs e x) (obs f x)) ->
    forall side, sb' L R side (Vis e k) (Vis f k').
  Proof.
    intros. apply step_sb'_vis; eauto.
  Qed.

  Lemma step_sb'_vis_l
    {R : _ -> rel _ _} {HR: Proper (eq ==> equ eq ==> equ eq ==> impl) R} {Z} :
    forall (e : E Z) (k : Z -> ctree E C X) (u : ctree F D Y),
      (forall x, exists l' u', trans l' u u' /\ (forall side, R side (k x) u') /\ L (obs e x) l') ->
      sb' L R true (Vis e k) u.
  Proof.
    split; intros; subst; try discriminate.
    unshelve eapply step_ss'_vis_l.
    - cbn. intros. specialize (H3 side). now subs.
    - apply H.
  Qed.

(*|
  With this definition [sb'] of bisimulation, delayed nodes allow to perform a coinductive step.
|*)
   Lemma step_sb'_guard
    {R : _ -> rel _ _} {HR: Proper (eq ==> equ eq ==> equ eq ==> impl) R}
    (t: ctree E C X) (t': ctree F D Y) side :
      R side t t' ->
      sb' L R side (Guard t) (Guard t').
  Proof.
    split; intros; subst; apply step_ss'_guard; auto.
  Qed.

  Lemma step_sb'_true_guard_l
    {R : Chain (sb' L)}
    (t: ctree E C X) (t': ctree F D Y) :
    ` R true t t' ->
    sb' L `R true (Guard t) t'.
  Proof.
    intros.
    split; intros; subst; try discriminate.
    now apply step_ss'_guard_l.
  Qed.

  Lemma step_sb'_guard_l
    {R : Chain (sb' L)}
    (t: ctree E C X) (t': ctree F D Y) side :
    sb' L (` R) side t t' ->
    sb' L `R side (Guard t) t'.
  Proof.
    intros.
    split; intros; subst.
    - apply step_ss'_guard_l; now step.
    - apply step_ss'_guard_r; now apply H.
  Qed.

  Lemma step_sb'_false_guard_r
    {R : Chain (sb' L)}
    (t: ctree E C X) (t': ctree F D Y) :
    ` R false t t' ->
    sb' L `R false t (Guard t').
  Proof.
    intros.
    split; intros; subst; try discriminate.
    now apply step_ss'_guard_l.
  Qed.

  Lemma step_sb'_guard_r
    {R : Chain (sb' L)}
    (t: ctree E C X) (t': ctree F D Y) side :
    sb' L (` R) side t t' ->
    sb' L `R side t (Guard t').
  Proof.
    intros.
    split; intros; subst.
    - apply step_ss'_guard_r; auto. now apply H.
    - apply step_ss'_guard_l; red; now step.
  Qed.

  Lemma step_sb'_br
    {R : _ -> rel _ _} {HR: Proper (eq ==> equ eq ==> equ eq ==> impl) R}
    {Z Z'} (a: C Z) (b: D Z')
    (k : Z -> ctree E C X) (k' : Z' -> ctree F D Y) side :
    (forall x, exists y, R side (k x) (k' y)) ->
    (forall y, exists x, R side (k x) (k' y)) ->
    sb' L R side (Br a k) (Br b k').
  Proof.
    split; intros; subst; apply step_ss'_br.
    - intros. destruct (H x). eauto.
    - intros. destruct (H0 x). cbn. eauto.
  Qed.

  Lemma step_sb'_br_id
    {R : _ -> rel _ _} {HR: Proper (eq ==> equ eq ==> equ eq ==> impl) R}
    {Z} (c: C Z) (d: D Z)
    (k : Z -> ctree E C X) (k' : Z -> ctree F D Y) side :
    (forall x, R side (k x) (k' x)) ->
    sb' L R side (Br c k) (Br d k').
  Proof.
    intros. apply step_sb'_br; eauto.
  Qed.

  Lemma step_sb'_true_br_l {R : Chain (sb' L)} {Z} :
    forall (c : C Z) (k : Z -> ctree E C X) (u : ctree F D Y),
    (forall x, `R true (k x) u) ->
    sb' L `R true (Br c k) u.
  Proof.
    intros; split; intros; subst; try discriminate.
    now apply step_ss'_br_l.
  Qed.

  Lemma step_sb'_br_l {R : Chain (sb' L)} {Z} :
    forall (c : C Z) (z : Z) (k : Z -> ctree E C X) (u : ctree F D Y) side,
    (forall x, sb' L `R side (k x) u) ->
    sb' L `R side (Br c k) u.
  Proof.
    intros; split; intros; subst.
    - apply step_ss'_br_l; intros; now step.
    - apply step_ss'_br_r with z; now apply H.
  Qed.

(*|
  Step
|*)
  Lemma step_sb'_step
    {R : _ -> rel _ _} {HR: Proper (eq ==> equ eq ==> equ eq ==> impl) R}
    (t : ctree E C X) (t': ctree F D Y) :
    L τ τ ->
    (forall side, R side t t') ->
    forall side, sb' L R side (Step t) (Step t').
  Proof.
    split; intros.
    unshelve eapply step_ss'_step; eauto.
    repeat intro; eapply HR; eauto.
    unshelve eapply step_ss'_step; eauto.
    repeat intro; eapply HR; eauto.
  Qed.

  (* Lemma step_sb'_brS_l *)
  (*   {R : Chain (sb' L)} : *)
  (*   forall (t : ctree E C X) (u : ctree F D Y), *)
  (*     (exists l' u', trans l' u u' /\ (forall side, `R side t u') /\ L τ l') -> *)
  (*     `R true (Step t) u. *)
  (* Proof. *)
  (*   intros. *)
  (*   step; split; intros. *)
  (*   - eapply step_ss'_step_l. apply step_ss'_gen_step_l. *)
  (*   apply step_sb'_br_l; intros. *)

End Proof_Rules.

(*|
    When matching visible brs one against another, in general we need to explain how
    we map the branches from the left to the branches to the right.
    A useful special case is the one where the arity coincide and we simply use the identity
    in both directions. We can in this case have [n] rather than [2n] obligations.
|*)
Lemma step_sb'_brS {E F C D X Y L}
  {R : Chain (sb' L)}
  {Z Z'} (c : C Z) (d : D Z')
  (k : Z -> ctree E C X) (k' : Z' -> ctree F D Y) :
  (forall x, exists y, forall side, `R side (k x) (k' y)) ->
  (forall y, exists x, forall side, `R side (k x) (k' y)) ->
  L τ τ ->
  forall side, sb' L `R side (BrS c k) (BrS d k').
Proof.
  intros.
  eapply step_sb'_br; auto.
  intros x; destruct (H x) as [z ?]; exists z.
  step. apply step_sb'_step; auto.
  intros x; destruct (H0 x) as [z ?]; exists z.
  step. apply step_sb'_step; auto.
Qed.

Lemma step_sb'_brS_id {E F C D X Y L}
  {R : Chain (sb' L)}
  {Z} (c : C Z) (d: D Z)
  (k: Z -> ctree E C X) (k': Z -> ctree F D Y) :
  L τ τ ->
  (forall x side, `R side (k x) (k' x)) ->
  forall side, sb' L `R side (BrS c k) (BrS d k').
Proof.
  intros; apply step_sb'_br_id; eauto.
  intros; step; apply step_sb'_step; auto.
Qed.

Lemma step_sb'_true_step_l {E F C D X Y L}
  {R : Chain (sb' L)} :
  forall (t : ctree E C X) (u : ctree F D Y),
    (exists l' u', trans l' u u' /\ (forall side, `R side t u') /\ L τ l') ->
    sb' L `R true (Step t) u.
Proof.
  intros.
  split; intros; try congruence.
  - unshelve eapply step_ss'_step_l; eauto.
    repeat intro; eauto.
    now rewrite <-H1,<-H2.
Qed.

Lemma step_sb'_true_brS_l {E F C D X Y L}
  {R : Chain (sb' L)}
  {Z} :
  forall (c : C Z) (k : Z -> ctree E C X) (u : ctree F D Y),
    (forall x, exists l' u', trans l' u u' /\ (forall side, `R side (k x) u') /\ L τ l') ->
    sb' L `R true (BrS c k) u.
Proof.
  intros.
  apply step_sb'_true_br_l; intros.
  step. apply step_sb'_true_step_l; intros.
  eauto.
Qed.

Section Inversion_Rules.

  Context {E F C D: Type -> Type}
          {X Y: Type}.
  Variable (L : rel (@label E) (@label F)).

  (* Lemmas to exploit sb' and sbisim' hypotheses *)
  (* TODO incomplete *)

  Lemma sb'_true_vis_inv {Z Z' R} :
    forall (e : E Z) (f : F Z') (k : Z -> ctree E C X) (k' : Z' -> ctree F D Y),
    (Proper (eq ==> equ eq ==> equ eq ==> impl) R) ->
    sb' L R true (Vis e k) (Vis f k') ->
    forall x, exists y, (forall side, R side (k x) (k' y)) /\ L (obs e x) (obs f y).
  Proof.
    intros.
    pose proof (trans_vis e x k).
    apply H0 in H1; etrans.
    destruct H1 as (? & ? & ? & ? & ?). inv_trans. subst.
    setoid_rewrite EQ in H2. etrans.
  Qed.

  Lemma sb'_true_vis_l_inv {Z R} :
    forall (e : E Z) (k : Z -> ctree E C X) (u : ctree F D Y) x,
    sb' L R true (Vis e k) u ->
    exists l' u', trans l' u u' /\ (forall side, R side (k x) u') /\ L (obs e x) l'.
  Proof.
    intros. apply sb'_true_ss' in H.
    now apply ss'_vis_l_inv with (x := x) in H.
  Qed.

  (* Lemma sbt'_true_brS_inv {R : Chain (sb' L)} *)
  (*   {Z Z'} : *)
  (*   forall (c : C Z) (c' : D Z') (k : Z -> ctree E C X) (k' : Z' -> ctree F D Y), *)
  (*   ` R true (BrS c k) (BrS c' k') -> *)
  (*   forall x, exists y, forall side, `R side (k x) (k' y). *)
  (* Proof. *)
  (*   intros. *)
  (*   pose proof (trans_brS c k x). *)
  (*   destruct H0 as [SB _]; specialize (SB eq_refl). *)
  (*   destruct SB as (SBA & SBB & SBC). *)
  (*   unshelve edestruct SBB as (u' & EPS & HR); try reflexivity; [exact x |]. *)
  (*   cbn in HR. *)
  (*   inv EPS. *)
  (*   apply SBB in H1; etrans. *)
  (*   destruct H1 as (? & ? & ? & ? & ?). inv_trans. subst. *)
  (*   setoid_rewrite EQ in H2. etrans. *)
  (* Qed. *)

  (* Lemma sb'_true_brS_l_inv {Z R} : *)
  (*   forall (c : C Z) (k : Z -> ctree E C X) (u : ctree F D Y) x, *)
  (*   sb' L R true (BrS c k) u -> *)
  (*   exists l' u', trans l' u u' /\ (forall side, R side (k x) u') /\ L τ l'. *)
  (* Proof. *)
  (*   intros. apply sb'_true_ss' in H. *)
  (*   now apply ss'_brS_l_inv with (x := x) in H. *)
  (* Qed. *)

  Lemma sb'_eq_vis_invT {Z Z' R} :
    forall side (e : E Z) (f : E Z') (k : Z -> ctree E C X) (k' : Z' -> ctree E D Y),
    sb' eq R side (Vis e k) (Vis f k') ->
    forall (x : Z) (x' : Z'), Z = Z'.
  Proof.
    intros. destruct side.
    + pose proof (trans_vis e x k).
      apply H in H0; etrans.
      destruct H0 as (? & ? & ? & ? & ?). inv_trans. subst.
      now apply obs_eq_invT in H2 as ?.
    + pose proof (trans_vis f x' k').
      apply H in H0; etrans.
      destruct H0 as (? & ? & ? & ? & ?). inv_trans. subst.
      now apply obs_eq_invT in H2 as ?.
  Qed.

  Lemma sb'_eq_vis_inv {Z R} :
    forall side (e f : E Z) (k : Z -> ctree E C X) (k' : Z -> ctree E D Y),
    (Proper (eq ==> equ eq ==> equ eq ==> impl) R) ->
    sb' eq R side (Vis e k) (Vis f k') ->
    forall x, e = f /\ forall side, R side (k x) (k' x).
  Proof.
    intros. destruct side.
    + pose proof (trans_vis e x k).
      apply H0 in H1; etrans.
      destruct H1 as (? & ? & ? & ? & ?). inv_trans. subst.
      setoid_rewrite EQ in H2. apply obs_eq_inv in H3 as [<- <-]. auto.
    + pose proof (trans_vis f x k').
      apply H0 in H1; etrans.
      destruct H1 as (? & ? & ? & ? & ?). inv_trans. subst.
      setoid_rewrite EQ in H2. apply obs_eq_inv in H3 as [<- <-]. auto.
  Qed.

  Lemma sb'_true_vis_l_inv' {Z R} :
    forall (e : E Z) (k : Z -> ctree E C X) (u : ctree F D Y),
    Respects_val L ->
    Respects_τ L ->
    (Proper (eq ==> equ eq ==> equ eq ==> impl) R) ->
    sb' L R true (Vis e k) u ->
    forall x, exists Z' (f : F Z') k' x',
      epsilon u (Vis f k') /\
      L (obs e x) (obs f x') /\
      forall side, R side (k x) (k' x').
  Proof.
    intros * RV RT ? SIM x.
    pose proof (TR := trans_vis e x k).
    apply SIM in TR; etrans.
    destruct TR as (l' & u' & TR & ? & ?).
    destruct l'.
    - apply RT in H1; intuition; discriminate.
    - apply trans_obs_epsilon in TR as (k' & EPS & EQ).
      setoid_rewrite EQ in H0.
      eauto 7 with trans.
    - apply trans_obs_void_epsilon in TR; contradiction.
    - apply RV in H1 as [_ ?].
      pose proof (H1 (Is_val _)). inversion H2.
  Qed.

  Lemma sb'_true_br_l_inv {Z R} :
    forall (c : C Z) (k : Z -> ctree E C X) (u : ctree F D Y),
    sb' L R true (Br c k) u ->
    forall x, exists u', epsilon u u' /\ R true (k x) u'.
  Proof.
    intros.
    pose proof (proj1 H eq_refl).
    destruct H0 as [_ [? _]].
    etrans.
  Qed.

  Lemma sb'_false_br_l_inv {Z R} :
    forall (t : ctree E C X) (c : D Z) (k : Z -> ctree F D Y),
    sb' L R false t (Br c k) ->
    forall x, exists t', epsilon t t' /\ R false t' (k x).
  Proof.
    intros.
    pose proof (proj2 H eq_refl).
    destruct H0 as [_ [? _]]. etrans.
  Qed.

  Lemma sb'_true_guard_l_inv {R} :
    forall (t : ctree E C X) (u : ctree F D Y),
    sb' L R true (Guard t) u ->
    exists u', epsilon u u' /\ R true t u'.
  Proof.
    intros.
    pose proof (proj1 H eq_refl).
    destruct H0 as [_ [_ ?]].
    etrans.
  Qed.

  Lemma sb'_false_guard_l_inv {R} :
    forall (t : ctree E C X) (u : ctree F D Y),
    sb' L R false t (Guard u) ->
    exists t', epsilon t t' /\ R false t' u.
  Proof.
    intros.
    pose proof (proj2 H eq_refl).
    destruct H0 as [_ [_ ?]]. etrans.
  Qed.

  Lemma sbisim'_br_l_inv {Z} c x (k : Z -> ctree E C X) (t' : ctree F D Y) :
    gfp (sb' L) true (Br c k) t' ->
    gfp (sb' L) true (k x) t'.
  Proof.
    intros. step in H.
    eapply sb'_true_br_l_inv with (x := x) in H as (? & ? & ?).
    step. split; intros; try discriminate.
    eapply step_ss'_epsilon_r; [| apply H].
    step in H0. now apply H0.
  Qed.

  Lemma sbisim'_br_r_inv {Z} c x (k : Z -> ctree F D Y) (t : ctree E C X) :
    gfp (sb' L) false t (Br c k) ->
    gfp (sb' L) false t (k x).
  Proof.
    intros. step in H.
    eapply sb'_false_br_l_inv with (x := x) in H as (? & ? & ?).
    step. split; intros; try discriminate.
    eapply step_ss'_epsilon_r; [| apply H].
    step in H0. now apply H0.
  Qed.

  Lemma sbisim'_guard_l_inv (t : ctree E C X) (t' : ctree F D Y) :
    gfp (sb' L) true (Guard t) t' ->
    gfp (sb' L) true t t'.
  Proof.
    intros. step in H.
    eapply sb'_true_guard_l_inv in H as (? & ? & ?).
    step. split; intros; try discriminate.
    eapply step_ss'_epsilon_r; [| apply H].
    step in H0. now apply H0.
  Qed.

  Lemma sbisim'_guard_r_inv (t : ctree E C X) (t' : ctree F D Y) :
    gfp (sb' L) false t (Guard t') ->
    gfp (sb' L) false t t'.
  Proof.
    intros. step in H.
    eapply sb'_false_guard_l_inv in H as (? & ? & ?).
    step. split; intros; try discriminate.
    eapply step_ss'_epsilon_r; [| apply H].
    step in H0. now apply H0.
  Qed.

End Inversion_Rules.

Definition guard_ctx {E C X} (R : ctree E C X -> Prop)
  (t : ctree E C X) :=
  exists t', t ≅ Guard t' /\ R t'.

Section upto.
  Context {E F C D: Type -> Type} {X Y: Type}
          (L : hrel (@label E) (@label F)).

  Program Definition ss_ctx3_l : mon (bool -> rel (ctree E C X) (ctree F D Y))
    := {| body R b t u := b = true /\ ss L (fun t u => forall side, R side t u) t u |}.
  Next Obligation.
    split; auto. intros. apply H1 in H0 as (? & ? & ? & ? & ?). eauto 6.
  Qed.

  Lemma ss_st'_l (r : Chain (sb' L)) :
    forall side x y, ss_ctx3_l `r side x y -> `r side x y.
  Proof.
    apply tower.
    - intros ? INC side x y [-> Hss]  ??. red.
      apply INC; auto.
      econstructor; eauto.
      intros ???.
      edestruct Hss as (?&?&?&?&?); eauto.
      do 2 eexists; ssplit; eauto.
      intros ?.
      apply leq_infx in H.
      now apply H.
    - clear.
      intros R IH side x y [-> Hss].
      apply sb'_true_ss'. ssplit; intros.
      + apply Hss in H0 as (? & ? & ? & ? & ?).
        do 2 eexists. ssplit; eauto.
        intros.
        step; auto.
      + rewrite H in Hss.
        eapply ss_br_l_inv with (x := x0) in Hss.
        exists y; split; auto.
        apply IH.
        constructor; auto.
        eapply (Hbody (ss L)); [| apply Hss].
        intros ????; now step.
      + rewrite H in Hss.
        eapply ss_guard_l_inv in Hss.
        exists y; split; auto.
        apply IH.
        constructor; auto.
        eapply (Hbody (ss L)); [| apply Hss].
        intros ????; now step.
  Qed.

  (* Up-to guard *)

  Program Definition guard_ctx3_l : mon (bool -> rel (ctree E C X) (ctree F D Y))
    := {| body R b t u := guard_ctx (fun t => R b t u) t |}.
  Next Obligation.
    destruct H0 as (? & ? & ?). red. eauto.
  Qed.

  Program Definition guard_ctx3_r : mon (bool -> rel (ctree E C X) (ctree F D Y))
    := {| body R b t u := guard_ctx (fun u => R b t u) u |}.
  Next Obligation.
    destruct H0 as (? & ? & ?). red. eauto.
  Qed.

  Lemma guard_ctx3_l_sbisim' (r : Chain (sb' L)) :
    forall side x y, guard_ctx3_l `r side x y -> `r side x y.
  Proof.
    apply tower.
    - intros ? INC side x y (? & EQ & ?) ??; red.
      apply INC; auto.
      econstructor; split; eauto.
      apply leq_infx in H0.
      now apply H0.
    - clear.
      intros R IH side x y (? & EQ & HR).
    split; intros; subst; subs.
      + apply step_ss'_guard_l.
        now step.
      + apply step_ss'_guard_r.
        eapply ss'_gen_mon. 3: apply HR; auto.
        all: auto.
  Qed.

  Lemma guard_ctx3_r_sbisim' (r : Chain (sb' L)) :
    forall side x y, guard_ctx3_r `r side x y -> `r side x y.
  Proof.
    apply tower.
    - intros ? INC side x y (? & EQ & ?) ??; red.
      apply INC; auto.
      econstructor; split; eauto.
      apply leq_infx in H0.
      now apply H0.
    - clear.
      intros R IH side x y (? & EQ & HR).
      split; intros; subst; subs.
      + apply step_ss'_guard_r.
        eapply ss'_gen_mon. 3: apply HR; auto.
        all: auto.
      + apply step_ss'_guard_l.
        now step.
  Qed.

  (* Up-to epsilon *)

  Program Definition epsilon_det_ctx3_l : mon (bool -> rel (ctree E C X) (ctree F D Y))
    := {| body R b t u := b = true /\ epsilon_det_ctx (fun t => R b t u) t |}.
  Next Obligation.
    destruct H1 as (? & ? & ?). split; auto. red. eauto.
  Qed.

  Definition pure_bind_ctx {E C X X0} (P : X0 -> Prop) (R : ctree E C X -> Prop)
    (t : ctree E C X) :=
    exists (t0 : ctree E C X0) k0,
      t ≅ CTree.bind t0 k0 /\
      (forall l t', trans l t0 t' -> exists v, l = val v /\ P v) /\
      forall x, P x -> R (k0 x).

  Program Definition pure_bind_ctx3_l {X0} (P : X0 -> Prop) : mon (bool -> rel (ctree E C X) (ctree F D Y))
    := {| body R b t u := b = true /\ pure_bind_ctx P (fun t => R b t u) t |}.
  Next Obligation.
    split; auto. destruct H1 as (? & ? & ? & ? & ?).
    red. eauto 7.
  Qed.

  Program Definition epsilon_ctx3_r : mon (bool -> rel (ctree E C X) (ctree F D Y))
    := {| body R b t u := b = true /\ epsilon_ctx (fun u => R b t u) u |}.
  Next Obligation.
    destruct H1 as (? & ? & ?). split; auto. red. eauto.
  Qed.

  Lemma epsilon_det_ctx3_l_sbisim' (r : Chain (sb' L)) :
    forall side x y, epsilon_det_ctx3_l `r side x y -> `r side x y.
  Proof.
    apply tower.
    - intros ? INC side x y (? & EQ & ? & ?) ??; red.
      apply INC; auto.
      split; auto.
      eexists; split; eauto.
      apply leq_infx in H2.
      now apply H2.
    - clear.
      intros R IH side x y (-> & ? & EQ & HR).
      split; intros; try discriminate.
      clear H.
      induction EQ.
      + apply sb'_true_ss' in HR. subs.
        eapply ss'_gen_mon. 3: apply HR.
        all: auto.
      + subs. apply step_ss'_guard_l.
        step. apply sb'_true_ss'. now apply IHEQ.
  Qed.

  Lemma pure_bind_ctx3_l_sbisim' {X0} (P : X0 -> Prop) (r : Chain (sb' L)) :
    forall side x y, pure_bind_ctx3_l P `r side x y -> `r side x y.
  Proof.
    apply tower.
    - intros ? INC side x y (-> & EQ & ? & (? & ? & ?)) ??; red.
      apply INC; auto.
      split; auto.
      do 2 eexists; ssplit.
      eauto.
      intros * TR; apply H0 in TR as (? & ? & ?).
      exists x1; auto.
      apply leq_infx in H2.
      intros; apply H2; auto.
    - clear.
      intros R IH side x y (-> & ? & (? & EQ & HTR & HB)).
      apply sb'_true_ss'.
      subs.
      ssplit.
      + intros PROD l t' TR.
        apply trans_bind_inv in TR as [(VAL & t'0 & TR0 & EQ) | (v & TR0 & TRk)].
        * apply HTR in TR0 as (v & -> & _). exfalso; etrans.
        * apply HTR in TR0 as ?. destruct H as (? & ? & Hv). apply val_eq_inv in H as <-.
          apply HB in TRk as (l' & u' & TRu & SIM & EQl); auto.
          2: {
            apply trans_val_epsilon in TR0 as [? _].
            apply productive_epsilon in H1; [| now apply productive_bind in PROD].
            now rewrite H1, bind_ret_l in PROD.
          }
          eauto.
      + intros Z c k0 EQ z.
        apply br_equ_bind in EQ as ?. destruct H as [(v & EQt0 & _) | (k1 & EQt0 & EQk0)].
        * rewrite EQt0, bind_ret_l in EQ.
          specialize (HB v). rewrite EQ in HB.
          setoid_rewrite EQt0 in HTR. clear x0 EQt0.
          destruct (HTR _ _ (trans_ret v)) as (? & ? & Hv). apply val_eq_inv in H as <-.
          specialize (HB Hv).
          apply sb'_true_br_l_inv with (x := z) in HB as (u' & EPS & SIM).
          eauto.
        * exists y. split; auto.
          eapply IH; split; auto.
          do 2 eexists; ssplit.
          apply EQk0.
          {
            intros ?? TR. eapply trans_br in TR; [| reflexivity].
            rewrite <- EQt0 in TR. now apply HTR in TR.
          }
          intros. now step; apply HB.
      + intros ? EQ.
        apply guard_equ_bind in EQ as ?. destruct H as [(v & EQt0 & _) | (k1 & EQt0 & EQk0)].
        * rewrite EQt0, bind_ret_l in EQ.
          specialize (HB v). rewrite EQ in HB.
          setoid_rewrite EQt0 in HTR. clear x0 EQt0.
          destruct (HTR _ _ (trans_ret v)) as (? & ? & Hv). apply val_eq_inv in H as <-.
          specialize (HB Hv).
          apply sb'_true_guard_l_inv in HB as (u' & EPS & SIM).
          eauto.
        * exists y. split; auto. rewrite <- EQk0 in EQ.
          eapply IH; split; auto.
          do 2 eexists; ssplit.
          symmetry; eauto.
          {
            intros ?? TR. eapply trans_guard in TR.
            rewrite <- EQt0 in TR. now apply HTR in TR.
          }
          intros. now step; apply HB.
  Qed.

  Lemma epsilon_ctx3_r_sbisim' (r : Chain (sb' L)) :
    forall side x y, epsilon_ctx3_r `r side x y <= `r side x y.
  Proof.
    apply tower.
    - intros ? INC side x y (? & ? & ? & ?) ??; red.
      apply INC; auto.
      split; auto.
      eexists; split; eauto.
      apply leq_infx in H2.
      apply H2; auto.
    - clear.
      intros c IH * (? & ? & ? & ?). subst.
      split; intros; try discriminate.
      eapply step_ss'_epsilon_r; [| eassumption].
      destruct H1 as [? _]. specialize (H1 eq_refl).
      eapply ss'_gen_mon. 3: apply H1; auto.
      all:eauto.
  Qed.

  #[global] Instance epsilon_det_st' : forall (R : Chain (@sb' E F C D X Y L)),
    Proper (epsilon_det ==> epsilon_det ==> flip impl) (` R true).
  Proof.
    cbn. intros.
    apply epsilon_det_ctx3_l_sbisim'.
    split; auto. exists y. split; auto.
    apply epsilon_ctx3_r_sbisim'.
    split; auto. exists y0. split; auto. now apply epsilon_det_epsilon.
  Qed.

  #[global] Instance epsilon_det_sbt' : forall (R : Chain (@sb' E F C D X Y L)),
    Proper (epsilon_det ==> epsilon_det ==> flip impl) (sb' L ` R true).
  Proof.
    intros ????????.
    eapply epsilon_det_st'; eauto.
  Qed.

End upto.

Section bind.
  Arguments label: clear implicits.
  Obligation Tactic := idtac.

  Context {E F C D: Type -> Type} {X X' Y Y': Type}
          (L : hrel (@label E) (@label F)) (R0 : rel X X').

  Lemma bind_chain_gen L0
    (ISVR : is_update_val_rel L R0 L0)
    (R : Chain (@sb' E F C D Y Y' L)) :
    forall (t : ctree E C X) (t' : ctree F D X') (k : X -> ctree E C Y) (k' : X' -> ctree F D Y'),
    forall side,
      gfp (sb' L0) side t t' ->
      (forall side' x x', R0 x x' -> `R side' (k x) (k' x')) ->
      ` R side (bind t k) (bind t' k').
  Proof.
    apply (@tower _ _ _ (fun (P : bool -> rel (ctree E C Y) (ctree F D Y')) =>
              forall (t : ctree E C X) (t' : ctree F D X') (k : X -> ctree E C Y) (k' : X' -> ctree F D Y') side,
                gfp (sb' L0) side t t' ->
                (forall side x x', R0 x x' -> P side (k x) (k' x')) ->
                P side (x <- t;; k x) (x <- t';; k' x))).
    - intros ? INC ???? ? ????; red.
      apply INC; auto.
      eapply leq_infx in H1.
      intros; apply H1; auto.
    - clear -ISVR.
      intros c IH * tt kk.
      split; intros; subst; ssplit.

      + simpl; intros PROD l u STEP.
        apply trans_bind_inv in STEP as [(H & u' & STEP & EQ) | (v & STEPres & STEP)].
        step in tt.
        apply tt in STEP as (l' & u'' & STEP & EQ' & ?); auto.
        2: { now apply productive_bind in PROD. }
        do 2 eexists. split; [| split].
        apply trans_bind_l; eauto.
        * intro Hl. destruct Hl.
          apply ISVR in H0; etrans.
          inversion H0; subst. apply H. constructor. apply H2. constructor.
        * intro; eapply equ_clos_st'_goal.
          reflexivity.
          apply EQ.
          reflexivity.
          apply IH; auto.
          intros. step. now apply kk.
        * apply ISVR in H0; etrans.
          destruct H0. exfalso. apply H. constructor. apply H2.
        * assert (t ≅ Ret v).
          { apply productive_bind in PROD. apply trans_val_epsilon in STEPres as [? _].
            now apply productive_epsilon. } subs.
          step in tt.
          apply tt in STEPres as (l' & u' & STEPres & EQ' & ?); auto.
          2: now eapply prod_ret.
          apply ISVR in H; etrans.
          dependent destruction H. 2: { exfalso. apply H. constructor. }
                                 pose proof (trans_val_inv STEPres) as EQ.
          rewrite EQ in STEPres.
          specialize (kk true v v2 H).
          rewrite bind_ret_l in PROD.
          apply kk in STEP as (? & u''' & STEP & EQ'' & ?); auto.
          do 2 eexists; split.
          eapply trans_bind_r; eauto.
          split; auto.

      + intros Z ?c ?k EQ z.
        apply br_equ_bind in EQ as EQ'. destruct EQ' as [(v & EQ' & EQ'') | (?k0 & EQ' & EQ'')].
        * subs. step in tt. destruct tt as [tt _]. specialize (tt eq_refl). destruct tt as [tt _].
          edestruct tt as (l & t'' & STEPres & _ & ?); etrans.
          apply ISVR in H; etrans.
          apply update_val_rel_val_l in H as (v' & -> & EQ').
          rewrite bind_ret_l in EQ.
          specialize (kk true v v' EQ').
          apply kk with (x := z) in EQ; auto. destruct EQ as (u' & EPS & EQ).
          exists u'.
          apply trans_val_epsilon in STEPres as [? _]. split; eauto.
          eapply epsilon_bind; eassumption.
        * subs. setoid_rewrite EQ''.
          (* clear k EQ EQ''. *)
          eexists. split. reflexivity.
          apply IH.
          step. split; [| intros; discriminate].
          intros _. simple apply sbisim'_br_l_inv with (x := z) in tt.
          step in tt. now apply tt.
          intros. step; eauto.


      + intros ? EQ.
        apply guard_equ_bind in EQ as EQ'. destruct EQ' as [(v & EQ' & EQ'') | (?k0 & EQ' & EQ'')].
        * subs. step in tt. destruct tt as [tt _]. specialize (tt eq_refl). destruct tt as [tt _].
          edestruct tt as (l & t'' & STEPres & _ & ?); etrans.
          apply ISVR in H; etrans.
          apply update_val_rel_val_l in H as (v' & -> & EQ').
          rewrite bind_ret_l in EQ.
          specialize (kk true v v' EQ').
          apply kk in EQ; auto. destruct EQ as (u' & EPS & EQ).
          exists u'.
          apply trans_val_epsilon in STEPres as [? _]. split; eauto.
          eapply epsilon_bind; eassumption.
        * subs. setoid_rewrite <- EQ''.
          (* clear k EQ EQ''. *)
          eexists. split. reflexivity.
          apply IH.
          step. split; [| intros; discriminate].
          intros _. simple apply sbisim'_guard_l_inv in tt.
          step in tt. now apply tt.
          intros. step; eauto.

      + simpl; intros PROD l u STEP.
        apply trans_bind_inv in STEP as [(H & ?t' & STEP & EQ) | (v & STEPres & STEP)].
        step in tt.
        apply tt in STEP as (l' & u' & STEP & EQ' & ?); auto.
        2: { now apply productive_bind in PROD. }
        do 2 eexists. split; [| split].
        apply trans_bind_l; eauto.
        * intro Hl. destruct Hl.
          apply ISVR in H0; etrans.
          inversion H0; subst. apply H. constructor. apply H1. constructor.
        * intros; rewrite EQ.
          apply IH; auto.
          intros ? ? ? ?; step; now apply kk.
        * apply ISVR in H0; etrans.
          destruct H0. exfalso. apply H. constructor. apply H2.
        * assert (t' ≅ Ret v).
          { apply productive_bind in PROD. apply trans_val_epsilon in STEPres as [? _].
            now apply productive_epsilon. } subs.
          step in tt.
          apply tt in STEPres as (l' & u' & STEPres & EQ' & ?); auto.
          2: now eapply prod_ret.
          apply ISVR in H; etrans.
          dependent destruction H. 2: { exfalso. apply H0. constructor. }
                                 pose proof (trans_val_inv STEPres) as EQ.
          rewrite EQ in STEPres.
          specialize (kk false v1 v H).
          rewrite bind_ret_l in PROD.
          apply kk in STEP as (? & u''' & STEP & EQ'' & ?); auto.
          do 2 eexists; split.
          eapply trans_bind_r; eauto.
          split; auto.

      + intros Z ?c ?k EQ z.
        apply br_equ_bind in EQ as EQ'. destruct EQ' as [(v & EQ' & EQ'') | (?k0 & EQ' & EQ'')].
        * subs. step in tt. destruct tt as [_ tt]. specialize (tt eq_refl). destruct tt as [tt _].
          edestruct tt as (l & t'' & STEPres & _ & ?); etrans.
          apply ISVR in H; etrans.
          apply update_val_rel_val_r in H as (v' & -> & EQ').
          rewrite bind_ret_l in EQ.
          specialize (kk false v' v EQ').
          apply kk with (x := z) in EQ; auto. destruct EQ as (u' & EPS & EQ).
          exists u'.
          apply trans_val_epsilon in STEPres as [? _]. split; eauto.
          eapply epsilon_bind; eassumption.
        * subs. setoid_rewrite EQ''.
          eexists. split. reflexivity.
          apply IH.
          step. split; [intros; discriminate |].
          intros _. apply sbisim'_br_r_inv with (x := z) in tt.
          step in tt. now apply tt.
          intros. step. now apply kk.

      + intros ? EQ.
        apply guard_equ_bind in EQ as EQ'. destruct EQ' as [(v & EQ' & EQ'') | (?k0 & EQ' & EQ'')].
        * subs. step in tt. destruct tt as [_ tt]. specialize (tt eq_refl). destruct tt as [tt _].
          edestruct tt as (l & t'' & STEPres & _ & ?); etrans.
          apply ISVR in H; etrans.
          apply update_val_rel_val_r in H as (v' & -> & EQ').
          rewrite bind_ret_l in EQ.
          specialize (kk false v' v EQ').
          apply kk in EQ; auto. destruct EQ as (u' & EPS & EQ).
          exists u'.
          apply trans_val_epsilon in STEPres as [? _]. split; eauto.
          eapply epsilon_bind; eassumption.
        * subs. setoid_rewrite <- EQ''.
          eexists. split. reflexivity.
          apply IH.
          step. split; [intros; discriminate |].
          intros _. apply sbisim'_guard_r_inv in tt.
          step in tt. now apply tt.
          intros. step. now apply kk.
  Qed.

End bind.

(*|
Expliciting the reasoning rule provided by the up-to principles.
|*)

Lemma st'_clo_bind {E F C D: Type -> Type} {X Y X' Y': Type} {L : rel (@label E) (@label F)}
      (R0 : rel X Y)
      side
      (t1 : ctree E C X) (t2: ctree F D Y)
      (k1 : X -> ctree E C X') (k2 : Y -> ctree F D Y')
      (R : Chain (sb' L)) :
  gfp (sb' (update_val_rel L R0)) side t1 t2 ->
  (forall x y, R0 x y -> forall b, `R b (k1 x) (k2 y)) ->
  `R side (t1 >>= k1) (t2 >>= k2).
Proof.
  intros ? ?.
  eapply bind_chain_gen; eauto.
  apply update_val_rel_correct.
Qed.

Lemma st'_clo_bind_eq {E C D: Type -> Type} {X X': Type}
      side (t1 : ctree E C X) (t2: ctree E D X)
      (k1 : X -> ctree E C X') (k2 : X -> ctree E D X')
      (R : Chain (sb' eq)) :
  gfp (sb' eq) side t1 t2 ->
  (forall x b, `R b (k1 x) (k2 x)) ->
  ` R side (t1 >>= k1) (t2 >>= k2).
Proof.
  intros ? ?.
  eapply bind_chain_gen; eauto.
  - apply update_val_rel_eq.
  - intros. now subst.
Qed.

Lemma sbt'_clo_bind_gen {E F C D: Type -> Type} {X Y X' Y': Type} {L : rel (@label E) (@label F)}
      R0 L0 b
      (HL0 : is_update_val_rel L R0 L0)
      (t1 : ctree E C X) (t2: ctree F D X')
      (k1 : X -> ctree E C Y) (k2 : X' -> ctree F D Y')
      (R : Chain (sb' L)) :
  gfp (sb' L0) b t1 t2 ->
  (forall x y, R0 x y -> forall b, sb' L `R b (k1 x) (k2 y)) ->
  sb' L `R b (t1 >>= k1) (t2 >>= k2).
Proof.
  intros ? ?.
  eapply bind_chain_gen; eauto.
  intros; now apply H0.
Qed.

Lemma sbt'_clo_bind {E F C D: Type -> Type} {X Y X' Y': Type} {L : rel (@label E) (@label F)}
      (R0 : rel X Y) b
      (t1 : ctree E C X) (t2: ctree F D Y)
      (k1 : X -> ctree E C X') (k2 : Y -> ctree F D Y')
      (R : Chain (sb' L)) :
  gfp (sb' (update_val_rel L R0)) b t1 t2 ->
  (forall x y, R0 x y -> forall b, sb' L `R b (k1 x) (k2 y)) ->
  sb' L `R b (t1 >>= k1) (t2 >>= k2).
Proof.
  intros ? ?.
  eapply sbt'_clo_bind_gen; eauto. apply update_val_rel_correct.
Qed.

Lemma sbt'_clo_bind_eq {E C D: Type -> Type} {X X': Type}
      b (t1 : ctree E C X) (t2: ctree E D X)
      (k1 : X -> ctree E C X') (k2 : X -> ctree E D X')
      (R : Chain (sb' eq)) :
  gfp (sb' eq) b t1 t2 ->
  (forall x b, sb' eq `R b (k1 x) (k2 x)) ->
  sb' eq `R b (t1 >>= k1) (t2 >>= k2).
Proof.
  intros ? ?.
  eapply sbt'_clo_bind_gen.
  - apply update_val_rel_eq.
  - apply H.
  - intros. now subst.
Qed.

Lemma step_sb'_guard_l' {E F C D X Y L}
  (t: ctree E C X) (t': ctree F D Y)
      (R : Chain (sb' L)) :
  (forall side, `R side t t') ->
  forall side, `R side (Guard t) t'.
Proof.
  intros.
  apply guard_ctx3_l_sbisim'.
  eexists; eauto.
Qed.

Lemma step_sb'_guard_r' {E F C D X Y L}
  (t: ctree E C X) (t': ctree F D Y) (R : Chain (sb' L)) :
  (forall side, `R side t t') ->
  forall side, `R side t (Guard t').
Proof.
  intros.
  apply (guard_ctx3_r_sbisim' R).
  eexists; eauto.
Qed.

Lemma sbisim'_epsilon_l {E F C D X Y} L :
  forall (t t' : ctree E C X) (u : ctree F D Y),
  gfp (sb' L) true t u ->
  epsilon t t' ->
  gfp (sb' L) true t' u.
Proof.
  intros. step. split; intro; [| discriminate].
  eapply ss'_gen_epsilon_l.
  - cbn. intros. step in H2. now apply H2.
  - step in H. now apply H.
  - apply H0.
Qed.

Lemma sbisim'_epsilon_r {E F C D X Y} L :
  forall (t : ctree E C X) (u u' : ctree F D Y),
  gfp (sb' L) false t u ->
  epsilon u u' ->
  gfp (sb' L) false t u'.
Proof.
  intros. step. split; intro; [discriminate |].
  eapply ss'_gen_epsilon_l.
  - cbn. intros. step in H2. now apply H2.
  - step in H. now apply H.
  - apply H0.
Qed.

Lemma ss_sb'_l_chain {E F C D X Y L} {R : Chain (sb' L)} :
  forall (t : ctree E C X) (u : ctree F D Y),
  ss L (fun t u => forall b, `R b t u) t u ->
  sb' L `R true t u.
Proof.
    intros. revert t u H. intros. split.
    2: intros; discriminate. intros _; ssplit; intros.
    + apply H in H1. destruct H1 as (? & ? & ? & ? & ?).
      eexists _, _. split; [apply H1 |]. split; [| apply H3].
      intro. destruct side; auto.
    + subs. apply ss_br_l_inv with (x := x) in H.
      exists u. split; eauto. now apply ss_st'_l.
    + subs. apply ss_guard_l_inv in H.
      exists u. split; eauto. now apply ss_st'_l.
Qed.

Theorem gfp_sb'_ss_sbisim {E F C D X Y} :
  forall L (t : ctree E C X) (u : ctree F D Y),
  (ss L (sbisim L) t u -> gfp (sb' L) true t u) /\
  (ss (flip L) (flip (sbisim L)) u t -> gfp (sb' L) false t u).
Proof.
  intros. revert t u. coinduction R CH. intros. split; split.
  2, 3: intros; discriminate.
  - intros _. apply ss_sb'_l_chain; auto.
    cbn. intros.
    apply H in H0. destruct H0 as (? & ? & ? & ? & ?).
    eexists _, _. split; [apply H0 |]. split; [| apply H2].
    step in H1. intro. destruct b; apply CH; apply H1.
  - intros _; ssplit; intros.
    + apply H in H1. destruct H1 as (? & ? & ? & ? & ?).
      eexists _, _. split; [apply H1 |]. split; [| apply H3].
      step in H2. destruct side; apply CH; apply H2.
    + subs. apply ss_br_l_inv with (x := x) in H.
      exists t. split; eauto. now apply CH.
    + subs. apply ss_guard_l_inv in H.
      exists t. split; eauto. now apply CH.
Qed.

Lemma gfp_sb'_true_ss_sbisim {E F C D X Y} :
  forall L (t : ctree E C X) (u : ctree F D Y),
  ss L (sbisim L) t u -> gfp (sb' L) true t u.
Proof.
  apply gfp_sb'_ss_sbisim.
Qed.

Theorem sbisim_sbisim' {E F C D X Y} :
  forall L (t : ctree E C X) (t' : ctree F D Y), sbisim L t t' <-> sbisim' L t t'.
Proof.
  split; intro.
  - intros [].
    + eapply (proj1 (gfp_sb'_ss_sbisim _ _ _)). step in H. apply H.
    + eapply (proj2 (gfp_sb'_ss_sbisim _ _ _)). step in H. apply H.
  - revert t t' H.
    coinduction R CH. intros. split; intros.
    + cbn. intros. apply trans_epsilon in H0 as (? & ? & ? & ?).
      apply sbisim'_epsilon_l with (t' := x) in H; auto.
      step in H. apply (proj1 H) in H2 as (? & ? & ? & ? & ?); auto. eauto 6.
    + cbn. intros. apply trans_epsilon in H0 as (? & ? & ? & ?).
      apply sbisim'_epsilon_r with (u' := x) in H; auto.
      step in H. apply (proj2 H) in H2 as (? & ? & ? & ? & ?); auto. eauto 6.
Qed.

Corollary sbisim_gfp_sb' {E F C D X Y} :
  forall L side (t : ctree E C X) (t' : ctree F D Y), sbisim L t t' -> gfp (sb' L) side t t'.
Proof.
  intros. apply sbisim_sbisim' in H. apply H.
Qed.

Theorem ss_sbisim_gfp_sb' {E F C D X Y} :
  forall L (t : ctree E C X) (u : ctree F D Y),
  (gfp (sb' L) true t u -> ss L (sbisim L) t u) /\
  (gfp (sb' L) false t u -> ss (flip L) (flip (sbisim L)) u t).
Proof.
  intros. revert t u. intros. split; cbn; intros.
  - apply trans_epsilon in H0 as (? & ? & ? & ?).
    apply sbisim'_epsilon_l with (t' := x) in H; auto.
    step in H. apply (proj1 H) in H2 as (? & ? & ? & ? & ?); auto.
    exists x0, x1. ssplit; auto. now apply sbisim_sbisim'.
  - apply trans_epsilon in H0 as (? & ? & ? & ?).
    apply sbisim'_epsilon_r with (u' := x) in H; auto.
    step in H. apply (proj2 H) in H2 as (? & ? & ? & ? & ?); auto.
    exists x0, x1. ssplit; auto. now apply sbisim_sbisim'.
Qed.

(*
Tactic Notation "__upto_bind_sbisim'" uconstr(R0) := TODO
Tactic Notation "__upto_bind_eq_sbisim'" uconstr(R0) := TODO
*)
