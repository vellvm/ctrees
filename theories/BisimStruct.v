(* begin hide *)
From Coq Require Import
     Program
     Setoid
     Morphisms
     RelationClasses.

From ITree Require Import
	Basics.HeterogeneousRelations.

From Coinduction Require Import
	coinduction rel tactics.

From CTree Require Import
	Utils CTrees Equ Shallow.

(* end hide *)

Section Schedule.

	(* We do not wish to observe internal non-deterministic choices.
		We therefore want to consider states, i.e. ctrees, that can
		be reached after a finite number of internal decisions, and
		are such that they are ready to expose an observation: their
		head constructor is either a Ret or a Vis.
		*)

  Context {E : Type -> Type} {R : Type}.

  Inductive schedule_ : ctree' E R -> ctree' E R -> Prop :=
  | SchedChoice {n} b (x : Fin.t n) k t :
    		schedule_ (observe (k x)) t ->
    		schedule_ (ChoiceF b n k) t
  | SchedRet x :
    		schedule_ (RetF x) (RetF x)
  | SchedVis {X} (e : E X) k k' :
    		(forall x, k x ≅ k' x) -> (* Because [schedule_] stops right there, we need to close explicitly up to [equ] if we want to be stable under it *)
    		schedule_ (VisF e k) (VisF e k').

  Definition schedule u v := schedule_ (observe u) (observe v).

End Schedule.

Section bisim.

  Context {E : Type -> Type} {R1 R2 : Type} (RR : R1 -> R2 -> Prop).

	(** * [matching]
	This relation captures the local challenge that two scheduled
	trees must solve. It corresponds from the more traditional
	bisimulation world to ensuring that they can take a small step
	emmitting the same event. *)

  Variant matching (bisim : ctree E R1 -> ctree E R2 -> Prop) :
    ctree' E R1 -> ctree' E R2 -> Prop :=
  | MatchRet x y (RET : RR x y) :
     matching bisim (RetF x) (RetF y)
  | MatchVis {X} (e : E X) k1 k2 (RET : forall v, bisim (k1 v) (k2 v)):
     matching bisim (VisF e k1) (VisF e k2)
  .
  Hint Constructors matching: core.

	(* The functor is shrinked to a single constructor mirroring
		exactly traditional definitions of bisimulations:
		for any observable state that the first process can reach,
		the second one can reach a matching one, and reciprocally.
	*)

  Variant bisimF (bisim : ctree E R1 -> ctree E R2 -> Prop) :
    ctree' E R1 -> ctree' E R2 -> Prop :=

  | BisimSched u t
            (SIMF : forall u', schedule_ u u' ->
              exists t', schedule_ t t' /\ matching bisim u' t')
            (SIMB : forall t', schedule_ t t' ->
              exists u', schedule_ u u' /\ matching bisim u' t')
               :
      bisimF bisim u t
  .
  Hint Constructors bisimF: core.

  Definition bisim_ eq : ctree E R1 -> ctree E R2 -> Prop :=
	fun t1 t2 => bisimF eq (observe t1) (observe t2).

  Lemma matching_mono u v sim sim'
              (IN : matching sim u v)
              (LE : sim <= sim') :
        matching sim' u v.
  Proof.
    inv IN; auto. constructor; intros. apply LE; auto.
  Qed.
  Hint Resolve matching_mono: core.

  Program Definition fbisim : mon (ctree E R1 -> ctree E R2 -> Prop) := {| body := bisim_ |}.
  Next Obligation.
   unfold pointwise_relation, impl, bisim_.
   intros ?? INC ?? EQ.
   constructor; inversion_clear EQ; intros; [edestruct SIMF as (? & ? & ?)| edestruct SIMB as (? & ? & ?)]; eauto.
  Qed.

End bisim.

(** associated relation *)
Definition bisim {E R} := (gfp (@fbisim E R R eq)).
(* Notation bisim := (gfp (fbisim eq)). *)

(** associated companions  *)
Notation T_bis RR  := (t (B (fbisim RR))).
Notation t_bis RR  := (t (fbisim RR)).
Notation bt_bis RR := (bt (fbisim RR)).

Infix "≈" := bisim (at level 70).
Notation "x ≊ y" := (t_bis eq _ x y) (at level 79).
Notation "x [≊] y" := (bt_bis eq _ x y) (at level 79).

Arguments bisim_ _ _ _ _/.
#[global] Hint Constructors bisimF: core.
#[global] Hint Constructors matching: core.

Variant passive_ {E R} : ctree' E R -> Prop :=
  | choice_passive b n k : passive_ (ChoiceF b n k).
Definition passive {E R} t := @passive_ E R (observe t).
#[global] Hint Constructors passive_: core.

Variant active_ {E R} : ctree' E R -> Prop :=
  | ret_active x : active_ (RetF x)
  | vis_active Y (e : E Y) k : active_ (VisF e k).
Definition active {E R} t := @active_ E R (observe t).
#[global] Hint Constructors active_: core.

Lemma scheduled_active_ : forall {E R} (t u : ctree' E R),
  schedule_ t u ->
  active_ u.
Proof.
  intros * SCHED.
  now induction SCHED.
Qed.

Lemma scheduled_active : forall {E R} (t u : ctree E R),
  schedule t u ->
  active u.
Proof.
  intros * SCHED; red.
  now induction SCHED.
Qed.

Lemma matching_active_refl {E R} (RR : R -> R -> Prop)
   (eq : ctree E R -> ctree E R -> Prop) (t : ctree' E R)
   `{Reflexive _ RR} `{Reflexive _ eq} :
   active_ t ->
   matching RR eq t t.
Proof.
  intros []; auto.
Qed.

Lemma matching_active_sym {E R} (RR : R -> R -> Prop)
   (eq : ctree E R -> ctree E R -> Prop) (t u : ctree' E R)
   `{Symmetric _ RR} :
   matching RR eq t u ->
   matching RR (converse eq) u t.
Proof.
  intros []; auto.
Qed.

Section bisim_equiv.

	Variable (E : Type -> Type) (R : Type) (RR : R -> R -> Prop).
  Notation T  := (coinduction.t (B (fbisim (E := E) RR))).
  Notation t  := (coinduction.t (fbisim (E := E) RR)).
	Notation bt := (coinduction.bt (fbisim (E := E) RR)).


  (** [eq] is a post-fixpoint, thus [const eq] is below [t] *)
	Lemma refl_t {RRR: Reflexive RR}: const eq <= t.
	Proof.
    apply leq_t.
		intros p t ? <-. cbn.
    constructor.
    - intros t' SCHED.
      exists t'; split; auto.
      apply matching_active_refl; auto.
      eapply scheduled_active_; eauto.
    - intros t' SCHED.
      exists t'; split; auto.
      apply matching_active_refl; auto.
      eapply scheduled_active_; eauto.
	Qed.

	(** converse is compatible *)
	Lemma converse_t {RRS: Symmetric RR}: converse <= t.
	Proof.
		apply leq_t. intros S t u H; cbn in *.
    destruct H. constructor.
    - intros t' SCHED.
      edestruct SIMB as (u' & SCHED' & MATCH'); eauto.
      exists u'; split; auto.
      apply matching_active_sym; auto.
    - intros u' SCHED.
      edestruct SIMF as (t' & SCHED' & MATCH'); eauto.
      exists t'; split; auto.
      apply matching_active_sym; auto.
	Qed.

	(** thus bisimilarity, [t R], [b (t R)] and [T f R] are always reflexive relations *)
	#[global] Instance Reflexive_t `{Reflexive _ RR} S: Reflexive (t S).
	Proof.  intro. now apply (ft_t refl_t). Qed.
	#[global] Instance Reflexive_T `{Reflexive _ RR} f S: Reflexive (T f S).
	Proof.  intro. now apply (fT_T refl_t). Qed.
	#[global] Instance Reflexive_bt `{Reflexive _ RR} S: Reflexive (bt S).
	Proof.  intro. now apply (fbt_bt refl_t). Qed.

	(** thus bisimilarity, [t R], [b (t R)] and [T f R] are always symmetric relations *)
	#[global] Instance Symmetric_t `{Symmetric _ RR} S: Symmetric (t S).
	Proof.  intros ???. now apply (ft_t converse_t). Qed.
	#[global] Instance Symmetric_T `{Symmetric _ RR} f S: Symmetric (T f S).
	Proof.  intros ???. now apply (fT_T converse_t). Qed.
	#[global] Instance Symmetric_bt `{Symmetric _ RR} S: Symmetric (bt S).
	Proof.  intros ???. now apply (fbt_bt converse_t). Qed.

End bisim_equiv.

#[global] Instance bisim_trans {E R}: Transitive (@bisim E R).
Proof.
  red. unfold bisim. coinduction S IH.
  intros t u v eq1 eq2.
  step in eq1; step in eq2.
  inversion eq1 as [? ? SIMF1 SIMB1]; subst.
  inversion eq2 as [? ? SIMF2 SIMB2]; subst.
  constructor.
  - intros u' SCHED.
    apply SIMF1 in SCHED as (ou' & SCHEDu & MATCHut).
    apply SIMF2 in SCHEDu as (ov' & SCHEDv & MATCHvu).
    exists ov'; split; auto.
    inv MATCHvu.
    + inv MATCHut; auto.
    + inv MATCHut.
      dependent induction H3.
      constructor.
      intros ?.
      eapply IH; eauto.
  - intros t' SCHED.
    apply SIMB2 in SCHED as (ou' & SCHEDu & MATCHut).
    apply SIMB1 in SCHEDu as (ov' & SCHEDv & MATCHvu).
    exists ov'; split; auto.
    inv MATCHvu.
    + inv MATCHut; auto.
    + inv MATCHut.
      dependent induction H2.
      constructor.
      intros ?.
      eapply IH; eauto.
Qed.

#[global] Instance equ_schedule_ {E X}:
  Proper (going (equ eq) ==> going (equ eq) ==> iff) (@schedule_ E X).
Proof.
  repeat red; intros * EQ1 * EQ2; split; intros SCHED.
  - inv EQ1. inv EQ2. rename H into EQ1. rename H0 into EQ2. step in EQ1; step in EQ2.
    unfold schedule in *.
    hinduction SCHED before X.
    + intros. inv EQ1. invert.
      eapply SchedChoice with x.
      apply IHSCHED. specialize (REL x).
      step in REL. apply REL. auto.
    + intros. inv EQ1; inv EQ2; constructor.
    + intros. inv EQ1. inv EQ2. invert.
      constructor. intros.
      rewrite <- REL0, <- REL. auto.
  - inv EQ1. inv EQ2. rename H into EQ1. rename H0 into EQ2. step in EQ1; step in EQ2.
    unfold schedule in *.
    hinduction SCHED before X.
    + intros. inv EQ1. invert.
      eapply SchedChoice with x.
      apply IHSCHED. specialize (REL x).
      step in REL. apply REL. auto.
    + intros. inv EQ1; inv EQ2; constructor.
    + intros. inv EQ1. inv EQ2. invert.
      constructor. intros.
      rewrite REL0, REL. auto.
Qed.

#[global] Instance equ_schedule {E X}:
	Proper (equ eq ==> equ eq ==> iff) (@schedule E X).
Proof.
  unfold schedule. repeat intro.
  apply equ_schedule_; constructor; [rewrite H | rewrite H0]; auto.
Qed.

(** * Sanity checks and meta-theory to establish at some point.
	We'll have to come after more basic meta-theory of course,
	but it's good to think about those.
	*)

Module Sanity.
  Import CTree.

  Lemma schedule_spin {E R} t : schedule_ (observe (@spin E R)) t -> False.
  Proof.
    intros.
    remember (observe spin).
    induction H; inversion Heqc.
    cbv in *. subst. apply inj_pair2 in H3. subst. auto.
  Qed.

  Goal forall {E R}, @spin E R ≈ spin.
  Proof.
    intros. reflexivity.
  Qed.

  Lemma schedule_spin_nary {E R} n t : schedule_ (observe (@spin_nary E R n)) t -> False.
  Proof.
    intros.
    remember (observe (spin_nary n)).
    induction H; inversion Heqc.
    cbv in *. subst. apply inj_pair2 in H3. subst. auto.
  Qed.

  #[global] Hint Unfold bisim : core.
  Goal forall {E R} n m, @spin_nary E R n ≈ spin_nary m.
  Proof.
    intros. unfold bisim. step.
    constructor; intros; exfalso; eapply schedule_spin_nary; eauto.
  Qed.

  Goal forall {E R} n, @spin_nary E R n ≈ spin.
  Proof.
    intros. unfold bisim. step.
    constructor; intros; exfalso.
    - eapply schedule_spin_nary; eauto.
    - eapply schedule_spin; eauto.
  Qed.

  Lemma choice2_assoc : forall {E X} (t u v : ctree E X),
	  choice2 (choice2 t u) v ≈
      choice2 t (choice2 u v).
  Proof.
    intros. unfold bisim. step. constructor.
    - intros. exists u'. split.
      2: { apply matching_active_refl; auto. eapply scheduled_active_; eauto. }
      inv H. apply inj_pair2 in H3. subst. remember 2. destruct x; inv Heqn.
      + inv H4. apply inj_pair2 in H2. subst. remember 2. destruct x; inv Heqn.
        * apply SchedChoice with (x:=Fin.F1); auto.
        * clear x. apply SchedChoice with (x:=Fin.FS Fin.F1).
          apply SchedChoice with (x:=Fin.F1); auto.
      + clear x. apply SchedChoice with (x:=Fin.FS Fin.F1).
        apply SchedChoice with (x:=Fin.FS Fin.F1); auto.
    - intros. exists t'. split.
      2: { apply matching_active_refl; auto. eapply scheduled_active_; eauto. }
      inv H. apply inj_pair2 in H3. subst. remember 2. destruct x; inv Heqn.
      + apply SchedChoice with (x:=Fin.F1).
        apply SchedChoice with (x:=Fin.F1); auto.
      + clear x. inv H4. apply inj_pair2 in H2. subst. remember 2. destruct x; inv Heqn.
        * apply SchedChoice with (x:=Fin.F1).
          apply SchedChoice with (x:=Fin.FS Fin.F1); auto.
        * clear x. apply SchedChoice with (x:=Fin.FS Fin.F1); auto.
  Qed.

  Lemma choice2_commut : forall {E X} (t u : ctree E X),
	  choice2 t u ≈ choice2 u t.
  Proof.
    intros. unfold bisim. step. constructor.
    - intros. exists u'. split.
      2: { apply matching_active_refl; auto. eapply scheduled_active_; eauto. }
      inv H. apply inj_pair2 in H3. subst. remember 2. destruct x; inv Heqn.
      + apply SchedChoice with (x:=Fin.FS Fin.F1); auto.
      + apply SchedChoice with (x0:=Fin.F1); auto.
    - intros. exists t'. split.
      2: { apply matching_active_refl; auto. eapply scheduled_active_; eauto. }
      inv H. apply inj_pair2 in H3. subst. remember 2. destruct x; inv Heqn.
      + apply SchedChoice with (x:=Fin.FS Fin.F1); auto.
      + apply SchedChoice with (x0:=Fin.F1); auto.
  Qed.

  (* To generalize to any arity *)
  Lemma choice_merge : forall {E X} (t u v : ctree E X),
	  choice2 (choice2 t u) v ≈
		      choice3 t u v.
  Proof.
    intros. unfold bisim. step. constructor.
    - intros. exists u'. split.
      2: { apply matching_active_refl; auto. eapply scheduled_active_; eauto. }
      inv H. apply inj_pair2 in H3. subst. remember 2. destruct x; inv Heqn.
      + inv H4. apply inj_pair2 in H2. subst. remember 2. destruct x; inv Heqn.
        * apply SchedChoice with (x:=Fin.F1); auto.
        * apply SchedChoice with (x0:=Fin.FS Fin.F1); auto.
      + apply SchedChoice with (x0:=Fin.FS (Fin.FS Fin.F1)); auto.
    - intros. exists t'. split.
      2: { apply matching_active_refl; auto. eapply scheduled_active_; eauto. }
      inv H. apply inj_pair2 in H3. subst. remember 3. destruct x; inv Heqn.
      + apply SchedChoice with (x:=Fin.F1).
        apply SchedChoice with (x:=Fin.F1); auto.
      + remember 2. destruct x; inv Heqn.
        * apply SchedChoice with (x:=Fin.F1).
          apply SchedChoice with (x:=Fin.FS Fin.F1); auto.
        * apply SchedChoice with (x0:=Fin.FS Fin.F1); auto.
  Qed.

  Lemma choice2_spin : forall {E X} (t : ctree E X),
	  choice2 t spin ≈ t.
  Proof.
    intros. unfold bisim. step. constructor.
    - intros. exists u'. split.
      2: { apply matching_active_refl; auto. eapply scheduled_active_; eauto. }
      inv H. apply inj_pair2 in H3. subst. remember 2. destruct x; inv Heqn; auto.
      exfalso. eapply schedule_spin; eauto.
    - intros. exists t'. split.
      2: { apply matching_active_refl; auto. eapply scheduled_active_; eauto. }
      apply SchedChoice with (x:=Fin.F1); auto.
  Qed.

  Lemma choice2_equ : forall {E X} (t u : ctree E X),
	  t ≅ u ->
	  choice2 t u ≈ t.
  Proof.
    intros. unfold bisim. step. constructor.
    - intros. exists u'. split.
      2: { apply matching_active_refl; auto. eapply scheduled_active_; eauto. }
      inv H0. apply inj_pair2 in H4. subst. remember 2. destruct x; inv Heqn; auto.
      (* We should be able to use something like equ_schedule for
         this, but we need a version with schedule_ *)
      admit.
    - intros. exists t'. split.
      2: { apply matching_active_refl; auto. eapply scheduled_active_; eauto. }
      apply SchedChoice with (x:=Fin.F1); auto.
  Abort.

  Lemma choice0_spin : forall {E X},
    ChoiceV 0 (fun x:fin 0 => match x with end) ≈ @spin E X.
  Proof.
    intros; unfold bisim; step; constructor; intros * SCHED.
    inv SCHED; inv x.
    exfalso; eapply schedule_spin; eauto.
  Qed.

End Sanity.

Lemma schedule_vis_inv :
  forall {E X Y} e (k : X -> ctree E Y) t,
    schedule (Vis e k) t -> t ≅ Vis e k.
Proof.
  intros * SCHED. inversion SCHED. apply inj_pair2 in H1, H2. subst.
  step. rewrite <- H3. constructor. intros.
  symmetry; auto.
Qed.


(* TODO : [equ] is a subrelation of [bisim] *)
Lemma equ_bisim : forall {E X Y} {RR: X -> Y -> Prop},
  subrelationH (gfp (@fequ E _ _ RR)) (gfp (@fbisim E _ _ RR)).
Proof.
	(*
	 intros; red.
	 pcofix CIH; intros s t EQ.
	 punfold EQ; pfold.
	 inv EQ.
	 - constructor 2; (intros ? SCHED; eexists; split; [constructor | inv SCHED; auto]).
	 - constructor 2; (intros ? SCHED; eexists; split; [constructor | apply schedule_vis_inv in SCHED; subst; pclearbot; auto]).
		 all: constructor; intros; right; apply CIH, REL.
	 - constructor 2; intros ? SCHED.
		 + pclearbot.
			 remember (Choice k1) as ft. revert k1 REL Heqft; induction SCHED; try now intuition.
			 intros; dependent destruction Heqft; pclearbot.
			 edestruct IHSCHED as (t' & SCHED' & MATCH).

	 - constructor 2; .
		 assert (u' = Vis e k1).
		 { inversion SCHED. dependent induction H1. dependent induction H2. }

 	*)
Admitted.
