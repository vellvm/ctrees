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
	Utils CTrees Equ. 

Section Step.

  Context {E : Type -> Type} {R : Type}.

	Variant label : Type := 
	| Internal
	| External {X : Type} (e : E X) (v : X).

	Inductive step_ : label -> ctree' E R -> ctree' E R -> Prop :=

  | StepChoice {n} (x : Fin.t n) k l t :
    		step_ l (observe (k x)) t ->
    		step_ l (ChoiceF false n k) t

  | StepInternal {n} (x : Fin.t n) k t x :
				k x ≅ t ->
    		step_ Internal (ChoiceF true n k) (observe t)

  | StepExternal {X} (e : E X) k x t :
				k x ≅ t ->
    		step_ (External e x) (VisF e k) (observe t)
	.

  Definition step l u v := step_ l (observe u) (observe v).

	Inductive trclo {X} (R : X -> X -> Prop) : X -> X -> Prop :=
	| trclo_refl : forall x, trclo R x x
	| trclo_step : forall x y z, R x y -> trclo R y z -> trclo R x z.

	Definition intern_steps := trclo (step Internal).

	Definition wsteps := trclo (step Internal).

	Definition rcomp {X} (R S : X -> X -> Prop) : X -> X -> Prop := 
		fun x z => exists y, R x y /\ R y z.

	Infix "∘" := rcomp.

  Definition steps l := intern_steps ∘ step l ∘ intern_steps.

End Step.

Section Bisim.

	Context {E : Type -> Type} {X : Type}.
	Notation S := (ctree E X).

  (** The function defining strong bisimulations *)
  Program Definition sb : mon (rel S S) :=
    {| body R t u :=
        (forall l t', step l t t' -> exists2 u', step l u u' & R t' u') /\
        (forall l u', step l u u' -> exists2 t', step l t t' & R t' u')
    |}.
  Next Obligation. 
		intros R1 R2 INCL t u [F B]; split; [intros l t' STEP | intros l u' STEP].
		- edestruct F; eauto.
			eexists; eauto; apply INCL; auto.
		- edestruct B; eauto.
			eexists; eauto; apply INCL; auto.
	Qed.

  (** The function defining weak bisimulations *)
  Program Definition wb : mon (rel S S) :=
    {| body R t u :=
        (forall l t', steps l t t' -> exists2 u', steps l u u' & R t' u') /\
        (forall l u', steps l u u' -> exists2 t', steps l t t' & R t' u')
    |}.
  Next Obligation. 
		intros R1 R2 INCL t u [F B]; split; [intros l t' STEP | intros l u' STEP].
		- edestruct F; eauto.
			eexists; eauto; apply INCL; auto.
		- edestruct B; eauto.
			eexists; eauto; apply INCL; auto.
	Qed.

  Notation sbisim := (gfp sb).
  Notation "t ~ u" := (gfp sb t u) (at level 70).
  Notation st := (t sb).
  Notation sbt := (bt sb).
  (** notations  for easing readability in proofs by enhanced coinduction *)
  Notation "t [~] u" := (st  _ t u) (at level 79). 
  Notation "t {~} u" := (sbt _ t u) (at level 79).

  (** [eq] is a post-fixpoint, thus [const eq] is below [t] *)
  Lemma refl_st: const eq <= st.
  Proof.
 	 apply leq_t.
 	 split; intros; cbn in *; subst; eauto.
  Qed.

  (** converse is compatible *)
  Lemma converse_st: converse <= st.
  Proof.
    apply leq_t.
	  intros R p q [F B]; split; firstorder.
		edestruct B; eauto.
		edestruct F; eauto.
  Qed.

  (** so is squaring *)
  Lemma square_st: square <= st.
  Proof.
    apply leq_t.
    intros R x z [y [F B] [F' B']]. 
    split.  
    - cbn; intros. 
      edestruct F; eauto.
      edestruct F'; eauto. 
    - cbn; intros. 
      edestruct B'; eauto.
      edestruct B; eauto.
  Qed. 
 
  (** thus bisimilarity and [t R] are always equivalence relations. *)
  Global Instance Equivalence_st R: Equivalence (st R).
  Proof. apply Equivalence_t. apply refl_st. apply square_st. apply converse_st. Qed.

  Corollary Equivalence_bisim: Equivalence sbisim.
  Proof. apply Equivalence_st. Qed.

  Notation wbisim := (gfp wb).
  Notation "t ≈ u" := (gfp wb t u) (at level 70).
  Notation wt := (t wb).
  Notation wbt := (bt wb).
  (** notations  for easing readability in proofs by enhanced coinduction *)
  Notation "t [≈] u" := (wt  _ t u) (at level 79). 
  Notation "t {≈} u" := (wbt _ t u) (at level 79).

 (** [eq] is a post-fixpoint, thus [const eq] is below [t] *)
  Lemma refl_wt: const eq <= wt.
  Proof.
 	 apply leq_t.
 	 split; intros; cbn in *; subst; eauto.
  Qed.

 (** converse is compatible *)
 Lemma converse_wt: converse <= wt.
 Proof.
  apply leq_t.
  intros R p q [F B]; split; intros * STEP.
	edestruct B; eauto.
	edestruct F; eauto.
 Qed.

End Bisim.

Notation sbisim := (gfp sb).
Notation wbisim := (gfp wb).
