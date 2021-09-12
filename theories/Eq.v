(* begin hide *)
From Paco Require Import paco.

From CTree Require Import
	Utils CTrees.

(* end hide *)

(** * Observational equality of [ctree]s
	Analogous to what is dubbed as _strong bisimulation_
	for [ctree], but trying to avoid this terminology here 
	to reserve the notion of bisimulation for the equivalence 
	relation that takes internal non-determinism into account.
*)

Section eq.

  Context {E : Type -> Type} {R1 R2 : Type} (RR : R1 -> R2 -> Prop).

  (** We also need to do some gymnastics to work around the
      two-layered definition of [ctree]. We first define a
      relation transformer [eqitF] as an indexed inductive type
      on [ctreeF], which is then composed with [observe] to obtain
      a relation transformer on [ctree] ([eqit_]).

      In short, this is necessitated by the fact that dependent
      pattern-matching is not allowed on [ctree].
   *)

  Variant equF (eq : ctree E R1 -> ctree E R2 -> Prop) :
    ctree' E R1 -> ctree' E R2 -> Prop :=
  | Eq_Ret x y (REL : RR x y) : equF eq (RetF x) (RetF y)
  | Eq_Vis {X} (e : E X) k1 k2
      (REL : forall x, eq (k1 x) (k2 x)) :
      equF eq (VisF e k1) (VisF e k2)
  | Eq_Fork {n} (k1 : Fin.t n -> _) (k2 : Fin.t n -> _)
      (REL : forall i, eq (k1 i) (k2 i)) :
      equF eq (ForkF k1) (ForkF k2)
  .
  Hint Constructors equF: core.

	Definition equ_ eq : ctree E R1 -> ctree E R2 -> Prop :=
		fun t1 t2 => equF eq (observe t1) (observe t2).

  Lemma equ__mono : monotone2 equ_.
  Proof.
    repeat red; intros. destruct IN; eauto.
  Qed.
  Hint Resolve equ__mono : paco.

  Definition equ := paco2 equ_ bot2.

End eq.

#[global] Hint Resolve equ__mono : paco.
#[global] Hint Constructors equF : core.
(* #[global] Hint Unfold equ_ : core. *)
Arguments equ_ {E R1 R2} RR eq t1 t2/.
Infix "≅[ R ]" := (equ R) (at level 20).
Infix "≅"      := (equ eq) (at level 20).
Infix "{ r }≅F[ R ]" := (equF R (upaco2 (equ_ R) r)) (at level 20, only printing). 
Infix "{ r }≅F" := (equF eq (upaco2 (equ_ eq) r)) (at level 20, only printing). 
Infix "{ r }≅gF[ R ]" := (equF R (gupaco2 (equ_ R) _ r)) (at level 20, only printing). 
Infix "{ r }≅gF" := (equF eq (gupaco2 (equ_ eq) _ r)) (at level 20, only printing). 
Notation "⊥" := bot2.

Section equ_trans_clo.

	Context {E : Type -> Type}.
	Context {R1 R2 : Type}.
	Context {RR : R1 -> R2 -> Prop}.

	(* ** Up-to equilarity 
		We start with another reasoning principle: one can reasoning up-to equilarity during
		a co-inductive proof to establish [equ] itself.
		This principle is embodied by the following closure.
	*)
	Inductive equ_trans_clo (r : ctree E R1 -> ctree E R2 -> Prop)
		: ctree E R1 -> ctree E R2 -> Prop :=
	| equ_trans_clo_intro t1 t2 t1' t2' RR1 RR2
				(EQVl: t1 ≅[RR1] t1')
				(EQVr: t2 ≅[RR2] t2')
				(LERR1: forall x x' y, RR1 x x' -> RR x' y -> RR x y)
				(LERR2: forall x y y', RR2 y y' -> RR x y' -> RR x y)
				(REL: r t1' t2')
		: equ_trans_clo r t1 t2
	.
	Hint Constructors equ_trans_clo: core.

	(* This closure is monotonous *)
	Lemma equ_trans_clo_mon :
		monotone2 equ_trans_clo.
	Proof.
		red; intros. destruct IN. econstructor; eauto.
	Qed.
	Hint Resolve equ_trans_clo_mon : paco.

	(* In order to justify the use of this enhanced reasoning principle,
		we prove that it is (weakly) compatible with the functor [equ']. *)
	Lemma equ_trans_clo_wcompat :
		wcompatible2 (equ_ RR) equ_trans_clo. 
	Proof.
		econstructor; eauto with paco.
		intros. destruct PR.
		punfold EQVl. punfold EQVr.
		cbn in *.
		induction REL.
		- genobs t1 ot1; genobs t2 ot2. 
			inv EQVl; auto.
			inv EQVr; eauto.
		- remember (VisF e k1).
			genobs t1 ot1.
			inv EQVl; try discriminate.
			genobs t2 ot2; remember (VisF e k2).
			inv EQVr; try discriminate.
			dependent destruction H2.
			dependent destruction H0.
			pclearbot. 
			constructor. 
			gclo.
			econstructor; eauto with paco.
			apply REL0.
			apply REL1.
		- genobs t1 ot1; genobs t2 ot2. 
			inv EQVl; auto.
			inv EQVr; auto.
			dependent destruction H2.
			dependent destruction H4.
			pclearbot.  
			constructor. 
			gclo.
			econstructor; eauto with paco.
			apply REL0.
			apply REL1.
	Qed.

	Lemma equ_clo_trans :
		equ_trans_clo <3= gupaco2 (equ_ RR) equ_trans_clo.
	Proof.
		intros. destruct PR. gclo. econstructor; eauto with paco.
	Qed.

End equ_trans_clo.

#[global] Hint Resolve equ_trans_clo_wcompat : paco.

