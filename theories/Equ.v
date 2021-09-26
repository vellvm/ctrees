(* begin hide *)
From Coq Require Import RelationClasses.

From Coinduction Require Import 
	coinduction rel tactics.

From CTree Require Import
	Utils CTrees.

(* end hide *)

(** * Structural equality of [ctree]s
	Analogous to what is dubbed as _strong bisimulation_
	for [ctree], but trying to avoid this terminology here
	to reserve the notion of bisimulation for the equivalence
	relation that takes internal non-determinism into account.
*)

Section equ.

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
      equF eq (ForkF n k1) (ForkF n k2)
  .
  Hint Constructors equF: core.

  Definition equ_ eq : ctree E R1 -> ctree E R2 -> Prop :=
	fun t1 t2 => equF eq (observe t1) (observe t2).

  Program Definition fequ: mon (ctree E R1 -> ctree E R2 -> Prop) := {|body := equ_|}.
  Next Obligation.
    unfold pointwise_relation, Basics.impl, equ_. 
    intros ?? INC ?? EQ. inversion_clear EQ; auto. 
  Qed.

End equ.

(** associated relation *)
Notation equ R := (gfp (fequ R)).
Infix "≅" := (equ eq) (at level 70).

(** associated companions  *)
Notation T_equ RR  := (t (B (fequ RR))).
Notation t_equ RR  := (t (fequ RR)).
Notation bt_equ RR := (bt (fequ RR)).
Arguments equ_ _ _ _ _/.
Ltac desobs x := destruct (observe x) .
#[global] Hint Constructors equF: core.

Section equ_equiv.

	Variable (E : Type -> Type) (R : Type) (RR : R -> R -> Prop).
  Notation T  := (coinduction.t (B (fequ (E := E) RR))).
  Notation t  := (coinduction.t (fequ (E := E) RR)).
	Notation bt := (coinduction.bt (fequ (E := E) RR)).

  (** [eq] is a post-fixpoint, thus [const eq] is below [t] *)
	Lemma refl_t {RRR: Reflexive RR}: const eq <= t.
	Proof.
		apply leq_t. intro. 
		change (@eq (ctree E R)  <= equ_ RR eq). 
		intros p ? <-. cbn. desobs p; auto. 
	Qed.
		
	(** converse is compatible *)
	Lemma converse_t {RRS: Symmetric RR}: converse <= t.
	Proof.
		apply leq_t. intros S x y H; cbn. destruct H; auto.
	Qed.

	Lemma Vis_eq1 T Y e k Z f h: @VisF E R T Y e k = @VisF E R T Z f h -> Y=Z.
	Proof. intro H. now dependent destruction H. Qed.
	
	Lemma Vis_eq2 T Y e k f h: @VisF E R T Y e k = @VisF E R T Y f h -> e=f /\ k=h.
	Proof. intro H. now dependent destruction H. Qed.
	
	Lemma Fork_eq1 T n m k h: @ForkF E R T n k = @ForkF E R T m h -> n=m.
	Proof. intro H. now dependent destruction H. Qed.

	Lemma Fork_eq2 T n k h: @ForkF E R T n k = @ForkF E R T n h -> k=h.
	Proof. intro H. now dependent destruction H. Qed.

	(** so is squaring *)
	Lemma square_t {RRR: Reflexive RR} {RRT: Transitive RR}: square <= t.
	Proof.
		apply leq_t.
		intros S x z [y xy yz]; cbn. 
		inversion xy; inversion yz; try (exfalso; congruence).
		- constructor. replace y0 with x1 in * by congruence. eauto.
		- rewrite <-H in H2.
			destruct (Vis_eq1 _ _ _ _ _ _ _ H2).
			destruct (Vis_eq2 _ _ _ _ _ _ H2) as [-> ->].
			constructor. intro x0. now exists (k2 x0).
		- rewrite <- H in H2.
			destruct (Fork_eq1 _ _ _ _ _ H2).
			destruct (Fork_eq2 _ _ _ _ H2).
			constructor. intros i. now (exists (k0 i)).
	Qed.
	
	(** thus bisimilarity, [t R], [b (t R)] and [T f R] are always equivalence relations *)
	#[global] Instance Equivalence_t `{Equivalence _ RR} S: Equivalence (t S).
	Proof. apply Equivalence_t. apply refl_t. apply square_t. apply converse_t. Qed.
	#[global] Instance Equivalence_T `{Equivalence _ RR} f S: Equivalence (T f S).
	Proof. apply Equivalence_T. apply refl_t. apply square_t. apply converse_t. Qed.
	#[global] Instance Equivalence_bt `{Equivalence _ RR} S: Equivalence (bt S).
	Proof. apply Equivalence_bt. apply refl_t. apply square_t. apply converse_t. Qed.

	(* This one is a bit annoyingly adhoc, but useful for unfolding laws *)
  #[global]Instance Reflexive_equF (equ : ctree E R -> ctree E R -> Prop) :
    Reflexive RR -> Reflexive equ -> Reflexive (equF RR equ).
  Proof.
    red. destruct x; auto.
  Qed.

End equ_equiv.

#[global] Corollary Equivalence_equ {E R}: Equivalence (gfp (@fequ E R _ eq)).
Proof. apply Equivalence_t. typeclasses eauto. Qed.

#[global] Hint Constructors equF : core.
Arguments equ_ {E R1 R2} RR eq t1 t2/.

(* A smarter version of this should be part of the [coinduction] library *)
Ltac step_in H :=
match type of H with
| gfp ?b ?x ?y => apply (gfp_fp b x y) in H
end;
simpl body in H.
Tactic Notation "step" "in" ident(H) := step_in H.

(* We assume JMeq to invert easily bisimilarity of dependently
	 typed constructors *)
Lemma equ_vis_invT {E X Y S} (e1 : E X) (e2 : E Y) (k1 : X -> ctree E S) k2 :
  Vis e1 k1 ≅ Vis e2 k2 ->
  X = Y.
Proof.
  intros EQ. 

	step in EQ. cbn in *; dependent induction EQ; auto.
Qed.

Lemma equ_vis_invE {E X S} (e1 e2 : E X) (k1 k2 : X -> ctree E S) :
  Vis e1 k1 ≅ Vis e2 k2 ->
  e1 = e2 /\ forall x, k1 x ≅ k2 x.
Proof.
  intros EQ; step in EQ.
	inv EQ.
	dependent destruction H1.
	dependent destruction H2.
	dependent destruction H.
	dependent destruction H4.
	auto.
Qed. 

Import CTree.
Import CTreeNotations.
Open Scope ctree.

(* Elementary equational theory *)
(* Example issue with universes *)
Lemma ctree_eta {E R} (t : ctree E R) : t ≅ go (observe t).
Proof.
	revert t; coinduction r CIH.
	intros.
	cbn.
	desobs t.	
	constructor; auto.
	constructor; auto.
	constructor; auto.
	(* Qed fails *)
	Restart. now step.
Qed. 

Lemma unfold_spin {E R} : @spin E R ≅ Tau spin.
Proof.
  exact (ctree_eta spin).
Qed.

Notation bind_ t k :=
  match observe t with
  | RetF r => k%function r
  | VisF e ke => Vis e (fun x => bind (ke x) k)
  | ForkF n ke => Fork n (fun x => bind (ke x) k)
  end.

Lemma unfold_bind {E R S} (t : ctree E R) (k : R -> ctree E S)
  : bind t k ≅ bind_ t k.
Proof.
	now step.
Qed.

Lemma unfold_iter {E R I} (step : I -> ctree E (I + R)) i: 
	iter step i ≅
    lr <- step i;;
    match lr with 
    | inl l => Tau (iter step l)
    | inr r => Ret r 
    end.
Proof.
	now step.
Qed.
                         
