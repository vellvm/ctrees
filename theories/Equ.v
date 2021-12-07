(* begin hide *)
From Coq Require Import RelationClasses Program.

From Coinduction Require Import
	coinduction rel tactics.

From CTree Require Import
	 Utils
     CTrees
     Shallow.
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
  | Eq_Choice b {n} (k1 : Fin.t n -> _) (k2 : Fin.t n -> _)
              (REL : forall i, eq (k1 i) (k2 i)) :
      equF eq (ChoiceF b n k1) (ChoiceF b n k2)
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
  Notation T  := (coinduction.T (fequ (E := E) RR)).
  Notation t  := (coinduction.t (fequ (E := E) RR)).
  Notation bt := (coinduction.bt (fequ (E := E) RR)).
  Definition seq: relation (ctree E R) := eq.

  (** [eq] is a post-fixpoint, thus [const eq] is below [t] *)
	Lemma refl_t {RRR: Reflexive RR}: const seq <= t.
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

	Lemma Choice_eq1 T b b' n m k h: @ChoiceF E R T b n k = @ChoiceF E R T b' m h -> b = b' /\ n=m.
	Proof. intro H. now dependent destruction H. Qed.

	Lemma Choice_eq2 T b n k h: @ChoiceF E R T b n k = @ChoiceF E R T b n h -> k=h.
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
			destruct (Choice_eq1 _ _ _ _ _ _ _ H2); subst.
			destruct (Choice_eq2 _ _ _ _ _ H2).
			constructor. intros i. now (exists (k0 i)).
	Qed.

	(** thus bisimilarity, [t R], [b (t R)] and [T f R] are always equivalence relations *)
	#[global] Instance Equivalence_et `{Equivalence _ RR} S: Equivalence (t S).
	Proof. apply Equivalence_t. apply refl_t. apply square_t. apply converse_t. Qed.
	#[global] Instance Equivalence_T `{Equivalence _ RR} f S: Equivalence (T f S).
	Proof.
    apply Equivalence_T. apply refl_t. apply square_t. apply converse_t. Qed.
	#[global] Instance Equivalence_bt `{Equivalence _ RR} S: Equivalence (bt S).
	Proof. apply Equivalence_bt. apply refl_t. apply square_t. apply converse_t. Qed.

	(* This one is a bit annoyingly adhoc, but useful for unfolding laws *)
  #[global] Instance Reflexive_equF (equ : ctree E R -> ctree E R -> Prop) :
    Reflexive RR -> Reflexive equ -> Reflexive (equF RR equ).
  Proof.
    red. destruct x; auto.
  Qed.

End equ_equiv.

#[global] Instance Equivalence_equ {E R}: Equivalence (gfp (@fequ E R _ eq)).
Proof. apply Equivalence_et. typeclasses eauto. Qed.

#[global] Hint Constructors equF : core.
Arguments equ_ {E R1 R2} RR eq t1 t2/.

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

Lemma equF_vis_invT {E X Y S} (e1 : E X) (e2 : E Y) (k1 : X -> ctree E S) k2 :
  equF eq (equ eq) (CTrees.VisF e1 k1) (CTrees.VisF e2 k2) ->
  X = Y.
Proof.
  intros EQ.
	dependent induction EQ; auto.
Qed.

Lemma equF_vis_invE {E X S} (e1 e2 : E X) (k1 k2 : X -> ctree E S) :
  equF eq (equ eq) (CTrees.VisF e1 k1) (CTrees.VisF e2 k2) ->
  e1 = e2 /\ forall x, equ eq (k1 x) (k2 x).
Proof.
  intros EQ.
	inv EQ.
	dependent destruction H; dependent destruction H4; auto.
Qed.

Lemma equF_choice_invT {E S b b' n m} (k1 : _ -> ctree E S) k2 :
  equF eq (equ eq) (CTrees.ChoiceF b n k1) (CTrees.ChoiceF b' m k2) ->
  n = m /\ b = b'.
Proof.
  intros EQ.
	dependent induction EQ; auto.
Qed.

Lemma equF_choice_invE {E S b n} (k1 : _ -> ctree E S) k2 :
  equF eq (equ eq) (CTrees.ChoiceF b n k1) (CTrees.ChoiceF b n k2) ->
  forall x, equ eq (k1 x) (k2 x).
Proof.
  intros EQ.
	inv EQ.
	dependent destruction H; auto.
Qed.

#[global] Instance equ_observe {E R} :
  Proper (equ eq ==> going (equ eq)) (@observe E R).
Proof.
  constructor. step in H. now step.
Qed.

#[global] Instance equ_ChoiceF {E R} b n :
  Proper (pointwise_relation _ (equ eq) ==> going (equ eq)) (@ChoiceF E R _ b n).
Proof.
  constructor. red in H. step. econstructor; eauto.
Qed.

#[global] Instance equ_VisF {E R X} (e : E X) :
  Proper (pointwise_relation _ (equ eq) ==> going (equ eq)) (@VisF E R _ _ e).
Proof.
  constructor. red in H. step. econstructor; eauto.
Qed.

#[global] Instance observing_sub_equ E R :
  subrelation (@observing E R R eq) (equ eq).
Proof.
  repeat intro.
  step. rewrite (observing_observe H). apply Reflexive_equF; eauto.
Qed.

#[global] Instance equ_eq_equF {E R r} :
  Proper (going (gfp (@fequ E R R eq)) ==> eq ==> flip impl)
	     (equF eq (t_equ eq r)).
Proof.
  unfold Proper, respectful, flip, impl. intros. subst.
  inv H. step in H0. inv H0; inv H1; auto.
  - invert.
    subst. constructor. intros. rewrite REL. auto.
  - invert.
    subst. constructor. intros. rewrite REL. auto.
Qed.

#[global] Instance eq_equ_equF {E R r} :
  Proper (eq ==> going (gfp (@fequ E R R eq)) ==> flip impl)
	     (equF eq (t_equ eq r)).
Proof.
  unfold Proper, respectful, flip, impl. intros. subst.
  inv H0. step in H. inv H; inv H1; auto.
  - invert.
    subst. constructor. intros. rewrite REL. auto.
  - invert.
    subst. constructor. intros. rewrite REL. auto.
Qed.

#[global] Instance gfp_bt_equ {E R r} :
	 Proper (gfp (@fequ E R R eq) ==> gfp (@fequ E R R eq) ==> flip impl)
	  (bt_equ eq r).
Proof.
	unfold Proper, respectful, flip, impl.
	intros.
	pose proof (gfp_bt (fequ eq) r).
	etransitivity; [|etransitivity]; [|apply H1 |].
	apply H2; assumption.
	apply H2; symmetry; assumption.
Qed.

(* Elementary equational theory *)
Import CTree.
Import CTreeNotations.
Open Scope ctree.

Lemma ctree_eta {E R} (t : ctree E R) : t ≅ go (observe t).
Proof.
  now step.
Qed.

Lemma unfold_spin {E R} : @spin E R ≅ TauI spin.
Proof.
  exact (ctree_eta spin).
Qed.

Notation bind_ t k :=
  match observe t with
  | RetF r => k%function r
  | VisF e ke => Vis e (fun x => bind (ke x) k)
  | ChoiceF b n ke => Choice b n (fun x => bind (ke x) k)
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
  | inl l => TauI (iter step l)
  | inr r => Ret r
  end.
Proof.
	now step.
Qed.

