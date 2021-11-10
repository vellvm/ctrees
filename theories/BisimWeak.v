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
	Utils CTrees Equ Bisim.

(* end hide *)

Section Internal.

	(* We do not wish to observe internal non-deterministic choices.
		We therefore want to consider states, i.e. ctrees, that can
		be reached after a finite number of internal decisions, and
		are such that they are ready to expose an observation: their
		head constructor is either a Ret or a Vis.
		*)

  Context {E : Type -> Type} {R : Type}.

  Inductive internal_ : ctree' E R -> ctree' E R -> Prop :=

  | InternalStep b {n} (x : Fin.t n) k t :
    		internal_ (observe (k x)) t ->
    		internal_ (ChoiceF b n k) t

  | InternalStop {n} k k' x :
    		k x ≅ k' x -> (* Because [internal_] stops right there, we need to close explicitly up to [equ] if we want to be stable under it *)
    		internal_ (ChoiceF true n k) (observe (k' x)).

  Definition internal u v := internal_ (observe u) (observe v).

  Variant internal_refl : ctree E R -> ctree E R -> Prop :=
  | InternalRefl : forall u, internal_refl u u 
  | InternalRel  : forall u v, internal u v -> internal_refl u v.

End Internal.

Section wbisim.

  Context {E : Type -> Type} {R1 R2 : Type} (RR : R1 -> R2 -> Prop).

	(** * [matching]
	This relation captures the local challenge that two scheduled
	trees must solve. It corresponds from the more traditional
	bisimulation world to ensuring that they can take a small step
	emmitting the same event. *)

  Variant matchingL (bisim : ctree E R1 -> ctree E R2 -> Prop) :
    ctree E R1 -> ctree E R2 -> Prop :=
  | MatchLRet x y (RET : RR x y) :
     matchingL bisim (Ret x) (Ret y)
  | MatchLVis {X} (e : E X) k1 k2 
     (RET : forall v t', 
        internal_refl (k1 v) t' ->
        exists u', internal_refl (k2 v) u' /\ bisim t' u'):
     matchingL bisim (Vis e k1) (Vis e k2)
  . 
  Hint Constructors matchingL: core.

  Variant matchingR (bisim : ctree E R1 -> ctree E R2 -> Prop) :
    ctree E R1 -> ctree E R2 -> Prop :=
  | MatchRRet x y (RET : RR x y) :
     matchingR bisim (Ret x) (Ret y)
  | MatchRVis {X} (e : E X) k1 k2 
     (RET : forall v t', 
        internal_refl (k1 v) t' ->
        exists u', internal_refl (k2 v) u' /\ bisim t' u'):
     matchingR bisim (Vis e k1) (Vis e k2)
  . 
  Hint Constructors matchingR: core.

  Variant wbisimF (wbisim : ctree E R1 -> ctree E R2 -> Prop) :
    ctree E R1 -> ctree E R2 -> Prop :=

  | WBisim u t
            (SIMFI : forall u', internal u u' ->
              exists t', internal_refl t t' /\ wbisim u' t')
            (SIMBI : forall t', internal t t' ->
              exists u', internal_refl u u' /\ wbisim u' t')
            (SIMFE : forall u', schedule u u' ->
              exists t', schedule t t' /\ matchingL wbisim u' t')
            (SIMBE : forall t', schedule t t' ->
              exists u', schedule u u' /\ matchingR wbisim u' t')
               :
      wbisimF wbisim u t.
 
  Hint Constructors wbisimF: core.
(* 
  Definition wbisim_ eq : ctree E R1 -> ctree E R2 -> Prop :=
	fun t1 t2 => bisimF eq (observe t1) (observe t2). *)

  Lemma matchingL_mono u v sim sim'
              (IN : matchingL sim u v)
              (LE : sim <= sim') :
        matchingL sim' u v.
  Proof.
    inv IN; auto. constructor; intros. edestruct RET as (? & ? & ?); eauto.
    eexists; split; eauto. 
    apply LE; auto.
  Qed.
  Hint Resolve matchingL_mono: core.

  Lemma matchingR_mono u v sim sim'
              (IN : matchingR sim u v)
              (LE : sim <= sim') :
        matchingR sim' u v.
  Proof.
    inv IN; auto. constructor; intros. edestruct RET as (? & ? & ?); eauto.
    eexists; split; eauto. 
    apply LE; auto.
  Qed.
  Hint Resolve matchingR_mono: core.


  Program Definition fwbisim : mon (ctree E R1 -> ctree E R2 -> Prop) := {| body := wbisimF |}.
  Next Obligation.
   unfold pointwise_relation, impl, bisim_.
   intros ?? INC ?? EQ.
   constructor; inversion_clear EQ; intros. 
  - edestruct SIMFI as (? & ? & ?); eauto. 
  - edestruct SIMBI as (? & ? & ?); eauto. 
  - edestruct SIMFE as (? & ? & ?); eauto. 
  - edestruct SIMBE as (? & ? & ?); eauto. 
  Qed.

End wbisim.

(** associated relation *)
Definition wbisim {E R} := (gfp (@fbisim E R R eq)).
(* Notation bisim := (gfp (fbisim eq)). *)

(** associated companions  *)
Notation T_bis RR  := (t (B (fwbisim RR))).
Notation t_bis RR  := (t (fwbisim RR)).
Notation bt_bis RR := (bt (fwbisim RR)).

Infix "≈" := wbisim (at level 70).
Notation "x ≊ y" := (t_bis eq _ x y) (at level 79).
Notation "x [≊] y" := (bt_bis eq _ x y) (at level 79).

Arguments wbisim _ _ _ _/.
#[global] Hint Constructors wbisimF: core.
#[global] Hint Constructors matchingL: core.
#[global] Hint Constructors matchingR: core.
