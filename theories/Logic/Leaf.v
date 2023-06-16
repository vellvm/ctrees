(** * Leaves of an CTree *)

From CTree Require Import
     CTree
     Equ.

From Coq Require Import Morphisms Basics Program.Equality.
Import CTree.
Import CTreeNotations EquNotations.

(** ** Leaves of ctree *)

(** The [Leaf a t] predicate expresses that [t] has a [Ret] leaf with
    value [a].

    We provide the elementary structural lemmas to work with this
    predicate, and one main useful result relying on [Leaf]: the
    up-to bind closure [eqit_bind_clo] can be refined such that
    continuations need only be related over the leaves of the
    first operand of [bind].
    *)

Inductive Leaf {E C} {A: Type} (a: A) : ctree E C A -> Prop :=
 | LeafRet: forall t,
   observe t = RetF a ->
   Leaf a t
 | LeafTau: forall {X} (c: C X) b t k x,
   observe t = BrF b c k ->
   Leaf a (k x) ->
   Leaf a t
 | LeafVis: forall {X} (e: E X) t k x,
   observe t = VisF e k ->
   Leaf a (k x) ->
   Leaf a t.
#[global] Hint Constructors Leaf : ctree.

Notation "a ∈ t" := (Leaf a t) (at level 70).

(** Smart constructors *)
Lemma Leaf_Ret : forall E C R a,
  a ∈ (Ret a : ctree E C R).
Proof.
  intros; econstructor; reflexivity.
Qed.

Lemma Leaf_Br : forall E X Y C b (c: C X) (k: _ -> ctree E C Y) a x,
  a ∈ k x ->
  a ∈ Br b c k.
Proof.
  intros; econstructor; [reflexivity | eauto].
Qed.

Lemma Leaf_Vis : forall E C X Y (e : E X) (k : _ -> ctree E C Y) b x,
  b ∈ (k x) ->
  b ∈ (Vis e k).
Proof.
  intros * IN; econstructor 3; [reflexivity | eauto].
Qed.

(** Inversion lemmas *)
Lemma Leaf_Ret_inv : forall E C R (a b : R),
  Leaf (E := E) (C := C) b (Ret a) ->
  b = a.
Proof.
  intros * IN; inv IN; cbn in *; try congruence.
Qed.

Lemma Leaf_Tau_inv : forall E C X Y (c: C X) (k: _ -> ctree E C Y) b a,
  a ∈ Br b c k ->
  exists x, a ∈ k x.
Proof.
  intros * IN *; inv IN; cbn in *; try congruence.
  revert x H0.
  refine (match H in _ = u return match u with BrF b c0 k0 =>  _ | _ => False end with eq_refl => _ end).
  eauto.
Qed.

Lemma Leaf_Vis_inv : forall E C X Y (e : E X) (k : _ -> ctree E C Y) b,
  b ∈ Vis e k ->
  exists x, b ∈ k x.
Proof.
  intros * IN *; inv IN; cbn in *; try congruence.
  revert x H0.
  refine (match H in _ = u return match u with VisF c0 k0 =>  _ | _ => False end with eq_refl => _ end).
  eauto.
Qed.
