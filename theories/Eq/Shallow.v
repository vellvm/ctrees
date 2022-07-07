(** * Shallow equivalence *)

(** Equality under [observe]: file adapted from the equivalent concept in [itree].

[[
  observing eq t1 t2 <-> t1.(observe) = t2.(observe)
]]

  We actually define a more general relation transformer
  [observing] to lift arbitrary relations through [observe].
 *)

(* begin hide *)
From CTree Require Import
     CTree.

From Coq Require Import
     Classes.RelationClasses
     Classes.Morphisms
     Setoids.Setoid
     Relations.Relations
     JMeq.

Set Implicit Arguments.
(* end hide *)

Definition eqeq {A : Type} (P : A -> Type) {a1 a2 : A} (p : a1 = a2) : P a1 -> P a2 -> Prop :=
  match p with
  | eq_refl => eq
  end.

Definition pweqeq {R1 R2} (RR : R1 -> R2 -> Prop) {X1 X2 : Type} (p : X1 = X2)
  : (X1 -> R1) -> (X2 -> R2) -> Prop :=
  match p with
  | eq_refl => fun k1 k2 => forall x, RR (k1 x) (k2 x)
  end.

Lemma pweqeq_mon {R1 R2} (RR1 RR2 : R1 -> R2 -> Prop) X1 X2 (p : X1 = X2) k1 k2
  : (forall r1 r2, RR1 r1 r2 -> RR2 r1 r2) -> pweqeq RR1 p k1 k2 -> pweqeq RR2 p k1 k2.
Proof.
  destruct p; cbn; auto.
Qed.

(** ** [observing]: Lift relations through [observe]. *)
Record observing {E R1 R2}
           (eq_ : ctree' E R1 -> ctree' E R2 -> Prop)
           (t1 : ctree E R1) (t2 : ctree E R2) : Prop :=
  observing_intros
  { observing_observe : eq_ (observe t1) (observe t2) }.
#[global] Hint Constructors observing: core.

Section observing_relations.

Context {E : Type -> Type} {R : Type}.
Variable (eq_ : ctree' E R -> ctree' E R -> Prop).

#[global] Instance observing_observe_ :
  Proper (observing eq_ ==> eq_) (@observe E R).
Proof. intros ? ? []; cbv; auto. Qed.

#[global] Instance observing_go : Proper (eq_ ==> observing eq_) (@go E R).
Proof. cbv; auto. Qed.

#[global] Instance monotonic_observing eq_' :
  subrelation eq_ eq_' ->
  subrelation (observing eq_) (observing eq_').
Proof. intros ? ? ? []; cbv; eauto. Qed.

#[global] Instance Equivalence_observing :
  Equivalence eq_ -> Equivalence (observing eq_).
Proof.
  intros []; split; cbv; auto.
  - intros ? ? []; auto.
  - intros ? ? ? [] []; eauto.
Qed.

End observing_relations.

(** ** Unfolding lemmas for [bind] *)

#[global] Instance observing_bind {E R S} :
  Proper (observing eq ==> eq ==> observing eq) (@CTree.bind E R S).
Proof.
  repeat intro; subst. constructor. unfold observe. cbn.
  rewrite (observing_observe H). reflexivity.
Qed.

Lemma bind_ret_ {E R S} (r : R) (k : R -> ctree E S) :
  observing eq (CTree.bind (Ret r) k) (k r).
Proof. constructor; reflexivity. Qed.

Lemma bind_Guard_ {E R} U t (k: U -> ctree E R) :
  observing eq (CTree.bind (Guard t) k) (Guard (CTree.bind t k)).
Proof. constructor; reflexivity. Qed.

Lemma bind_vis_ {E R U V} (e: E V) (ek: V -> ctree E U) (k: U -> ctree E R) :
  observing eq
    (CTree.bind (Vis e ek) k)
    (Vis e (fun x => CTree.bind (ek x) k)).
Proof. constructor; reflexivity. Qed.

(** Unfolding lemma for [aloop]. There is also a variant [unfold_aloop]
    without [Tau]. *)
Lemma unfold_aloop_ {E A B} (f : A -> ctree E (A + B)) (x : A) :
  observing eq
    (CTree.iter f x)
    (CTree.bind (f x) (fun lr => CTree.on_left lr l (Guard (CTree.iter f l)))).
Proof. constructor; reflexivity. Qed.

(** Unfolding lemma for [forever]. *)
Lemma unfold_forever_ {E R S} (t: ctree E R):
  observing eq (@CTree.forever E R S t) (CTree.bind t (fun _ => Guard (CTree.forever t))).
Proof. econstructor. reflexivity. Qed.

(** ** [going]: Lift relations through [go]. *)

Inductive going {E R1 R2} (r : ctree E R1 -> ctree E R2 -> Prop)
          (ot1 : ctree' E R1) (ot2 : ctree' E R2) : Prop :=
| going_intros : r (go ot1) (go ot2) -> going r ot1 ot2.
#[global] Hint Constructors going: core.

Lemma observing_going {E R1 R2} (eq_ : ctree' E R1 -> ctree' E R2 -> Prop) ot1 ot2 :
  going (observing eq_) ot1 ot2 <-> eq_ ot1 ot2.
Proof.
  split; auto.
  intros [[]]; auto.
Qed.

Section going_relations.

Context {E : Type -> Type} {R : Type}.
Variable (eq_ : ctree E R -> ctree E R -> Prop).

#[global] Instance going_go : Proper (going eq_ ==> eq_) (@go E R).
Proof. intros ? ? []; auto. Qed.

#[global] Instance monotonic_going eq_' :
  subrelation eq_ eq_' ->
  subrelation (going eq_) (going eq_').
Proof. intros ? ? ? []; eauto. Qed.

#[global] Instance Equivalence_going :
  Equivalence eq_ -> Equivalence (going eq_).
Proof.
  intros []; constructor; cbv; eauto.
  - intros ? ? []; auto.
  - intros ? ? ? [] []; eauto.
Qed.

End going_relations.
