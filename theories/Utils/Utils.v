#[export] Set Warnings "-intuition-auto-with-star".
#[export] Set Warnings "-warn-library-file-stdlib-vector".

From Stdlib Require Import Fin.
From Stdlib Require Export Program.Equality.
From Coinduction Require Import all.
From ITree Require Import Basics.Basics.
From CTree Require Export coinduction_addon.
       
Notation fin := Fin.t.

Polymorphic Class MonadTrigger (E : Type -> Type) (M : Type -> Type) : Type :=
  mtrigger : forall {X}, E X -> M X.

Polymorphic Class MonadBr (B : Type -> Type) (M : Type -> Type) : Type :=
  mbr : forall X (b: B X), M X.

Polymorphic Class MonadStep (M : Type -> Type) : Type :=
  mstep : M unit.

Polymorphic Class MonadStuck (M : Type -> Type) : Type :=
  mstuck : forall X, M X.

Notation rel X Y := (X -> Y -> Prop).
Notation rel1 E F := (forall X Y, E X -> F Y -> Prop).

Ltac invert :=
  match goal with
  | h : existT _ _ _ = existT _ _ _ |- _ => dependent induction h
  end.

Ltac copy h :=
  let foo := fresh "cpy" in
  assert (foo := h).

Ltac break :=
  repeat match goal with
         | h : _ \/ _  |- _ => destruct h
         | h : _ /\ _  |- _ => destruct h
         | h : exists x, _ |- _ => destruct h
         end.

Ltac break_match_in H :=
  match type of H with
  | context [ match ?x with _ => _ end ] => destruct x eqn:? end.

(* A smarter version of this should be part of the [coinduction] library *)

Ltac step_ :=
  match goal with
  | |- gfp ?b ?x ?y ?z => apply (proj1 (gfp_fp b x y z))
  | |- elem ?R ?x ?y ?z => apply (b_chain R x y z)
  | |- gfp ?b ?x ?y => apply (proj1 (gfp_fp b x y))
  | |- elem ?R ?x ?y => apply (b_chain R x y)
  | |- gfp ?b ?x => apply (proj1 (gfp_fp b x))
  | |- elem ?R ?x => apply (b_chain R x)
  end.

Ltac step := first [step_ | red; step_].

Ltac step_in H :=
  match type of H with
  | gfp ?b ?x ?y ?z => apply (gfp_fp b x y z) in H
  | gfp ?b ?x ?y => apply (gfp_fp b x y) in H
  | gfp ?b ?x => apply (gfp_fp b x) in H
  | _ => red in H; step_in H
  end.
Tactic Notation "step" "in" ident(H) := step_in H.

Class Injective {A B}(R: rel A B) := {
    inj: forall x x' y, R x y /\ R x' y -> x = x';
  }.

Class Deterministic {A B}(R: rel A B) := {
    det: forall x y y', R x y /\ R x y' -> y = y';
  }.

#[global] Instance Injective_eq A: @Injective A A eq.
Proof.
  split; intros ? ? ? [H H'].
  subst; reflexivity.
Qed.

#[global] Instance Deterministic_eq A: @Deterministic A A eq.
Proof.
  split; intros ? ? ? [H H'].
  subst; reflexivity.
Qed.

Ltac do_inj :=
  match goal with
  | [ _: Injective ?L, H: ?L ?x ?y, H': ?L ?x' ?y |- _ ] =>
      pose proof (@inj _ _ L _ _ _ _ (conj H H')) as RWTinj;
      rewrite <- RWTinj in *;
      clear RWTinj H'
  end.

Ltac do_det :=
  match goal with
  | [ _: Deterministic ?L, H: ?L ?x ?y, H': ?L ?x ?y' |- _ ] =>
      pose proof (@det _ _ L _ _ _ _ (conj H H')) as RWTdet;
      rewrite <- RWTdet in *;
      clear RWTdet H'
  end.

(* #[global] Notation inhabited X := { x: X | True}. *)

Definition sum_rel {A1 A2 B1 B2} Ra Rb : rel (A1 + B1) (A2 + B2) :=
  fun ab ab' =>
    match ab, ab' with
    | inl a, inl a' => Ra a a'
    | inr b, inr b' => Rb b b'
    | _, _ => False
    end.

Ltac ex  :=  eexists.
Ltac ex2 := do 2 eexists.
Ltac ex3 := do 3 eexists.
Ltac split3 := split; [| split].
Ltac split4 := split; [| split; [| split]].
Ltac edestruct3 H := edestruct H as (? & ? & ?).
Ltac edestruct4 H := edestruct H as (? & ? & ? & ?).
Ltac edestruct5 H := edestruct H as (? & ? & ? & ? & ?).

(* Simple inhabited class in the sytle of stdpp.
   Long term to do: use stdpp
 *)
Class Inhabited (A : Type) : Type := populate { inhabitant : A }.
Global Hint Mode Inhabited ! : typeclass_instances.
Global Arguments populate {_} _ : assert.
