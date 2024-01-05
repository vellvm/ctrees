#[global] Set Warnings "-intuition-auto-with-star".

From Coq Require Import Fin.
From Coq Require Export Program.Equality.
From Coinduction Require Import
	coinduction rel tactics.
From ITree Require Import Basics.Basics.

Notation fin := Fin.t.

#[global] Arguments bt : simpl never.
Ltac next := unfold bt; cbn.
Tactic Notation "cbn*" := next.

Polymorphic Class MonadTrigger (E : Type -> Type) (M : Type -> Type) : Type :=
  mtrigger : forall {X}, E X -> M X.

Notation rel X Y := (X -> Y -> Prop).

Lemma t_gfp_bt : forall {X} `{CompleteLattice X} (b : mon X),
  t b (gfp (bt b)) == gfp b.
Proof.
  intros. cbn.
  rewrite <- enhanced_gfp. rewrite t_gfp.
  reflexivity.
Qed.

#[global] Instance t_weq : forall {X Y},
  Proper (weq ==> weq) (@t (rel X Y) _).
Proof.
  split; repeat red; intros.
  - destruct H0. exists x0; auto.
    repeat red. intros.
    apply H. apply H0.
    eapply (Hbody x0). { cbn. red. intros. apply H. apply H3. }
    apply H2.
  - destruct H0. exists x0; auto.
    repeat red. intros.
    apply H. apply H0.
    eapply (Hbody x0). { cbn. red. intros. apply H. apply H3. }
    apply H2.
Qed.

#[global] Instance gfp_weq : forall {X Y},
  Proper (weq ==> weq) (@gfp (rel X Y) _).
Proof.
  intros. intros ? ? ?. now apply t_weq.
Qed.

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
  | |- gfp ?b ?x ?y ?z => apply (proj2 (gfp_fp b x y z))
  | |- body (t ?b) ?R ?x ?y ?z => apply (bt_t b R x y z)
  | |- body (body (T ?b) ?f) ?R ?x ?y ?z => apply (bT_T b f R x y z)
  | |- gfp ?b ?x ?y => apply (proj2 (gfp_fp b x y))
  | |- body (t ?b) ?R ?x ?y => apply (bt_t b R x y)
  | |- body (body (T ?b) ?f) ?R ?x ?y => apply (bT_T b f R x y)
  | |- gfp ?b ?x => apply (proj2 (gfp_fp b x))
  | |- body (t ?b) ?R ?x => apply (bt_t b R x)
  | |- body (body (T ?b) ?f) ?R ?x => apply (bT_T b f R x)
  end.

Ltac step := first [step_ | red; step_].

Ltac step_in H :=
  match type of H with
  | gfp ?b ?x ?y ?z => apply (gfp_fp b x y z) in H
  | body (t ?b) ?R ?x ?y ?z => apply (bt_t b R x y z) in H
  | gfp ?b ?x ?y => apply (gfp_fp b x y) in H
  | body (t ?b) ?R ?x ?y => apply (bt_t b R x y) in H
  | gfp ?b ?x => apply (gfp_fp b x) in H
  | body (t ?b) ?R ?x => apply (bt_t b R x) in H
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

#[global] Notation inhabited X := { x: X | True}.

Definition sum_rel {A B1 B2} Ra Rb : rel (A + B1) (A + B2) :=
  fun ab ab' =>
    match ab, ab' with
    | inl a, inl a' => Ra a a'
    | inr b, inr b' => Rb b b'
    | _, _ => False
    end.

