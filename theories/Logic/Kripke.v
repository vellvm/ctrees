From Coq Require Import
  Relations
  Program.Basics
  Classes.Morphisms
  Classes.RelationPairs.

From CTree Require Import Utils.Utils.
Generalizable All Variables.

(*| Polymorphic Kripke model over family M |*)
Class Kripke (M: Type -> Type)(W: Type) := {
    (* - [ktrans] the transition relation over [M X * W] *)
    ktrans {X}: rel (M X * W) (M X * W);

    (* - refinement relation between states *)
    mequ X: relation (M X);

    (* - Equivalence [equ] *)
    equivalence_mequ {X} :: Equivalence (mequ X);
    
    (* - [ktrans] does not allow rewriting, but there does
       exist a [t'] for which the rewriting makes sense. *)
    ktrans_semiproper {X} : forall (t s s': M X) w w',
      mequ X s t ->
      ktrans (s,w) (s',w') ->
      exists t', ktrans (t,w) (t',w') /\ mequ X s' t';
  }.
Global Hint Mode Kripke ! +: core.

(*| Tactic to work with Eq TS product of equivalences |*)
Ltac destruct2 Heq :=
  let Ht := fresh "Heqt" in
  let Hs := fresh "Heqσ" in
  unfold fst, snd, RelCompFun in Heq;
  cbn in Heq; destruct Heq as (Ht & Hs);
  unfold fst, snd, RelCompFun in Ht, Hs; cbn in Ht, Hs.

Declare Custom Entry ctl.
Declare Scope ctl_scope.

(* Transition relation *)
Notation "p ↦ p'" := (ktrans p p') (at level 78,
                         right associativity): ctl_scope.

Inductive trc{A}(R: relation A): relation A :=
| TrcRefl: forall (a: A), trc R a a
| TrcTrans: forall (a b c: A),
  R a b ->
  trc R b c ->
  trc R a c.
Global Hint Constructors trc: core.

(* TRC relation *)
Notation "p ↦* p'" := (trc ktrans p p') (at level 78,
                         right associativity): ctl_scope.

Definition can_step `{Kripke M W} {X} (m: M X * W): Prop :=
  exists m' w', ktrans m (m', w').

Global Instance can_step_proper `{Kripke M W} {X}:
  Proper (mequ X * eq ==> iff) can_step.
Proof.
  unfold Proper, respectful, can_step, impl; intros [t w] [t' w']; split; intros;
    destruct2 H0; subst; destruct H1 as (x & w & ?); subst.
  - destruct (ktrans_semiproper t' t _ _ w Heqt H0)
      as (y' & TR' & EQ').
    now (exists y', w).
  - symmetry in Heqt.
    destruct (ktrans_semiproper _ _ _ _ w Heqt H0)
      as (y' & TR' & EQ').
    now (exists y', w).
Qed.

Ltac ktrans_equ Ht :=
  match type of Ht with
  | ktrans ?y ?z => 
      match goal with
      | [H: mequ ?X ?x ?y |- _] =>
          symmetry in H;
          let TR := fresh "TR" in
          let EQ := fresh "EQ" in
          let z := fresh "z" in
          destruct (ktrans_semiproper _ _ _ _ _ H Ht) as (z & TR & EQ)
      | [H: mequ ?X ?x ?y |- _] =>
          let TR := fresh "TR" in
          let EQ := fresh "EQ" in
          let z := fresh "z" in
          destruct (ktrans_semiproper _ _ _ _ _ H Ht) as (z & TR & EQ)
      end
  end.
