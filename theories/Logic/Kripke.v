From Coq Require Import
  Relations
  Program.Basics
  Classes.Morphisms
  Classes.RelationPairs.

From ExtLib Require Import Structures.Monad.
From CTree Require Import Utils.Utils.
Generalizable All Variables.

(*| Polymorphic Kripke model over family M |*)
Class Kripke M `{Monad M} (mequ: forall X, relation (M X)) `{forall X, Equivalence (mequ X)} (W: Type) := {
    (* - [ktrans] the transition relation over [M X * W] *)
    ktrans {X}: rel (M X * option W) (M X * option W);

    (* - [ktrans] does not allow rewriting, but there does
       exist a [t'] equivalent to [s'] *)
    ktrans_semiproper {X} : forall (t s s': M X) w w',
      mequ X s t ->
      ktrans (s,w) (s',w') ->
      exists t', ktrans (t,w) (t',w') /\ mequ X s' t';

    (* - we always step from [Some w] to [Some w'] |*)
    ktrans_option_some {X} : forall (t t': M X) w w',
      ktrans (t, Some w) (t', w') ->
      exists x, w' = Some x
  }.

(*| Tactic to work with Eq TS product of equivalences |*)
Ltac destruct2 Heq :=
  let Ht := fresh "Heqt" in
  let Hs := fresh "Heqσ" in
  unfold fst, snd, RelCompFun in Heq;
  cbn in Heq; destruct Heq as (Ht & Hs);
  unfold fst, snd, RelCompFun in Ht, Hs; cbn in Ht, Hs.

Ltac split2 := unfold RelCompFun, fst, snd; cbn; split.

Declare Custom Entry ctl.
Declare Scope ctl_scope.

(* Transition relation *)
Notation "p ↦ p'" := (ktrans p p') (at level 78,
                         right associativity): ctl_scope.

(*| Compose relation [R] n-times with itself |*)
Fixpoint rel_iter {A}(eqA: relation A)`{Equivalence A eqA}(n: nat) (R: relation A): relation A :=
  match n with
  | 0%nat => eqA
  | (S n)%nat => fun a c => exists b, R a b /\ rel_iter eqA n R b c
  end.

Definition ktrans_trc `{Kripke M meq W} {X} (p p': M X * option W) :=
  exists n, rel_iter (meq _ * eq)%signature n ktrans p p'.

(* TRC relation *)
Notation "p ↦* p'" := (ktrans_trc p p') (at level 78,
                         right associativity): ctl_scope.

Definition can_step `{Kripke M meq W} {X} (m: M X * option W): Prop :=
  exists m' w', ktrans m (m', w').

Global Instance can_step_proper `{Kripke M meq W} {X}:
  Proper (meq X * eq ==> iff) can_step.
Proof.
  unfold Proper, respectful, can_step, impl; intros [t w] [t' w']; split; intros;
    destruct2 H2; subst; destruct H3 as (x & w & ?); subst.
  - destruct (ktrans_semiproper t' t _ _ w Heqt H2) as (y' & TR' & EQ').
    now (exists y', w).
  - symmetry in Heqt.
    destruct (ktrans_semiproper _ _ _ _ w Heqt H2) as (y' & TR' & EQ').
    now (exists y', w).
Qed.

Local Open Scope ctl_scope.
Global Hint Extern 2 =>
         match goal with
         | [ H: ?m ↦ ?m' |- can_step ?m ] => exists (fst m'), (snd m'); apply H
end: core.

Global Hint Extern 2 =>
         match goal with
         | [ H: (?t, Some ?w) ↦ (?t', Some _) |- _ ] => fail
         | [ H: (?t, Some ?w) ↦ (?t', ?w') |- _ ] =>
               let w_ := fresh "w" in
               let H_ := fresh "H" in
               destruct (ktrans_option_some t t' w w' H) as (w_ & H_); inv H
             end: core.

Ltac ktrans_equ TR :=
  match type of TR with
  | @ktrans _ _ ?mequ _ _ _ _ (?y,?s) (?z,?w) => 
      match goal with
      | [H: @mequ ?X ?x ?y |- _] =>
          symmetry in H;
          let TR_ := fresh "TR" in
          let EQ_ := fresh "EQ" in
          let z_ := fresh "z" in
          destruct (ktrans_semiproper _ _ _ _ _ H TR) as (z_ & TR_ & EQ_)
      | [H: @mequ ?X ?x ?y |- _] =>
          let TR_ := fresh "TR" in
          let EQ_ := fresh "EQ" in
          let z_ := fresh "z" in
          destruct (ktrans_semiproper _ _ _ _ _ H TR) as (z_ & TR_ & EQ_)
      end
  end.
