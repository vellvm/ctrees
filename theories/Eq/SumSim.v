From Coq Require Import
     Basics
     RelationClasses
     Program.Equality
     Logic.Eqdep.

From Coinduction Require Import
     coinduction rel tactics.

From ITree Require Import
     Core.Subevent.

From CTree Require Import
     CTree
     Utils
     Eq.Equ
     Eq.Shallow
     Eq.Trans.

From RelationAlgebra Require Export
     rel monoid srel.

Import CTree.
Set Implicit Arguments.

(* TODO: Decide where to set this *)
Arguments trans : simpl never.

(*| The function defining weak simulation (left plays): [trans] of [L] must be answered by
  [ltrans] of [L +' R] plays. |*)
Program Definition wsl {L R C X} `{B0 -< C}:
  mon (ctree L C X -> ctree (L +' R) C X -> Prop) :=
  {| body R t u :=
    forall l t' (x: X), trans (obs l x) t t' -> exists u' , ltrans l x u u' /\ R t' u'
  |}.
Next Obligation.
  edestruct H1 as (u' & l' & ?); eauto.
Qed.

(*| The function defining weak simulation (right plays): [trans] of [R] must be answered by
  [rtrans] of [L +' R] plays. |*)
Program Definition wsr {L R C X} `{B0 -< C}:
  mon (ctree R C X -> ctree (L +' R) C X -> Prop) :=
  {| body R t u :=
    forall l t' (x: X), trans (obs l x) t t' -> exists u' , rtrans l x u u' /\ R t' u'
  |}.
Next Obligation.
  edestruct H1 as (u' & l' & ?); eauto.
Qed.

#[global] Instance weq_wsl : forall {L R C X} `{B0 -< C},
    Proper (weq ==> weq) (@wsl L R C X _).
  Proof.
    cbn; intros; split; intros; apply H1 in H2 as (? & ? & ?);
      exists x1; split.
    - apply H2; now apply H0.
    - now apply H0.
    - apply H2; now apply H0.
    - now apply H0.
  Qed.

Definition wsiml {L R C X} `{HasStuck : B0 -< C} :=
  (gfp (@wsl L R C X _): hrel _ _).

#[global] Instance weq_wsr : forall {L R C X} `{B0 -< C},
    Proper (weq ==> weq) (@wsr L R C X _).
  Proof.
    cbn; intros; split; intros; apply H1 in H2 as (? & ? & ?);
      exists x1; split.
    - apply H2; now apply H0.
    - now apply H0.
    - apply H2; now apply H0.
    - now apply H0.
  Qed.

Definition wsimr {L R C X} `{HasStuck : B0 -< C} :=
  (gfp (@wsr L R C X _): hrel _ _).
