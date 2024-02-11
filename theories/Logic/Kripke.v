From Coq Require Import
  Relations
  Program.Basics
  Classes.Morphisms.

From ExtLib Require Import Structures.Monad.
From CTree Require Import
  Utils.Utils
  Events.Core
  Utils.Trc.

Generalizable All Variables.

Variant World (E:Type@{eff}) `{Encode E} :=
  | Pure
  | Obs (e : E) (v : encode e)
  | Done {X} (x: X)
  | Finish {X} (e: E) (v: encode e) (x: X).    
Global Hint Constructors World: ctl.

Arguments Pure {E} {_}.
Arguments Obs {E} {_} e v.
Arguments Done {E} {_} {X} x.
Arguments Finish {E} {_} {X} e v x.

Variant not_pure `{Encode E}: World E -> Prop :=
  | NotPureObs: forall (e: E) (v: encode e),
      not_pure (Obs e v)
  | NotPureFinish {X}: forall (e: E) (v: encode e) (x: X),
      not_pure (Finish e v x).
Global Hint Constructors not_pure: ctl.

Variant is_pure `{Encode E}: World E -> Prop :=
  | IsPurePure:
      is_pure Pure
  | IsPureDone {X}: forall (x: X),
      is_pure (Done x).
Global Hint Constructors is_pure: ctl.

Variant done_with `{Encode E} {X} (R: X -> World E -> Prop): World E -> Prop :=
  | DoneWithDone: forall (x: X),
      R x Pure -> done_with R (Done x)
  | DoneWithFinish: forall (e: E) (v: encode e) (x: X),
      R x (Obs e v) -> done_with R (Finish e v x).
Global Hint Constructors done_with: ctl.

Variant vis_with `{Encode E} R : World E -> Prop :=
  | VisWithVis: forall (e: E) (v: encode e),
      R e v -> vis_with R (Obs e v).
Global Hint Constructors vis_with: ctl.

Inductive return_val `{Encode E} X (x: X): World E -> Prop :=
| ReturnValDone:
    return_val X x (Done x)
| ReturnValFinish: forall (e: E) (v: encode e),
    return_val X x (Finish e v x).
Global Hint Constructors return_val: ctl.
  
Variant not_done `{Encode E}: World E -> Prop :=
  | NotDonePure: not_done Pure
  | NotDoneObs: forall (e: E) (v: encode e),
      not_done (Obs e v).
Global Hint Constructors not_done: ctl.

Variant is_done `{Encode E}: World E -> Prop :=
  | DoneDone: forall X (x: X), is_done (Done x)
  | DoneFinish: forall X (e: E) (v: encode e) (x: X),
      is_done (Finish e v x).
Global Hint Constructors is_done: ctl.

Definition not_done_dec `{Encode E}: forall (w: World E),
    {not_done w} + {is_done w}.
Proof.
  dependent destruction w; intros.
  - left; econstructor.
  - left; econstructor.
  - right; econstructor. 
  - right; econstructor.
Qed.

Definition not_pure_dec `{Encode E}: forall (w: World E),
    {not_pure w} + {is_pure w}.
Proof.
  dependent destruction w; intros.
  - right; econstructor. 
  - left; econstructor.
  - right; econstructor. 
  - left; econstructor.
Qed.

(*| Polymorphic Kripke model over family M |*)
Class Kripke (M: Type -> Type) (E: Type) `{HE: Encode E} := {

    (* - [ktrans] the transition relation over [M X * W] *)
    ktrans {X}: M X -> World E -> M X -> World E -> Prop;

    (* - [ktrans] only if [not_done] *)
    ktrans_not_done {X}: forall (t t': M X) (w w': World E),
      ktrans t w t' w' ->
      not_done w;

    (* - [ktrans] preserves impure effects *)
    ktrans_not_pure {X}: forall (t t': M X) (w w': World E),
      ktrans t w t' w' ->
      not_pure w ->
      not_pure w'
  }.

Declare Custom Entry ctl.
Declare Scope ctl_scope.

(* Transition relation *)
Notation "[ t , w ]  ↦ [ t' , w' ]" :=
  (ktrans t w t' w')
    (at level 78,
      right associativity): ctl_scope.
Local Open Scope ctl_scope.

Definition can_step `{Kripke M W} {X} (m: M X) (w: World W): Prop :=
  exists m' w', [m,w] ↦ [m',w'].

Lemma can_step_not_done `{Kripke M W} {X}: forall (t: M X) w,
    can_step t w ->
    not_done w.
Proof.
  intros.
  destruct H0 as (t' & w' & TR).
  now apply ktrans_not_done in TR.
Qed.
Global Hint Resolve can_step_not_done: ctl.

Ltac world_inv :=
  match goal with
  | [H: @Obs ?E ?HE ?e ?x = ?w |- _] =>
      dependent destruction H
  | [H: @Pure ?E ?HE = ?w |- _] =>
      dependent destruction H
  | [H: @Done ?E ?HE ?X ?x = ?w |- _] =>
      dependent destruction H
  | [H: @Finish ?E ?HE ?X ?e ?v ?x = ?w |- _] =>
      dependent destruction H
  | [H: ?w = @Obs ?E ?HE ?e ?x |- _] =>
      dependent destruction H
  | [H: ?w = @Pure ?E ?HE |- _] =>
      dependent destruction H
  | [H: ?w = @Done ?E ?HE ?X ?x |- _] =>
      dependent destruction H
  | [H: ?w = @Finish ?E ?HE ?X ?e ?v ?x |- _] =>
      dependent destruction H
  end.
Global Hint Extern 2 => world_inv: ctl.
