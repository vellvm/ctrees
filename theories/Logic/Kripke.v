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
  | NotPureDone {X}: forall (e: E) (v: encode e) (x: X),
      not_pure (Finish e v x).
Global Hint Constructors not_pure: ctl.

Variant obs_with `{Encode E} (R: forall (e: E), encode e -> Prop): World E -> Prop :=
  | ObsWithCtor: forall (e: E) (v: encode e),
      R e v -> obs_with R (Obs e v).
Global Hint Constructors obs_with: ctl.

Variant finish_with `{Encode E} {X} (R: forall (e: E), encode e -> X -> Prop): World E -> Prop :=
  | FinishWithCtor: forall (e: E) (v: encode e) (x: X),
      R e v x -> finish_with R (Finish e v x).
Global Hint Constructors finish_with: ctl.

Variant done_with `{Encode E} {X} (R: X -> Prop): World E -> Prop :=
  |DoneWithCtor: forall (x: X),
      R x -> done_with R (Done x).
Global Hint Constructors done_with: ctl.

Definition return_eq `{Encode E} X (x: X)(w: World E): Prop :=
  done_with (eq x) w \/ finish_with (fun _ _ => eq x) w.
Global Hint Unfold return_eq: ctl.
  
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

(*| Polymorphic Kripke model over family M |*)
Class Kripke (M: Type -> Type) (meq: forall X, relation (M X)) E := {

    EncodeE :: Encode E;

    EquM :: forall X, Equivalence (meq X);
    
    (* - [ktrans] the transition relation over [M X * W] *)
    ktrans {X}: M X -> World E -> M X -> World E -> Prop;

    (* - [ktrans] does not allow rewriting with bisimulation,
       but there does exist a [t'] equivalent to [s'] *)
    ktrans_semiproper {X} : forall (t s s': M X) w w',
      meq X s t ->
      ktrans s w s' w' ->
      exists t', ktrans t w t' w' /\ meq X s' t';

    (* - [ktrans] only if [not_done] *)
    ktrans_not_done {X}: forall (t t': M X) (w w': World E),
      ktrans t w t' w' ->
      not_done w
  }.

Arguments EncodeE /.
Arguments EquM /.

Declare Custom Entry ctl.
Declare Scope ctl_scope.

(* Transition relation *)
Notation "[ t , w ]  ↦ [ t' , w' ]" := (ktrans t w t' w')
                                        (at level 78,
                                          right associativity): ctl_scope.
Local Open Scope ctl_scope.

Definition can_step `{Kripke M meq W} {X} (m: M X) (w: World W): Prop :=
  exists m' w', [m,w] ↦ [m',w'].

Global Instance can_step_proper `{Kripke M meq W} {X}:
  Proper (meq X ==> eq ==> iff) can_step.
Proof.
  unfold Proper, respectful, can_step, impl; intros t t' Heqt w w' Heqw;
    split; intros; subst; destruct H0 as (t_ & w_ & ?).
  - destruct (ktrans_semiproper t' t _ _ w_ Heqt H0) as (y' & TR' & EQ').
    now (exists y', w_).
  - symmetry in Heqt.
    destruct (ktrans_semiproper _ _ _ _ w_ Heqt H0) as (y' & TR' & EQ').
    now (exists y', w_).
Qed.

Lemma can_step_not_done `{Kripke M meq W} {X}: forall (t: M X) w,
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

Ltac ktrans_equ TR :=
  match type of TR with
  | @ktrans ?M ?mequ _ ?KMS _ ?y ?s ?z ?w => 
      match goal with
      | [H: @mequ ?X ?x ?y |- _] =>
          symmetry in H;
          let TR_ := fresh "TR" in
          let EQ_ := fresh "EQ" in
          let z_ := fresh "z" in
          destruct (ktrans_semiproper _ _ _ _ _
                      H TR) as (z_ & TR_ & EQ_)
      | [H: @mequ ?X ?x ?y |- _] =>
          let TR_ := fresh "TR" in
          let EQ_ := fresh "EQ" in
          let z_ := fresh "z" in
          destruct (ktrans_semiproper _ _ _ _ _ H TR) as (z_ & TR_ & EQ_)
      end
  end.
