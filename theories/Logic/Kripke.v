From Coq Require Import
  Relations
  Program.Basics
  Classes.Morphisms
  Classes.RelationPairs.

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

Variant non_pure `{Encode E}: World E -> Prop :=
  | NonPureObs: forall (e: E) (v: encode e),
      non_pure (Obs e v)
  | NonPureDone {X}: forall (e: E) (v: encode e) (x: X),
      non_pure (Finish e v x).
Global Hint Constructors non_pure: ctl.

Variant is_done_with `{Encode E}{X}: World E -> X -> Prop :=
  | IsDoneCtor: forall (x: X), is_done_with (Done x) x
  | IsDoneFinish: forall (x: X) (e: E) (v: encode e),
      is_done_with (Finish e v x)  x.
Global Hint Constructors is_done_with: ctl.

Variant not_done `{Encode E}: World E -> Prop :=
  | NotDonePure: not_done Pure
  | NotDoneObs: forall (e: E) (v: encode e),
      not_done (Obs e v).
Global Hint Constructors not_done: ctl.

Definition is_done_dec`{Encode E}: forall (w: World E),
    {exists X (x: X), is_done_with w x} + {not_done w}.
Proof.
  destruct w.
  - right; constructor.
  - right; econstructor.
  - left; exists X, x; constructor.
  - left; exists X, x; constructor. 
Qed.

Definition non_pure_dec `{Encode E}: forall (w: World E),
    {w = Pure} + {exists X (x:X), w = Done x} + {non_pure w}.
Proof.
  destruct w; try (right; constructor). 
  - left; left; reflexivity.
  - left; right; eauto.  
Qed.  

Lemma not_done_done_with`{Encode E}{X}: forall (w: World E)(x:X),
    is_done_with w x -> ~ not_done w.
Proof.
  intros; inv H0; intro Hcontra; inv Hcontra.
Qed.
Global Hint Resolve not_done_done_with: ctl.

(*| Polymorphic Kripke model over family M |*)
Class Kripke (M: Type -> Type) (meq: forall X, relation (M X)) E := {

    EncodeE :: Encode E;

    EquM :: forall X, Equivalence (meq X);
    
    (* - [ktrans] the transition relation over [M X * W] *)
    ktrans {X}: rel (M X * World E) (M X * World E);

    (* - [ktrans] does not allow rewriting with bisimulation,
       but there does exist a [t'] equivalent to [s'] *)
    ktrans_semiproper {X} : forall (t s s': M X) w w',
      meq X s t ->
      ktrans (s,w) (s',w') ->
      exists t', ktrans (t,w) (t',w') /\ meq X s' t';

    (* - we always step from impore [w] to impure [w']  |*)
    ktrans_started {X} : forall (t t': M X) w w',
      ktrans (t, w) (t', w') ->
      non_pure w ->
      non_pure w';

    (* - If [ktrans] steps, [w] is not done *)
    ktrans_done {X}: forall (t t': M X) w w',
      ktrans (t, w) (t', w') ->
      not_done w;
  }.

Arguments EncodeE /.
Arguments EquM /.

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
Local Open Scope ctl_scope.

Definition ktrans_trc `{Kripke M meq W} {X} p p' :=
  trc (meq X * eq)%signature ktrans p p'.
Arguments ktrans_trc /.
Global Hint Unfold ktrans_trc: ctl.

(* TRC relation *)
Notation "p ↦* p'" := (ktrans_trc p p') (at level 78,
                          right associativity): ctl_scope.

Lemma ktrans_iter_semiproper `{Kripke M meq W} {X} :
  forall (t s s': M X) w w' n,
    meq X s t ->
    rel_iter (meq X * eq)%signature n ktrans (s, w) (s', w') ->
    exists t', rel_iter (meq X * eq)%signature n ktrans (t, w) (t', w') /\ meq X s' t'.
Proof.
  intros * EQ TR.           
  revert TR EQ.
  revert t s w w' s'.
  induction n; intros.
  - destruct2 TR; subst.
    exists t; split; auto.
    symmetry; symmetry in EQ.
    transitivity s; auto.
  - destruct TR as ([s_ w_] & TR & TRi).
    destruct (ktrans_semiproper _ _ _ _ _ EQ TR) as (z_ & TR_ & EQ_).
    destruct (IHn _ _ _ _ _ TRi EQ_) as (zf & TRf & EQf).
    exists zf; cbn; split; eauto.
Qed.

Lemma ktrans_trc_semiproper `{Kripke M meq W} {X} : forall (t s s': M X) w w',
    meq X s t ->
    (s,w) ↦* (s',w') ->    
    exists t', (t,w) ↦* (t',w') /\ meq X s' t'.
Proof.
  intros.
  destruct H1 as (n & TR).
  destruct (ktrans_iter_semiproper _ _ _ _ _ _ H0 TR) as (? & ? & ?).
  exists x; split; auto.
  now (exists n).
Qed.  

Lemma ktrans_ktrans_trc `{Kripke M meq W} {X} : forall (m m' m_: M X * World W),
    m ↦ m' ->
    m' ↦* m_ ->
    m ↦* m_.
Proof.
  intros.
  destruct H1.
  exists (S x); cbn.
  exists m'; split; auto.
Qed.

Lemma ktrans_trc_ktrans `{Kripke M meq W} {X} : forall (m m' m_: M X * World W),
    m ↦* m' ->
    m' ↦ m_ ->
    m ↦* m_.
Proof.
  intros.
  destruct H0.
  revert H1 H0.
  revert m m' m_.
  induction x; intros.
  - destruct m, m', m_; destruct2 H0; subst.
    symmetry in Heqt.
    destruct (ktrans_semiproper _ _ _ _ _ Heqt H1) as (z_ & TR_ & EQ_).
    exists 1, (z_, w1); split; auto.
    split2; red; cbn; symmetry; auto.
  - destruct m, m', m_; destruct H0 as ([m' o'] & TR & TRi).
    eapply ktrans_ktrans_trc; eauto.
Qed.

Global Instance Transitive_ktrans_trc `{Kripke M meq W} {X}:
  Transitive (@ktrans_trc M meq W _ X).
Proof.
  red; intros.
  destruct H0 as (n0 & TR0).
  destruct H1 as (n1 & TR1).
  exists (n0 + n1)%nat.
  revert TR0 TR1.
  revert x y z n1.
  induction n0; intros; destruct x, y, z.
  - destruct2 TR0; subst.
    symmetry in Heqt.    
    destruct (ktrans_iter_semiproper _ _ _ _ _ _ Heqt TR1) as (t' & TR' & EQ').
    replace (0 + n1)%nat with n1 by reflexivity.
    (* Why can I not prove this? *)
Abort.
    
Definition can_step `{Kripke M meq W} {X} (m: M X * World W): Prop :=
  exists m' w', ktrans m (m', w').

Global Instance can_step_proper `{Kripke M meq W} {X}:
  Proper (meq X * eq ==> iff) can_step.
Proof.
  unfold Proper, respectful, can_step, impl; intros [t w] [t' w'];
    split; intros; destruct2 H0; subst; destruct H1 as (x & w & ?).
  - destruct (ktrans_semiproper t' t _ _ w Heqt H0) as (y' & TR' & EQ').
    now (exists y', w).
  - symmetry in Heqt.
    destruct (ktrans_semiproper _ _ _ _ w Heqt H0) as (y' & TR' & EQ').
    now (exists y', w).
Qed.

Global Hint Extern 2 =>
         match goal with
         | [ H: ?m ↦ ?m' |- can_step ?m ] =>
             exists (fst m'), (snd m'); apply H
end: ctl.

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
  | @ktrans ?M ?mequ _ ?KMS _ (?y,?s) (?z,?w) => 
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
