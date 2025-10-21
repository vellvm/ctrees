(*|
==========================================
Transition relations over concurrent trees
==========================================

Trees represent the dynamics of non-deterministic procesess.
In order to capture their behavioral equivalence, we follow the
process-algebra tradition and define bisimulation atop of labelled
transition systems.

A node is said to be _observable_ if it is a visible event, a return
node, or an internal br tagged as visible.
The first transition relation we introduce is [trans]: a tree can
finitely descend through unobservable brs until it reaches an
observable node. At this point, it steps following the simple rules:
- [Ret v] steps to a silently blocked state by emitting a value
label of [v]
- [Vis e k] can step to any [k x] by emitting an event label tagged
with both [e] and [x]
- [BrS k] can step to any [k x] by emitting a tau label

This transition system will define a notion of strong bisimulation
in the process algebra tradition.
It also leads to a weak bisimulation by defining [wtrans] as a
sequence of tau steps, and allowing a challenge to be answered by
[wtrans . trans . wtrans].
Once [trans] is defined over our structure, we can reuse the constructions
used by Pous in [Coinduction All the Way Up] to build these weak relations
-- with the exception that we need to work in Kleene Algebras w.r.t. to model
closed under [equ] rather than [eq].

.. coq:: none
|*)

From Stdlib Require Import Fin.

From Coinduction Require Import all.

From ITree Require Import
     Core.Subevent
     Indexed.Sum.

From CTree Require Import
     CTree Eq.Shallow Eq.Equ.

From RelationAlgebra Require Import
     monoid
     kat
     kat_tac
     prop
     rel
     srel
     comparisons
     rewriting
     normalisation.

Import CTree.
Import CTreeNotations.
Import EquNotations.
Open Scope ctree.

Set Implicit Arguments.
Set Primitive Projections.

#[local] Tactic Notation "step" := __step_equ.
#[local] Tactic Notation "step" "in" ident(H) := __step_in_equ H.

(*|
.. coq::
|*)

Section Trans.

  Context {E B : Type -> Type} {R : Type}.

  Notation S' := (ctree' E B R).
  Notation S  := (ctree  E B R).

  Definition SS : EqType :=
    {| type_of := S ; Eq := equ eq |}.

  (*|
The domain of labels of the LTS.
Note that it could be typed more strongly: [val] labels can only
be of type [R]. However typing it statically makes lemmas about
[bind] particularly awkward to state, so this seems to be the
least annoying solution.
|*)
  Variant label : Type :=
    | τ
    | obs {X : Type} (e : E X) (v : X)
    | die {X : Type} (e : E X) (empty : forall (x : X), False)
    | val {X : Type} (v : X).

  Variant is_val : label -> Prop :=
    | Is_val : forall X (x : X), is_val (val x).

  Variant is_die : label -> Prop :=
    | Is_die : forall {X} (e : E X) empty, is_die (die e empty).

  Definition is_end (l : label) : Prop := is_val l \/ is_die l.

  Lemma is_val_τ : ~ is_val τ.
  Proof.
    intro H. inversion H.
  Qed.

  Lemma is_val_obs {X} (e : E X) x : ~ is_val (obs e x).
  Proof.
    intro H. inversion H.
  Qed.

  Lemma is_val_die {X} (e : E X) empty : ~ is_val (die e empty).
  Proof.
    intro H. inversion H.
  Qed.

  Lemma is_die_τ : ~ is_die τ.
  Proof.
    intro H. inversion H.
  Qed.

  Lemma is_die_obs {X} (e : E X) x : ~ is_die (obs e x).
  Proof.
    intro H. inversion H.
  Qed.

  Lemma is_die_val {X} (x: X) : ~ is_die (val x).
  Proof.
    intro H. inversion H.
  Qed.

  Lemma is_end_τ : ~ is_end τ.
  Proof.
    intros [H | H];
      inversion H.
  Qed.

  Lemma is_end_obs {X} (e : E X) x : ~ is_end (obs e x).
  Proof.
    intros [H | H];
      inversion H.
  Qed.

  Lemma not_is_end_not_is_val (l : label) :
    ~ is_end l -> ~ is_val l.
  Proof.
    intros.
    unfold is_end in H.
    tauto.
  Qed.

  Lemma not_is_end_not_is_die (l : label) :
    ~ is_end l -> ~ is_die l.
  Proof.
    intros.
    unfold is_end in H.
    tauto.
  Qed.  

  (*|
The transition relation over [ctree]s.
It can either:
- recursively crawl through invisible [br] node;
- stop at a successor of a [Step] node, labelling the transition [tau];
- stop at a successor of a [Vis] node, labelling the transition by the event and branch taken;
- stop at a sink (implemented as a [Stuck] node) by stepping from a [ret v]
node, labelling the transition by the returned value.
|*)
  Inductive trans_ : label -> hrel S' S' :=

  | Transbr {X} (c : B X) x k l t :
    trans_ l (observe (k x)) t ->
    trans_ l (BrF c k) t

  | Transguard t t' l :
    trans_ l (observe t) t' ->
    trans_ l (GuardF t) t'

  | Transtau t u :
    u ≅ t ->
    trans_ τ (StepF t) (observe u)

  | Transobs {X} (e : E X) k x t :
    k x ≅ t ->
    trans_ (obs e x) (VisF e k) (observe t)

  | Transdie {X} (e : E X) k (empty : forall (x : X), False) :
    trans_ (die e empty) (VisF e k) StuckF

  | Transval r :
    trans_ (val r) (RetF r) StuckF.
  Hint Constructors trans_ : core.

  Definition transR l : hrel S S :=
    fun u v => trans_ l (observe u) (observe v).

  Ltac FtoObs :=
    match goal with
      |- trans_ _ _ ?t =>
        change t with (observe {| _observe := t |})
    end.

  #[local] Instance trans_equ_aux1 l t :
    Proper (going (equ eq) ==> flip impl) (trans_ l t).
  Proof.
    intros u u' equ; intros TR.
    inv equ; rename H into equ.
    step in equ.
    revert u equ.
    dependent induction TR; intros; subst; eauto.
    + inv equ.
      * rewrite H2; eauto.
      * FtoObs.
        constructor.
        rewrite <- H.
        apply observing_sub_equ; eauto.
      * FtoObs.
        constructor.
        rewrite <- H, REL.
        apply observing_sub_equ; eauto.
      * FtoObs.
        constructor.
        rewrite <- H, REL.
        apply observing_sub_equ; eauto.
      * FtoObs.
        constructor.
        rewrite <- H.
        step; rewrite <- H2; constructor; intros.
        auto.
      * FtoObs.
        constructor.
        rewrite <- H.
        step; rewrite <- H2; constructor; intros.
        auto.
   + FtoObs.
      econstructor.
      rewrite H; symmetry; step; auto.
   + inv equ. eauto.
   + inv equ. eauto.
  Qed.

  #[local] Instance trans_equ_aux2 l :
    Proper (going (equ eq) ==> going (equ eq) ==> impl) (trans_ l).
  Proof.
    intros t t' eqt u u' equ TR.
    rewrite <- equ; clear u' equ.
    inv eqt; rename H into eqt.
    revert t' eqt.
    dependent induction TR; intros; auto.
    + step in eqt; dependent induction eqt.
      econstructor.
      apply IHTR.
      rewrite REL; reflexivity.
    + step in eqt; dependent induction eqt.
      econstructor.
      apply IHTR. rewrite REL; reflexivity.
    + step in eqt; dependent induction eqt.
      econstructor. rewrite H,REL; auto.
    + step in eqt; dependent induction eqt.
      econstructor.
      rewrite <- REL; eauto.
    + step in eqt; dependent induction eqt.
      econstructor.
    + step in eqt; dependent induction eqt.
      econstructor.
  Qed.

  #[global] Instance trans_equ_ l :
    Proper (going (equ eq) ==> going (equ eq) ==> iff) (trans_ l).
  Proof.
    intros ? ? eqt ? ? equ; split; intros TR.
    - eapply trans_equ_aux2; eauto.
    - symmetry in equ; symmetry in eqt; eapply trans_equ_aux2; eauto.
  Qed.

(*|
[equ] is congruent for [trans], we can hence build a [srel] and build our
relations in this model to still exploit the automation from the [RelationAlgebra]
library.
|*)
  #[global] Instance trans_equ l :
    Proper (equ eq ==> equ eq ==> iff) (transR l).
  Proof.
    intros ? ? eqt ? ? equ; unfold transR.
    rewrite eqt, equ; reflexivity.
  Qed.

  Definition trans l : srel SS SS := {| hrel_of := transR l : hrel SS SS |}.

  Lemma trans__trans : forall l t u,
      trans_ l (observe t) (observe u) = trans l t u.
  Proof.
    reflexivity.
  Qed.

  Lemma transR_trans : forall l (t t' : S),
      transR l t t' = trans l t t'.
  Proof.
    reflexivity.
  Qed.

(*|
Extension of [trans] with its reflexive closure, labelled by [τ].
|*)
  Definition etrans (l : label) : srel SS SS :=
    match l with
    | τ => (cup (trans l) 1)
    | _ => trans l
    end.

(*|
The transition for the weak bisimulation: a sequence of
internal steps, a labelled step, and a new sequence of internal ones
|*)
  Definition wtrans l : srel SS SS :=
    (trans τ)^* ⋅ etrans l ⋅ (trans τ)^*.

  Definition pwtrans l : srel SS SS :=
    (trans τ)^* ⋅ trans l ⋅ (trans τ)^*.

  Definition τtrans : srel SS SS :=
    (trans τ)^+.

  (*|
----------------------------------------------
Elementary theory for the transition relations
----------------------------------------------

Inclusion relation between the three relations:
[trans l ≤ etrans l ≤ wtrans l]

[etrans] is reflexive, and hence so is [wtrans]
[etrans τ p p]

[wtrans] can be built by consing or snocing [trans τ]
[trans τ p p' -> wtrans l p' p'' -> wtrans l p p'']
[wtrans l p p' -> trans τ p' p'' -> wtrans l p p'']

Introduction rules for [trans]
[trans (val v)   (ret v)       stuck]
[trans (obs e v) (Vis e k)     (k v)]
[trans l (k x) u -> trans l (BrD n k) u]
[trans τ       (Step t) t]
[trans τ       (BrS n k) (k x)]
[trans l t u     -> trans l (Guard t) u]

Elimination rules for [trans]
[trans l (Ret x)       u -> l = val x /\ t ≅ stuck]
[trans l (Vis e k)     u -> exists v, l = obs e v /\ t ≅ k v]
[trans l (Step t)      u -> t ≅ u /\ l = τ]
[trans l (Br n k) u -> exists x, trans l (k x) u]
[trans l (BrS n k) u -> exists x, t' ≅ k x /\ l = τ]
[trans l (Guard t)      u -> trans l t u]

|*)
  Lemma trans_etrans l: trans l ≦ etrans l.
  Proof.
    unfold etrans; case l; ka.
  Qed.
  Lemma etrans_wtrans l: etrans l ≦ wtrans l.
  Proof.
    unfold wtrans; ka.
  Qed.
  Lemma trans_wtrans l: trans l ≦ wtrans l.
  Proof. rewrite trans_etrans. apply etrans_wtrans. Qed.
  Lemma τtrans_wtrans : τtrans ≦ wtrans τ.
  Proof.
    unfold τtrans, wtrans, etrans; ka.
  Qed.
  Lemma pwtrans_wtrans l : pwtrans l ≦ wtrans l.
  Proof.
    unfold pwtrans, wtrans, etrans; case l; ka.
  Qed.

  Lemma trans_etrans_ l: forall p p', trans l p p' -> etrans l p p'.
  Proof. apply trans_etrans. Qed.
  Lemma trans_wtrans_ l: forall p p', trans l p p' -> wtrans l p p'.
  Proof. apply trans_wtrans. Qed.
  Lemma etrans_wtrans_ l: forall p p', etrans l p p' -> wtrans l p p'.
  Proof. apply etrans_wtrans. Qed.
  Lemma τtrans_wtrans_ : forall p p', τtrans p p' -> wtrans τ p p'.
  Proof. apply τtrans_wtrans. Qed.
  Lemma pwtrans_wtrans_ l : forall p p', pwtrans l p p' -> wtrans l p p'.
  Proof. apply pwtrans_wtrans. Qed.

  Lemma enil p: etrans τ p p.
  Proof. cbn. now right. Qed.
  Lemma wnil p: wtrans τ p p.
  Proof. apply etrans_wtrans, enil. Qed.

  Lemma wcons l: forall p p' p'', trans τ p p' -> wtrans l p' p'' -> wtrans l p p''.
  Proof.
    assert ((trans τ: srel SS SS) ⋅ wtrans l ≦ wtrans l) as H
        by (unfold wtrans; ka).
    intros. apply H. eexists; eassumption.
  Qed.
  Lemma wsnoc l: forall p p' p'', wtrans l p p' -> trans τ p' p'' -> wtrans l p p''.
  Proof.
    assert (wtrans l ⋅ trans τ ≦ wtrans l) as H
        by (unfold wtrans; ka).
    intros. apply H. eexists; eassumption.
  Qed.

  Lemma wconss l: forall p p' p'', wtrans τ p p' -> wtrans l p' p'' -> wtrans l p p''.
  Proof.
    assert (wtrans τ ⋅ wtrans l ≦ wtrans l) as H by (unfold wtrans, etrans; ka).
    intros. apply H. eexists; eassumption.
  Qed.
  Lemma wsnocs l: forall p p' p'', wtrans l p p' -> wtrans τ p' p'' -> wtrans l p p''.
  Proof.
    assert (wtrans l ⋅ wtrans τ ≦ wtrans l) as H by (unfold wtrans, etrans; ka).
    intros. apply H. eexists; eassumption.
  Qed.

  Lemma wtrans_τ: wtrans τ ≡ (trans τ)^*.
  Proof.
    unfold wtrans, etrans. ka.
  Qed.

  Lemma pwtrans_τ: pwtrans τ ≡ (trans τ)^+.
  Proof.
    unfold pwtrans, etrans. ka.
  Qed.

  #[global] Instance PreOrder_wtrans_τ: PreOrder (wtrans τ).
  Proof.
    split.
    intro. apply wtrans_τ.
    now (apply (str_refl (trans τ)); cbn).
    intros ?????. apply wtrans_τ. apply (str_trans (trans τ)).
    eexists; apply wtrans_τ; eassumption.
  Qed.


End Trans.

#[global] Hint Resolve
  not_is_end_not_is_val
  not_is_end_not_is_die
  : LABELS.


Class Respects_val {E F} (L : rel (@label E) (@label F)) :=
  { respects_val:
    forall l l',
      L l l' ->
      is_val l <-> is_val l' }.

Class Respects_τ {E F} (L : rel (@label E) (@label F)) :=
  { respects_τ: forall l l',
      L l l' ->
      l = τ <-> l' = τ }.

Definition eq_obs {E} (L : relation (@label E)) : Prop :=
  forall X X' e e' (x : X) (x' : X'),
    L (obs e x) (obs e' x') ->
    obs e x = obs e' x'.

#[global] Instance Respects_val_eq A: @Respects_val A A eq.
split; intros; subst; reflexivity.
Defined.

#[global] Instance Respects_τ_eq A: @Respects_τ A A eq.
split; intros; subst; reflexivity.
Defined.

(*|
Backward reasoning for [trans]
------------------------------
Note: we need to be a bit careful to define these proof rules
explicitly over [ctree]s and not [rel_of SS] as gets coerced
in the section above so that [eauto with trans] works smoothly.
|*)
Section backward.

  Context {E B : Type -> Type} {X : Type}.

(*|
Structural rules
|*)

  Lemma trans_ret : forall (x : X),
      trans (E := E) (B := B) (val x) (Ret x) Stuck.
  Proof.
    intros; constructor.
  Qed.

  Lemma trans_vis : forall {Y} (e : E Y) x (k : Y -> ctree E B X),
      trans (obs e x) (Vis e k) (k x).
  Proof.
    intros; constructor; auto.
  Qed.

  Lemma trans_br : forall {Y} l (t t' : ctree E B X) (c : B Y) k x,
      trans l t t' ->
      k x ≅ t ->
      trans l (Br c k) t'.
  Proof.
    intros * TR Eq.
    apply Transbr with x.
    rewrite Eq; auto.
  Qed.

  Lemma trans_brS : forall {Y} (c : B Y) (k : _ -> ctree E B X) x,
      trans τ (BrS c k) (k x).
  Proof.
    intros.
    apply Transbr with x, Transtau.
    reflexivity.
  Qed.

(*|
Ad-hoc rules for pre-defined finite branching
|*)

  Variable (l : @label E) (t t' : ctree E B X).

  Lemma trans_step :
    trans τ (Step t) t.
  Proof.
    now econstructor.
  Qed.

  Lemma trans_guard :
    trans l t t' ->
    trans l (Guard t) t'.
  Proof.
    now econstructor.
  Qed.

End backward.

Section BackwardBounded.

  Context {E B : Type -> Type} {X : Type}.
  Context `{B2 -< B}.
  Context `{B3 -< B}.
  Context `{B4 -< B}.
  Variable (l : @label E) (t t' u u' v v' w w' : ctree E B X).

  Lemma trans_brS21 :
    trans τ (brS2 t u) t.
  Proof.
    intros.
    unfold brS2.
    apply Transbr with true.
    now constructor.
  Qed.

  Lemma trans_brS22 :
    trans τ (brS2 t u) u.
  Proof.
    intros.
    unfold brS2.
    apply Transbr with false.
    now constructor.
  Qed.

  Lemma trans_br21 :
    trans l t t' ->
    trans l (br2 t u) t'.
  Proof.
    intros * TR.
    eapply trans_br with (x := true); eauto.
  Qed.

  Lemma trans_br22 :
    trans l u u' ->
    trans l (br2 t u) u'.
  Proof.
    intros * TR.
    eapply trans_br with (x := false); eauto.
  Qed.

  Lemma trans_brS31 :
    trans τ (brS3 t u v) t.
  Proof.
    intros.
    unfold brS3.
    apply Transbr with t31.
    now constructor.
  Qed.

  Lemma trans_brS32 :
    trans τ (brS3 t u v) u.
  Proof.
    intros.
    unfold brS3.
    apply Transbr with t32.
    now constructor.
  Qed.

  Lemma trans_brS33 :
    trans τ (brS3 t u v) v.
  Proof.
    intros.
    unfold brS3.
    apply Transbr with t33.
    now constructor.
  Qed.

  Lemma trans_br31 :
    trans l t t' ->
    trans l (br3 t u v) t'.
  Proof.
    intros * TR.
    eapply trans_br with (x := t31); eauto.
  Qed.

  Lemma trans_br32 :
    trans l u u' ->
    trans l (br3 t u v) u'.
  Proof.
    intros * TR.
    eapply trans_br with (x := t32); eauto.
  Qed.

  Lemma trans_br33 :
    trans l v v' ->
    trans l (br3 t u v) v'.
  Proof.
    intros * TR.
    eapply trans_br with (x := t33); eauto.
  Qed.

  Lemma trans_brS41 :
    trans τ (brS4 t u v w) t.
  Proof.
    intros.
    unfold brS4.
    apply Transbr with t41.
    now constructor.
  Qed.

  Lemma trans_brS42 :
    trans τ (brS4 t u v w) u.
  Proof.
    intros.
    unfold brS4.
    apply Transbr with t42.
    now constructor.
  Qed.

  Lemma trans_brS43 :
    trans τ (brS4 t u v w) v.
  Proof.
    intros.
    unfold brS4.
    apply Transbr with t43.
    now constructor.
  Qed.

  Lemma trans_brS44 :
    trans τ (brS4 t u v w) w.
  Proof.
    intros.
    unfold brS4.
    apply Transbr with t44.
    now constructor.
  Qed.

  Lemma trans_br41 :
    trans l t t' ->
    trans l (br4 t u v w) t'.
  Proof.
    intros * TR.
    eapply trans_br with (x := t41); eauto.
  Qed.

  Lemma trans_br42 :
    trans l u u' ->
    trans l (br4 t u v w) u'.
  Proof.
    intros * TR.
    eapply trans_br with (x := t42); eauto.
  Qed.

  Lemma trans_br43 :
    trans l v v' ->
    trans l (br4 t u v w) v'.
  Proof.
    intros * TR.
    eapply trans_br with (x := t43); eauto.
  Qed.

  Lemma trans_br44 :
    trans l w w' ->
    trans l (br4 t u v w) w'.
  Proof.
    intros * TR.
    eapply trans_br with (x := t44); eauto.
  Qed.

End BackwardBounded.

(*|
Forward reasoning for [trans]
------------------------------
|*)

Section forward.

  Context {E B : Type -> Type} {X : Type}.

(*|
Inverting equalities between labels
|*)

  Lemma val_eq_invT : forall X Y x y, @val E X x = @val E Y y -> X = Y.
    clear B. intros * EQ.
    now dependent induction EQ.
  Qed.

  Lemma val_eq_inv : forall X x y, @val E X x = val y -> x = y.
    clear B. intros * EQ.
    now dependent induction EQ.
  Qed.

  Lemma obs_eq_invT : forall X Y e1 e2 v1 v2, @obs E X e1 v1 = @obs E Y e2 v2 -> X = Y.
    clear B. intros * EQ.
    now dependent induction EQ.
  Qed.

  Lemma obs_eq_inv : forall X e1 e2 v1 v2, @obs E X e1 v1 = @obs E X e2 v2 -> e1 = e2 /\ v1 = v2.
    clear B. intros * EQ.
    now dependent induction EQ.
  Qed.

(*|
Structural rules
|*)

  Lemma trans_ret_inv : forall x l (t : ctree E B X),
      trans l (Ret x) t ->
      t ≅ Stuck /\ l = val x.
  Proof.
    intros * TR; inv TR; intuition.
    rewrite ctree_eta, <- H2; auto.
  Qed.

  Lemma trans_vis_inv : forall {Y} (e : E Y) k l (u : ctree E B X) (y : Y),
      trans l (Vis e k) u ->
      exists x, u ≅ k x /\ l = obs e x.
  Proof.
    intros * y TR.
    inv TR; try contradiction.
    dependent induction H3; eexists; split; eauto.
    rewrite ctree_eta, <- H4, <- ctree_eta; symmetry; auto.
  Qed.

  Lemma trans_br_inv : forall {Y} l (c : B Y) k (u : ctree E B X),
      trans l (Br c k) u ->
      exists n, trans l (k n) u.
  Proof.
    intros * TR.
    cbn in *.
    unfold transR in *.
    cbn in TR |- *.
    match goal with
    | h: trans_ _ ?x ?y |- _ =>
        remember x as ox; remember y as oy
    end.
    revert c k u Heqox Heqoy.
    induction TR; intros; inv Heqox; eauto.
  Qed.

  Lemma trans_guard_inv : forall l (t : ctree E B X) u,
      trans l (Guard t) u ->
      trans l t u.
  Proof.
    intros * TR.
    now inv TR.
  Qed.

  Lemma trans_step_inv : forall l (t : ctree E B X) u,
      trans l (Step t) u ->
      u ≅ t /\ l = τ.
  Proof.
    intros * TR.
    inv TR; split; auto.
    rewrite <- H2. apply observe_equ_eq; auto.
  Qed.

  Lemma trans_brS_inv : forall {Y} l (c : B Y) k (u : ctree E B X),
      trans l (BrS c k) u ->
      exists n, u ≅ k n /\ l = τ.
  Proof.
    intros * TR.
    apply trans_br_inv in TR as [n ?].
    inv H.
    exists n; split; auto.
    rewrite <- H3. apply observe_equ_eq; auto.
  Qed.

  Lemma trans_stuck_inv : forall l (u : ctree E B X),
      trans l Stuck u ->
      False.
  Proof.
    intros * TR.
    inv TR.
  Qed.

(*|
Ad-hoc rules for pre-defined finite branching
|*)

  Variable (l : @label E) (t t' u v w : ctree E B X).
  Context `{B2 -< B} `{B3 -< B} `{B4 -< B}.

  Lemma trans_br2_inv :
    trans l (br2 t u) t' ->
    (trans l t t' \/ trans l u t').
  Proof.
    intros * TR; apply trans_br_inv in TR as [[] TR]; auto.
  Qed.

  Lemma trans_br3_inv :
    trans l (br3 t u v) t' ->
    (trans l t t' \/ trans l u t' \/ trans l v t').
  Proof.
    intros * TR; apply trans_br_inv in TR as [n TR].
    destruct n; auto.
  Qed.

  Lemma trans_br4_inv :
    trans l (br4 t u v w) t' ->
    (trans l t t' \/ trans l u t' \/ trans l v t' \/ trans l w t').
  Proof.
    intros * TR; apply trans_br_inv in TR as [n TR].
    destruct n; auto.
  Qed.

  Lemma trans_brS2_inv :
    trans l (brS2 t u) t' ->
    (l = τ /\ (t' ≅ t \/ t' ≅ u)).
  Proof.
    intros * TR; apply trans_brS_inv in TR as (? & TR & ->); split; auto.
    destruct x; auto.
  Qed.

  Lemma trans_brS3_inv :
    trans l (brS3 t u v) t' ->
    (l = τ /\ (t' ≅ t \/ t' ≅ u \/ t' ≅ v)).
  Proof.
    intros * TR; apply trans_brS_inv in TR as (? & TR & ->); split; auto.
    destruct x; auto.
  Qed.

  Lemma trans_brS4_inv :
    trans l (brS4 t u v w) t' ->
    (l = τ /\ (t' ≅ t \/ t' ≅ u \/ t' ≅ v \/ t' ≅ w)).
  Proof.
    intros * TR; apply trans_brS_inv in TR as (? & TR & ->); split; auto.
    destruct x; auto.
  Qed.

(*|
Inversion rules for [trans] based on the value of the label
-----------------------------------------------------------
In general, these would require to introduce the relation that
only steps through the non-observable internal br.
I'll skip them for now and introduce them if they turn out to be
useful.
|*)

  Lemma trans__val_inv {Y} :
    forall (T U : ctree' E B X) (x : Y),
      trans_ (val x) T U ->
      go U ≅ Stuck.
  Proof.
    intros * TR.
    remember (val x) as ox.
    rewrite ctree_eta; induction TR; intros; auto; try now inv Heqox.
  Qed.

  Lemma trans_val_inv {Y} :
    forall (t u : ctree E B X) (x : Y),
      trans (val x) t u ->
      u ≅ Stuck.
  Proof.
    intros * TR. cbn in TR. red in TR.
    apply trans__val_inv in TR. rewrite ctree_eta. apply TR.
  Qed.

  Lemma trans__die_inv {Y} :
    forall (T U : ctree' E B X) (e : E Y) empty,
      trans_ (die e empty) T U ->
      go U ≅ Stuck.
  Proof.
    intros * TR.
    remember (die e empty) as ox.
    rewrite ctree_eta; induction TR; intros; auto; try now inv Heqox.
  Qed.

  Lemma trans_die_inv {Y} :
    forall (t u : ctree E B X) (e : E Y) empty,
      trans (die e empty) t u ->
      u ≅ Stuck.
  Proof.
    intros * TR. cbn in TR. red in TR.
    apply trans__die_inv in TR. rewrite ctree_eta. apply TR.
  Qed.

  Lemma wtrans_val_inv : forall (x : X),
      wtrans (val x) u Stuck ->
      exists t, wtrans τ u t /\ trans (val x) t Stuck.
  Proof.
    intros * TR.
    destruct TR as [t2 [t1 step1 step2] step3].
    exists t1; split.
    apply wtrans_τ; auto.
    erewrite <- trans_val_inv; eauto.
  Qed.

  Lemma wtrans_die_inv : forall Y (e : E Y) empty,
      wtrans (die e empty) u Stuck ->
      exists t, wtrans τ u t /\ trans (die e empty) t Stuck.
  Proof.
    intros * TR.
    destruct TR as [t2 [t1 step1 step2] step3].
    exists t1; split.
    apply wtrans_τ; auto.
    erewrite <- trans_die_inv; eauto.
  Qed.


End forward.

(*|
[etrans] theory
---------------
|*)

Lemma etrans_case {E B X} : forall l (t u : ctree E B X),
    etrans l t u ->
    (trans l t u \/ (l = τ /\ t ≅ u)).
Proof.
  intros [] * TR; cbn in *; intuition.
Qed.

Lemma etrans_ret_inv {E B X} : forall x l (t : ctree E B X),
    etrans l (Ret x) t ->
    (l = τ /\ t ≅ Ret x) \/ (l = val x /\ t ≅ Stuck).
Proof.
  intros ? [] ? step; cbn in step.
  - intuition; try (eapply trans_ret in step; now apply step).
    inv H.
  - eapply trans_ret_inv in step; intuition.
  - eapply trans_ret_inv in step; intuition.
  - eapply trans_ret_inv in step; intuition.
Qed.

(*|
Stuck processes
---------------
A process is said to be stuck if it cannot step. The [stuck] process used
to reduce pure computations is of course stuck, but so is [spinI], while [spinV]
is not.
|*)

Section stuck.

  Context {E B : Type -> Type} {X : Type}.
  Variable (l : @label E) (t u : ctree E B X).

  Definition is_stuck : ctree E B X -> Prop :=
    fun t => forall l u, ~ (trans l t u).

  #[global] Instance is_stuck_equ : Proper (equ eq ==> iff) is_stuck.
  Proof.
    intros ? ? EQ; split; intros ST; red; intros * ABS.
    rewrite <- EQ in ABS; eapply ST; eauto.
    rewrite EQ in ABS; eapply ST; eauto.
  Qed.

  Lemma etrans_is_stuck_inv (v v' : ctree E B X) :
    is_stuck v ->
    etrans l v v' ->
    (l = τ /\ v ≅ v').
  Proof.
    intros * ST TR.
    edestruct @etrans_case; eauto.
    apply ST in H; tauto.
  Qed.

  Lemma transs_is_stuck_inv (v v' : ctree E B X) :
    is_stuck v ->
    (trans τ)^* v v' ->
    v ≅ v'.
  Proof.
    intros * ST TR.
    destruct TR as [[] TR]; intuition.
    destruct TR.
    apply ST in H; tauto.
  Qed.

  Lemma wtrans_is_stuck_inv :
    is_stuck t ->
    wtrans l t u ->
    (l = τ /\ t ≅ u).
  Proof.
    intros * ST TR.
    destruct TR as [? [? ?] ?].
    apply transs_is_stuck_inv in H; auto.
    rewrite H in ST; apply etrans_is_stuck_inv in H0 as [-> ?]; auto.
    rewrite H0 in ST; apply transs_is_stuck_inv in H1; auto.
    intuition.
    rewrite H, H0; auto.
  Qed.

  Lemma Stuck_is_stuck :
     is_stuck Stuck.
  Proof.
    repeat intro; eapply trans_stuck_inv; eauto.
  Qed.

  Lemma br_void_is_stuck (c : B void) (k : void -> _) :
    is_stuck (Br c k).
  Proof.
    red. intros. intro. inv H; destruct x.
  Qed.

  Lemma br_fin0_is_stuck (c : B (fin 0)) (k : fin 0 -> _) :
    is_stuck (Br c k).
  Proof.
    red. intros. intro. inv H; now apply case0.
  Qed.

  Lemma spinD_gen_is_stuck {Y} (x : B Y) :
    is_stuck (spin_gen x).
  Proof.
    red; intros * abs.
    remember (spin_gen x) as v.
    assert (EQ: v ≅ spin_gen x) by (subst; reflexivity); clear Heqv; revert EQ; rewrite ctree_eta.
    induction abs; auto; try now (rewrite ctree_eta; intros abs; step in abs; inv abs).
    - intros EQ; apply IHabs.
      rewrite <- ctree_eta.
      rewrite ctree_eta in EQ.
      step in EQ; cbn in *.
      dependent induction EQ; auto.
    - intros EQ; apply IHabs.
      rewrite <- ctree_eta.
      rewrite ctree_eta in EQ.
      step in EQ; cbn in *.
      dependent induction EQ; auto.
  Qed.

  Lemma spin_is_stuck :
    is_stuck spin.
  Proof.
    red; intros * abs.
    remember spin as v.
    assert (EQ: v ≅ spin) by (subst; reflexivity); clear Heqv; revert EQ; rewrite ctree_eta.
    induction abs; auto; try now (rewrite unfold_spin; intros abs; step in abs; inv abs).
    - intros EQ; apply IHabs.
      rewrite <- ctree_eta.
      rewrite unfold_spin in EQ.
      step in EQ.
      dependent induction EQ; auto.
    - intros EQ; apply IHabs.
      rewrite <- ctree_eta.
      rewrite unfold_spin in EQ.
      step in EQ.
      dependent induction EQ; auto.
  Qed.

  Lemma spinS_is_not_stuck :
    ~ (is_stuck spinS).
  Proof.
    red; intros * abs.
    apply (abs τ spinS).
    rewrite ctree_eta at 1; cbn.
    constructor; auto.
  Qed.

End stuck.

(*|
wtrans theory
---------------
|*)

Section wtrans.

  Context {E B : Type -> Type} {X : Type}.

  Lemma wtrans_step : forall l (t t' : ctree E B X),
      wtrans l t t' ->
      wtrans l (Step t) t'.
  Proof.
    intros * TR.
    eapply wcons; eauto.
    apply trans_step.
  Qed.

  Lemma trans_τ_str_ret_inv : forall x (t : ctree E B X),
      (trans τ)^* (Ret x) t ->
      t ≅ Ret x.
  Proof.
    intros * [[|] step].
    - cbn in *; symmetry; eauto.
    - destruct step.
      apply trans_ret_inv in H; intuition congruence.
  Qed.

  Lemma wtrans_ret_inv : forall x l (t : ctree E B X),
      wtrans l (Ret x) t ->
      (l = τ /\ t ≅ Ret x) \/ (l = val x /\ t ≅ Stuck).
  Proof.
    intros * step.
    destruct step as [? [? step1 step2] step3].
    apply trans_τ_str_ret_inv in step1.
    rewrite step1 in step2; clear step1.
    apply etrans_ret_inv in step2 as [[-> EQ] |[-> EQ]].
    rewrite EQ in step3; apply trans_τ_str_ret_inv in step3; auto.
    rewrite EQ in step3.
    apply transs_is_stuck_inv in step3; [| apply Stuck_is_stuck].
    intuition.
  Qed.

  Lemma wtrans_val_inv' : forall (x : X) (t v : ctree E B X),
      wtrans (val x) t v ->
      exists u, wtrans τ t u /\ trans (val x) u v /\ v ≅ Stuck.
  Proof.
    intros * TR.
    destruct TR as [t2 [t1 step1 step2] step3].
    pose proof trans_val_inv step2 as EQ.
    rewrite EQ in step3, step2.
    apply transs_is_stuck_inv in step3; auto using Stuck_is_stuck.
    exists t1; repeat split.
    apply wtrans_τ, step1.
    rewrite <- step3; auto.
    symmetry; auto.
  Qed.

End wtrans.

(*|
Forward and backward rules for [trans] w.r.t. [bind]
----------------------------------------------------
trans l (t >>= k) u -> (trans l t t' /\ u ≅ t' >>= k) \/ (trans (ret x) t stuck /\ trans l (k x) u)
l <> val x -> trans l t u -> trans l (t >>= k) (u >>= k)
trans (val x) t stuck -> trans l (k x) u -> trans l (bind t k) u.
|*)
Lemma trans_bind_inv_aux {E B X Y} l T U :
  trans_ l T U ->
  forall (t : ctree E B X) (k : X -> ctree E B Y) (u : ctree E B Y),
    go T ≅ t >>= k ->
    go U ≅ u ->
    (~ (is_end l) /\ exists t', trans l t t' /\ u ≅ t' >>= k) \/
      (exists (x : X), trans (val x) t Stuck /\ trans l (k x) u) \/
      (* t "dies", shouldn't have to continue into k *)
      (exists Z (e : E Z) (empty: forall (z : Z), False), trans (die e empty) t Stuck /\ u ≅ Stuck).
Proof.
  intros TR; induction TR; intros.

  - rewrite unfold_bind in H; setoid_rewrite (ctree_eta t0).
    desobs t0.
    + right; left.
      exists r; split.
      constructor.
      rewrite <- H.
      apply (Transbr _ x); auto.
      rewrite <- H0; auto.
    + step in H; inv H.
    + step in H; dependent induction H.
    + step in H; dependent induction H.
    + step in H; dependent induction H.
    + step in H; dependent induction H.
      specialize (IHTR (k1 x) k0 u).
      destruct IHTR as [(? & ? & ? & ?) | [(? & ? & ?) | (? & ? & ?)]]; auto.
      rewrite <- ctree_eta, REL; reflexivity.
      left; split; eauto.
      exists x0; split; auto.
      apply (Transbr _ x); auto.
      right; left.
      exists x0; split; auto.
      apply (Transbr _ x); auto.
      right; right.
      destruct H as (?&?&?).
      exists x0; auto.
      exists x1. exists x2.
      split; [apply (Transbr _ x); auto|auto].

  - symmetry in H; apply guard_equ_bind in H.
    destruct H as [(? & EQ & EQ') | (? & EQ & EQ')].
    + right; left.
      exists x; split; [rewrite EQ; constructor |].
      rewrite EQ'; auto.
      rewrite <- H0; constructor; auto.
    + destruct (IHTR x k u).
      rewrite EQ', <- ctree_eta; auto.
      auto.
      destruct H as (?& (? & ? & ?)); left; split; eauto.
      eexists; split.
      rewrite EQ; constructor; apply H1.
      auto.
      destruct H as [(? & ? & ?) | (? & ? & ? & ? & ?)].
      * right; left; eexists; split; eauto.
        rewrite EQ; constructor.
        apply H.
      * right; right; eexists; eexists; eexists; eauto.
        split; eauto.
        rewrite EQ; constructor.
        apply H.
  - symmetry in H0; apply step_equ_bind in H0.
    destruct H0 as [(? & EQ & EQ') | (? & EQ & EQ')].
    + right; left.
      exists x; split; [rewrite EQ; constructor |].
      rewrite EQ'; constructor.
      rewrite <- ctree_eta in H1; rewrite <- H1; auto.
    + left; split; [apply is_end_τ |].
      eexists; split; [rewrite EQ; constructor; reflexivity |].
      rewrite <- H1, <- ctree_eta, H, <-EQ'; auto.
  - symmetry in H0; apply vis_equ_bind in H0.
    destruct H0 as [(? & EQ & EQ') | (? & EQ & EQ')].
    + right; left.
      exists x0; split; [rewrite EQ; constructor |].
      rewrite EQ'; constructor.
      rewrite <- ctree_eta in H1; rewrite <- H1; auto.
    + left; split; [apply is_end_obs |].
      eexists; split; [rewrite EQ; constructor; reflexivity |].
      rewrite <- H1, <- ctree_eta, <- H, <-EQ'; auto.
  - symmetry in H; apply vis_equ_bind in H.
    destruct H as [(? & EQ & EQ') | (? & EQ & EQ')].
    + right; left.
      exists x; split; [rewrite EQ; constructor |].
      rewrite <- H0.
      rewrite EQ'; constructor.
    + right; right.
      exists X0, e, empty.
      rewrite EQ.
      symmetry in H0.
      split; eauto.
      constructor.
  - symmetry in H; apply ret_equ_bind in H.
    destruct H as (? & EQ & EQ').
    right; left.
    exists x; split; [rewrite EQ; constructor |].
    rewrite EQ', <- H0; econstructor.
Qed.

Lemma trans_bind_inv {E B X Y} (t : ctree E B X) (k : X -> ctree E B Y) (u : ctree E B Y) l :
  trans l (t >>= k) u ->
  (~ (is_end l) /\ exists t', trans l t t' /\ u ≅ t' >>= k) \/
    (exists (x : X), trans (val x) t Stuck /\ trans l (k x) u) \/
    (exists Z (e : E Z) (empty: forall (z : Z), False), trans (die e empty) t Stuck /\ u ≅ Stuck).
Proof.
  intros TR.
  eapply trans_bind_inv_aux.
  apply TR.
  rewrite <- ctree_eta; reflexivity.
  rewrite <- ctree_eta; reflexivity.
Qed.

Lemma trans_bind_inv_l {E B X Y} (t : ctree E B X) (k : X -> ctree E B Y) (u : ctree E B Y) l :
  trans l (t >>= k) u ->
  exists l' t', trans l' t t'.
Proof.
  intros TR.
  apply trans_bind_inv in TR.
  destruct TR as [(? & ? & ? & ?) | [(? & ? & ?) | (? & ? & ? & ? & ?)]]; eauto.
Qed.

Lemma trans_bind_l {E B X Y} (t : ctree E B X) (k : X -> ctree E B Y) (u : ctree E B X) l :
  ~ (@is_val E l) ->
  trans l t u ->
  trans l (t >>= k) (u >>= k).
Proof.
  cbn; unfold transR; intros NOV TR.
  dependent induction TR; cbn in *.
  - rewrite unfold_bind, <- x.
    cbn.
    econstructor.
    now apply IHTR.
  - rewrite unfold_bind, <- x; cbn.
    constructor.
    apply IHTR; auto.
  - rewrite unfold_bind.
    rewrite <- x0; cbn.
    econstructor.
    now rewrite <- H, (ctree_eta u0), x, <- ctree_eta.
  - rewrite unfold_bind.
    rewrite <- x1; cbn.
    econstructor.
    rewrite H.
    rewrite (ctree_eta t0),x,<- ctree_eta.
    reflexivity.
  - rewrite unfold_bind.
    rewrite <- x0; cbn.
    rewrite unfold_bind.
    rewrite <- x; cbn.
    constructor.
  - exfalso; eapply NOV; constructor.
Qed.

Lemma trans_bind_r {E B X Y} (t : ctree E B X) (k : X -> ctree E B Y) (u : ctree E B Y) x l :
  trans (val x) t Stuck ->
  trans l (k x) u ->
  trans l (t >>= k) u.
Proof.
  cbn; unfold transR; intros TR1.
  genobs t ot.
  remember (observe Stuck) as oc.
  remember (val x) as v.
  revert t x Heqot Heqoc Heqv.
  induction TR1; intros; try (inv Heqv; fail).
  - subst.
    rewrite (ctree_eta t0), <- Heqot; cbn; econstructor.
    eapply IHTR1; eauto.
  - rewrite (ctree_eta t0), <- Heqot; cbn; econstructor.
    eapply IHTR1; eauto.
  - dependent induction Heqv.
    rewrite (ctree_eta t), <- Heqot, unfold_bind; cbn; auto.
Qed.

Lemma is_stuck_bind : forall {E B X Y}
                        (t : ctree E B X) (k : X -> ctree E B Y),
    is_stuck t -> is_stuck (bind t k).
Proof.
  repeat intro.
  apply trans_bind_inv in H0 as [].
  - destruct H0 as (? & ? & ? & ?).
    now apply H in H1.
  - destruct H0 as [(? & ? & ?) | (? & ? & ? & ? & ?)];
      now apply H in H0.
Qed.

(*|
Forward and backward rules for [wtrans] w.r.t. [bind]
-----------------------------------------------------
|*)

Lemma etrans_bind_inv {E B X Y} (t : ctree E B X) (k : X -> ctree E B Y) (u : ctree E B Y) l :
  etrans l (t >>= k) u ->
  (~ (is_end l) /\ exists t', etrans l t t' /\ u ≅ t' >>= k) \/
    (exists (x : X), trans (val x) t Stuck /\ etrans l (k x) u) \/
    (exists Z (e : E Z) (empty: forall (z : Z), False), trans (die e empty) t Stuck /\ u ≅ Stuck).
Proof.
  intros TR.
  apply @etrans_case in TR as [ | (-> & ?)].
  - apply trans_bind_inv in H as [[? (? & ? & ?)]|[( ? & ? & ?) | (? & ? & ? & ? & ?)]]; eauto.
    + left; split; eauto with LABELS.
      eexists; split; eauto; apply trans_etrans; auto.
    + right; left; eexists; split; eauto; apply trans_etrans; auto.
    + right; right; eauto.
  - left; split.
    intros abs; apply is_end_τ in abs; contradiction.
    exists t; split; auto using enil; symmetry; auto.
Qed.

Lemma transs_bind_inv {E B X Y} (t : ctree E B X) (k : X -> ctree E B Y) (u : ctree E B Y) :
  (trans τ)^* (t >>= k) u ->
  (exists t', (trans τ)^* t t' /\ u ≅ t' >>= k) \/
    (exists (x : X), wtrans (val x) t Stuck /\ (trans τ)^* (k x) u) \/
    (exists Z (e : E Z) (empty: forall (z : Z), False), wtrans (die e empty) t Stuck).
Proof.
  intros [n TR].
  revert t k u TR.
  induction n as [| n IH]; intros; subst.
  - cbn in TR.
    left; exists t; split.
    exists 0%nat; reflexivity.
    symmetry; auto.
  - destruct TR as [t1 TR1 TR2].
    apply trans_bind_inv in TR1 as [(_ & t2 & TR1 & EQ) | [(x & TR1 & TR1') | (? & ? & ? & ? & ?)]].
    + rewrite EQ in TR2; clear t1 EQ.
      apply IH in TR2 as [(t3 & TR2 & EQ')| [(x & TR2 & TR3) | (? & ? & ? & ?)]].
      * left; eexists; split; eauto.
        apply wtrans_τ; eapply wcons; eauto.
        apply wtrans_τ; auto.
      * right; left; exists x; split; eauto.
        eapply wcons; eauto.
      * right; right; exists x, x0, x1; eauto.
        eapply wcons; eauto.
    + right; left.
      exists x; split.
      apply trans_wtrans; auto.
      exists (S n), t1; auto.
    + right; right.
      exists x, x0, x1.
      apply trans_wtrans; auto.
Qed.

(*|
Things are a bit ugly with [wtrans], we end up with three cases:
- the reduction entirely takes place in the prefix
- the computation spills over the continuation, with the label taking place
in the continuation
- the computation splills over the continuation, with the label taking place
in the prefix. This is a bit more annoying to express: we cannot necessarily
[wtrans l] all the way to a [Ret] as the end of the computation might contain
just before the [Ret] some invisible br nodes. We therefore have to introduce
the last visible state reached by [wtrans] and add a [trans (val _)] afterward.
|*)
Lemma wtrans_bind_inv {E B X Y} (t : ctree E B X) (k : X -> ctree E B Y) (u : ctree E B Y) l :
  wtrans l (t >>= k) u ->
  (~ (is_end l) /\ exists t', wtrans l t t' /\ u ≅ t' >>= k) \/
    (exists (x : X), wtrans (val x) t Stuck /\ wtrans l (k x) u) \/
    (exists (x : X) s, wtrans l t s /\ trans (val x) s Stuck /\ wtrans τ (k x) u) \/
    (exists Z (e : E Z) (empty: forall (z : Z), False) s, wtrans l t s /\ trans (die e empty) s Stuck).
Proof.
  intros TR.
  destruct TR as [t2 [t1 step1 step2] step3].
  apply transs_bind_inv in step1 as [(u1 & TR1 & EQ1)| [(x & TR1 & TR1') | (?&?&?&?)]].
  - rewrite EQ1 in step2; clear t1 EQ1.
    apply etrans_bind_inv in step2 as [(H & u2 & TR2 & EQ2)| [(x & TR2 & TR2')|(?&?&?&?&?)]].
    + rewrite EQ2 in step3; clear t2 EQ2.
      apply transs_bind_inv in step3 as [(u3 & TR3 & EQ3)| [(x & TR3 & TR3')|(?&?&?&?)]].
      * left; split; auto.
        eexists; split; eauto.
        exists u2; auto; exists u1; auto.
      * right; right; left.
        apply wtrans_val_inv in TR3 as (u3 & TR2' & TR2'').
        exists x, u3.
        split; [|split]; auto.
        2:apply wtrans_τ; auto.
        exists u2; [exists u1; assumption | ].
        apply wtrans_τ; apply wtrans_τ in TR1.
        eapply wconss; eauto.
      * right; right; right.
        eapply wtrans_die_inv in H0 as (u3 & TR2' & TR2'').
        exists x, x0, x1, u3.
        split; auto.
        exists u2; [exists u1; assumption | ].
        apply wtrans_τ; auto. 
    + right; left.
      exists x; split.
      eexists; [eexists |]; eauto; apply wtrans_τ, wnil.
      eexists; [eexists |]; eauto; apply wtrans_τ, wnil.
    + rewrite H0 in step3.
      apply wtrans_τ in step3.
      eapply wtrans_is_stuck_inv in step3 as (?&?).
      2: apply Stuck_is_stuck.

      right; right; right.
      

      
      exists x, x0, x1, u1; split; auto.
      apply wtrans_τ.
      eexists.
      apply TR1.
      eexists; [eexists |]; eauto; apply wtrans_τ, wnil.
      eexists; [eexists |]; eauto; apply wtrans_τ, wnil.
      rewrite
      apply wtrans_τ. , wnil.
      eexists.
      split; eauto.
      eexists; [eexists |]; eauto; apply wtrans_τ, wnil.
      eexists; [eexists |]; eauto; apply wtrans_τ, wnil.
  - right; left.
    exists x; split; eauto.
    eexists; [eexists |]; eauto.
Qed.

Lemma etrans_bind_l {E B X Y} (t : ctree E B X) (k : X -> ctree E B Y) (u : ctree E B X) l :
  ~ is_val l ->
  etrans l t u ->
  etrans l (t >>= k) (u >>= k).
Proof.
  destruct l; cbn; try apply trans_bind_l; auto.
  intros NOV [|].
  left; apply trans_bind_l; auto.
  right; rewrite H; auto.
Qed.

Lemma transs_bind_l {E B X Y} (t : ctree E B X) (k : X -> ctree E B Y) (u : ctree E B X) :
  (trans τ)^* t u ->
  (trans τ)^* (t >>= k) (u >>= k).
Proof.
  intros [n TR].
  revert t u TR.
  induction n as [| n IH].
  - cbn; intros; exists 0%nat; cbn; rewrite TR; reflexivity.
  - intros t u [v TR1 TR2].
    apply IH in TR2.
    eapply wtrans_τ, wcons.
    apply trans_bind_l; eauto; intros abs; inv abs.
    apply wtrans_τ; eauto.
Qed.

Lemma wtrans_bind_l {E B X Y} (t : ctree E B X) (k : X -> ctree E B Y) (u : ctree E B X) l :
  ~ (@is_val E l) ->
  wtrans l t u ->
  wtrans l (t >>= k) (u >>= k).
Proof.
  intros NOV [t2 [t1 TR1 TR2] TR3].
  eexists; [eexists |].
  apply transs_bind_l; eauto.
  apply etrans_bind_l; eauto.
  apply transs_bind_l; eauto.
Qed.

Lemma wtrans_case {E B X} (t u : ctree E B X) l:
  wtrans l t u ->
  t ≅ u \/ (exists v, trans l t v /\ wtrans τ v u) \/ (exists v, trans τ t v /\ wtrans l v u).
Proof.
  intros [t2 [t1 [n TR1] TR2] TR3].
  destruct n as [| n].
  - apply wtrans_τ in TR3.
    cbn in TR1; rewrite <- TR1 in TR2.
    destruct l; eauto.
    destruct TR2; eauto.
    cbn in H; rewrite <- H in TR3.
    apply wtrans_τ in TR3.
    destruct TR3 as [[| n] ?]; eauto.
    destruct H0 as [? ? ?]; right; left; eexists; split; eauto.
    apply wtrans_τ; exists n; auto.
  - destruct TR1 as [? ? ?].
    right; right.
    eexists; split; eauto.
    exists t2; [exists t1|]; eauto.
    exists n; eauto.
Qed.

Lemma wtrans_case' {E B X} (t u : ctree E B X) l:
  wtrans l t u ->
  match l with
  | τ => (t ≅ u \/ exists v, trans τ t v /\ wtrans τ v u)
  | _   => (exists v, trans l t v /\ wtrans τ v u) \/
            (exists v, trans τ t v /\ wtrans l v u)
  end.
Proof.
  intros [t2 [t1 [n TR1] TR2] TR3].
  destruct n as [| n].
  - apply wtrans_τ in TR3.
    cbn in TR1; rewrite <- TR1 in TR2.
    destruct l; eauto.
    destruct TR2; eauto.
    cbn in H; rewrite <- H in TR3.
    apply wtrans_τ in TR3.
    destruct TR3 as [[| n] ?]; eauto.
    destruct H0 as [? ? ?]; right; eexists; split; eauto.
    apply wtrans_τ; exists n; auto.
  - destruct TR1 as [? ? ?].
    destruct l; right.
    all:eexists; split; eauto.
    all:exists t2; [exists t1|]; eauto.
          all:exists n; eauto.
Qed.

Lemma wtrans_Stuck_inv {E B R} :
  forall (t : ctree E B R) l,
    wtrans l Stuck t ->
    match l with | τ => t ≅ Stuck | _ => False end.
Proof.
  intros * TR.
  apply wtrans_case' in TR.
  destruct l; break; cbn in *.
  symmetry; auto.
  all: exfalso; eapply Stuck_is_stuck; now apply H.
Qed.

Lemma pwtrans_case {E B X} (t u : ctree E B X) l:
  pwtrans l t u ->
  (exists v, trans l t v /\ wtrans τ v u) \/ (exists v, trans τ t v /\ wtrans l v u).
Proof.
  intros [t2 [t1 [n TR1] TR2] TR3].
  destruct n as [| n].
  - apply wtrans_τ in TR3.
    cbn in TR1; rewrite <- TR1 in TR2. eauto.
  - destruct TR1 as [? ? ?].
    right.
    eexists; split; eauto.
    exists t2; [exists t1|]; eauto.
    exists n; eauto.
    apply trans_etrans; auto.
Qed.

(*|
It's a bit annoying that we need two cases in this lemma, but if
[t = Guard (Ret x)] and [u = k x], we can process the [Guard] node
by taking the [Ret] in the prefix, but we cannot process it to
reach [u] in the bound computation.
|*)
Lemma wtrans_bind_r {E B X Y} (t : ctree E B X) (k : X -> ctree E B Y) (u : ctree E B Y) x l :
  wtrans (val x) t Stuck ->
  wtrans l (k x) u ->
  (u ≅ k x \/ wtrans l (t >>= k) u).
Proof.
  intros TR1 TR2.
  apply wtrans_val_inv in TR1 as (t' & TR1 & TR1').
  eapply wtrans_bind_l in TR1; [| intros abs; inv abs].
  apply wtrans_case in TR2 as [? | [|]].
  - left; symmetry; assumption.
  - right;eapply wconss; [apply TR1 | clear t TR1].
    destruct H as (? & ? & ?).
    eapply trans_bind_r in TR1'; eauto.
    eapply wsnocs; eauto.
    apply trans_wtrans; auto.
  - right;eapply wconss; [apply TR1 | clear t TR1].
    destruct H as (? & ? & ?).
    eapply trans_bind_r in TR1'; eauto.
    eapply wconss; [|eauto].
    apply trans_wtrans; auto.
Qed.

Lemma wtrans_bind_r' {E B X Y} (t : ctree E B X) (k : X -> ctree E B Y) (u : ctree E B Y) x l :
  wtrans (val x) t Stuck ->
  pwtrans l (k x) u ->
  (wtrans l (t >>= k) u).
Proof.
  intros TR1 TR2.
  apply wtrans_val_inv in TR1 as (t' & TR1 & TR1').
  eapply wtrans_bind_l in TR1; [| intros abs; inv abs].
  apply pwtrans_case in TR2 as [? | ].
  - eapply wconss; [apply TR1 | clear t TR1].
    destruct H as (? & ? & ?).
    eapply trans_bind_r in TR1'; eauto.
    eapply wsnocs; eauto.
    apply trans_wtrans; auto.
  - eapply wconss; [apply TR1 | clear t TR1].
    destruct H as (? & ? & ?).
    eapply trans_bind_r in TR1'; eauto.
    eapply wconss; [|eauto].
    apply trans_wtrans; auto.
Qed.

Lemma trans_val_invT {E B R R'} :
  forall (t u : ctree E B R) (v : R'),
    trans (val v) t u ->
    R = R'.
Proof.
  intros * TR.
  remember (val v) as ov.
  induction TR; intros; auto; try now inv Heqov.
Qed.

Lemma wtrans_bind_lr {E B X Y} (t u : ctree E B X) (k : X -> ctree E B Y) (v : ctree E B Y) x l :
  pwtrans l t u ->
  wtrans (val x) u Stuck ->
  pwtrans τ (k x) v ->
  (wtrans l (t >>= k) v).
Proof.
  intros [t2 [t1 TR1 TR1'] TR1''] TR2 TR3.
  exists (x <- t2;; k x).
  - assert (~ is_val l).
    {
      destruct l; try now intros abs; inv abs.
      exfalso.
      pose proof (trans_val_invT TR1'); subst.
      apply trans_val_inv in TR1'.
      rewrite TR1' in TR1''.
      apply transs_is_stuck_inv in TR1''; [| apply Stuck_is_stuck].
      rewrite <- TR1'' in TR2.
      apply wtrans_is_stuck_inv in TR2; [| apply Stuck_is_stuck].
      destruct TR2 as [abs _]; inv abs.
    }
    eexists.
    2:apply trans_etrans, trans_bind_l; eauto.
    apply wtrans_τ; eapply wtrans_bind_l; [intros abs; inv abs| apply wtrans_τ; auto].
  - apply wtrans_τ.
    eapply wconss.
    eapply wtrans_bind_l; [intros abs; inv abs| apply wtrans_τ; eauto].
    eapply wtrans_bind_r'; eauto.
Qed.

Lemma trans_trigger : forall {E B X Y} (e : E X) x (k : X -> ctree E B Y),
    trans (obs e x) (trigger e >>= k) (k x).
Proof.
  intros.
  unfold CTree.trigger.
  rewrite unfold_bind; cbn.
  setoid_rewrite bind_ret_l.
  constructor; auto.
Qed.

Lemma trans_trigger' : forall {E B X Y} (e : E X) x (t : ctree E B Y),
    trans (obs e x) (trigger e;; t) t.
Proof.
  intros.
  unfold CTree.trigger.
  rewrite unfold_bind; cbn.
  setoid_rewrite bind_ret_l.
  constructor; auto.
Qed.

Lemma trans_trigger_inv : forall {E B X Y} (e : E X) (k : X -> ctree E B Y) l u,
    trans l (trigger e >>= k) u ->
    exists x, u ≅ k x /\ l = obs e x.
Proof.
  intros * TR.
  unfold trigger in TR.
  apply trans_bind_inv in TR.
  destruct TR as [(? & ? & TR & ?) |(? & TR & ?)].
  - apply trans_vis_inv in TR.
    destruct TR as (? & ? & ->); eexists; split; eauto.
    rewrite H0, H1, bind_ret_l; reflexivity.
  - apply trans_vis_inv in TR.
    destruct TR as (? & ? & abs); inv abs.
Qed.

Lemma trans_branch :
  forall {E B : Type -> Type} {X : Type} {Y : Type}
    [l : label] [t t' : ctree E B X] (c : B Y) (k : Y -> ctree E B X) (x : Y),
    trans l t t' -> k x ≅ t -> trans l (branch c >>= k) t'.
Proof.
  intros.
  setoid_rewrite bind_branch.
  eapply trans_br; eauto.
Qed.

(*|
[wf_val] states that a [label] is well-formed:
if it is a [val] it should be of the right type.
|*)
Definition wf_val {E} X l := forall Y (v : Y), l = @val E Y v -> X = Y.

Lemma wf_val_val {E} X (v : X) : wf_val X (@val E X v).
Proof.
  red. intros. apply val_eq_invT in H. assumption.
Qed.

Lemma wf_val_nonval {E} X (l : @label E) : ~is_val l -> wf_val X l.
Proof.
  red. intros. subst. exfalso. apply H. constructor.
Qed.

Lemma wf_val_trans {E B X} (l : @label E) (t t' : ctree E B X) :
  trans l t t' -> wf_val X l.
Proof.
  red. intros. subst.
  now apply trans_val_invT in H.
Qed.

Lemma wf_val_is_val_inv : forall {E} X (l : @label E),
  is_val l ->
  wf_val (E := E) X l ->
  exists (x : X), l = val x.
Proof.
  intros.
  destruct H. red in H0.
  specialize (H0 X0 x eq_refl). subst. eauto.
Qed.

(*| If the LTS has events of type [L +' R] then
  it is possible to step it as either an [L] LTS
  or [R] LTS ignoring the other.
*)
Section Coproduct.
  Arguments label: clear implicits.
  Context {L R C: Type -> Type} {X: Type}.
  Notation S := (ctree (L +' R) C X).
  Notation S' := (ctree' (L +' R) C X).
  Notation SP := (SS -> label (L +' R) -> Prop).

  (* Skip an [R] event *)
  Inductive srtrans_: rel S' S' :=
  | IgnoreR {X} (e : R X) k x t :
    srtrans_ (observe (k x)) t ->
    srtrans_ (VisF (inr1 e) k) t.

  (* Skip an [L] event *)
  Inductive sltrans_: rel S' S' :=
  | IgnoreL {X} (e : L X) k x t :
    sltrans_ (observe (k x)) t ->
    sltrans_ (VisF (inl1 e) k) t.

  Hint Constructors srtrans_ sltrans_: core.

  (* Make those relations that respect equality [srel] *)
  Program Definition srtrans : srel SS SS :=
    {| hrel_of := (fun (u v: SS) => srtrans_ (observe u) (observe v)) |}.
  Next Obligation. split; induction 1; auto. Defined.

  Program Definition sltrans : srel SS SS :=
    {| hrel_of := (fun (u v: SS) => sltrans_ (observe u) (observe v)) |}.
  Next Obligation. split; induction 1; auto. Defined.

  (*| Obs transition on the left, ignores right transitions and [τ] |*)
  Definition ltrans {X}(l: L X)(x: X): srel SS SS :=
    (trans τ ⊔ srtrans)^* ⋅ trans (obs (inl1 l) x) ⋅ (trans τ ⊔ srtrans)^*.

  (*| Obs transition on the right, ignores left transitions and [τ] |*)
  Definition rtrans {X}(r: R X)(x: X): srel SS SS :=
    (trans τ ⊔ sltrans)^* ⋅ trans (obs (inr1 r) x) ⋅ (trans τ ⊔ sltrans)^*.

End Coproduct.

(*|
[inv_trans] is an helper tactic to automatically
invert hypotheses involving [trans].
|*)

#[local] Notation trans' l t u := (hrel_of (trans l) t u).

Ltac inv_trans_one :=
  let inv_trans_one_tau_r EQl :=
    match type of EQl with
    | τ     = τ => clear EQl
    | val _   = τ => now inv EQl
    | obs _ _ = τ => now inv EQl
    | die _ _ = τ => now inv EQl
    | _ => idtac
    end in
  let inv_trans_one_val_r EQl :=
    match type of EQl with
    | val _   = val _ => apply val_eq_inv in EQl; try (inversion EQl; fail)
    | τ     = val _ => now inv EQl
    | obs _ _ = val _ => now inv EQl
    | die _ _ = val _ => now inv EQl
    | _ => idtac
    end in
  match goal with

  (* Ret *)
  | h : trans' _ (Ret ?x) _ |- _ =>
      let EQl := fresh "EQl" in
      apply trans_ret_inv in h as [?EQ EQl];
      inv_trans_one_val_r EQl

  (* Vis *)
  | h : trans' _ (Vis ?e ?k) _ |- _ =>
      let EQl := fresh "EQl" in
      apply trans_vis_inv in h as (?x & ?EQ & EQl);
      match type of EQl with
      | @obs _ ?X _ _ = obs _ _ =>
          let EQt := fresh "EQt" in
          let EQe := fresh "EQe" in
          let EQv := fresh "EQv" in
          apply obs_eq_invT in EQl as EQt;
          subst_hyp_in EQt h;
          apply obs_eq_inv in EQl as [EQe EQv];
          try (inversion EQv; inversion EQe; fail)
      | die _ _   = obs _ _ => now inv EQl
      | val _   = obs _ _ => now inv EQl
      | τ     = obs _ _ => now inv EQl
      | _ => idtac
      end

  (* Step *)
  | h : trans' _ (Step _) _ |- _ =>
      let EQl := fresh "EQl" in
      apply trans_step_inv in h as (?EQ & EQl);
      inv_trans_one_tau_r EQl

  (* BrS *)
  | h : trans' _ (BrS ?n ?k) _ |- _ =>
      let x := fresh "x" in
      let EQl := fresh "EQl" in
      apply trans_brS_inv in h as (x & ?EQ & EQl);
      inv_trans_one_tau_r EQl

  (* brS2 *)
  | h : trans' _ (brS2 _ _) _ |- _ =>
      let EQl := fresh "EQl" in
      apply trans_brS2_inv in h as (EQl & [?EQ | ?EQ]);
      inv_trans_one_tau_r EQl

  (* brS3 *)
  | h : trans' _ (brS3 _ _ _) _ |- _ =>
      let EQl := fresh "EQl" in
      apply trans_brS3_inv in h as (EQl & [?EQ | [?EQ | ?EQ]]);
      inv_trans_one_tau_r EQl

  (* brS4 *)
  | h : trans' _ (brS4 _ _ _ _) _ |- _ =>
      let EQl := fresh "EQl" in
      apply trans_brS4_inv in h as (EQl & [?EQ | [?EQ | [?EQ | ?EQ]]]);
      inv_trans_one_tau_r EQl

  (* Guard *)
  | h : trans' _ (Guard _) _ |- _ =>
      apply trans_guard_inv in h

  (* Br *)
  | h : trans' _ (Br ?n ?k) _ |- _ =>
      let x := fresh "x" in
      apply trans_br_inv in h as (x & ?TR)

  (* br2 *)
  | h : trans' _ (br2 _ _) _ |- _ =>
      apply trans_br2_inv in h as [?TR | ?TR]

  (* br3 *)
  | h : trans' _ (br3 _ _ _) _ |- _ =>
      apply trans_br3_inv in h as [?TR | [?TR | ?TR]]

  (* br4 *)
  | h : trans' _ (br4 _ _ _ _) _ |- _ =>
      apply trans_br4_inv in h as [?TR | [?TR | [?TR | ?TR]]]

  (* Stuck *)
  | h : trans' _ Stuck _ |- _ =>
      exfalso; eapply Stuck_is_stuck; now apply h
  (* (* stuckS *) *)
  (* | h : trans' _ stuckS _ |- _ => *)
  (*     exfalso; eapply stuckS_is_stuck; now apply h *)

  (* trigger *)
  | h : trans' _ (CTree.bind (CTree.trigger ?e) ?t) _ |- _ =>
      apply trans_trigger_inv in h as (?x & ?EQ & ?EQl)

  end; try subs
.

Ltac inv_trans := repeat inv_trans_one.

Create HintDb trans.
#[global] Hint Resolve
 trans_ret trans_vis trans_brS trans_br
 trans_guard
 trans_br21 trans_br22
 trans_br31 trans_br32 trans_br33
 trans_br41 trans_br42 trans_br43 trans_br44
 trans_step
 trans_brS21 trans_brS22
 trans_brS31 trans_brS32 trans_brS33
 trans_brS41 trans_brS42 trans_brS43 trans_brS44
 trans_trigger trans_bind_l trans_bind_r
  : trans.

#[global] Hint Constructors is_val : trans.
#[global] Hint Resolve
  is_val_τ is_val_obs
  wf_val_val wf_val_nonval wf_val_trans : trans.

Ltac etrans := eauto with trans.
