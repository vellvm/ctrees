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

From Coq Require Import Fin.

From Coinduction Require Import
     coinduction rel tactics.

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
  Context {HasStuck: B0 -< B}.

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
    | tau
    | obs {X : Type} (e : E X) (v : X)
    | val {X : Type} (v : X).

  Variant is_val : label -> Prop :=
    | Is_val : forall X (x : X), is_val (val x).

  Lemma is_val_tau : ~ is_val tau.
  Proof.
    intro H. inversion H.
  Qed.

  Lemma is_val_obs {X} (e : E X) x : ~ is_val (obs e x).
  Proof.
    intro H. inversion H.
  Qed.

  (*|
The transition relation over [ctree]s.
It can either:
- recursively crawl through invisible [br] node;
- stop at a successor of a visible [br] node, labelling the transition [tau];
- stop at a successor of a [Vis] node, labelling the transition by the event and branch taken;
- stop at a sink (implemented as a [br] node with no successor) by stepping from a [ret v]
node, labelling the transition by the returned value.
|*)
  Inductive trans_ : label -> hrel S' S' :=

  | Stepbr {X} (c : B X) x k l t :
    trans_ l (observe (k x)) t ->
    trans_ l (BrF false c k) t

  | Steptau {X} (c : B X) x k t :
    k x ≅ t ->
    trans_ tau (BrSF c k) (observe t)

  | Stepobs {X} (e : E X) k x t :
    k x ≅ t ->
    trans_ (obs e x) (VisF e k) (observe t)

  | Stepval r k :
    trans_ (val r) (RetF r) (brDF branch0 k).
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
	apply (Steptau c x).
	rewrite H.
	rewrite (ctree_eta t), <- H2.
	step; constructor; intros; symmetry; auto.
      * FtoObs.
	apply (Steptau c x).
	rewrite H.
	rewrite (ctree_eta t), <- H2.
	step; constructor; intros; symmetry; auto.
    + FtoObs.
      econstructor.
      rewrite H; symmetry; step; auto.
    + inv equ. dependent destruction H3. econstructor.
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
      apply (Stepbr c x).
      apply IHTR.
      rewrite REL; reflexivity.
    + step in eqt; dependent induction eqt.
      econstructor.
      rewrite <- REL; eauto.
    + step in eqt; dependent induction eqt.
      econstructor.
      rewrite <- REL; eauto.
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
Extension of [trans] with its reflexive closure, labelled by [tau].
|*)
  Definition etrans (l : label) : srel SS SS :=
    match l with
    | tau => (cup (trans l) 1)
    | _ => trans l
    end.

  (*|
The transition for the weak bisimulation: a sequence of
internal steps, a labelled step, and a new sequence of internal ones
|*)
  Definition wtrans l : srel SS SS :=
    (trans tau)^* ⋅ etrans l ⋅ (trans tau)^*.

  Definition pwtrans l : srel SS SS :=
    (trans tau)^* ⋅ trans l ⋅ (trans tau)^*.

  Definition tautrans : srel SS SS :=
    (trans tau)^+.

  (*|
----------------------------------------------
Elementary theory for the transition relations
----------------------------------------------

Inclusion relation between the three relations:
[trans l ≤ etrans l ≤ wtrans l]

[etrans] is reflexive, and hence so is [wtrans]
[etrans tau p p]

[wtrans] can be built by consing or snocing [trans tau]
[trans tau p p' -> wtrans l p' p'' -> wtrans l p p'']
[wtrans l p p' -> trans tau p' p'' -> wtrans l p p'']

Introduction rules for [trans]
[trans (val v)   (ret v)       stuck]
[trans (obs e v) (Vis e k)     (k v)]
[trans tau       (BrS n k) (k x)]
[trans tau       (Step t) t]
[trans l (k x) u -> trans l (BrI n k) u]
[trans l t u     -> trans l (Guard t) u]

Elimination rules for [trans]
[trans l (Ret x)       u -> l = val x /\ t ≅ stuck]
[trans l (Vis e k)     u -> exists v, l = obs e v /\ t ≅ k v]
[trans l (BrS n k) u -> exists x, t' ≅ k x /\ l = tau]
[trans l (Step t)      u -> t ≅ u /\ l = tau]
[trans l (BrI n k) u -> exists x, trans l (k x) u]
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
  Lemma tautrans_wtrans : tautrans ≦ wtrans tau.
  Proof.
    unfold tautrans, wtrans, etrans; ka.
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
  Lemma tautrans_wtrans_ : forall p p', tautrans p p' -> wtrans tau p p'.
  Proof. apply tautrans_wtrans. Qed.
  Lemma pwtrans_wtrans_ l : forall p p', pwtrans l p p' -> wtrans l p p'.
  Proof. apply pwtrans_wtrans. Qed.

  Lemma enil p: etrans tau p p.
  Proof. cbn. now right. Qed.
  Lemma wnil p: wtrans tau p p.
  Proof. apply etrans_wtrans, enil. Qed.

  Lemma wcons l: forall p p' p'', trans tau p p' -> wtrans l p' p'' -> wtrans l p p''.
  Proof.
    assert ((trans tau: srel SS SS) ⋅ wtrans l ≦ wtrans l) as H
        by (unfold wtrans; ka).
    intros. apply H. eexists; eassumption.
  Qed.
  Lemma wsnoc l: forall p p' p'', wtrans l p p' -> trans tau p' p'' -> wtrans l p p''.
  Proof.
    assert (wtrans l ⋅ trans tau ≦ wtrans l) as H
        by (unfold wtrans; ka).
    intros. apply H. eexists; eassumption.
  Qed.

  Lemma wconss l: forall p p' p'', wtrans tau p p' -> wtrans l p' p'' -> wtrans l p p''.
  Proof.
    assert (wtrans tau ⋅ wtrans l ≦ wtrans l) as H by (unfold wtrans, etrans; ka).
    intros. apply H. eexists; eassumption.
  Qed.
  Lemma wsnocs l: forall p p' p'', wtrans l p p' -> wtrans tau p' p'' -> wtrans l p p''.
  Proof.
    assert (wtrans l ⋅ wtrans tau ≦ wtrans l) as H by (unfold wtrans, etrans; ka).
    intros. apply H. eexists; eassumption.
  Qed.

  Lemma wtrans_tau: wtrans tau ≡ (trans tau)^*.
  Proof.
    unfold wtrans, etrans. ka.
  Qed.

  Lemma pwtrans_tau: pwtrans tau ≡ (trans tau)^+.
  Proof.
    unfold pwtrans, etrans. ka.
  Qed.

  #[global] Instance PreOrder_wtrans_tau: PreOrder (wtrans tau).
  Proof.
    split.
    intro. apply wtrans_tau.
    now (apply (str_refl (trans tau)); cbn).
    intros ?????. apply wtrans_tau. apply (str_trans (trans tau)).
    eexists; apply wtrans_tau; eassumption.
  Qed.


End Trans.

Class Respects_val {E F} (L : rel (@label E) (@label F)) :=
  { respects_val:
    forall l l',
      L l l' ->
      is_val l <-> is_val l' }.

Class Respects_tau {E F} (L : rel (@label E) (@label F)) :=
  { respects_tau: forall l l',
      L l l' ->
      l = tau <-> l' = tau }.

Definition eq_obs {E} (L : relation (@label E)) : Prop :=
  forall X X' e e' (x : X) (x' : X'),
    L (obs e x) (obs e' x') ->
    obs e x = obs e' x'.

#[global] Instance Respects_val_eq A: @Respects_val A A eq.
split; intros; subst; reflexivity.
Defined.

#[global] Instance Respects_tau_eq A: @Respects_tau A A eq.
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
  Context `{B0 -< B}.
  Context `{B1 -< B}.

  (*|
Structural rules
|*)

  Lemma trans_ret : forall (x : X),
      trans (E := E) (B := B) (val x) (Ret x) stuckD.
  Proof.
    intros; constructor.
  Qed.

  Lemma trans_vis : forall {Y} (e : E Y) x (k : Y -> ctree E B X),
      trans (obs e x) (Vis e k) (k x).
  Proof.
    intros; constructor; auto.
  Qed.

  Lemma trans_brD : forall {Y} l (t t' : ctree E B X) (c : B Y) k x,
      trans l t t' ->
      k x ≅ t ->
      trans l (BrD c k) t'.
  Proof.
    intros * TR Eq.
    apply Stepbr with x.
    rewrite Eq; auto.
  Qed.

  Lemma trans_brS : forall {Y} (c : B Y) (k : _ -> ctree E B X) x,
      trans tau (BrS c k) (k x).
  Proof.
    intros.
    apply Steptau with x; reflexivity.
  Qed.

  (*|
Ad-hoc rules for pre-defined finite branching
|*)

  Variable (l : @label E) (t t' u u' v v' w w' : ctree E B X).

  Lemma trans_step :
    trans tau (Step t) t.
  Proof.
    intros; apply (@trans_brS unit _ (fun _ => t) tt).
  Qed.

  Lemma trans_guard :
    trans l t t' ->
    trans l (Guard t) t'.
  Proof.
    intros * TR; eapply trans_brD; eauto; exact F1.
  Qed.

End backward.

Section BackwardBounded.

  Context {E B : Type -> Type} {X : Type}.
  Context `{B0 -< B}.
  Context `{B2 -< B}.
  Context `{B3 -< B}.
  Context `{B4 -< B}.
  Variable (l : @label E) (t t' u u' v v' w w' : ctree E B X).

  Lemma trans_brS21 :
    trans tau (brS2 t u) t.
  Proof.
    intros.
    unfold brS2.
    match goal with
      |- _ (trans tau) (BrS _ ?k) ?t => exact (trans_brS _ k true)
    end.
  Qed.

  Lemma trans_brS22 :
    trans tau (brS2 t u) u.
  Proof.
    intros.
    unfold brS2.
    match goal with
      |- _ (trans tau) (BrS _ ?k) ?t => exact (trans_brS _ k false)
    end.
  Qed.

  Lemma trans_brD21 :
    trans l t t' ->
    trans l (brD2 t u) t'.
  Proof.
    intros * TR.
    eapply trans_brD with (x := true); eauto.
  Qed.

  Lemma trans_brD22 :
    trans l u u' ->
    trans l (brD2 t u) u'.
  Proof.
    intros * TR.
    eapply trans_brD with (x := false); eauto.
  Qed.

  Lemma trans_brS31 :
    trans tau (brS3 t u v) t.
  Proof.
    intros.
    unfold brS3.
    match goal with
      |- _ (trans tau) (BrS _ ?k) ?t => exact (trans_brS _ k t31)
    end.
  Qed.

  Lemma trans_brS32 :
    trans tau (brS3 t u v) u.
  Proof.
    intros.
    unfold brS3.
    match goal with
      |- _ (trans tau) (BrS _ ?k) ?t => exact (trans_brS _ k t32)
    end.
  Qed.

  Lemma trans_brS33 :
    trans tau (brS3 t u v) v.
  Proof.
    intros.
    unfold brS3.
    match goal with
      |- _ (trans tau) (BrS _ ?k) ?t => exact (trans_brS _ k t33)
    end.
  Qed.

  Lemma trans_brD31 :
    trans l t t' ->
    trans l (brD3 t u v) t'.
  Proof.
    intros * TR.
    eapply trans_brD with (x := t31); eauto.
  Qed.

  Lemma trans_brD32 :
    trans l u u' ->
    trans l (brD3 t u v) u'.
  Proof.
    intros * TR.
    eapply trans_brD with (x := t32); eauto.
  Qed.

  Lemma trans_brD33 :
    trans l v v' ->
    trans l (brD3 t u v) v'.
  Proof.
    intros * TR.
    eapply trans_brD with (x := t33); eauto.
  Qed.

  Lemma trans_brS41 :
    trans tau (brS4 t u v w) t.
  Proof.
    intros.
    unfold brS4.
    match goal with
      |- _ (trans tau) (BrS _ ?k) ?t => exact (trans_brS _ k t41)
    end.
  Qed.

  Lemma trans_brS42 :
    trans tau (brS4 t u v w) u.
  Proof.
    intros.
    unfold brS4.
    match goal with
      |- _ (trans tau) (BrS _ ?k) ?t => exact (trans_brS _ k t42)
    end.
  Qed.

  Lemma trans_brS43 :
    trans tau (brS4 t u v w) v.
  Proof.
    intros.
    unfold brS4.
    match goal with
      |- _ (trans tau) (BrS _ ?k) ?t => exact (trans_brS _ k t43)
    end.
  Qed.

  Lemma trans_brS44 :
    trans tau (brS4 t u v w) w.
  Proof.
    intros.
    unfold brS4.
    match goal with
      |- _ (trans tau) (BrS _ ?k) ?t => exact (trans_brS _ k t44)
    end.
  Qed.

  Lemma trans_brD41 :
    trans l t t' ->
    trans l (brD4 t u v w) t'.
  Proof.
    intros * TR.
    eapply trans_brD with (x := t41); eauto.
  Qed.

  Lemma trans_brD42 :
    trans l u u' ->
    trans l (brD4 t u v w) u'.
  Proof.
    intros * TR.
    eapply trans_brD with (x := t42); eauto.
  Qed.

  Lemma trans_brD43 :
    trans l v v' ->
    trans l (brD4 t u v w) v'.
  Proof.
    intros * TR.
    eapply trans_brD with (x := t43); eauto.
  Qed.

  Lemma trans_brD44 :
    trans l w w' ->
    trans l (brD4 t u v w) w'.
  Proof.
    intros * TR.
    eapply trans_brD with (x := t44); eauto.
  Qed.

End BackwardBounded.

(*|
Forward reasoning for [trans]
------------------------------
|*)

Section forward.

  Context {E B : Type -> Type} `{HasStuck : B0 -< B} {X : Type}.

  (*|
Inverting equalities between labels
|*)

  Lemma val_eq_invT : forall X Y x y, @val E X x = @val E Y y -> X = Y.
    clear B HasStuck. intros * EQ.
    now dependent induction EQ.
  Qed.

  Lemma val_eq_inv : forall X x y, @val E X x = val y -> x = y.
    clear B HasStuck. intros * EQ.
    now dependent induction EQ.
  Qed.

  Lemma obs_eq_invT : forall X Y e1 e2 v1 v2, @obs E X e1 v1 = @obs E Y e2 v2 -> X = Y.
    clear B HasStuck. intros * EQ.
    now dependent induction EQ.
  Qed.

  Lemma obs_eq_inv : forall X e1 e2 v1 v2, @obs E X e1 v1 = @obs E X e2 v2 -> e1 = e2 /\ v1 = v2.
    clear B HasStuck. intros * EQ.
    now dependent induction EQ.
  Qed.

  (*|
Structural rules
|*)

  Lemma trans_ret_inv : forall x l (t : ctree E B X),
      trans l (Ret x) t ->
      t ≅ stuckD /\ l = val x.
  Proof.
    intros * TR; inv TR; intuition.
    rewrite ctree_eta, <- H2; auto.
    step; constructor; intros abs; inv abs.
  Qed.

  Lemma trans_vis_inv : forall {Y} (e : E Y) k l (u : ctree E B X),
      trans l (Vis e k) u ->
      exists x, u ≅ k x /\ l = obs e x.
  Proof.
    intros * TR.
    inv TR.
    dependent induction H3; eexists; split; eauto.
    rewrite ctree_eta, <- H4, <- ctree_eta; symmetry; auto.
  Qed.

  Lemma trans_brD_inv : forall {Y} l (c : B Y) k (u : ctree E B X),
      trans l (BrD c k) u ->
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

  (*|
Ad-hoc rules for pre-defined finite branching
|*)

  Variable (l : @label E) (t t' u v w : ctree E B X).
  Context `{B1 -< B} `{B2 -< B} `{B3 -< B} `{B4 -< B}.

  Lemma trans_guard_inv :
    trans l (Guard t) t' ->
    trans l t t'.
  Proof.
    intros * TR; apply trans_brD_inv in TR as [_ TR]; auto.
  Qed.

  Lemma trans_brD2_inv :
    trans l (brD2 t u) t' ->
    (trans l t t' \/ trans l u t').
  Proof.
    intros * TR; apply trans_brD_inv in TR as [[] TR]; auto.
  Qed.

  Lemma trans_brD3_inv :
    trans l (brD3 t u v) t' ->
    (trans l t t' \/ trans l u t' \/ trans l v t').
  Proof.
    intros * TR; apply trans_brD_inv in TR as [n TR].
    destruct n; auto.
  Qed.

  Lemma trans_brD4_inv :
    trans l (brD4 t u v w) t' ->
    (trans l t t' \/ trans l u t' \/ trans l v t' \/ trans l w t').
  Proof.
    intros * TR; apply trans_brD_inv in TR as [n TR].
    destruct n; auto.
  Qed.

  Lemma trans_brS_inv : forall {X} (c : B X) k,
      trans l (BrS c k) t' ->
      exists x, t' ≅ k x /\ l = tau.
  Proof.
    intros * TR.
    cbn in *; red in TR; cbn in TR.
    dependent induction TR.
    eexists; split; auto.
    rewrite H3, ctree_eta, (ctree_eta t0), x; reflexivity.
  Qed.

  Lemma trans_step_inv :
    trans l (Step t) t' ->
    t' ≅ t /\ l = tau.
  Proof.
    intros * TR; apply trans_brS_inv in TR as (_ & ? & ?); auto.
  Qed.

  Lemma trans_brS2_inv :
    trans l (brS2 t u) t' ->
    (l = tau /\ (t' ≅ t \/ t' ≅ u)).
  Proof.
    intros * TR; apply trans_brS_inv in TR as (? & TR & ->); split; auto.
    destruct x; auto.
  Qed.

  Lemma trans_brS3_inv :
    trans l (brS3 t u v) t' ->
    (l = tau /\ (t' ≅ t \/ t' ≅ u \/ t' ≅ v)).
  Proof.
    intros * TR; apply trans_brS_inv in TR as (? & TR & ->); split; auto.
    destruct x; auto.
  Qed.

  Lemma trans_brS4_inv :
    trans l (brS4 t u v w) t' ->
    (l = tau /\ (t' ≅ t \/ t' ≅ u \/ t' ≅ v \/ t' ≅ w)).
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
      go U ≅ stuckD.
  Proof.
    intros * TR.
    remember (val x) as ox.
    rewrite ctree_eta; induction TR; intros; auto; try now inv Heqox.
    step; econstructor; intros abs; inv abs.
  Qed.

  Lemma trans_val_inv {Y} :
    forall (t u : ctree E B X) (x : Y),
      trans (val x) t u ->
      u ≅ stuckD.
  Proof.
    intros * TR. cbn in TR. red in TR.
    apply trans__val_inv in TR. rewrite ctree_eta. apply TR.
  Qed.

  Lemma wtrans_val_inv : forall (x : X),
      wtrans (val x) u stuckD ->
      exists t, wtrans tau u t /\ trans (val x) t stuckD.
  Proof.
    intros * TR.
    destruct TR as [t2 [t1 step1 step2] step3].
    exists t1; split.
    apply wtrans_tau; auto.
    erewrite <- trans_val_inv; eauto.
  Qed.

End forward.

(*|
[etrans] theory
---------------
|*)

Lemma etrans_case {E B X} `{B0 -< B} : forall l (t u : ctree E B X),
    etrans l t u ->
    (trans l t u \/ (l = tau /\ t ≅ u)).
Proof.
  intros [] * TR; cbn in *; intuition.
Qed.

Lemma etrans_ret_inv {E B X} `{HasStuck : B0 -< B} : forall x l (t : ctree E B X),
    etrans l (Ret x) t ->
    (l = tau /\ t ≅ Ret x) \/ (l = val x /\ t ≅ stuckD).
Proof.
  intros ? [] ? step; cbn in step.
  - intuition; try (eapply trans_ret in step; now apply step).
    inv H.
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

  Context {E B : Type -> Type} {X : Type} {HasStuck: B0 -< B}.
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
    (l = tau /\ v ≅ v').
  Proof.
    intros * ST TR.
    edestruct @etrans_case; eauto.
    apply ST in H; tauto.
  Qed.

  Lemma transs_is_stuck_inv (v v' : ctree E B X) :
    is_stuck v ->
    (trans tau)^* v v' ->
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
    (l = tau /\ t ≅ u).
  Proof.
    intros * ST TR.
    destruct TR as [? [? ?] ?].
    apply transs_is_stuck_inv in H; auto.
    rewrite H in ST; apply etrans_is_stuck_inv in H0 as [-> ?]; auto.
    rewrite H0 in ST; apply transs_is_stuck_inv in H1; auto.
    intuition.
    rewrite H, H0; auto.
  Qed.

  Lemma Br0_is_stuck b (c : B void) (k : void -> _) :
    is_stuck (Br b c k).
  Proof.
    red. intros. intro. inv H; destruct x.
  Qed.

  Lemma Br_fin0_is_stuck b (c : B (fin 0)) (k : fin 0 -> _) :
    is_stuck (Br b c k).
  Proof.
    red. intros. intro. inv H; now apply case0.
  Qed.

  Lemma stuckD_is_stuck :
    is_stuck stuckD.
  Proof.
    apply Br0_is_stuck.
  Qed.

  Lemma stuckS_is_stuck :
    is_stuck stuckS.
  Proof.
    apply Br0_is_stuck.
  Qed.

  Lemma spinD_gen_is_stuck {Y} (x : B Y) :
    is_stuck (spinD_gen x).
  Proof.
    red; intros * abs.
    remember (spinD_gen x) as v.
    assert (EQ: v ≅ spinD_gen x) by (subst; reflexivity); clear Heqv; revert EQ; rewrite ctree_eta.
    induction abs; auto; try now (rewrite ctree_eta; intros abs; step in abs; inv abs).
    intros EQ; apply IHabs.
    rewrite <- ctree_eta.
    rewrite ctree_eta in EQ.
    step in EQ; cbn in *.
    dependent induction EQ; auto.
  Qed.

  Lemma spinD_is_stuck `{B1 -< B}:
    is_stuck spinD.
  Proof.
    red; intros * abs.
    remember spinD as v.
    assert (EQ: v ≅ spinD) by (subst; reflexivity); clear Heqv; revert EQ; rewrite ctree_eta.
    induction abs; auto; try now (rewrite unfold_spinD; intros abs; step in abs; inv abs).
    intros EQ; apply IHabs.
    rewrite <- ctree_eta.
    rewrite unfold_spinD in EQ.
    step in EQ.
    dependent induction EQ; auto.
  Qed.

  Lemma spinS_is_not_stuck `{B1 -< B} :
    ~ (is_stuck spinS).
  Proof.
    red; intros * abs.
    apply (abs tau spinS).
    rewrite ctree_eta at 1; cbn.
    constructor; [exact tt | reflexivity].
  Qed.

End stuck.

(*|
wtrans theory
---------------
|*)

Section wtrans.

  Context {E B : Type -> Type} {X : Type} `{HasStuck : B0 -< B}.

  Lemma wtrans_step `{B1 -< B} : forall l (t t' : ctree E B X),
      wtrans l t t' ->
      wtrans l (Step t) t'.
  Proof.
    intros * TR.
    eapply wcons; eauto.
    apply trans_step.
  Qed.

  Lemma trans_tau_str_ret_inv : forall x (t : ctree E B X),
      (trans tau)^* (Ret x) t ->
      t ≅ Ret x.
  Proof.
    intros * [[|] step].
    - cbn in *; symmetry; eauto.
    - destruct step.
      apply trans_ret_inv in H; intuition congruence.
  Qed.

  Lemma wtrans_ret_inv : forall x l (t : ctree E B X),
      wtrans l (Ret x) t ->
      (l = tau /\ t ≅ Ret x) \/ (l = val x /\ t ≅ stuckD).
  Proof.
    intros * step.
    destruct step as [? [? step1 step2] step3].
    apply trans_tau_str_ret_inv in step1.
    rewrite step1 in step2; clear step1.
    apply etrans_ret_inv in step2 as [[-> EQ] |[-> EQ]].
    rewrite EQ in step3; apply trans_tau_str_ret_inv in step3; auto.
    rewrite EQ in step3.
    apply transs_is_stuck_inv in step3; [| apply stuckD_is_stuck].
    intuition.
  Qed.

  Lemma wtrans_val_inv' : forall (x : X) (t v : ctree E B X),
      wtrans (val x) t v ->
      exists u, wtrans tau t u /\ trans (val x) u v /\ v ≅ stuckD.
  Proof.
    intros * TR.
    destruct TR as [t2 [t1 step1 step2] step3].
    pose proof trans_val_inv step2 as EQ.
    rewrite EQ in step3, step2.
    apply transs_is_stuck_inv in step3; auto using stuckD_is_stuck.
    exists t1; repeat split.
    apply wtrans_tau, step1.
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
Lemma trans_bind_inv_aux {E B X Y} `{HasStuck : B0 -< B} l T U :
  trans_ l T U ->
  forall (t : ctree E B X) (k : X -> ctree E B Y) (u : ctree E B Y),
    go T ≅ t >>= k ->
    go U ≅ u ->
    (~ (is_val l) /\ exists t', trans l t t' /\ u ≅ t' >>= k) \/
      (exists (x : X), trans (val x) t stuckD /\ trans l (k x) u).
Proof.
  intros TR; induction TR; intros.
  - rewrite unfold_bind in H; setoid_rewrite (ctree_eta t0).
    desobs t0.
    + right.
      exists r; split.
      constructor.
      rewrite <- H.
      apply (Stepbr _ x); auto.
      rewrite <- H0; auto.
    + step in H; inv H.
    + step in H; dependent induction H.
      specialize (IHTR (k1 x) k0 u).
      destruct IHTR as [(? & ? & ? & ?) | (? & ? & ?)]; auto.
      rewrite <- ctree_eta, REL; reflexivity.
      left; split; eauto.
      exists x0; split; auto.
      apply (Stepbr _ x); auto.
      right.
      exists x0; split; auto.
      apply (Stepbr _ x); auto.
  - rewrite unfold_bind in H0; setoid_rewrite (ctree_eta t0).
    desobs t0.
    + right.
      exists r; split.
      constructor.
      rewrite <- H0.
      apply (Steptau _ x); auto.
      rewrite H, <- H1, ctree_eta; auto.
    + step in H0; inv H0.
    + step in H0; dependent induction H0.
      left; split; [intros abs; inv abs |].
      exists (k1 x); split.
      econstructor; reflexivity.
      rewrite <- H1, <- ctree_eta, <- H.
      apply REL.
  - rewrite unfold_bind in H0; setoid_rewrite (ctree_eta t0).
    desobs t0.
    + right.
      exists r; split.
      constructor.
      rewrite <- H0.
      constructor.
      rewrite H, <- H1, ctree_eta; auto.
    + step in H0; dependent induction H0.
      left; split; [intros abs; inv abs |].
      exists (k1 x); split.
      econstructor; reflexivity.
      rewrite <- H1, <- ctree_eta, <- H.
      apply REL.
    + step in H0; inv H0.
  - rewrite unfold_bind in H; setoid_rewrite (ctree_eta t).
    desobs t.
    + right.
      exists r0; split.
      constructor.
      rewrite <- H, <- H0.
      constructor.
    + step in H; inv H.
    + step in H; inv H.
Qed.

Lemma trans_bind_inv {E B X Y} `{B0 -< B} (t : ctree E B X) (k : X -> ctree E B Y) (u : ctree E B Y) l :
  trans l (t >>= k) u ->
  (~ (is_val l) /\ exists t', trans l t t' /\ u ≅ t' >>= k) \/
    (exists (x : X), trans (val x) t stuckD /\ trans l (k x) u).
Proof.
  intros TR.
  eapply trans_bind_inv_aux.
  apply TR.
  rewrite <- ctree_eta; reflexivity.
  rewrite <- ctree_eta; reflexivity.
Qed.

Lemma trans_bind_inv_l {E B X Y} `{B0 -< B} (t : ctree E B X) (k : X -> ctree E B Y) (u : ctree E B Y) l :
  trans l (t >>= k) u ->
  exists l' t', trans l' t t'.
Proof.
  intros TR.
  apply trans_bind_inv in TR.
  destruct TR as [(? & ? & ? & ?) | (? & ? & ?)]; eauto.
Qed.

Lemma trans_bind_l {E B X Y} `{HasStuck : B0 -< B} (t : ctree E B X) (k : X -> ctree E B Y) (u : ctree E B X) l :
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
  - rewrite unfold_bind.
    rewrite <- x1; cbn.
    econstructor.
    rewrite H.
    rewrite (ctree_eta t0),x,<- ctree_eta.
    reflexivity.
  - rewrite unfold_bind.
    rewrite <- x1; cbn.
    econstructor.
    rewrite H.
    rewrite (ctree_eta t0),x,<- ctree_eta.
    reflexivity.
  - exfalso; eapply NOV; constructor.
Qed.

Lemma trans_bind_r {E B X Y} `{B0 -< B} (t : ctree E B X) (k : X -> ctree E B Y) (u : ctree E B Y) x l :
  trans (val x) t stuckD ->
  trans l (k x) u ->
  trans l (t >>= k) u.
Proof.
  cbn; unfold transR; intros TR1.
  genobs t ot.
  remember (observe stuckD) as oc.
  remember (val x) as v.
  revert t x Heqot Heqoc Heqv.
  induction TR1; intros; try (inv Heqv; fail).
  - rewrite (ctree_eta t0), <- Heqot; cbn; econstructor.
    eapply IHTR1; eauto.
  - dependent induction Heqv.
    rewrite (ctree_eta t), <- Heqot, unfold_bind; cbn; auto.
Qed.

Lemma is_stuck_bind : forall {E B X Y} `{B0 -< B}
                        (t : ctree E B X) (k : X -> ctree E B Y),
    is_stuck t -> is_stuck (bind t k).
Proof.
  repeat intro.
  apply trans_bind_inv in H1 as [].
  - destruct H1 as (? & ? & ? & ?).
    now apply H0 in H2.
  - destruct H1 as (? & ? & ?).
    now apply H0 in H1.
Qed.

(*|
Forward and backward rules for [wtrans] w.r.t. [bind]
-----------------------------------------------------
|*)

Lemma etrans_bind_inv {E B X Y} `{HasStuck : B0 -< B} (t : ctree E B X) (k : X -> ctree E B Y) (u : ctree E B Y) l :
  etrans l (t >>= k) u ->
  (~ (is_val l) /\ exists t', etrans l t t' /\ u ≅ t' >>= k) \/
    (exists (x : X), trans (val x) t stuckD /\ etrans l (k x) u).
Proof.
  intros TR.
  apply @etrans_case in TR as [ | (-> & ?)].
  - apply trans_bind_inv in H as [[? (? & ? & ?)]|( ? & ? & ?)]; eauto.
    left; split; eauto.
    eexists; split; eauto; apply trans_etrans; auto.
    right; eexists; split; eauto; apply trans_etrans; auto.
  - left; split.
    intros abs; inv abs.
    exists t; split; auto using enil; symmetry; auto.
Qed.

Lemma transs_bind_inv {E B X Y} `{B0 -< B} (t : ctree E B X) (k : X -> ctree E B Y) (u : ctree E B Y) :
  (trans tau)^* (t >>= k) u ->
  (exists t', (trans tau)^* t t' /\ u ≅ t' >>= k) \/
    (exists (x : X), wtrans (val x) t stuckD /\ (trans tau)^* (k x) u).
Proof.
  intros [n TR].
  revert t k u TR.
  induction n as [| n IH]; intros; subst.
  - cbn in TR.
    left; exists t; split.
    exists 0%nat; reflexivity.
    symmetry; auto.
  - destruct TR as [t1 TR1 TR2].
    apply trans_bind_inv in TR1 as [(_ & t2 & TR1 & EQ) | (x & TR1 & TR1')].
    + rewrite EQ in TR2; clear t1 EQ.
      apply IH in TR2 as [(t3 & TR2 & EQ')| (x & TR2 & TR3)].
      * left; eexists; split; eauto.
        apply wtrans_tau; eapply wcons; eauto.
        apply wtrans_tau; auto.
      * right; exists x; split; eauto.
        eapply wcons; eauto.
    + right.
      exists x; split.
      apply trans_wtrans; auto.
      exists (S n), t1; auto.
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
Lemma wtrans_bind_inv {E B X Y} `{HasStuck : B0 -< B} (t : ctree E B X) (k : X -> ctree E B Y) (u : ctree E B Y) l :
  wtrans l (t >>= k) u ->
  (~ (is_val l) /\ exists t', wtrans l t t' /\ u ≅ t' >>= k) \/
    (exists (x : X), wtrans (val x) t stuckD /\ wtrans l (k x) u) \/
    (exists (x : X) s, wtrans l t s /\ trans (val x) s stuckD /\ wtrans tau (k x) u).
Proof.
  intros TR.
  destruct TR as [t2 [t1 step1 step2] step3].
  apply transs_bind_inv in step1 as [(u1 & TR1 & EQ1)| (x & TR1 & TR1')].
  - rewrite EQ1 in step2; clear t1 EQ1.
    apply etrans_bind_inv in step2 as [(H & u2 & TR2 & EQ2)| (x & TR2 & TR2')].
    + rewrite EQ2 in step3; clear t2 EQ2.
      apply transs_bind_inv in step3 as [(u3 & TR3 & EQ3)| (x & TR3 & TR3')].
      * left; split; auto.
        eexists; split; eauto.
        exists u2; auto; exists u1; auto.
      * right; right.
        apply wtrans_val_inv in TR3 as (u3 & TR2' & TR2'').
        exists x, u3.
        split; [|split]; auto.
        2:apply wtrans_tau; auto.
        exists u2; [exists u1; assumption | ].
        apply wtrans_tau; apply wtrans_tau in TR1.
        eapply wconss; eauto.
    + right; left.
      exists x; split.
      eexists; [eexists |]; eauto; apply wtrans_tau, wnil.
      eexists; [eexists |]; eauto; apply wtrans_tau, wnil.
  - right; left.
    exists x; split; eauto.
    eexists; [eexists |]; eauto.
Qed.

Lemma etrans_bind_l {E B X Y} `{B0 -< B} (t : ctree E B X) (k : X -> ctree E B Y) (u : ctree E B X) l :
  ~ is_val l ->
  etrans l t u ->
  etrans l (t >>= k) (u >>= k).
Proof.
  destruct l; cbn; try apply trans_bind_l; auto.
  intros NOV [|].
  left; apply trans_bind_l; auto.
  right; rewrite H0; auto.
Qed.

Lemma transs_bind_l {E B X Y} `{B0 -< B} (t : ctree E B X) (k : X -> ctree E B Y) (u : ctree E B X) :
  (trans tau)^* t u ->
  (trans tau)^* (t >>= k) (u >>= k).
Proof.
  intros [n TR].
  revert t u TR.
  induction n as [| n IH].
  - cbn; intros; exists 0%nat; cbn; rewrite TR; reflexivity.
  - intros t u [v TR1 TR2].
    apply IH in TR2.
    eapply wtrans_tau, wcons.
    apply trans_bind_l; eauto; intros abs; inv abs.
    apply wtrans_tau; eauto.
Qed.

Lemma wtrans_bind_l {E B X Y} `{B0 -< B} (t : ctree E B X) (k : X -> ctree E B Y) (u : ctree E B X) l :
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

Lemma wtrans_case {E B X} `{HasStuck : B0 -< B} (t u : ctree E B X) l:
  wtrans l t u ->
  t ≅ u \/ (exists v, trans l t v /\ wtrans tau v u) \/ (exists v, trans tau t v /\ wtrans l v u).
Proof.
  intros [t2 [t1 [n TR1] TR2] TR3].
  destruct n as [| n].
  - apply wtrans_tau in TR3.
    cbn in TR1; rewrite <- TR1 in TR2.
    destruct l; eauto.
    destruct TR2; eauto.
    cbn in H; rewrite <- H in TR3.
    apply wtrans_tau in TR3.
    destruct TR3 as [[| n] ?]; eauto.
    destruct H0 as [? ? ?]; right; left; eexists; split; eauto.
    apply wtrans_tau; exists n; auto.
  - destruct TR1 as [? ? ?].
    right; right.
    eexists; split; eauto.
    exists t2; [exists t1|]; eauto.
    exists n; eauto.
Qed.

Lemma wtrans_case' {E B X} `{HasStuck : B0 -< B} (t u : ctree E B X) l:
  wtrans l t u ->
  match l with
  | tau => (t ≅ u \/ exists v, trans tau t v /\ wtrans tau v u)
  | _   => (exists v, trans l t v /\ wtrans tau v u) \/
            (exists v, trans tau t v /\ wtrans l v u)
  end.
Proof.
  intros [t2 [t1 [n TR1] TR2] TR3].
  destruct n as [| n].
  - apply wtrans_tau in TR3.
    cbn in TR1; rewrite <- TR1 in TR2.
    destruct l; eauto.
    destruct TR2; eauto.
    cbn in H; rewrite <- H in TR3.
    apply wtrans_tau in TR3.
    destruct TR3 as [[| n] ?]; eauto.
    destruct H0 as [? ? ?]; right; eexists; split; eauto.
    apply wtrans_tau; exists n; auto.
  - destruct TR1 as [? ? ?].
    destruct l; right.
    all:eexists; split; eauto.
    all:exists t2; [exists t1|]; eauto.
          all:exists n; eauto.
Qed.

Lemma wtrans_stuckD_inv {E B R} `{HasStuck : B0 -< B} :
  forall (t : ctree E B R) l,
    wtrans l stuckD t ->
    match l with | tau => t ≅ stuckD | _ => False end.
Proof.
  intros * TR.
  apply wtrans_case' in TR.
  destruct l; break; cbn in *.
  symmetry; auto.
  all: exfalso; eapply stuckD_is_stuck; now apply H.
Qed.

Lemma pwtrans_case {E B X} `{B0 -< B} (t u : ctree E B X) l:
  pwtrans l t u ->
  (exists v, trans l t v /\ wtrans tau v u) \/ (exists v, trans tau t v /\ wtrans l v u).
Proof.
  intros [t2 [t1 [n TR1] TR2] TR3].
  destruct n as [| n].
  - apply wtrans_tau in TR3.
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
Lemma wtrans_bind_r {E B X Y} `{HasStuck : B0 -< B} (t : ctree E B X) (k : X -> ctree E B Y) (u : ctree E B Y) x l :
  wtrans (val x) t stuckD ->
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

Lemma wtrans_bind_r' {E B X Y} `{HasStuck : B0 -< B} (t : ctree E B X) (k : X -> ctree E B Y) (u : ctree E B Y) x l :
  wtrans (val x) t stuckD ->
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

Lemma trans_val_invT {E B R R'} `{B0 -< B}:
  forall (t u : ctree E B R) (v : R'),
    trans (val v) t u ->
    R = R'.
Proof.
  intros * TR.
  remember (val v) as ov.
  induction TR; intros; auto; try now inv Heqov.
Qed.

Lemma wtrans_bind_lr {E B X Y} `{B0 -< B} (t u : ctree E B X) (k : X -> ctree E B Y) (v : ctree E B Y) x l :
  pwtrans l t u ->
  wtrans (val x) u stuckD ->
  pwtrans tau (k x) v ->
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
      apply transs_is_stuck_inv in TR1''; [| apply stuckD_is_stuck].
      rewrite <- TR1'' in TR2.
      apply wtrans_is_stuck_inv in TR2; [| apply stuckD_is_stuck].
      destruct TR2 as [abs _]; inv abs.
    }
    eexists.
    2:apply trans_etrans, trans_bind_l; eauto.
    apply wtrans_tau; eapply wtrans_bind_l; [intros abs; inv abs| apply wtrans_tau; auto].
  - apply wtrans_tau.
    eapply wconss.
    eapply wtrans_bind_l; [intros abs; inv abs| apply wtrans_tau; eauto].
    eapply wtrans_bind_r'; eauto.
Qed.

Lemma trans_trigger : forall {E B X Y} `{B0 -< B} (e : E X) x (k : X -> ctree E B Y),
    trans (obs e x) (trigger e >>= k) (k x).
Proof.
  intros.
  unfold CTree.trigger.
  rewrite unfold_bind; cbn.
  setoid_rewrite bind_ret_l.
  constructor; auto.
Qed.

Lemma trans_trigger' : forall {E B X Y} `{B0 -< B} (e : E X) x (t : ctree E B Y),
    trans (obs e x) (trigger e;; t) t.
Proof.
  intros.
  unfold CTree.trigger.
  rewrite unfold_bind; cbn.
  setoid_rewrite bind_ret_l.
  constructor; auto.
Qed.

Lemma trans_trigger_inv : forall {E B X Y} `{HasStuck : B0 -< B} (e : E X) (k : X -> ctree E B Y) l u,
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
  forall {E B : Type -> Type} {X : Type} {H : B0 -< B} {Y : Type}
    [l : label] [t t' : ctree E B X] (c : B Y) (k : Y -> ctree E B X) (x : Y),
    trans l t t' -> k x ≅ t -> trans l (CTree.branch false c >>= k) t'.
Proof.
  intros.
  setoid_rewrite bind_branch.
  eapply trans_brD; eauto.
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

Lemma wf_val_trans {E B X} `{B0 -< B} (l : @label E) (t t' : ctree E B X) :
  trans l t t' -> wf_val X l.
Proof.
  red. intros. subst.
  now apply trans_val_invT in H0.
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
 |*)
Section Coproduct.
  Arguments label: clear implicits.
  Context {L R C: Type -> Type} {X: Type} {HasStuck: B0 -< C}.
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

  (*| Obs transition on the left, ignores right transitions and [tau] |*)
  Definition ltrans {X}(l: L X)(x: X): srel SS SS := 
    (trans tau ⊔ srtrans)^* ⋅ trans (obs (inl1 l) x) ⋅ (trans tau ⊔ srtrans)^*.

  (*| Obs transition on the right, ignores left transitions and [tau] |*)
  Definition rtrans {X}(r: R X)(x: X): srel SS SS := 
    (trans tau ⊔ sltrans)^* ⋅ trans (obs (inr1 r) x) ⋅ (trans tau ⊔ sltrans)^*.
  
End Coproduct.

(*|
[inv_trans] is an helper tactic to automatically
invert hypotheses involving [trans].
|*)

#[local] Notation trans' l t u := (hrel_of (trans l) t u).

Ltac inv_trans_one :=
  match goal with

  (* Ret *)
  | h : trans' _ (Ret ?x) _ |- _ =>
      let EQl := fresh "EQl" in
      apply trans_ret_inv in h as [?EQ EQl];
      match type of EQl with
      | val _   = val _ => apply val_eq_inv in EQl; try (inversion EQl; fail)
      | tau     = val _ => now inv EQl
      | obs _ _ = val _ => now inv EQl
      | _ => idtac
      end

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
      | val _   = obs _ _ => now inv EQl
      | tau     = obs _ _ => now inv EQl
      | _ => idtac
      end

  (* Step *)
  | h : trans' _ (Step _) _ |- _ =>
      let EQl := fresh "EQl" in
      apply trans_step_inv in h as (?EQ & EQl);
      match type of EQl with
      | tau     = tau => clear EQl
      | val _   = tau => now inv EQl
      | obs _ _ = tau => now inv EQl
      | _ => idtac
      end

  (* BrS *)
  | h : trans' _ (BrS ?n ?k) _ |- _ =>
      let x := fresh "x" in
      let EQl := fresh "EQl" in
      apply trans_brS_inv in h as (x & ?EQ & EQl);
      match type of EQl with
      | tau     = tau => clear EQl
      | val _   = tau => now inv EQl
      | obs _ _ = tau => now inv EQl
      | _ => idtac
      end

  (* brS2 *)
  | h : trans' _ (brS2 _ _) _ |- _ =>
      let EQl := fresh "EQl" in
      apply trans_brS2_inv in h as (EQl & [?EQ | ?EQ]);
      match type of EQl with
      | tau     = tau => clear EQl
      | val _   = tau => now inv EQl
      | obs _ _ = tau => now inv EQl
      | _ => idtac
      end

  (* brS3 *)
  | h : trans' _ (brS3 _ _ _) _ |- _ =>
      let EQl := fresh "EQl" in
      apply trans_brS3_inv in h as (EQl & [?EQ | [?EQ | ?EQ]]);
      match type of EQl with
      | tau     = tau => clear EQl
      | val _   = tau => now inv EQl
      | obs _ _ = tau => now inv EQl
      | _ => idtac
      end

  (* brS4 *)
  | h : trans' _ (brS4 _ _ _ _) _ |- _ =>
      let EQl := fresh "EQl" in
      apply trans_brS4_inv in h as (EQl & [?EQ | [?EQ | [?EQ | ?EQ]]]);
      match type of EQl with
      | tau     = tau => clear EQl
      | val _   = tau => now inv EQl
      | obs _ _ = tau => now inv EQl
      | _ => idtac
      end

  (* Guard *)
  | h : trans' _ (Guard _) _ |- _ =>
      apply trans_guard_inv in h

  (* BrD *)
  | h : trans' _ (BrD ?n ?k) _ |- _ =>
      let x := fresh "x" in
      apply trans_brD_inv in h as (x & ?TR)

  (* brD2 *)
  | h : trans' _ (brD2 _ _) _ |- _ =>
      apply trans_brD2_inv in h as [?TR | ?TR]

  (* brD3 *)
  | h : trans' _ (brD3 _ _ _) _ |- _ =>
      apply trans_brD3_inv in h as [?TR | [?TR | ?TR]]

  (* brD4 *)
  | h : trans' _ (brD4 _ _ _ _) _ |- _ =>
      apply trans_brD4_inv in h as [?TR | [?TR | [?TR | ?TR]]]

  (* stuckD *)
  | h : trans' _ stuckD _ |- _ =>
      exfalso; eapply stuckD_is_stuck; now apply h
  (* stuckS *)
  | h : trans' _ stuckS _ |- _ =>
      exfalso; eapply stuckS_is_stuck; now apply h

  (* trigger *)
  | h : trans' _ (CTree.bind (CTree.trigger ?e) ?t) _ |- _ =>
      apply trans_trigger_inv in h as (?x & ?EQ & ?EQl)

  end; try subs
.

Ltac inv_trans := repeat inv_trans_one.

Create HintDb trans.
#[global] Hint Resolve
 trans_ret trans_vis trans_brS trans_brD
 trans_guard
 trans_brD21 trans_brD22
 trans_brD31 trans_brD32 trans_brD33
 trans_brD41 trans_brD42 trans_brD43 trans_brD44
 trans_step
 trans_brS21 trans_brS22
 trans_brS31 trans_brS32 trans_brS33
 trans_brS41 trans_brS42 trans_brS43 trans_brS44
 trans_trigger trans_bind_l trans_bind_r
  : trans.

#[global] Hint Constructors is_val : trans.
#[global] Hint Resolve
  is_val_tau is_val_obs
  wf_val_val wf_val_nonval wf_val_trans : trans.

Ltac etrans := eauto with trans.
