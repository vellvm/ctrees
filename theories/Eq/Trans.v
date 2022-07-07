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

This transition system is used to define a notion of strong bisimulation
in the process algebra tradition.
It also leads to a weak bisimulation by defining [wtrans] as a
sequence of tau steps, and allowing a challenge to be answered by
[wtrans . trans . wtrans], and to a strong simulation by considering only
half of the bisimulation game.
Once [trans] is defined over our structure, we can reuse the constructions
used by Pous in [Coinduction All the Way Up] to build these weak relations
-- with the exception that we need to work in Kleene Algebras w.r.t. to model
closed under [equ] rather than [eq].

.. coq:: none
|*)

From Coq Require Import Fin.

From Coinduction Require Import
     coinduction rel tactics.

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

  Context {E : Type -> Type} {R : Type}.

  Notation S' := (ctree' E R).
  Notation S  := (ctree  E R).

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

  | Stepbr {n} (x : Fin.t n) k l t :
    trans_ l (observe (k x)) t ->
    trans_ l (BrF false n k) t

  | Steptau {n} (x : Fin.t n) k t :
    k x ≅ t ->
    trans_ tau (BrSF n k) (observe t)

  | Stepobs {X} (e : E X) k x t :
    k x ≅ t ->
    trans_ (obs e x) (VisF e k) (observe t)

  | Stepval r k :
    trans_ (val r) (RetF r) (BrF false 0 k)
  .
  Hint Constructors trans_ : core.

  Definition transR l : hrel S S :=
    fun u v => trans_ l (observe u) (observe v).

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
      * change (VisF e k1) with (observe (Vis e k1)).
        apply (Steptau x).
        rewrite H.
        rewrite (ctree_eta t), <- H2.
        step; constructor; intros; symmetry; auto.
      * change (BrF b n0 k1) with (observe (Br b n0 k1)).
        apply (Steptau x).
        rewrite H.
        rewrite (ctree_eta t), <- H2.
        step; constructor; intros; symmetry; auto.
    + change u with (observe (go u)).
      econstructor.
      rewrite H; symmetry; step; auto.
    + inv equ.
      econstructor.
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
      apply (Stepbr x).
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

(*|
Backward reasoning for [trans]
------------------------------
Note: we need to be a bit careful to define these proof rules
explicitly over [ctree]s and not [rel_of SS] as gets coerced
in the section above so that [eauto with trans] works smoothly.
|*)
Section backward.

  Context {E : Type -> Type} {X : Type}.

(*|
Structural rules
|*)

  Lemma trans_ret : forall (x : X),
      trans (E := E) (val x) (Ret x) stuckD.
  Proof.
    intros; constructor.
  Qed.

  Lemma trans_vis : forall {Y} (e : E Y) x (k : Y -> ctree E X),
      trans (obs e x) (Vis e k) (k x).
  Proof.
    intros; constructor; auto.
  Qed.

  Lemma trans_brD : forall l (t t' : ctree E X) n k x,
      trans l t t' ->
      k x ≅ t ->
      trans l (BrD n k) t'.
  Proof.
    intros * TR Eq.
    apply Stepbr with x.
    rewrite Eq; auto.
  Qed.

  Lemma trans_brS : forall n (k : _ -> ctree E X) x,
      trans tau (BrS n k) (k x).
  Proof.
    intros.
    apply Steptau with x; reflexivity.
  Qed.

(*|
Ad-hoc rules for pre-defined finite branching
|*)

  Variable (l : @label E) (t t' u u' v v' w w' : ctree E X).

  Lemma trans_step :
      trans tau (Step t) t.
  Proof.
    intros; apply (@trans_brS 1%nat (fun _ => t) F1).
  Qed.

  Lemma trans_brS21 :
      trans tau (brS2 t u) t.
  Proof.
    intros.
    unfold brS2.
    match goal with
      |- _ (trans tau) (BrS 2 ?k) ?t => exact (trans_brS k F1)
    end.
  Qed.

  Lemma trans_brS22 :
      trans tau (brS2 t u) u.
  Proof.
    intros.
    unfold brS2.
    match goal with
      |- _ (trans tau) (BrS 2 ?k) ?t => exact (trans_brS k (FS F1))
    end.
  Qed.

  Lemma trans_brD21 :
      trans l t t' ->
      trans l (brD2 t u) t'.
  Proof.
    intros * TR.
    eapply trans_brD with (x := F1); eauto.
  Qed.

  Lemma trans_brD22 :
      trans l u u' ->
      trans l (brD2 t u) u'.
  Proof.
    intros * TR.
    eapply trans_brD with (x := FS F1); eauto.
  Qed.

  Lemma trans_brS31 :
      trans tau (brS3 t u v) t.
  Proof.
    intros.
    unfold brS3.
    match goal with
      |- _ (trans tau) (BrS 3 ?k) ?t => exact (trans_brS k F1)
    end.
  Qed.

  Lemma trans_brS32 :
      trans tau (brS3 t u v) u.
  Proof.
    intros.
    unfold brS3.
    match goal with
      |- _ (trans tau) (BrS 3 ?k) ?t => exact (trans_brS k (FS F1))
    end.
  Qed.

  Lemma trans_brS33 :
      trans tau (brS3 t u v) v.
  Proof.
    intros.
    unfold brS3.
    match goal with
      |- _ (trans tau) (BrS 3 ?k) ?t => exact (trans_brS k (FS (FS F1)))
    end.
  Qed.

  Lemma trans_brD31 :
      trans l t t' ->
      trans l (brD3 t u v) t'.
  Proof.
    intros * TR.
    eapply trans_brD with (x := F1); eauto.
  Qed.

  Lemma trans_brD32 :
      trans l u u' ->
      trans l (brD3 t u v) u'.
  Proof.
    intros * TR.
    eapply trans_brD with (x := FS F1); eauto.
  Qed.

  Lemma trans_brD33 :
      trans l v v' ->
      trans l (brD3 t u v) v'.
  Proof.
    intros * TR.
    eapply trans_brD with (x := FS (FS F1)); eauto.
  Qed.

  Lemma trans_brS41 :
      trans tau (brS4 t u v w) t.
  Proof.
    intros.
    unfold brS4.
    match goal with
      |- _ (trans tau) (BrS 4 ?k) ?t => exact (trans_brS k F1)
    end.
  Qed.

  Lemma trans_brS42 :
      trans tau (brS4 t u v w) u.
  Proof.
    intros.
    unfold brS4.
    match goal with
      |- _ (trans tau) (BrS 4 ?k) ?t => exact (trans_brS k (FS F1))
    end.
  Qed.

  Lemma trans_brS43 :
      trans tau (brS4 t u v w) v.
  Proof.
    intros.
    unfold brS4.
    match goal with
      |- _ (trans tau) (BrS 4 ?k) ?t => exact (trans_brS k (FS (FS F1)))
    end.
  Qed.

  Lemma trans_brS44 :
      trans tau (brS4 t u v w) w.
  Proof.
    intros.
    unfold brS4.
    match goal with
      |- _ (trans tau) (BrS 4 ?k) ?t => exact (trans_brS k (FS (FS (FS F1))))
    end.
  Qed.

  Lemma trans_guard :
      trans l t t' ->
      trans l (Guard t) t'.
  Proof.
    intros * TR; eapply trans_brD; eauto; exact F1.
  Qed.

  Lemma trans_brD41 :
      trans l t t' ->
      trans l (brD4 t u v w) t'.
  Proof.
    intros * TR.
    eapply trans_brD with (x := F1); eauto.
  Qed.

  Lemma trans_brD42 :
      trans l u u' ->
      trans l (brD4 t u v w) u'.
  Proof.
    intros * TR.
    eapply trans_brD with (x := FS F1); eauto.
  Qed.

  Lemma trans_brD43 :
      trans l v v' ->
      trans l (brD4 t u v w) v'.
  Proof.
    intros * TR.
    eapply trans_brD with (x := FS (FS F1)); eauto.
  Qed.

  Lemma trans_brD44 :
      trans l w w' ->
      trans l (brD4 t u v w) w'.
  Proof.
    intros * TR.
    eapply trans_brD with (x := FS (FS (FS F1))); eauto.
  Qed.

End backward.

(*|
Forward reasoning for [trans]
------------------------------
|*)

Section forward.

  Context {E : Type -> Type} {X : Type}.

(*|
Inverting equalities between labels
|*)

  Lemma val_eq_invT : forall X Y x y, @val E X x = @val E Y y -> X = Y.
    intros * EQ.
    now dependent induction EQ.
  Qed.

  Lemma val_eq_inv : forall X x y, @val E X x = val y -> x = y.
    intros * EQ.
    now dependent induction EQ.
  Qed.

  Lemma obs_eq_invT : forall X Y e1 e2 v1 v2, @obs E X e1 v1 = @obs E Y e2 v2 -> X = Y.
    intros * EQ.
    now dependent induction EQ.
  Qed.

  Lemma obs_eq_inv : forall X e1 e2 v1 v2, @obs E X e1 v1 = @obs E X e2 v2 -> e1 = e2 /\ v1 = v2.
    intros * EQ.
    now dependent induction EQ.
  Qed.

(*|
Structural rules
|*)

  Lemma trans_ret_inv : forall x l (t : ctree E X),
      trans l (Ret x) t ->
       t ≅ stuckD /\ l = val x.
  Proof.
    intros * TR; inv TR; intuition.
    rewrite ctree_eta, <- H2; auto.
    step; constructor; intros abs; inv abs.
  Qed.

  Lemma trans_vis_inv : forall {Y} (e : E Y) k l (u : ctree E X),
      trans l (Vis e k) u ->
      exists x, u ≅ k x /\ l = obs e x.
  Proof.
    intros * TR.
    inv TR.
    dependent induction H3; eexists; split; eauto.
    rewrite ctree_eta, <- H4, <- ctree_eta; symmetry; auto.
  Qed.

  Lemma trans_brD_inv : forall l n k (u : ctree E X),
      trans l (BrD n k) u ->
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
    revert n k u Heqox Heqoy.
    induction TR; intros; inv Heqox; eauto.
  Qed.

(*|
Ad-hoc rules for pre-defined finite branching
|*)

  Variable (l : @label E) (t t' u v w : ctree E X).

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
    destruct n0; auto.
  Qed.

  Lemma trans_brD4_inv :
      trans l (brD4 t u v w) t' ->
      (trans l t t' \/ trans l u t' \/ trans l v t' \/ trans l w t').
  Proof.
    intros * TR; apply trans_brD_inv in TR as [n TR].
    destruct n; auto.
    destruct n0; auto.
    destruct n0; auto.
  Qed.

  Lemma trans_brS_inv : forall n k,
      trans l (BrS n k) t' ->
      exists x, t' ≅ k x /\ l = tau.
  Proof.
    intros * TR.
    cbn in *; red in TR; cbn in TR.
    dependent induction TR.
        eexists; split; auto.
      rewrite H, ctree_eta, (ctree_eta t0), x; reflexivity.
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
    destruct x; auto.
  Qed.

  Lemma trans_brS4_inv :
      trans l (brS4 t u v w) t' ->
      (l = tau /\ (t' ≅ t \/ t' ≅ u \/ t' ≅ v \/ t' ≅ w)).
  Proof.
    intros * TR; apply trans_brS_inv in TR as (? & TR & ->); split; auto.
    destruct x; auto.
    destruct x; auto.
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
    forall (T U : ctree' E X) (x : Y),
      trans_ (val x) T U ->
      go U ≅ stuckD.
  Proof.
    intros * TR.
    remember (val x) as ox.
    rewrite ctree_eta; induction TR; intros; auto; try now inv Heqox.
    step; econstructor; intros abs; inv abs.
  Qed.

  Lemma trans_val_inv {Y} :
    forall (t u : ctree E X) (x : Y),
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

Lemma etrans_case {E X} : forall l (t u : ctree E X),
    etrans l t u ->
    (trans l t u \/ (l = tau /\ t ≅ u)).
Proof.
  intros [] * TR; cbn in *; intuition.
Qed.

Lemma etrans_ret_inv {E X} : forall x l (t : ctree E X),
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
to reduce pure computations is of course stuck, but so is [spinD],
while [spinS] is not.
|*)

Section stuck.

  Context {E : Type -> Type} {X : Type}.
  Variable (l : @label E) (t u : ctree E X).

  Definition is_stuck : ctree E X -> Prop :=
    fun t => forall l u, ~ (trans l t u).

  #[global] Instance is_stuck_equ : Proper (equ eq ==> iff) is_stuck.
  Proof.
    intros ? ? EQ; split; intros ST; red; intros * ABS.
    rewrite <- EQ in ABS; eapply ST; eauto.
    rewrite EQ in ABS; eapply ST; eauto.
  Qed.

  Lemma etrans_is_stuck_inv (v v' : ctree E X) :
      is_stuck v ->
      etrans l v v' ->
      (l = tau /\ v ≅ v').
  Proof.
    intros * ST TR.
    edestruct @etrans_case; eauto.
    apply ST in H; tauto.
  Qed.

  Lemma transs_is_stuck_inv (v v' : ctree E X) :
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

  Lemma stuckD_is_stuck :
    is_stuck stuckD.
  Proof.
    red; intros * abs; inv abs; inv x.
  Qed.

  Lemma stuckS_is_stuck :
    is_stuck stuckS.
  Proof.
    red; intros * abs; inv abs; inv x.
  Qed.

  Lemma spinD_nary_is_stuck n :
    is_stuck (spinD_nary n).
  Proof.
    red; intros * abs.
    remember (spinD_nary n) as v.
    assert (EQ: v ≅ spinD_nary n) by (subst; reflexivity); clear Heqv; revert EQ; rewrite ctree_eta.
    induction abs; auto; try now (rewrite ctree_eta; intros abs; step in abs; inv abs).
    intros EQ; apply IHabs.
    rewrite <- ctree_eta.
    rewrite ctree_eta in EQ.
    step in EQ; cbn in *.
    dependent induction EQ; auto.
  Qed.

  Lemma spinD_is_stuck :
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

  Lemma spinS_is_not_stuck :
    ~ (is_stuck spinS).
  Proof.
    red; intros * abs.
    apply (abs tau spinS).
    rewrite ctree_eta at 1; cbn.
    constructor; [exact Fin.F1 | reflexivity].
  Qed.

End stuck.

(*|
wtrans theory
---------------
|*)

Section wtrans.

  Context {E : Type -> Type} {X : Type}.

  Lemma wtrans_step : forall l (t t' : ctree E X),
      wtrans l t t' ->
      wtrans l (Step t) t'.
  Proof.
    intros * TR.
    eapply wcons; eauto.
    apply trans_step.
  Qed.

  Lemma trans_tau_str_ret_inv : forall x (t : ctree E X),
      (trans tau)^* (Ret x) t ->
      t ≅ Ret x.
  Proof.
    intros * [[|] step].
    - cbn in *; symmetry; eauto.
    - destruct step.
      apply trans_ret_inv in H; intuition congruence.
  Qed.

  Lemma wtrans_ret_inv : forall x l (t : ctree E X),
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

  Lemma wtrans_val_inv' : forall (x : X) (t v : ctree E X),
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
Variant is_val {E} : (@label E) -> Prop :=
  | Is_val : forall X (x : X), is_val (val x).

Lemma trans_bind_inv_aux {E X Y} l T U :
  trans_ l T U ->
  forall (t : ctree E X) (k : X -> ctree E Y) (u : ctree E Y),
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
      apply (Stepbr x); auto.
      rewrite <- H0; auto.
    + step in H; inv H.
    + step in H; dependent induction H.
      specialize (IHTR (k1 x) k0 u).
      destruct IHTR as [(? & ? & ? & ?) | (? & ? & ?)]; auto.
      rewrite <- ctree_eta, REL; reflexivity.
      left; split; eauto.
      exists x0; split; auto.
      apply (Stepbr x); auto.
      right.
      exists x0; split; auto.
      apply (Stepbr x); auto.
  - rewrite unfold_bind in H0; setoid_rewrite (ctree_eta t0).
    desobs t0.
    + right.
      exists r; split.
      constructor.
      rewrite <- H0.
      apply (Steptau x); auto.
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

Lemma trans_bind_inv {E X Y} (t : ctree E X) (k : X -> ctree E Y) (u : ctree E Y) l :
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

Lemma trans_bind_l {E X Y} (t : ctree E X) (k : X -> ctree E Y) (u : ctree E X) l :
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

Lemma trans_bind_r {E X Y} (t : ctree E X) (k : X -> ctree E Y) (u : ctree E Y) x l :
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

(*|
Forward and backward rules for [wtrans] w.r.t. [bind]
-----------------------------------------------------
|*)

Lemma etrans_bind_inv {E X Y} (t : ctree E X) (k : X -> ctree E Y) (u : ctree E Y) l :
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

Lemma transs_bind_inv {E X Y} (t : ctree E X) (k : X -> ctree E Y) (u : ctree E Y) :
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
Lemma wtrans_bind_inv {E X Y} (t : ctree E X) (k : X -> ctree E Y) (u : ctree E Y) l :
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

Lemma etrans_bind_l {E X Y} (t : ctree E X) (k : X -> ctree E Y) (u : ctree E X) l :
  ~ is_val l ->
  etrans l t u ->
  etrans l (t >>= k) (u >>= k).
Proof.
  destruct l; cbn; try apply trans_bind_l; auto.
  intros NOV [|].
  left; apply trans_bind_l; auto.
  right; rewrite H; auto.
Qed.

Lemma transs_bind_l {E X Y} (t : ctree E X) (k : X -> ctree E Y) (u : ctree E X) :
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

Lemma wtrans_bind_l {E X Y} (t : ctree E X) (k : X -> ctree E Y) (u : ctree E X) l :
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

Lemma wtrans_case {E X} (t u : ctree E X) l:
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

Lemma wtrans_case' {E X} (t u : ctree E X) l:
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

Lemma wtrans_stuckD_inv {E R} :
  forall (t : ctree E R) l,
    wtrans l stuckD t ->
    match l with | tau => t ≅ stuckD | _ => False end.
Proof.
  intros * TR.
  apply wtrans_case' in TR.
  destruct l; break; cbn in *.
  symmetry; auto.
  all: exfalso; eapply stuckD_is_stuck; now apply H.
Qed.

Lemma pwtrans_case {E X} (t u : ctree E X) l:
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
Lemma wtrans_bind_r {E X Y} (t : ctree E X) (k : X -> ctree E Y) (u : ctree E Y) x l :
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

Lemma wtrans_bind_r' {E X Y} (t : ctree E X) (k : X -> ctree E Y) (u : ctree E Y) x l :
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

Lemma trans_val_invT {E R R'}:
  forall (t u : ctree E R) (v : R'),
    trans (val v) t u ->
    R = R'.
Proof.
  intros * TR.
  remember (val v) as ov.
  induction TR; intros; auto; try now inv Heqov.
Qed.

Lemma wtrans_bind_lr {E X Y} (t u : ctree E X) (k : X -> ctree E Y) (v : ctree E Y) x l :
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

Lemma trans_trigger : forall {E X Y} (e : E X) x (k : X -> ctree E Y),
    trans (obs e x) (trigger e >>= k) (k x).
Proof.
  intros.
  unfold CTree.trigger.
  rewrite unfold_bind; cbn.
  setoid_rewrite bind_ret_l.
  constructor; auto.
Qed.

Lemma trans_trigger' : forall {E X Y} (e : E X) x (t : ctree E Y),
    trans (obs e x) (trigger e;; t) t.
Proof.
  intros.
  unfold CTree.trigger.
  rewrite unfold_bind; cbn.
  setoid_rewrite bind_ret_l.
  constructor; auto.
Qed.

Lemma trans_trigger_inv : forall {E X Y} (e : E X) (k : X -> ctree E Y) l u,
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
      | obs _ _ = obs _ _ =>
          let EQe := fresh "EQe" in
          let EQv := fresh "EQv" in
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
      let EQl := fresh "EQl" in
      apply trans_brS_inv in h as (?n & ?EQ & EQl);
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
      apply trans_brD_inv in h as (?n & ?TR)

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

Ltac etrans := eauto with trans.
