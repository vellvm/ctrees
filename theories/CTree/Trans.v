(*|
==========================================
Transition relations over ctrees
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

From Coq Require Import
  Basics
  Datatypes
  Fin.

From Coinduction Require Import
     coinduction rel tactics.

From CTree Require Import
  CTree.Core
  CTree.Equ.

Import Ctree.
Import CTreeNotations.
Local Open Scope ctree_scope.

Generalizable All Variables.
Set Implicit Arguments.
Set Primitive Projections.

Section Trans.
  Context {E : Type} `{HE: Encode E} {X : Type}.

(*|
The domain of labels of the LTS.
Note that it could be typed more strongly: [val] labels can only
be of type [R]. However typing it statically makes lemmas about
[bind] particularly awkward to state, so this seems to be the
least annoying solution.
|*)
  Variant label : Type :=
    | tau
    | obs (e : E) (v : encode e)
    | val {X : Type} (v : X).

(*|
The transition relation over [ctree]s.
It can either:
- recursively crawl through invisible [br] node;
- stop at a successor of a visible [br] node, labelling the transition [tau];
- stop at a successor of a [Vis] node, labelling the transition by the event and branch taken;
- stop at a sink (implemented as a [spin] node that has no successor.
|*)
  Inductive trans_ : label -> relation (ctree' E X) :=

  | Stepguard l t u:
    trans_ l (observe t) u ->
    trans_ l (GuardF t) u

  | Steptau {n} (x : fin' n) k t :
    k x ≅ t ->
    trans_ tau (BrF n k) (observe t)

  | Stepobs (e : E) k (x: encode e) t :
    k x ≅ t ->
    trans_ (obs x) (VisF e k) (observe t)

  | Stepval t r :
    stuck ≅ t ->
    trans_ (val r) (RetF r) (observe t).
  Hint Constructors trans_ : core.

  Definition trans l : relation (ctree E X) :=
    fun u v => trans_ l (observe u) (observe v).

  #[local] Instance trans_equ_aux1 l t :
    Proper (going (equ eq) ==> flip impl) (trans_ l t).
  Proof.
    intros u u' equ; intros TR.
    inv equ; rename H into equ.
    step in equ.
    revert u equ.
    dependent induction TR; intros.
    + econstructor.
      now apply IHTR.
    + inv equ; cbn in H1; rewrite <- H1.
      * rewrite H0; now apply Steptau with x. 
      * change (VisF e k1) with (observe (Vis e k1)).
        apply (Steptau x).
        rewrite H.
        rewrite (ctree_eta t); rewrite <- H0. 
        step; constructor; intros; symmetry; auto.
      * change (BrF n k) with (observe (Br n k)).
        change (GuardF t1) with (observe (Guard t1)).
        apply (Steptau x).
        rewrite H.
        rewrite (ctree_eta t), <- H0.
        step; constructor; intros; symmetry; auto.
      * change (BrF n k) with (observe (Br n k)).
        change (BrF n0 k1) with (observe (Br n0 k1)).
        apply (Steptau x). 
        rewrite H.
        rewrite (ctree_eta t), <- H0.
        step; constructor; intros; symmetry; auto.
    + change u with (observe (go u)).
      econstructor.
      rewrite H; symmetry; step; auto.
    + change u with (observe (go u)).
      cbn in equ.
      econstructor.
      rewrite H.
      symmetry.
      step; cbn; apply equ.
  Qed.

  #[local] Instance trans_equ_aux2 l :
    Proper (going (equ eq) ==> going (equ eq) ==> impl) (trans_ l).
  Proof.
    intros t t' eqt u u' equ TR.
    rewrite <- equ; clear u' equ.
    inv eqt; rename H into eqt.
    revert t' eqt.
    dependent induction TR; intros; auto.
    + step in eqt; cbn in eqt; dependent induction eqt.
      apply Stepguard.
      apply IHTR.
      rewrite H; reflexivity.
    + step in eqt; cbn in eqt; dependent induction eqt.
      apply Steptau with x.
      now rewrite <- H0.
    + step in eqt; cbn in eqt; dependent induction eqt.
      econstructor.
      rewrite <- H.
      now symmetry.
    + step in eqt; cbn in eqt; dependent induction eqt.
      now econstructor.
  Qed.

  #[global] Instance trans_equ_ l :
    Proper (going (equ eq) ==> going (equ eq) ==> iff) (trans_ l).
  Proof.
    intros ? ? eqt ? ? equ; split; intros TR.
    - eapply trans_equ_aux2; eauto.
    - symmetry in equ; symmetry in eqt; eapply trans_equ_aux2; eauto.
  Qed.

  #[global] Instance trans_equ l :
    Proper (equ eq ==> equ eq ==> iff) (trans l).
  Proof.
    intros ? ? eqt ? ? equ; unfold trans.
    rewrite eqt, equ; reflexivity.
  Qed.

End Trans.

Ltac ind_trans H :=
  unfold trans, trans in H; cbn in H;
  dependent induction H.

Section Trans.
  Context {E : Type} `{HE: Encode E} {X : Type}. 

  (*| Backward reasoning for [trans] |*)
  Lemma trans_ret : forall (x : X),
      trans (val x) (Ret x) stuck.
  Proof. intros; now constructor. Qed.

  Lemma trans_vis : forall (e : E) (x: encode e) (k : encode e -> ctree E X),
      trans (obs e x) (Vis e k) (k x).
  Proof. intros; now constructor. Qed.

  Lemma trans_guard : forall l (t u: ctree E X),
      trans l t u ->
      trans l (Guard t) u.
  Proof.
    intros * TR.
    apply Stepguard.
    apply TR.
  Qed.

  Lemma trans_br : forall n (k : _ -> ctree E X) t x,
      k x ≅ t ->
      trans tau (Br n k) t.
  Proof.
    intros.
    apply Steptau with x; apply H. 
  Qed.

  Lemma trans_step : forall (t: ctree E X),
      trans tau (step t) t.
  Proof.
    intros.
    apply Steptau; [exact Fin.F1 | reflexivity].
  Qed.

  Lemma trans_br2_l : forall (t u: ctree E X),
      trans tau (br2 t u) t.
  Proof.
    intros.
    unfold br2.
    apply trans_br with Fin.F1.
    reflexivity.
  Qed.

  Lemma trans_br2_r: forall (t u: ctree E X),
      trans tau (br2 t u) u.
  Proof.
    intros.
    unfold br2.
    eapply trans_br with (Fin.FS Fin.F1).
    reflexivity.
  Qed.

  (*| Forward reasoning for [trans] |*)
  Lemma trans_ret_inv : forall x l (t : ctree E X),
      trans l (Ret x) t ->
       t ≅ stuck /\ l = val x.
  Proof.
    intros * TR; inv TR; intuition.
    observe_equ H1.
    symmetry.
    now rewrite <- Eqt.
  Qed.

  Lemma trans_vis_inv : forall (e : E) (k: encode e -> _) l (u : ctree E X),
      trans l (Vis e k) u ->
      exists x, u ≅ k x /\ l = obs e x.
  Proof.
    intros * TR.
    ind_trans TR.
    observe_equ x.
    exists x0; split.
    - rewrite H; now symmetry.
    - reflexivity.
  Qed.

  Lemma trans_guard_inv : forall l (t u : ctree E X),
      trans l (Guard t) u ->
      trans l t u.
  Proof.
    intros * TR.
    unfold trans in *.
    cbn in TR |- *.
    match goal with
    | h: trans_ _ ?x ?y |- _ =>
        remember x as ox; remember y as oy
    end.
    clear Heqoy u.
    induction TR; intros; dependent destruction Heqox;
      eauto.
  Qed.

  Lemma trans_br_inv : forall n k l (t' : ctree E X),
      trans l (Br n k) t' ->
      exists x, t' ≅ k x /\ l = tau.
  Proof.
    intros * TR.
    cbn in *; red in TR; cbn in TR.
    dependent induction TR.
    eexists; split; auto.
    rewrite H, ctree_eta, (ctree_eta t), x; reflexivity.
  Qed.

  Lemma trans_step_inv: forall l (t t': ctree E X),
      trans l (step t) t' ->
      t' ≅ t /\ l = tau.
  Proof.
    intros * TR; apply trans_br_inv in TR as (_ & ? & ?); auto.
  Qed.

  Lemma trans_br2_inv : forall l (t t' u : ctree E X),
      trans l (br2 t u) t' ->
      (l = tau /\ (t' ≅ t \/ t' ≅ u)).
  Proof.
    intros * TR; apply trans_br_inv in TR as (? & TR & ->); split; auto.
    destruct x; auto.
  Qed.

  Lemma trans_br3_inv : forall l (t t' u v: ctree E X),
      trans l (br3 t u v) t' ->
      (l = tau /\ (t' ≅ t \/ t' ≅ u \/ t' ≅ v)).
  Proof.
    intros * TR.
    apply trans_br_inv in TR as (? & TR & ->); split; [reflexivity|].
    dependent destruction x; [|dependent destruction x].
    - now left.
    - now right; left.
    - now right; right.
  Qed.
  
  (*| Inversion rules for [trans] based on the value of the label |*)
  Lemma trans__val_inv {Y} : 
    forall (T U : ctree' E X) (x : Y),
      trans_ (val x) T U ->
      stuck ≅ go U.
  Proof.
    intros * TR.
    remember (val x) as ox.
    rewrite ctree_eta; induction TR; intros; auto; try now inv Heqox.
    rewrite H.
    reflexivity.
  Qed.

  Lemma trans_val_inv {Y} :
    forall (t u : ctree E X) (x : Y),
      trans (val x) t u ->
      stuck ≅ u.
  Proof.
    intros * TR. cbn in TR. red in TR.
    apply trans__val_inv in TR. rewrite ctree_eta.
    rewrite (ctree_eta u), TR.
    reflexivity.
  Qed.

  Lemma trans_stuck: forall l (t: ctree E X),
      ~ trans l stuck t.
  Proof.
    intros * Hcontra.
    unfold trans in Hcontra.
    dependent induction Hcontra.
    eapply IHHcontra; reflexivity.
  Qed.
  Hint Resolve trans_stuck: trans.

End Trans.

Arguments label E {_}.

(*| Forward and backward rules for [trans] w.r.t. [bind] |*)
Variant is_val `{Encode E}: label E -> Prop :=
  | Is_val : forall X (x : X), is_val (val x).

Lemma trans_bind_inv_aux {X Y} `{HE: Encode E} (l: label E)  T U :
  trans_ l T U ->
  forall (t : ctree E X) (k : X -> ctree E Y) (u : ctree E Y),
    go T ≅ t >>= k ->
    go U ≅ u ->
    (~ (is_val l) /\ exists t', trans l t t' /\ u ≅ t' >>= k) \/
      (exists (x : X), trans (val x) t stuck /\ trans l (k x) u).
Proof.
  intros TR; induction TR; intros.
  - rewrite unfold_bind in H; setoid_rewrite (ctree_eta t0).
    desobs t0.
    + right.
      exists x; split.
      constructor.
      reflexivity.
      rewrite <- H.
      apply Stepguard; auto.
      rewrite <- H0; auto.
    + step in H; cbn in H; inversion H.
    + step in H; cbn in H; dependent destruction H.
      specialize (IHTR t1 k u0).
      destruct IHTR as [(? & ? & ? & ?) | (? & ? & ?)]; auto.
      rewrite <- ctree_eta, H; reflexivity.
      left; split; eauto.
      exists x; split; auto.
      apply Stepguard; auto.
      right.
      exists x; split; auto.
      apply Stepguard; auto.
    + step in H; inversion H.
  - rewrite unfold_bind in H0; setoid_rewrite (ctree_eta t0).
    desobs t0.
    + right.
      exists x0; split.
      constructor.
      reflexivity.
      rewrite <- H0.
      apply (Steptau x); auto.
      rewrite H, <- H1, ctree_eta; auto.
    + step in H0; cbn in H0; dependent induction H0.
      left; split; [intros abs; inv abs |].
      exists (k1 x); split.
      econstructor; reflexivity.
      rewrite <- H1, <- ctree_eta, <- H.
      apply H0.
    + step in H0; inversion H0.
    + step in H0; inversion H0.
  - rewrite unfold_bind in H0; setoid_rewrite (ctree_eta t0).
    desobs t0.
    + right.
      exists x0; split.
      constructor.
      reflexivity.
      rewrite <- H0.
      constructor.
      rewrite H, <- H1, ctree_eta; auto.
    + step in H0; inversion H0.
    + step in H0; cbn in H0; inversion H0. 
    + step in H0; cbn in H0; dependent destruction H0.
      left; split; [intros abs; inv abs |].
      exists (k1 x); split.
      econstructor; reflexivity.
      rewrite <- H1, <- ctree_eta, <- H.
      apply H0.
  - rewrite unfold_bind in H0.
    setoid_rewrite (ctree_eta t0).
    desobs t0.
    + right.
      exists x; split.
      constructor.
      reflexivity.
      rewrite <- H1, <- H0, <- ctree_eta.
      now constructor.
    + step in H0; inversion H0.
    + step in H0; inversion H0.
    + step in H0; inversion H0.
Qed.

Lemma trans_bind_inv {X Y} `{HE: Encode E} (t : ctree E X)
  (k : X -> ctree E Y) (u : ctree E Y) (l: label E) :
  trans l (t >>= k) u ->
  (~ (is_val l) /\ exists t', trans l t t' /\ u ≅ t' >>= k) \/
    (exists (x : X), trans (val x) t stuck /\ trans l (k x) u).
Proof.
  intros TR.
  eapply trans_bind_inv_aux.
  apply TR.
  rewrite <- ctree_eta; reflexivity.
  rewrite <- ctree_eta; reflexivity.
Qed.

Lemma trans_bind_inv_l {X Y} `{Encode E} (t : ctree E X)
  (k : X -> ctree E Y) (u : ctree E Y) l :
  trans l (t >>= k) u ->
  exists l' t', trans l' t t'.
Proof.
  intros TR.
  apply trans_bind_inv in TR.
  destruct TR as [(? & ? & ? & ?) | (? & ? & ?)]; eauto.
Qed.

(* Why this is needed? *)
Local Typeclasses Transparent equ.
Lemma trans_bind_l {X Y} `{HE: Encode E} (t : ctree E X)
  (k : X -> ctree E Y) (u : ctree E X) (l: label E) :
  ~ (is_val l) ->
  trans l t u ->
  trans l (t >>= k) (u >>= k).
Proof.
  cbn; unfold trans; intros NOV TR.
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

Lemma trans_bind_r {X Y} `{HE: Encode E} (t : ctree E X)
  (k : X -> ctree E Y) (u : ctree E Y) x l :
  trans (val x) t stuck ->
  trans l (k x) u ->
  trans l (t >>= k) u.
Proof.
  cbn; unfold trans; intros TR1.
  remember (observe stuck) as oc.
  remember (val x) as v.
  remember (observe t) as T.
  generalize dependent t.
  revert Heqv.
  revert x Heqoc l u k.
  induction TR1; intros; try (inv Heqv; fail).
  - rewrite (ctree_eta t0), <- HeqT; cbn; econstructor.
    eapply IHTR1; eauto.
  - dependent induction Heqv.
    rewrite (ctree_eta t0), <- HeqT, unfold_bind; cbn; auto.
Qed.

Lemma trans_val_invT {R R'} `{HE: Encode E}:
  forall (t u : ctree E R) (v : R'),
    trans (val v) t u ->
    R = R'.
Proof.
  intros * TR.
  remember (val v) as ov.
  induction TR; intros; auto; try now inv Heqov.
Qed.

Lemma trans_trigger : forall {Y} `{HE: Encode E} (e : E) x (k: encode e -> ctree E Y),
    trans (obs e x) (trigger e >>= k) (k x).
Proof.
  intros.
  unfold Ctree.trigger.
  rewrite unfold_bind; cbn.
  setoid_rewrite bind_ret_l.
  constructor; auto.
Qed.

Lemma trans_trigger_inv : forall {Y} `{HE: Encode E} (e : E)
                            (k : encode e -> ctree E Y) l u,
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

(*| [wf_val] states that a [label] is well-formed:
  if it is a [val] it should be of the right type. |*)
Definition wf_val `{Encode E} X l :=
  forall Y (v : Y), l = @val E _ Y v -> X = Y.

Lemma wf_val_val `{Encode E} X (v : X):
  wf_val X (@val E _ X v).
Proof.
  red. intros.
  dependent destruction H0.
  reflexivity.
Qed.

Lemma wf_val_nonval `{Encode E} X (l : label E):
  ~is_val l -> wf_val X l.
Proof.
  red. intros. subst. exfalso. apply H0. constructor.
Qed.

Lemma wf_val_trans `{Encode E} {X} (l: label E)
  (t t': ctree E X) :
  trans l t t' -> wf_val X l.
Proof.
  red. intros. subst.
  now apply trans_val_invT in H0.
Qed.

#[global] Hint Resolve
 trans_ret trans_vis trans_br trans_guard
 trans_br2_l trans_br2_r
 trans_step trans_trigger trans_bind_l trans_bind_r: trans.

#[global] Hint Constructors is_val : trans.
#[global] Hint Resolve
  wf_val_val wf_val_nonval wf_val_trans : trans.

Ltac etrans := eauto with trans.

Tactic Notation "trans" "in" ident(TR) :=
  match type of TR with
  | trans ?x (Ret ?r) ?u =>
      let x' := fresh "x" in
      let Eql := fresh "Eql" in
      apply trans_ret_inv in TR as (x' & Eql); rewrite ?Eql in *
  | trans (val ?x) ?t ?u =>
      let Eqt := fresh "Eqt" in
      rewrite ?(trans_val_invT TR) in *;
      apply trans_val_inv in TR as Eqt
  | trans ?l (Guard ?t) ?u =>
      apply trans_guard_inv in TR
  | trans ?l (step ?t) ?u =>
      let Eqt := fresh "Eqt" in
      let Eql := fresh "Eql" in
      apply trans_step_inv in TR as (Eqt & Eql); rewrite ?Eql in *
  | trans ?l (br2 ?t ?u) ?v =>
      let Eqt := fresh "Eqt" in
      let Eql := fresh "Eql" in
      apply trans_br2_inv in TR as (Eql & [Eqt | Eqt]); rewrite ?Eql in *
  | trans ?l (br3 ?t ?u ?v) ?t' =>
      let Eqt := fresh "Eqt" in
      let Eql := fresh "Eql" in
      apply trans_br3_inv in TR as (Eql & [Eqt | [ Eqt | Equt ]]);
      rewrite ?Eql in *
  | trans ?l (Vis ?e ?k) ?u =>
      let x := fresh "x" in
      let Eqt := fresh "Eqt" in
      let Eql := fresh "Eql" in
      apply trans_vis_inv in TR as (x & Eqt & Eql); rewrite ?Eql in *
  | trans ?l (x <- trigger ?e ;; ?k ?x) ?u =>
      let x := fresh "x" in
      let Eql := fresh "Eql" in
      let Eqt := fresh "Eqt" in
      apply trans_trigger_inv in TR as (x & Eqt & Eql); rewrite ?Eql in *
  | trans ?l (Br ?n ?k) ?t =>
      let n := fresh "n" in
      let Eqt := fresh "Eqt" in
      let Eql := fresh "Eql" in
      apply trans_br_inv in TR as (n & Eqt & Eql); rewrite ?Eql in *
  end.
