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

  Variant S := | Active (t : ctree E B R) | Passive {X} (e : E X) (k : X -> ctree E B R).
  (* Notation S' := (ctree' E B R). *)
  (* Notation S  := (ctree  E B R). *)
  Variant Seq : S -> S -> Prop :=
    | ActAct t u (EQ: equ eq t u) : Seq (Active t) (Active u)
    | PasPas {X} e (k g : X -> _) (EQ: pointwise_relation _ (equ eq) k g) : Seq (Passive e k) (Passive e g)
  .
  Hint Constructors Seq : core.
  #[global] Instance Seq_equiv : Equivalence Seq.
  Proof.
    constructor.
    - intros []; auto.
    - intros ? ? []; constructor; intros; now symmetry.
    - intros ? ? ? EQ1 EQ2.
      inv EQ1.
      inv EQ2; constructor; intros; etransitivity; eauto.
      dependent induction EQ2; constructor; intros; etransitivity; eauto.
  Qed.
  
  Definition SS : EqType :=
    {| type_of := S ; Eq := Seq |}.

(*|
The domain of labels of the LTS.
Note that it could be typed more strongly: [val] labels can only
be of type [R]. However typing it statically makes lemmas about
[bind] particularly awkward to state, so this seems to be the
least annoying solution.
|*)
  Variant label : Type :=
    | τ
    | ask {X : Type} (e : E X)
    | rcv {X : Type} (e : E X) (v : X) (* Note: I think we need to remember which request led to the response for the bisimilarity to be right, but I am not 100% sure, [e] might be spurious *)
    | val {X : Type} (v : X).

  Variant is_val : label -> Prop :=
    | Is_val : forall X (x : X), is_val (val x).

  Lemma is_val_τ : ~ is_val τ.
  Proof.
    intro H. inversion H.
  Qed.

  Lemma is_val_ask {X} (e : E X) : ~ is_val (ask e).
  Proof.
    intro H. inversion H.
  Qed.

  Lemma is_val_rcv {X} (e : E X) (x : X) : ~ is_val (rcv e x).
  Proof.
    intro H. inversion H.
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
  Inductive transR : label -> hrel S S :=

  | Transbr {X} (c : B X) x k l t t' u :
    t  ≅ Br c k ->
    t' ≅ k x ->
    transR l (Active t') u ->
    transR l (Active t) u

  | Transguard t t' u l :
    t ≅ Guard t' ->
    transR l (Active t') u ->
    transR l (Active t) u

  | Transstep t t' u :
    t ≅ Step t' ->
    u ≅ t' ->
    transR τ (Active t) (Active u)

  | Transask {X} (e : E X) t k :
    t ≅ Vis e k ->
    transR (ask e) (Active t) (Passive e k)

  | Transrcv {X} (e : E X) (x : X) k t :
    k x ≅ t ->
    transR (rcv e x) (Passive e k) (Active t)

  | Transval r t u :
    t ≅ Ret r ->
    u ≅ Stuck ->
    transR (val r) (Active t) (Active u).
  Hint Constructors transR : core.

  #[global] Instance equ_Seq_active : Proper (equ eq ==> Seq) Active.
  Proof.
    now intros ?? EQ; constructor.
  Qed.
  
  #[global] Instance equ_Seq_passive {X} (e : E X) : Proper (pointwise_relation X (equ eq) ==> Seq) (Passive e).
  Proof.
    now intros ?? EQ; constructor.
  Qed. 

  #[global] Instance transR_equ_ l :
    Proper (Seq ==> Seq ==> iff) (transR l).
  Proof.
    intros ?? EQ1 ?? EQ2; split; intros TR.
    - revert y y0 EQ1 EQ2; dependent induction TR; intros y y0 EQ1 EQ2.
      + inv EQ1.
        econstructor 1.
        rewrite <- EQ, H; reflexivity.
        apply H0.
        apply IHTR; auto.
      + inv EQ1.
        econstructor 2.
        rewrite <- EQ, H; reflexivity.
        apply IHTR; auto.
      + inv EQ1; inv EQ2.
        econstructor 3.
        rewrite <- EQ , H; reflexivity.
        rewrite <- EQ0, H0; reflexivity.
      + inv EQ1. dependent induction EQ2.
        econstructor 4.
        rewrite <- EQ0,H.
        step; constructor.
        apply EQ.
      + dependent induction EQ1; inv EQ2.
        econstructor 5.
        specialize (EQ x); rewrite <- EQ, H; auto.
      + inv EQ1; inv EQ2.
        econstructor 6.
        rewrite <- EQ, H; reflexivity.
        rewrite <- EQ0, H0; reflexivity.
    - revert x x0 EQ1 EQ2; dependent induction TR; intros y y0 EQ1 EQ2.
      + inv EQ1.
        econstructor 1.
        rewrite EQ, H; reflexivity.
        apply H0.
        apply IHTR; auto.
      + inv EQ1.
        econstructor 2.
        rewrite EQ, H; reflexivity.
        apply IHTR; auto.
      + inv EQ1; inv EQ2.
        econstructor 3.
        rewrite EQ , H; reflexivity.
        rewrite EQ0, H0; reflexivity.
      + inv EQ1. dependent induction EQ2.
        econstructor 4.
        rewrite EQ0,H.
        step; constructor.
        intros ?; symmetry; apply EQ.
      + dependent induction EQ1; inv EQ2.
        econstructor 5.
        specialize (EQ x); rewrite EQ, H, EQ0; auto.
      + inv EQ1; inv EQ2.
        econstructor 6.
        rewrite EQ, H; reflexivity.
        rewrite EQ0, H0; reflexivity.
  Qed.
        
(*|
[equ] is congruent for [transR], we can hence build a [srel] and build our
relations in this model to still exploit the automation from the [RelationAlgebra]
library.
|*)
  #[global] Instance transR_equ l :
    Proper (Seq ==> Seq ==> iff) (transR l).
  Proof.
    intros ? ? eqt ? ? equ.
    inv eqt; inv equ.
    all: now rewrite EQ, EQ0.
  Qed.

  Definition trans l : srel SS SS := {| hrel_of := transR l : hrel SS SS |}.

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

#[global] Infix "⩸" := Seq (at level 10).
#[global] Hint Constructors Seq : core.
#[global] Hint Constructors transR : core.

Ltac rem_weak_ t s :=
  let tmp := fresh in
  let name := fresh "EQ" in
  remember t as s eqn:tmp;
  assert (EQ: Seq s t) by (now subst);
  clear tmp.
  
Tactic Notation "rem_weak" constr(t) "as" ident(s) := rem_weak_ t s.

Class Respects_val {E F} (L : rel (@label E) (@label F)) :=
  { respects_val:
    forall l l',
      L l l' ->
      is_val l <-> is_val l' }.

Class Respects_τ {E F} (L : rel (@label E) (@label F)) :=
  { respects_τ: forall l l',
      L l l' ->
      l = τ <-> l' = τ }.

#[global] Instance Respects_val_eq A: @Respects_val A A eq.
split; intros; subst; reflexivity.
Defined.

#[global] Instance Respects_τ_eq A: @Respects_τ A A eq.
split; intros; subst; reflexivity.
Defined.

Coercion Active : ctree >-> S.
Notation "'α' t" := (Active t) (at level 100).
Notation "'β' e" := (Passive e) (at level 0).
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

We essentially lift the constructors to the [trans] bundling, and
eliminate on the way the noise from closing up everything to [equ eq].
|*)

  Lemma trans_ret : forall (x : X),
      trans (E := E) (B := B) (val x) (Ret x) Stuck.
  Proof.
    intros; constructor; auto.
  Qed.

  Lemma trans_ask : forall {Y} (e : E Y) (k : Y -> ctree E B X),
      trans (ask e) (Vis e k) (β e k).
  Proof.
    intros; constructor; auto.
  Qed.

  Lemma trans_rcv : forall {Y} (e : E Y) (k : Y -> ctree E B X) y,
      trans (rcv e y) (β e k) (k y).
  Proof.
    intros; constructor; auto.
  Qed.

  Lemma trans_br : forall {Y} l (c : B Y) (k : Y -> ctree E B X) u y,
      trans l (k y) u ->
      trans l (Br c k) u.
  Proof.
    intros * TR.
    eapply Transbr; [reflexivity| reflexivity |].
    apply TR.
  Qed.

  Lemma trans_step : forall (t : ctree E B X),
      trans τ (Step t) t.
  Proof.
    intros.
    eapply Transstep; reflexivity.
  Qed.

  Lemma trans_guard : forall l (t : ctree E B X) u,
      trans l t u ->
      trans l (Guard t) u.
  Proof.
    intros * TR.
    eapply Transguard; [reflexivity | auto].
  Qed.

  Lemma trans_brS : forall {Y} (c : B Y) (k : _ -> ctree E B X) x,
      trans τ (BrS c k) (k x).
  Proof.
    intros.
    apply trans_br with x, trans_step.
  Qed.

End backward.

#[global] Hint Resolve trans_br trans_guard trans_brS trans_step trans_ask trans_rcv trans_ret : core.

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
    apply trans_br with true, trans_step.
  Qed.

  Lemma trans_brS22 :
    trans τ (brS2 t u) u.
  Proof.
    intros.
    apply trans_br with false, trans_step.
  Qed.

  Lemma trans_br21 x :
    trans l t x ->
    trans l (br2 t u) x.
  Proof.
    intros * TR.
    now apply trans_br with true.
  Qed.

  Lemma trans_br22 x :
    trans l u x ->
    trans l (br2 t u) x.
  Proof.
    intros * TR.
    now apply trans_br with false.
  Qed.

  Lemma trans_brS31 :
    trans τ (brS3 t u v) t.
  Proof.
    now apply trans_br with t31.
  Qed.

  Lemma trans_brS32 :
    trans τ (brS3 t u v) u.
  Proof.
    now apply trans_br with t32.
  Qed.

  Lemma trans_brS33 :
    trans τ (brS3 t u v) v.
  Proof.
    now apply trans_br with t33.
  Qed.

  Lemma trans_br31 :
    trans l t t' ->
    trans l (br3 t u v) t'.
  Proof.
    intros * TR.
    now apply trans_br with t31.
  Qed.

  Lemma trans_br32 :
    trans l u u' ->
    trans l (br3 t u v) u'.
  Proof.
    intros * TR.
    now apply trans_br with t32.
  Qed.

  Lemma trans_br33 :
    trans l v v' ->
    trans l (br3 t u v) v'.
  Proof.
    intros * TR.
    now apply trans_br with t33.
  Qed.

  Lemma trans_brS41 :
    trans τ (brS4 t u v w) t.
  Proof.
    eapply trans_br with t41; eauto.
  Qed.

  Lemma trans_brS42 :
    trans τ (brS4 t u v w) u.
  Proof.
    eapply trans_br with t42; eauto.
  Qed.

  Lemma trans_brS43 :
    trans τ (brS4 t u v w) v.
  Proof.
    eapply trans_br with t43; eauto.
  Qed.

  Lemma trans_brS44 :
    trans τ (brS4 t u v w) w.
  Proof.
    eapply trans_br with t44; eauto.
  Qed.

  Lemma trans_br41 :
    trans l t t' ->
    trans l (br4 t u v w) t'.
  Proof.
    intros * TR.
    eapply trans_br with t41; eauto.
  Qed.

  Lemma trans_br42 :
    trans l u u' ->
    trans l (br4 t u v w) u'.
  Proof.
    intros * TR.
    eapply trans_br with t42; eauto.
  Qed.

  Lemma trans_br43 :
    trans l v v' ->
    trans l (br4 t u v w) v'.
  Proof.
    intros * TR.
    eapply trans_br with t43; eauto.
  Qed.

  Lemma trans_br44 :
    trans l w w' ->
    trans l (br4 t u v w) w'.
  Proof.
    intros * TR.
    eapply trans_br with t44; eauto.
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

(*|
Structural rules
|*)

  (* In the primed versions, [u] is left as an arbitrary S.
     In the main version, we can only invert if we already know
     that the resulting state is an active one.
     (it is of course always one)
   *) 
  Lemma trans_ret_inv' : forall x l u,
      trans l (Ret x : ctree E B X) u ->
      Seq u (α Stuck) /\ l = val x.
  Proof.
    intros * TR; inv TR; inv_equ.
    intuition.
  Qed.

  Lemma trans_ret_inv : forall x l (u : ctree E B X),
      trans l (Ret x) u ->
      u ≅ Stuck /\ l = val x.
  Proof.
    intros * TR; inv TR; inv_equ.
    intuition.
  Qed.

  Lemma trans_vis_inv' : forall {Y} (e : E Y) (k : _ -> ctree E B X) l u,
      trans l (Vis e k) u ->
      Seq u (β e k) /\ l = ask e.
  Proof.
    intros * TR.
    inv TR; inv_equ.
    split; auto.
    constructor; intros ?; symmetry; eauto.
  Qed.

  Lemma trans_vis_inv : forall {Y} (e : E Y) k l (u : ctree E B X),
      trans l (Vis e k) u ->
      Seq u (β e k) /\ l = ask e.
  Proof.
    intros * TR.
    inv TR; inv_equ.
  Qed.

  Lemma trans_passive_inv' : forall {Y} (e : E Y) (k : Y -> ctree E B X) l u,
      trans l (β e k) u ->
      exists x, Seq u (α k x) /\ l = rcv e x.
  Proof.
    intros * TR.
    cbn in TR; dependent induction TR.
    eexists; split; eauto.
    constructor; symmetry; eauto.
  Qed.

  Lemma trans_passive_inv : forall {Y} (e : E Y) (k : Y -> ctree E B X) l (u : ctree E B X),
      trans l (β e k) u ->
      exists x, u ≅ (k x) /\ l = rcv e x.
  Proof.
    intros * TR.
    apply trans_passive_inv' in TR as (? & ? & ?).
    inv H; eauto.
  Qed.

  Lemma trans_br_inv : forall {Y} l (c : B Y) (k : _ -> ctree E B X) u,
      trans l (Br c k) u ->
      exists n, trans l (k n) u.
  Proof.
    intros * TR.
    cbn in *.
    match goal with
    | h: transR _ ?x ?y |- _ =>
        remember x as ox; remember y as oy
    end.
    revert c k u Heqox Heqoy.
    inv TR; intros; subst; inv Heqox; inv_equ. 
    exists x; now rewrite H0, <- (EQ x) in H1.
  Qed.

  Lemma trans_guard_inv : forall l (t : ctree E B X) u,
      trans l (Guard t) u ->
      trans l t u.
  Proof.
    intros * TR.
    inv TR; inv_equ.
    now rewrite H0.
  Qed.

  Lemma trans_step_inv' : forall l (t : ctree E B X) u,
      trans l (Step t) u ->
      Seq u t /\ l = τ.
  Proof.
    intros * TR.
    inv TR; inv_equ; split; auto.
    now rewrite H0,H2.
  Qed.

  Lemma trans_step_inv : forall l (t u : ctree E B X),
      trans l (Step t) u ->
      u ≅ t /\ l = τ.
  Proof.
    intros * TR.
    apply trans_step_inv' in TR as [? ?]; split; auto.
    now inv H.
  Qed.

  Lemma trans_brS_inv' : forall {Y} l (c : B Y) (k : _ -> ctree E B X) u,
      trans l (BrS c k) u ->
      exists n, Seq u (α (k n)) /\ l = τ.
  Proof.
    intros * TR.
    eapply trans_br_inv in TR as [n ?].
    apply trans_step_inv' in H as [? ?].
    eauto.
  Qed.

  Lemma trans_brS_inv : forall {Y} l (c : B Y) k (u : ctree E B X),
      trans l (BrS c k) u ->
      exists n, u ≅ k n /\ l = τ.
  Proof.
    intros * TR.
    apply trans_brS_inv' in TR as (? & H & ?); inv H; eauto.
  Qed.

  Lemma trans_stuck_inv : forall l u,
      trans l (Stuck : ctree E B X) u ->
      False.
  Proof.
    intros * TR.
    cbn in TR; dependent induction TR; inv_equ.
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

  Lemma trans_val_inv' {Y} :
    forall t u (x : Y),
      trans (val x) t u ->
      Seq u (α (Stuck : ctree E B X)).
  Proof.
    intros * TR.
    remember (val x) as ox.
    revert x Heqox.
    cbn in TR; induction TR; intros ? Heqox; try now inv Heqox.
    all: eauto.
  Qed.

  Lemma trans_val_inv {Y} :
    forall (t u : ctree E B X) (x : Y),
      trans (val x) t u ->
      u ≅ Stuck.
  Proof.
    now intros * TR; apply trans_val_inv' in TR; inv TR.
  Qed.

  Lemma wtrans_val_inv : forall (x : X),
      wtrans (val x) u Stuck ->
      exists t, wtrans τ u t /\ trans (val x) t Stuck.
  Proof.
    intros * TR.
    destruct TR as [t2 [t1 step1 step2] step3].
    exists t1; split.
    apply wtrans_τ; auto.
    erewrite <- trans_val_inv'; eauto.
  Qed.

End forward.

(*|
[etrans] theory
---------------
|*)

Lemma etrans_case' {E B X} : forall l t u,
    etrans l t u ->
    (trans l t u \/ (l = τ /\ @Seq E B X t u)).
Proof.
  intros [] * TR; cbn in *; intuition.
Qed.

Lemma etrans_case {E B X} : forall l (t u : ctree E B X),
    etrans l t u ->
    (trans l t u \/ (l = τ /\ t ≅ u)).
Proof.
  intros [] * TR; cbn in *; intuition.
  inv H; intuition.
Qed.

Lemma etrans_ret_inv' {E B X} : forall x l t,
    etrans l (Ret x) t ->
    (l = τ /\ @Seq E B X t (α Ret x)) \/ (l = val x /\ Seq t (α Stuck)).
Proof.
  intros ? [] ? step; cbn in step.
  - intuition; try (eapply trans_ret in step; now apply step).
    apply trans_ret_inv' in H; intuition.
  - eapply trans_ret_inv' in step; intuition.
  - eapply trans_ret_inv' in step; intuition.
  - eapply trans_ret_inv' in step; intuition.
Qed.

Lemma etrans_ret_inv {E B X} : forall x l (t : ctree E B X),
    etrans l (Ret x) t ->
    (l = τ /\ t ≅ Ret x) \/ (l = val x /\ t ≅ Stuck).
Proof.
  intros ? [] ? step; cbn in step.
  - intuition; try (eapply trans_ret in step; now apply step).
    apply trans_ret_inv in H; intuition.
    inv H; intuition.
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

  Lemma etrans_is_stuck_inv' (v : ctree E B X) v' :
    is_stuck v ->
    etrans l v v' ->
    l = τ /\ Seq v v'.
  Proof.
    intros * ST TR.
    edestruct @etrans_case'; eauto.
    apply ST in H; tauto.
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

  Lemma transs_is_stuck_inv' (v : ctree E B X) v' :
    is_stuck v ->
    (trans τ)^* v v' ->
    Seq v v'.
  Proof.
    intros * ST TR.
    destruct TR as [[] TR].
    inv TR; eauto.
    destruct TR.
    apply ST in H; tauto.
  Qed.
  
  Lemma transs_is_stuck_inv (v v' : ctree E B X) :
    is_stuck v ->
    (trans τ)^* v v' ->
    v ≅ v'.
  Proof.
    intros * ST TR.
    eapply transs_is_stuck_inv' in TR; eauto.
    now inv TR.
  Qed.

  Lemma wtrans_is_stuck_inv :
    is_stuck t ->
    wtrans l t u ->
    (l = τ /\ t ≅ u).
  Proof.
    intros * ST TR.
    destruct TR as [? [? ?] ?].
    apply transs_is_stuck_inv' in H; auto.
    inv H.
    rewrite EQ in ST; apply etrans_is_stuck_inv' in H0 as [-> ?]; auto.
    inv H.
    rewrite EQ0 in ST; apply transs_is_stuck_inv in H1; auto.
    intuition.
    rewrite EQ, EQ0; auto.
  Qed.

  Lemma Stuck_is_stuck :
     is_stuck Stuck.
  Proof.
    repeat intro; eapply trans_stuck_inv; eauto.
  Qed.

  Lemma br_void_is_stuck (c : B void) (k : void -> _) :
    is_stuck (Br c k).
  Proof.
    red. intros * ?.
    apply trans_br_inv in H as [[] ?].
  Qed.

  Lemma br_fin0_is_stuck (c : B (fin 0)) (k : fin 0 -> _) :
    is_stuck (Br c k).
  Proof.
    red. intros * ?. 
    apply trans_br_inv in H as [? ?].
    now apply case0.
  Qed.

  Lemma spinD_gen_is_stuck {Y} (x : B Y) :
    is_stuck (spin_gen x).
  Proof.
    red; intros * abs.
    rem_weak (α (@spin_gen E B X _ x)) as v.
    revert EQ.
    cbn in abs; induction abs.
    3-6: intros EQ; inv EQ; rewrite EQ0 in H; step in H; inv H.
    - intros EQ; inv EQ.
      apply IHabs; constructor.
      rewrite H0.
      rewrite EQ0 in H; step in H; dependent induction H.
      symmetry; apply REL.
    - intros EQ; inv EQ.
      apply IHabs; constructor.
      rewrite EQ0 in H; step in H; dependent induction H.
  Qed.

  Lemma spin_is_stuck :
    is_stuck spin.
  Proof.
    red; intros * abs.
    rem_weak (α @spin E B X) as v; revert EQ.
    cbn in abs; induction abs.
    3-6: intros EQ; inv EQ; rewrite EQ0 in H; step in H; inv H.
    - intros EQ; inv EQ.
      apply IHabs; constructor.
      rewrite H0.
      rewrite EQ0 in H; step in H; dependent induction H.
    - intros EQ; inv EQ.
      apply IHabs; constructor.
      rewrite EQ0 in H; step in H; dependent induction H.
      now rewrite <- REL.
  Qed.

  Lemma spinS_is_not_stuck :
    ~ (is_stuck spinS).
  Proof.
    red; intros * abs.
    apply (abs τ spinS).
    rewrite ctree_eta at 1; cbn.
    apply trans_step.
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
  Qed.

  Lemma trans_τ_str_ret_inv' : forall x t,
      (trans τ)^* (Ret x) t ->
      @Seq E B X t (α Ret x).
  Proof.
    intros * [[|] step].
    - cbn in *; now symmetry.
    - destruct step.
      apply trans_ret_inv' in H; intuition congruence.
  Qed.

  Lemma trans_τ_str_ret_inv : forall x (t : ctree E B X),
      (trans τ)^* (Ret x) t ->
      t ≅ Ret x.
  Proof.
    intros * [[|] step].
    - inv step; now symmetry.
    - destruct step.
      apply trans_ret_inv' in H; intuition congruence.
  Qed.

  Lemma wtrans_ret_inv : forall x l (t : ctree E B X),
      wtrans l (Ret x) t ->
      (l = τ /\ t ≅ Ret x) \/ (l = val x /\ t ≅ Stuck).
  Proof.
    intros * step.
    destruct step as [? [? step1 step2] step3].
    apply trans_τ_str_ret_inv' in step1.
    rewrite step1 in step2; clear step1.
    apply etrans_ret_inv' in step2 as [[-> EQ] |[-> EQ]].
    rewrite EQ in step3; apply trans_τ_str_ret_inv in step3; auto.
    rewrite EQ in step3.
    apply transs_is_stuck_inv in step3; [| apply Stuck_is_stuck].
    intuition.
  Qed.

  Lemma wtrans_val_inv' : forall (x : X) t u,
      wtrans (val x) t u ->
      exists t', @wtrans E B X τ t t' /\ @trans E B X (val x) t' u /\ Seq u Stuck.
  Proof.
    intros * TR.
    destruct TR as [t2 [t1 step1 step2] step3].
    exists t1; split.
    apply wtrans_τ; auto.
    clear step1.
    pose proof trans_val_inv' step2.
    rewrite H in step3.
    apply transs_is_stuck_inv' in step3; auto using Stuck_is_stuck.
    split; [| rewrite <- step3; auto].
    rewrite H in step2. rewrite <- step3.
    auto.
  Qed.

End wtrans.

(*|
Forward and backward rules for [trans] w.r.t. [bind]
----------------------------------------------------
trans l (t >>= k) u -> (trans l t t' /\ u ≅ t' >>= k) \/ (trans (ret x) t stuck /\ trans l (k x) u)
l <> val x -> trans l t u -> trans l (t >>= k) (u >>= k)
trans (val x) t stuck -> trans l (k x) u -> trans l (bind t k) u.
|*)

Lemma trans_bind_inv {E B X Y}
  (t : ctree E B X) (k : X -> ctree E B Y) u l :
  trans l (t >>= k) u ->
  (l = τ /\ exists t', trans l t (α t') /\ Seq u (α t' >>= k)) \/
  (exists Z (e : E Z), l = ask e /\
   exists (g : Z -> ctree E B X), trans l t (β e g) /\ Seq u (β e (fun x => g x >>= k))) \/
  (exists (x : X), trans (val x) t Stuck /\ trans l (k x) u).
Proof.
  intros TR.
  rem_weak (α x <- t ;; k x) as ob.
  revert t EQ.
  induction TR.
  - intros ? EQ.
    inv EQ.
    rewrite EQ0 in H.
    apply br_equ_bind in H as [(r & EQ1 & EQ2) | (v & EQ1 & EQ2)].
    + right; right.
      exists r; split.
      rewrite EQ1; auto.
      rewrite EQ2.
      apply trans_br with x.
      rewrite <- H0; auto.
    + edestruct IHTR as [H | [H | H]]; [rewrite H0, EQ2; reflexivity |..]; clear IHTR.
      * destruct H as (-> & u' & EQ1' & EQ2').
        left. split; auto.
        eexists; split; [| eassumption]; rewrite EQ1; eauto.
      * destruct H as (Z & e & -> & g & TR' & EQ).
        right; left.
        exists Z,e; split; auto; exists g; split; auto.
        rewrite EQ1; eauto.
      * destruct H as (y & TR' & TR'').
        right; right.
        exists y; split; auto.
        rewrite EQ1; eauto.
 
  - intros ? EQ.
    inv EQ.
    rewrite EQ0 in H.
    apply guard_equ_bind in H as [(r & EQ1 & EQ2) | (v & EQ1 & EQ2)].
    + right; right.
      exists r; split.
      rewrite EQ1; auto.
      rewrite EQ2; auto.
    + edestruct IHTR as [H | [H | H]]; [rewrite <- EQ2; reflexivity | ..]; clear IHTR.
      * destruct H as (-> & u' & EQ1' & EQ2').
        left. split; auto.
        eexists; split; [| eassumption]; rewrite EQ1; auto.
      * destruct H as (Z & e & -> & g & TR' & EQ).
        right; left.
        exists Z,e; split; auto; exists g; split; auto.
        rewrite EQ1; auto.
      * destruct H as (x & TR' & TR'').
        right; right.
        exists x; split; auto.
        rewrite EQ1; auto.
        
  - intros ? EQ.
    inv EQ.
    rewrite EQ0 in H.
    apply step_equ_bind in H as [(r & EQ1 & EQ2) | (v & EQ1 & EQ2)].
    + right; right.
      exists r; split.
      rewrite EQ1; auto.
      rewrite EQ2, H0; auto.
    + left.
      split; auto.
      exists v; split.
      rewrite EQ1; auto.
      rewrite H0, <- EQ2; auto.
      
  - intros ? EQ.
    inv EQ.
    rewrite EQ0 in H.
    apply vis_equ_bind in H as [(r & EQ1 & EQ2) | (v & EQ1 & EQ2)].
    + right; right.
      exists r; split.
      rewrite EQ1; auto.
      rewrite EQ2; auto.
    + right; left.
      exists X0, e; split; auto.
      exists v; split.
      rewrite EQ1; auto.
      constructor.
      intros ?.
      rewrite EQ2; auto.
       
  - intros ? EQ.
    inv EQ.
       
  - intros ? EQ.
    inv EQ.
    rewrite EQ0 in H.
    apply ret_equ_bind in H as (r' & EQ1 & EQ2).
    right; right.
    exists r'; split.
    rewrite EQ1; auto.
    rewrite EQ2, H0; auto.
Qed.
  
Lemma trans_bind_inv_l {E B X Y} (t : ctree E B X) (k : X -> ctree E B Y) (u : ctree E B Y) l :
  trans l (t >>= k) u ->
  exists l' t', trans l' t t'.
Proof.
  intros TR.
  apply trans_bind_inv in TR.
  destruct TR as [(? & ? & ? & ?) | [(? & ? & ? & ? & ? & ?) | (? & ? & ?)]]; eauto.
Qed.

Lemma trans_bind_l_τ {E B X Y} (t : ctree E B X) (k : X -> ctree E B Y) (u : ctree E B X) :
  trans τ t u ->
  trans τ (t >>= k) (u >>= k).
Proof.
  cbn; intros TR.
  dependent induction TR; cbn in *.
  - rewrite H, bind_br.
    apply trans_br with x.
    specialize (IHTR t' k u eq_refl eq_refl eq_refl).
    now rewrite H0 in IHTR.
  - rewrite H, bind_guard.
    apply trans_guard.
    apply IHTR; auto.
  - rewrite H, bind_step.
    rewrite H0; apply trans_step.
Qed.

Lemma trans_bind_l_ask {E B X Y Z} (t : ctree E B X) (k : X -> ctree E B Y) (e : E Z) (g : Z -> ctree E B X) :
  trans (ask e) t (β e g) ->
  trans (ask e) (t >>= k) (β e (fun x => g x >>= k)).
Proof.
  cbn; intros TR.
  dependent induction TR; cbn in *.
  - rewrite H, bind_br.
    apply trans_br with x.
    specialize (IHTR Z t' k e g eq_refl eq_refl eq_refl).
    now rewrite H0 in IHTR.
  - rewrite H, bind_guard.
    apply trans_guard.
    apply IHTR; auto.
  - rewrite H, bind_vis.
    apply trans_ask.
Qed.

Lemma trans_bind_r {E B X Y} (t : ctree E B X) (k : X -> ctree E B Y) u x l :
  trans (val x) t Stuck ->
  trans l (k x) u ->
  trans l (t >>= k) u.
Proof.
  cbn; intros TR1.
  dependent induction TR1; cbn in *.
  - intros TR2; rewrite H, bind_br.
    apply trans_br with x0.
    rewrite <- H0; eapply IHTR1; eauto.
  - intros TR2; rewrite H, bind_guard.
    apply trans_guard.
    eapply IHTR1; eauto.
  - intros TR2; rewrite H, bind_ret_l; auto.
Qed.

Lemma is_stuck_bind : forall {E B X Y} (t : ctree E B X) (k : X -> ctree E B Y),
    is_stuck t -> is_stuck (bind t k).
Proof.
  repeat intro.
  apply trans_bind_inv in H0 as [|[]].
  - destruct H0 as (? & ? & TR & ?).
    now apply H in TR.
  - destruct H0 as (? & ? & ? & ? & TR & ?).
    now apply H in TR.
  - destruct H0 as (? & TR & ?).
    now apply H in TR.
Qed.

(*|
Forward and backward rules for [wtrans] w.r.t. [bind]
-----------------------------------------------------
|*)

Lemma etrans_bind_inv {E B X Y} (t : ctree E B X) (k : X -> ctree E B Y) u l :
  etrans l (t >>= k) u ->
  (l = τ /\ exists t', etrans l t (α t') /\ Seq u (t' >>= k)) \/
  (exists Z (e : E Z), l = ask e /\
   exists (g : Z -> ctree E B X), trans l t (β e g) /\ Seq u (β e (fun x => g x >>= k))) \/
  (exists (x : X), trans (val x) t Stuck /\ etrans l (k x) u).
Proof.
  intros TR.
  apply @etrans_case' in TR as [ | (-> & ?)].
  - apply trans_bind_inv in H as [[? (? & ? & ?)]|[( ? & ? & ? & ? & ? & ?)|( ? & ? & ?)]]; eauto.
    + subst; left; split; eauto using is_val_τ.
      eexists; split; eauto; apply trans_etrans; auto.
    + subst; right; left.
      eexists; eexists; split; eauto.
    + right; right; eexists; split; eauto. now apply trans_etrans.
  - inv H; left; split; auto.
    exists t; split; auto using enil; symmetry; auto.
Qed.

Lemma transs_bind_inv {E B X Y} (t : ctree E B X) (k : X -> ctree E B Y) u :
  (trans τ)^* (t >>= k) u ->
  (exists t', (trans τ)^* t (α t') /\ Seq u (t' >>= k)) \/
  (exists (x : X), wtrans (val x) t Stuck /\ (trans τ)^* (k x) u).
Proof.
  intros [n TR].
  revert t k u TR.
  induction n as [| n IH]; intros; subst.
  - cbn in TR.
    left; exists t; split.
    exists 0%nat; reflexivity.
    symmetry; auto.
  - destruct TR as [t1 TR1 TR2].
    apply trans_bind_inv in TR1 as [(_ & t2 & TR1 & EQ) | [(x & TR1 & abs & ?) | (x & TR1 & TR1')]].
    + rewrite EQ in TR2; clear t1 EQ.
      apply IH in TR2 as [(t3 & TR2 & EQ')| (x & TR2 & TR3)].
      * left; eexists; split; eauto.
        apply wtrans_τ; eapply wcons; eauto.
        apply wtrans_τ; auto.
      * right; exists x; split; eauto.
        eapply wcons; eauto.
    + inv abs.
    + right.
      exists x; split.
      apply trans_wtrans; auto.
      exists (Datatypes.S n), t1; auto.
Qed.

Lemma passive_τ_trans {E B X Y} e (g : X -> ctree E B Y) u :
  trans τ (β e g) u ->
  False.
Proof.
  intros TR; cbn in TR; dependent induction TR.
Qed.

Lemma passive_τ_etrans {E B X Y} e (g : X -> ctree E B Y) u :
  etrans τ (β e g) u ->
  Seq u (β e g).
Proof.
  intros [TR | EQ].
  - cbn in TR; dependent induction TR.
  - symmetry; apply EQ.
Qed.

Lemma passive_τ_wtrans {E B X Y} e (g : X -> ctree E B Y) u :
  wtrans τ (β e g) u ->
  Seq u (β e g).
Proof.
  intros [? [? [n TR1] TR2] [m TR3]].
  destruct n.
  - cbn in TR1. rewrite <- TR1 in TR2.
    apply passive_τ_etrans in TR2.
    destruct m.
    * cbn in TR3.
      now rewrite <- TR3, TR2.
    * destruct TR3 as [? TR _].
      rewrite TR2 in TR.
      exfalso; eapply passive_τ_trans; eauto.
  - destruct TR1 as [? TR _].
    exfalso; eapply passive_τ_trans; eauto.
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
Lemma wtrans_bind_inv {E B X Y} (t : ctree E B X) (k : X -> ctree E B Y) u l :
  wtrans l (t >>= k) u ->
  (l = τ /\ exists t', wtrans l t (α t') /\ Seq u (t' >>= k)) \/
  (exists Y (e : E Y), l = ask e /\ exists g, wtrans l t (β e g) /\ Seq u (β e (fun x => g x >>= k))) \/
  (exists (x : X), wtrans (val x) t Stuck /\ wtrans l (k x) u) \/
  (exists (x : X) s, wtrans l t s /\ trans (val x) s Stuck /\ wtrans τ (k x) u).
Proof.
  intros TR.
  destruct TR as [t2 [t1 step1 step2] step3].
  apply transs_bind_inv in step1 as [(u1 & TR1 & EQ1)| (x & TR1 & TR1')].
  - rewrite EQ1 in step2.
    apply etrans_bind_inv in step2 as [(H & u2 & TR2 & EQ2)| [(Z & e & EQ & g & TR2 & EQ2) | (x & TR2 & TR2')]].
    + rewrite EQ2 in step3.
      subst.
      apply transs_bind_inv in step3 as [(u3 & TR3 & EQ3)| (x & TR3 & TR3')].
      * left; split; auto.
        eexists; split. 2:apply EQ3.
        exists (α u2); [exists (α u1) |]; auto.
      * right; right; right.
        apply wtrans_val_inv in TR3 as (u3 & TR2' & TR2'').
        exists x, u3.
        split; [|split]; auto.
        2:apply wtrans_τ; auto.
        exists (α u2); [exists (α u1) |]; auto.
        apply wtrans_τ; apply wtrans_τ in TR1.
        eapply wconss; eauto.
    + destruct t2 as [? | h]; [inv EQ2 |].
      dependent induction EQ2.     
      assert (Seq u (β (e) k0)).
      { apply passive_τ_wtrans, wtrans_τ; auto. }
      right; left.
      exists Z, e; split; auto.
      eexists; split.
      2:rewrite H; constructor; intros x; rewrite (EQ x); reflexivity.
      exists (β (e) g); [exists (α u1) |]; auto.
      apply  wtrans_τ; apply wnil.
    + right; right; left.
      exists x; split.
      eexists; [eexists |]; eauto; apply wtrans_τ, wnil.
      eexists; [eexists |]; eauto; apply wtrans_τ, wnil.
  - right; right; left.
    exists x; split; eauto.
    eexists; [eexists |]; eauto.
Qed.

Lemma etrans_bind_l_τ {E B X Y} (t : ctree E B X) (k : X -> ctree E B Y) (u : ctree E B X) :
  etrans τ t u ->
  etrans τ (t >>= k) (u >>= k).
Proof.
  cbn.
  intros [|].
  left; apply trans_bind_l_τ; auto.
  inv H; rewrite EQ; auto.
Qed.

Lemma etrans_bind_l_ask {E B X Y Z} (t : ctree E B X) (k : X -> ctree E B Y) (e : E Z) (g : Z -> ctree E B X) :
  etrans (ask e) t (β e g) ->
  etrans (ask e) (t >>= k) (β e (fun x => g x >>= k)).
Proof.
  cbn; intros TR.
  apply trans_bind_l_ask; auto.
Qed.

Lemma trans_τ_active {E B X} (t : ctree E B X) u :
  trans τ (α t) u ->
  exists u', Seq u (α u').
Proof.
  intros TR; cbn in TR; dependent induction TR.
  - edestruct IHTR; auto.
    inv H1; eauto.
  - edestruct IHTR; eauto.
  - eauto.
Qed.
 
Lemma etrans_τ_active {E B X} (t : ctree E B X) u :
  etrans τ (α t) u ->
  exists u', Seq u (α u').
Proof.
  intros [TR | TR].
  - eapply trans_τ_active; eauto.
  - cbn in *; exists t; rewrite TR; auto.
Qed.

Lemma trans_ask_passive {E B X Y} (t : ctree E B X) (e : E Y) u :
  trans (ask e) (α t) u ->
  exists g, Seq u (β e g).
Proof.
  intros TR; cbn in TR; dependent induction TR.
  - edestruct IHTR; auto.
    dependent induction H1; eauto.
  - edestruct IHTR; eauto.
  - eauto.
Qed.
  
Lemma etrans_ask_active {E B X Y} (t : ctree E B X) (e : E Y) u :
  etrans (ask e) (α t) u ->
  exists g, Seq u (β e g).
Proof.
  intros TR; eapply trans_ask_passive; eauto.
Qed.

Lemma transs_τ_passive {E B X Y} e (g : X -> ctree E B Y) u :
  (trans τ)^* (β e g) u ->
  Seq u (β e g).
Proof.
  intros TR.
  eapply passive_τ_wtrans.
  now apply wtrans_τ.
Qed.

Lemma transs_τ_active {E B X} (t : ctree E B X) u :
  (trans τ)^* (α t) u ->
  exists u', Seq u (α u').
Proof.
  intros [n TR]. revert t TR.
  induction n as [| n IH]; intros t TR.
  - cbn in TR; exists t; symmetry; eauto.
  - destruct TR as [? TR TRs].
    eapply trans_τ_active in TR as [u' EQ].
    rewrite EQ in TRs.
    edestruct IH; eauto.
Qed.
 
Lemma wtrans_τ_active {E B X} (t : ctree E B X) u :
  wtrans τ (α t) u ->
  exists u', Seq u (α u').
Proof.
  intros TR; apply wtrans_τ in TR; eapply transs_τ_active; eauto.
Qed.
  
Lemma transs_bind_l {E B X Y} (t : ctree E B X) (k : X -> ctree E B Y) (u : ctree E B X) :
  (trans τ)^* t u ->
  (trans τ)^* (t >>= k) (u >>= k).
Proof.
  intros [n TR].
  revert t u TR.
  induction n as [| n IH].
  - cbn; intros; exists 0%nat; cbn; inv TR; rewrite EQ; auto.
  - intros t u [v TR1 TR2].
    pose proof trans_τ_active TR1 as (v' & EQv).
    rewrite EQv in TR1,TR2.
    apply IH in TR2.
    eapply wtrans_τ, wcons.
    2:apply wtrans_τ; eauto.
    apply trans_bind_l_τ; eauto.
Qed.

Lemma wtrans_bind_l_τ {E B X Y} (t : ctree E B X) (k : X -> ctree E B Y) (u : ctree E B X) :
  wtrans τ t u ->
  wtrans τ (t >>= k) (u >>= k).
Proof.
  intros [t2 [t1 TR1 TR2] TR3].
  pose proof transs_τ_active TR1 as (x & EQx).
  rewrite EQx in TR1,TR2.
  pose proof etrans_τ_active TR2 as (y & EQy).
  rewrite EQy in TR2,TR3.
  pose proof transs_τ_active TR3 as (z & EQz).
  eexists; [eexists |].
  apply transs_bind_l; eauto.
  apply etrans_bind_l_τ; eauto.
  apply transs_bind_l; eauto.
Qed.

Lemma wtrans_bind_l_ask {E B X Y Z} (t : ctree E B X) (k : X -> ctree E B Y) (e : E Z) (g : Z -> ctree E B X) :
  wtrans (ask e) t (β e g) ->
  wtrans (ask e) (t >>= k) (β e (fun x => g x >>= k)).
Proof.
  intros [t2 [t1 TR1 TR2] TR3].
  pose proof transs_τ_active TR1 as (x & EQx).
  rewrite EQx in TR1,TR2.
  pose proof etrans_ask_active TR2 as (y & EQy).
  rewrite EQy in TR2,TR3.
  pose proof transs_τ_passive TR3 as EQz.
  eexists; [eexists |].
  apply transs_bind_l; eauto.
  apply etrans_bind_l_ask; eauto.
  apply wtrans_τ.
  assert (Seq (β (e) (fun x0 : Z => x <- y x0;; k x)) (β (e) (fun x0 : Z => x <- g x0;; k x))).
  { dependent induction EQz.
    constructor; intros a.
    now rewrite <- (EQ a). }
  rewrite H. apply wnil.
Qed.

Lemma wtrans_case_active {E B X} (t u : ctree E B X) l:
  wtrans l t u ->
  (l = τ /\ t ≅ u) \/
  (exists v, trans l t v /\ wtrans τ v u) \/
  (exists v, trans τ t v /\ wtrans l v u).
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
    cbn in H0; inv H0; eauto.
    destruct H0 as [? ? ?]; right; left; eexists; split; eauto.
    apply wtrans_τ; exists n; auto.
  - destruct TR1 as [? ? ?].
    right; right.
    eexists; split; eauto.
    exists t2; [exists t1|]; eauto.
    exists n; eauto.
Qed.

Lemma trans_rcv_inv {E B X Y} (e : E Y) (y : Y) u v :
  trans (rcv e y) u v ->
  exists (g : Y -> ctree E B X), Seq u (β e g) /\ Seq v (α g y).
Proof.
  intros TR.
  remember (rcv e y).
  revert e y Heql.
  induction TR; intros * EQl; subst; auto; inv_equ.
  - edestruct IHTR as (g & abs & ?); [reflexivity |].
    inv abs.
  - edestruct IHTR as (g & abs & ?); [reflexivity |].
    inv abs.
  - inv EQl.
  - dependent induction EQl.
    exists k; split; auto.
    now rewrite <- H.
  - inv EQl.
Qed.

Lemma trans_rcv_active {E B X Y} (e : E Y) (y : Y) (u : ctree E B X) v :
  trans (rcv e y) (α u) v ->
  False.
Proof.
  intros TR; pose proof trans_rcv_inv TR as (? & abs & ?); inv abs.
Qed.

Lemma wtrans_stuck {E B X} l t :
  wtrans l (Stuck : ctree E B X) t ->
  l = τ /\ Seq t (Stuck : ctree E B X).
Proof.
  intros WTR.
  destruct l.
  1: split; auto.
  2-4:exfalso.
  apply wtrans_τ in WTR as [[|n] WTR].
  now symmetry.
  exfalso; destruct WTR as [? TR WTR].
  eapply trans_stuck_inv; eauto.
  all: destruct WTR as [t2 [t1 TR1 TR2] TR3].
  all: destruct TR1 as [[|n] TR1].
  all: cbn in TR1; try (rewrite <- TR1 in TR2; eapply trans_stuck_inv; now eauto).
  all: destruct TR1 as [? TR WTR]; eapply trans_stuck_inv; now apply TR.
Qed.

Lemma wtrans_stuck' {E B R} :
  forall (t : ctree E B R) l,
    wtrans l Stuck t ->
    match l with | τ => t ≅ Stuck | _ => False end.
Proof.
  intros * TR.
  pose proof wtrans_stuck TR as [-> EQ].
  now inv EQ.
Qed.

Lemma wtrans_case_passive {E B X Y} (t : ctree E B X) (e : E Y) (g : Y -> ctree E B X) l:
  wtrans l t (β e g) ->
  (l = ask e /\ exists v h, wtrans τ t (α v) /\ trans (ask e) v (β e h) /\ Seq (β e h) (β e g)).  
Proof.
  intros [t2 [t1 TR1 TR2] TR3].
  apply wtrans_τ in TR1.
  pose proof wtrans_τ_active TR1 as [? EQ1].
  rewrite EQ1 in *. 
  destruct l.
  - pose proof etrans_τ_active TR2 as [? EQ2].
    rewrite EQ2 in *.
    apply wtrans_τ in TR3.
    pose proof wtrans_τ_active TR3 as [? EQ3].
    inv EQ3.
  - cbn in TR2.
    pose proof trans_ask_passive TR2 as [h EQ].
    rewrite EQ in *; clear t2 EQ.
    clear t1 EQ1.
    apply wtrans_τ in TR3.
    pose proof passive_τ_wtrans TR3 as EQ.
    dependent induction EQ.
    split; auto.
    exists x, h; split; auto.
    split; auto.
    now constructor.
  - exfalso.
    eapply trans_rcv_active; eauto.
  - exfalso.
    apply trans_val_inv' in TR2.
    rewrite TR2 in TR3.
    apply wtrans_τ in TR3.
    apply wtrans_stuck in TR3 as [_ EQ].
    inv EQ.
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

Lemma wtrans_bind_r_τ {E B X Y} (t : ctree E B X) (k : X -> ctree E B Y) (u : ctree E B Y) x :
  wtrans (val x) t Stuck ->
  wtrans τ (k x) u ->
  (u ≅ k x \/ wtrans τ (t >>= k) u).
Proof.
  intros TR1 TR2.
  apply wtrans_val_inv in TR1 as (t' & TR1 & TR1').
  pose proof wtrans_τ_active TR1 as (a & EQa).
  rewrite EQa in TR1.
  eapply wtrans_bind_l_τ in TR1.
  apply wtrans_case_active in TR2 as [[? ?] | [|(v & TR & WTR)]].
  - left; symmetry; assumption.
  - right; eapply wconss; [apply TR1 | clear t TR1].
    destruct H as (? & ? & ?).
    rewrite EQa in TR1'; clear t' EQa.
    pose proof trans_τ_active H as [? EQ].
    rewrite EQ in H,H0.
    eapply trans_bind_r in H; [| eauto].
    eapply wcons; eauto.
  - right; eapply wconss; [apply TR1 | clear t TR1].
    rewrite EQa in TR1'.
    pose proof trans_τ_active TR as [? EQ].
    rewrite EQ in TR,WTR.
    eapply trans_bind_r in TR1'; eauto.
    eapply wconss; [|eauto].
    apply trans_wtrans; auto.
Qed.

Lemma wtrans_bind_r_val {E B X Y} (t : ctree E B X) (k : X -> ctree E B Y) x (y : Y) :
  wtrans (val x) t Stuck ->
  wtrans (val y) (k x) Stuck ->
  wtrans (val y) (t >>= k) Stuck.
Proof.
  intros TR1 TR2.
  apply wtrans_val_inv in TR1 as (t' & TR1 & TR1').
  pose proof wtrans_τ_active TR1 as (a & EQa).
  rewrite EQa in TR1, TR1'; clear t' EQa.
  eapply wconss.
  eapply wtrans_bind_l_τ, TR1.
  clear t TR1.
  apply wtrans_case_active in TR2 as [[abs ?] | [(v & TR & WTR)|(v & TR & WTR)]].
  - inv abs.
  - eapply wsnocs; eauto.
    apply trans_wtrans.
    pose proof trans_val_inv' TR as EQ; rewrite EQ in TR |-*.
    eapply trans_bind_r; eauto.
  - pose proof trans_τ_active TR as [? EQ].
    rewrite EQ in TR,WTR.
    eapply trans_bind_r in TR1'; eauto.
    eapply wconss; [|eauto].
    apply trans_wtrans; auto.
Qed.

Lemma wtrans_bind_r_ask {E B X Y Z} (t : ctree E B X) (k : X -> ctree E B Y) (e : E Z) (u : Z -> ctree E B Y) x :
  wtrans (val x) t Stuck ->
  wtrans (ask e) (k x) (β e u) ->
  wtrans (ask e) (t >>= k) (β e u).
Proof.
  intros TR1 TR2.
  apply wtrans_val_inv in TR1 as (t' & TR1 & TR1').
  apply wtrans_case_passive in TR2 as (_ & v & h & WTR & TR & EQ).
  rewrite <- EQ.
  clear u EQ.
  pose proof wtrans_τ_active TR1 as [? EQ].
  rewrite EQ in *; clear t' EQ.
  eapply wconss.
  eapply wtrans_bind_l_τ, TR1.
  clear t TR1.
  apply wtrans_case_active in WTR as [[_ EQ] | [(?v & TRv & WTRv) | (?v & TRv & WTRv)]].
  - rewrite <- EQ in *.
    clear v EQ.
    apply trans_wtrans.
    eapply trans_bind_r; eauto.
  - pose proof trans_τ_active TRv as [? EQ].
    rewrite EQ in *; clear v0 EQ. 
    eapply wcons.
    eapply trans_bind_r; eauto.
    eapply wconss; eauto.
    now apply trans_wtrans.
  - pose proof trans_τ_active TRv as [? EQ].
    rewrite EQ in *; clear v0 EQ. 
    eapply wcons.
    eapply trans_bind_r; eauto.
    eapply wconss; eauto.
    now apply trans_wtrans.
Qed.    

(* Lemma wtrans_bind_r' {E B X Y} (t : ctree E B X) (k : X -> ctree E B Y) (u : ctree E B Y) x l : *)
(*   wtrans (val x) t Stuck -> *)
(*   pwtrans l (k x) u -> *)
(*   (wtrans l (t >>= k) u). *)
(* Proof. *)
(*   intros TR1 TR2. *)
(*   apply wtrans_val_inv in TR1 as (t' & TR1 & TR1'). *)
(*   eapply wtrans_bind_l in TR1; [| intros abs; inv abs]. *)
(*   apply pwtrans_case in TR2 as [? | ]. *)
(*   - eapply wconss; [apply TR1 | clear t TR1]. *)
(*     destruct H as (? & ? & ?). *)
(*     eapply trans_bind_r in TR1'; eauto. *)
(*     eapply wsnocs; eauto. *)
(*     apply trans_wtrans; auto. *)
(*   - eapply wconss; [apply TR1 | clear t TR1]. *)
(*     destruct H as (? & ? & ?). *)
(*     eapply trans_bind_r in TR1'; eauto. *)
(*     eapply wconss; [|eauto]. *)
(*     apply trans_wtrans; auto. *)
(* Qed. *)

Lemma trans_val_invT {E B R R'} :
  forall t u (v : R'),
    @trans E B R (val v) t u ->
    R = R'.
Proof.
  intros * TR.
  remember (val v) as ov.
  induction TR; intros; auto; try now inv Heqov.
Qed.

(* Lemma wtrans_bind_lr {E B X Y} (t u : ctree E B X) (k : X -> ctree E B Y) (v : ctree E B Y) x l : *)
(*   pwtrans l t u -> *)
(*   wtrans (val x) u Stuck -> *)
(*   pwtrans τ (k x) v -> *)
(*   (wtrans l (t >>= k) v). *)
(* Proof. *)
(*   intros [t2 [t1 TR1 TR1'] TR1''] TR2 TR3. *)
(*   exists (x <- t2;; k x). *)
(*   - assert (~ is_val l). *)
(*     { *)
(*       destruct l; try now intros abs; inv abs. *)
(*       exfalso. *)
(*       pose proof (trans_val_invT TR1'); subst. *)
(*       apply trans_val_inv in TR1'. *)
(*       rewrite TR1' in TR1''. *)
(*       apply transs_is_stuck_inv in TR1''; [| apply Stuck_is_stuck]. *)
(*       rewrite <- TR1'' in TR2. *)
(*       apply wtrans_is_stuck_inv in TR2; [| apply Stuck_is_stuck]. *)
(*       destruct TR2 as [abs _]; inv abs. *)
(*     } *)
(*     eexists. *)
(*     2:apply trans_etrans, trans_bind_l; eauto. *)
(*     apply wtrans_τ; eapply wtrans_bind_l; [intros abs; inv abs| apply wtrans_τ; auto]. *)
(*   - apply wtrans_τ. *)
(*     eapply wconss. *)
(*     eapply wtrans_bind_l; [intros abs; inv abs| apply wtrans_τ; eauto]. *)
(*     eapply wtrans_bind_r'; eauto. *)
(* Qed. *)

Lemma trans_trigger : forall {E B X Y} (e : E X) (k : X -> ctree E B Y),
    trans (ask e) (trigger e >>= k) (β e k).
Proof.
  intros.
  unfold CTree.trigger.
  rewrite unfold_bind; cbn.
  setoid_rewrite bind_ret_l.
  constructor; auto.
Qed.

Lemma trans_trigger' : forall {E B X Y} (e : E X) (t : ctree E B Y),
    trans (ask e) (trigger e;; t) (β e (fun _ => t)).
Proof.
  intros.
  unfold CTree.trigger.
  rewrite unfold_bind; cbn.
  setoid_rewrite bind_ret_l.
  constructor; auto.
Qed.

Lemma trans_trigger_inv : forall {E B X Y} (e : E X) (k : X -> ctree E B Y) l u,
    trans l (trigger e >>= k) u ->
    Seq u (β e k) /\ l = ask e.
Proof.
  intros * TR.
  unfold trigger in TR.
  rewrite bind_vis in TR.
  apply trans_vis_inv' in TR as [EQ ->].
  setoid_rewrite bind_ret_l in EQ.
  split; auto.
Qed.

Lemma trans_branch :
  forall {E B : Type -> Type} {X : Type} {Y : Type}
    [l : label] [t t' : ctree E B X] (c : B Y) (k : Y -> ctree E B X) (x : Y),
    trans l (k x) t' ->
    trans l (branch c >>= k) t'.
Proof.
  intros.
  rewrite bind_branch.
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

Lemma wf_val_trans {E B X} (l : @label E) t t' :
  @trans E B X l t t' -> wf_val X l.
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

(* (*| If the LTS has events of type [L +' R] then *)
(*   it is possible to step it as either an [L] LTS *)
(*   or [R] LTS ignoring the other. *)
(* *) *)
(* Section Coproduct. *)
(*   Arguments label: clear implicits. *)
(*   Context {L R C: Type -> Type} {X: Type}. *)
(*   Notation S := (ctree (L +' R) C X). *)
(*   Notation S' := (ctree' (L +' R) C X). *)
(*   Notation SP := (SS -> label (L +' R) -> Prop). *)

(*   (* Skip an [R] event *) *)
(*   Inductive srtrans_: rel S' S' := *)
(*   | IgnoreR {X} (e : R X) k x t : *)
(*     srtrans_ (observe (k x)) t -> *)
(*     srtrans_ (VisF (inr1 e) k) t. *)

(*   (* Skip an [L] event *) *)
(*   Inductive sltrans_: rel S' S' := *)
(*   | IgnoreL {X} (e : L X) k x t : *)
(*     sltrans_ (observe (k x)) t -> *)
(*     sltrans_ (VisF (inl1 e) k) t. *)

(*   Hint Constructors srtrans_ sltrans_: core. *)

(*   (* Make those relations that respect equality [srel] *) *)
(*   Program Definition srtrans : srel SS SS := *)
(*     {| hrel_of := (fun (u v: SS) => srtrans_ (observe u) (observe v)) |}. *)
(*   Next Obligation. split; induction 1; auto. Defined. *)

(*   Program Definition sltrans : srel SS SS := *)
(*     {| hrel_of := (fun (u v: SS) => sltrans_ (observe u) (observe v)) |}. *)
(*   Next Obligation. split; induction 1; auto. Defined. *)

(*   (*| Obs transition on the left, ignores right transitions and [τ] |*) *)
(*   Definition ltrans {X}(l: L X)(x: X): srel SS SS := *)
(*     (trans τ ⊔ srtrans)^* ⋅ trans (obs (inl1 l) x) ⋅ (trans τ ⊔ srtrans)^*. *)

(*   (*| Obs transition on the right, ignores left transitions and [τ] |*) *)
(*   Definition rtrans {X}(r: R X)(x: X): srel SS SS := *)
(*     (trans τ ⊔ sltrans)^* ⋅ trans (obs (inr1 r) x) ⋅ (trans τ ⊔ sltrans)^*. *)

(* End Coproduct. *)

(*|
[inv_trans] is an helper tactic to automatically
invert hypotheses involving [trans].
|*)

(* #[local] Notation trans' l t u := (hrel_of (trans l) t u). *)

(* Ltac inv_trans_one := *)
(*   match goal with *)

(*   (* Ret *) *)
(*   | h : trans' _ (Ret ?x) _ |- _ => *)
(*       let EQl := fresh "EQl" in *)
(*       apply trans_ret_inv in h as [?EQ EQl]; *)
(*       match type of EQl with *)
(*       | val _   = val _ => apply val_eq_inv in EQl; try (inversion EQl; fail) *)
(*       | τ     = val _ => now inv EQl *)
(*       | obs _ _ = val _ => now inv EQl *)
(*       | _ => idtac *)
(*       end *)

(*   (* Vis *) *)
(*   | h : trans' _ (Vis ?e ?k) _ |- _ => *)
(*       let EQl := fresh "EQl" in *)
(*       apply trans_vis_inv in h as (?x & ?EQ & EQl); *)
(*       match type of EQl with *)
(*       | @obs _ ?X _ _ = obs _ _ => *)
(*           let EQt := fresh "EQt" in *)
(*           let EQe := fresh "EQe" in *)
(*           let EQv := fresh "EQv" in *)
(*           apply obs_eq_invT in EQl as EQt; *)
(*           subst_hyp_in EQt h; *)
(*           apply obs_eq_inv in EQl as [EQe EQv]; *)
(*           try (inversion EQv; inversion EQe; fail) *)
(*       | val _   = obs _ _ => now inv EQl *)
(*       | τ     = obs _ _ => now inv EQl *)
(*       | _ => idtac *)
(*       end *)

(*   (* Step *) *)
(*   | h : trans' _ (Step _) _ |- _ => *)
(*       let EQl := fresh "EQl" in *)
(*       apply trans_step_inv in h as (?EQ & EQl); *)
(*       match type of EQl with *)
(*       | τ     = τ => clear EQl *)
(*       | val _   = τ => now inv EQl *)
(*       | obs _ _ = τ => now inv EQl *)
(*       | _ => idtac *)
(*       end *)

(*   (* BrS *) *)
(*   | h : trans' _ (BrS ?n ?k) _ |- _ => *)
(*       let x := fresh "x" in *)
(*       let EQl := fresh "EQl" in *)
(*       apply trans_brS_inv in h as (x & ?EQ & EQl); *)
(*       match type of EQl with *)
(*       | τ     = τ => clear EQl *)
(*       | val _   = τ => now inv EQl *)
(*       | obs _ _ = τ => now inv EQl *)
(*       | _ => idtac *)
(*       end *)

(*   (* brS2 *) *)
(*   | h : trans' _ (brS2 _ _) _ |- _ => *)
(*       let EQl := fresh "EQl" in *)
(*       apply trans_brS2_inv in h as (EQl & [?EQ | ?EQ]); *)
(*       match type of EQl with *)
(*       | τ     = τ => clear EQl *)
(*       | val _   = τ => now inv EQl *)
(*       | obs _ _ = τ => now inv EQl *)
(*       | _ => idtac *)
(*       end *)

(*   (* brS3 *) *)
(*   | h : trans' _ (brS3 _ _ _) _ |- _ => *)
(*       let EQl := fresh "EQl" in *)
(*       apply trans_brS3_inv in h as (EQl & [?EQ | [?EQ | ?EQ]]); *)
(*       match type of EQl with *)
(*       | τ     = τ => clear EQl *)
(*       | val _   = τ => now inv EQl *)
(*       | obs _ _ = τ => now inv EQl *)
(*       | _ => idtac *)
(*       end *)

(*   (* brS4 *) *)
(*   | h : trans' _ (brS4 _ _ _ _) _ |- _ => *)
(*       let EQl := fresh "EQl" in *)
(*       apply trans_brS4_inv in h as (EQl & [?EQ | [?EQ | [?EQ | ?EQ]]]); *)
(*       match type of EQl with *)
(*       | τ     = τ => clear EQl *)
(*       | val _   = τ => now inv EQl *)
(*       | obs _ _ = τ => now inv EQl *)
(*       | _ => idtac *)
(*       end *)

(*   (* Guard *) *)
(*   | h : trans' _ (Guard _) _ |- _ => *)
(*       apply trans_guard_inv in h *)

(*   (* Br *) *)
(*   | h : trans' _ (Br ?n ?k) _ |- _ => *)
(*       let x := fresh "x" in *)
(*       apply trans_br_inv in h as (x & ?TR) *)

(*   (* br2 *) *)
(*   | h : trans' _ (br2 _ _) _ |- _ => *)
(*       apply trans_br2_inv in h as [?TR | ?TR] *)

(*   (* br3 *) *)
(*   | h : trans' _ (br3 _ _ _) _ |- _ => *)
(*       apply trans_br3_inv in h as [?TR | [?TR | ?TR]] *)

(*   (* br4 *) *)
(*   | h : trans' _ (br4 _ _ _ _) _ |- _ => *)
(*       apply trans_br4_inv in h as [?TR | [?TR | [?TR | ?TR]]] *)

(*   (* Stuck *) *)
(*   | h : trans' _ Stuck _ |- _ => *)
(*       exfalso; eapply Stuck_is_stuck; now apply h *)
(*   (* (* stuckS *) *) *)
(*   (* | h : trans' _ stuckS _ |- _ => *) *)
(*   (*     exfalso; eapply stuckS_is_stuck; now apply h *) *)

(*   (* trigger *) *)
(*   | h : trans' _ (CTree.bind (CTree.trigger ?e) ?t) _ |- _ => *)
(*       apply trans_trigger_inv in h as (?x & ?EQ & ?EQl) *)

(*   end; try subs *)
(* . *)

(* Ltac inv_trans := repeat inv_trans_one. *)

Create HintDb trans.
#[global] Hint Resolve
 trans_ret trans_ask trans_brS trans_br
 trans_guard
 trans_br21 trans_br22
 trans_br31 trans_br32 trans_br33
 trans_br41 trans_br42 trans_br43 trans_br44
 trans_step
 trans_brS21 trans_brS22
 trans_brS31 trans_brS32 trans_brS33
 trans_brS41 trans_brS42 trans_brS43 trans_brS44
 trans_trigger trans_bind_l_τ trans_bind_l_ask trans_bind_r
  : trans.

#[global] Hint Constructors is_val : trans.
#[global] Hint Resolve
  is_val_τ
  (* is_val_obs *)
  wf_val_val wf_val_nonval wf_val_trans : trans.

Ltac etrans := eauto with trans.
