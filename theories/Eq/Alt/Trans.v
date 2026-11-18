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
The first transition relation we introduce is [trans_alt]: a tree can
finitely descend through unobservable brs until it reaches an
observable node. At this point, it steps following the simple rules:
- [Ret v] steps to a silently blocked state by emitting a value
label of [v]
- [Vis e k] can step to any [k x] by emitting an event label tagged
with both [e] and [x]


(* TODO remove, note: this above will change with the vis fix *)

- [BrS k] can step to any [k x] by emitting a tau label

This transition system will define a notion of strong bisimulation
in the process algebra tradition.
It also leads to a weak bisimulation by defining [wtrans] as a
sequence of tau steps, and allowing a challenge to be answered by
[wtrans . trans_alt . wtrans].
Once [trans_alt] is defined over our structure, we can reuse the constructions
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
     CTree Eq.Equ.

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

Variant S E B R :=
  | Active (t : ctree E B R)
  | Passive {X} (e : E X) (k : X -> ctree E B R).

Variant SeqR {E B X Y} (RR : hrel X Y) : S E B X -> S E B Y -> Prop :=
  | ActAct t u (EQ: equ RR t u) : SeqR RR (Active t) (Active u)
  | PasPas {A} e (k g : A -> _) (EQ: forall a, equ RR (k a) (g a)) : SeqR RR (Passive e k) (Passive e g)
.
Hint Constructors SeqR : core.
Definition Seq {E B X} := (@SeqR E B X X eq).
Hint Unfold Seq : core.

#[global] Instance SeqR_equiv {E B R} {RR : rel R R} {RE: Equivalence RR}: Equivalence (@SeqR E B R R RR).
Proof.
  constructor.
  - intros []; auto.
  - intros ? ? []; constructor; intros; now symmetry.
  - intros ? ? ? EQ1 EQ2.
    inv EQ1.
    inv EQ2; constructor; intros; etransitivity; eauto.
    dependent induction EQ2; constructor; intros; etransitivity; eauto.
Qed.
Arguments Active {E B R}.
Arguments Passive {E B R X} e k.

Section Trans.

  Context {E B : Type -> Type} {R : Type}.
  Notation S   := (S E B R).
  Notation Seq := (@Seq E B R).
  
  Definition SS : EqType :=
    {| type_of := S ; Eq := Seq |}.


    (* HERE *)
(* Step one: new LTS. Therefore step zero is new labels. *)

(*|
The domain of labels of the LTS.
Note that it could be typed more strongly: [val] labels can only
be of type [R]. However typing it statically makes lemmas about
[bind] particularly awkward to state, so this seems to be the
least annoying solution.
|*)
  Variant label : Type :=
    | τ
    | ε (* \upepsilon or \varepsilon depending on your extension *) 
    | ask {X : Type} (e : E X)
    | rcv {X : Type} (e : E X) (v : X) (* Note: I think we need to remember which request led to the response for the bisimilarity to be right, but I am not 100% sure, [e] might be spurious *)
    | val (v : R).

  Variant is_val : label -> Prop :=
    | Is_val : forall x, is_val (val x).

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


(* question: equ constraints as before or direct constructors? *)
  Variant transR : label -> hrel S S :=

  | Transbr {X} (c : B X) t k u : 
    (* u reachable from (Br c k) *)
    t ≅ Br c k -> 
    forall x, u ≅ k x -> 
    transR ε (Active t) (Active u)
    
  | Transguard t t' u :
    t ≅ Guard t' ->   
    u ≅ t' ->   
    transR ε (Active t) (Active u)

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

  | Transval t r u :
    t ≅ Ret r -> 
    u ≅ Stuck -> 
    transR (val r) (Active t) (Active u)
    
    .
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
      + inv EQ1; inv EQ2. 
        * econstructor 1.
          rewrite <- EQ, H; reflexivity.
          rewrite <- EQ0. eassumption.
      + inv EQ1; inv EQ2. 
        econstructor 2. 
        rewrite <- EQ, H; reflexivity.
        now rewrite <- EQ0.   
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
      + inv EQ1; inv EQ2. 
        econstructor 1.
        rewrite EQ, H; reflexivity.
        rewrite EQ0. eauto. 
      + inv EQ1; inv EQ2. 
        econstructor 2.
        rewrite EQ, H; reflexivity.
        now rewrite EQ0. 
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
    now rewrite EQ,EQ0.
    rewrite EQ. 
    all: try now rewrite EQ, EQ0.
    assert (H: Seq (Passive e k) (Passive e g))
    by (apply equ_Seq_passive; red; apply EQ0); now rewrite H.
    rewrite EQ0.
    assert (H: Seq (Passive e k) (Passive e g))
    by (apply equ_Seq_passive; red; apply EQ); now rewrite H.
    assert (H1: Seq (Passive e k) (Passive e g))
    by (apply equ_Seq_passive; red; apply EQ);
    assert (H2: Seq (Passive e0 k0) (Passive e0 g0))
    by (apply equ_Seq_passive; red; apply EQ0);
      now rewrite H1,H2.
  Qed.

  Definition trans_alt l : srel SS SS := {| hrel_of := transR l : hrel SS SS |}.

(*|
Extension of [trans_alt] with its reflexive closure, labelled by [τ].
|*)
  Definition etrans (l : label) : srel SS SS :=
    match l with
    | τ => (cup (trans_alt l) 1)
    | _ => trans_alt l
    end.

(*|
The transition for the weak bisimulation: a sequence of
internal steps, a labelled step, and a new sequence of internal ones
|*)
 
  Definition wtrans l : srel SS SS :=
    (trans_alt τ)^* ⋅ etrans l ⋅ (trans_alt τ)^*.

  Definition pwtrans l : srel SS SS :=
    (trans_alt τ)^* ⋅ trans_alt l ⋅ (trans_alt τ)^*.

  Definition τtrans : srel SS SS :=
    (trans_alt τ)^+.

  (*|
----------------------------------------------
Elementary theory for the transition relations
----------------------------------------------

Inclusion relation between the three relations:
[trans_alt l ≤ etrans l ≤ wtrans l]

[etrans] is reflexive, and hence so is [wtrans]
[etrans τ p p]

[wtrans] can be built by consing or snocing [trans_alt τ]
[trans_alt τ p p' -> wtrans l p' p'' -> wtrans l p p'']
[wtrans l p p' -> trans_alt τ p' p'' -> wtrans l p p'']

Introduction rules for [trans_alt]
[trans_alt (val v)   (ret v)       stuck]
[trans_alt (obs e v) (Vis e k)     (k v)]
[trans_alt l (k x) u -> trans_alt l (BrD n k) u]
[trans_alt τ       (Step t) t]
[trans_alt τ       (BrS n k) (k x)]
[trans_alt l t u     -> trans_alt l (Guard t) u]

Elimination rules for [trans_alt]
[trans_alt l (Ret x)       u -> l = val x /\ t ≅ stuck]
[trans_alt l (Vis e k)     u -> exists v, l = obs e v /\ t ≅ k v]
[trans_alt l (Step t)      u -> t ≅ u /\ l = τ]
[trans_alt l (Br n k) u -> exists x, trans_alt l (k x) u]
[trans_alt l (BrS n k) u -> exists x, t' ≅ k x /\ l = τ]
[trans_alt l (Guard t)      u -> trans_alt l t u]

|*)
  Lemma trans_etrans l: trans_alt l ≦ etrans l.
  Proof.
    unfold etrans; case l; ka.
  Qed.
  Lemma etrans_wtrans l: etrans l ≦ wtrans l.
  Proof.
    unfold wtrans; ka.
  Qed.
  Lemma trans_wtrans l: trans_alt l ≦ wtrans l.
  Proof. rewrite trans_etrans. apply etrans_wtrans. Qed.
  Lemma τtrans_wtrans : τtrans ≦ wtrans τ.
  Proof.
    unfold τtrans, wtrans, etrans; ka.
  Qed.
  Lemma pwtrans_wtrans l : pwtrans l ≦ wtrans l.
  Proof.
    unfold pwtrans, wtrans, etrans; case l; ka.
  Qed.

  Lemma trans_etrans_ l: forall p p', trans_alt l p p' -> etrans l p p'.
  Proof. apply trans_etrans. Qed.
  Lemma trans_wtrans_ l: forall p p', trans_alt l p p' -> wtrans l p p'.
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

  Lemma wcons l: forall p p' p'', trans_alt τ p p' -> wtrans l p' p'' -> wtrans l p p''.
  Proof.
    assert ((trans_alt τ: srel SS SS) ⋅ wtrans l ≦ wtrans l) as H
        by (unfold wtrans; ka).
    intros. apply H. eexists; eassumption.
  Qed.
  Lemma wsnoc l: forall p p' p'', wtrans l p p' -> trans_alt τ p' p'' -> wtrans l p p''.
  Proof.
    assert (wtrans l ⋅ trans_alt τ ≦ wtrans l) as H
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

  Lemma wtrans_τ: wtrans τ ≡ (trans_alt τ)^*.
  Proof.
    unfold wtrans, etrans. ka.
  Qed.

  Lemma pwtrans_τ: pwtrans τ ≡ (trans_alt τ)^+.
  Proof.
    unfold pwtrans, etrans. ka.
  Qed.

  #[global] Instance PreOrder_wtrans_τ: PreOrder (wtrans τ).
  Proof.
    split.
    intro. apply wtrans_τ.
    now (apply (str_refl (trans_alt τ)); cbn).
    intros ?????. apply wtrans_τ. apply (str_trans (trans_alt τ)).
    eexists; apply wtrans_τ; eassumption.
  Qed.

End Trans.

Arguments label : clear implicits.
#[global] Infix "⩸" := Seq (at level 10).
#[global] Hint Constructors transR : core.

Ltac rem_weak_ t s :=
  let tmp := fresh in
  let name := fresh "EQ" in
  remember t as s eqn:tmp;
  assert (EQ: Seq s t) by (now subst);
  clear tmp.
  
Tactic Notation "rem_weak" constr(t) "as" ident(s) := rem_weak_ t s.


Coercion Active : ctree >-> S.
Notation "'α' t" := (Active t) (at level 100).
(* Out of curiosity: do coercion for β in rocq-elpi *)
Notation "'β' e" := (Passive e) (at level 0).
(*|
Backward reasoning for [trans_alt]
------------------------------
Note: we need to be a bit careful to define these proof rules
explicitly over [ctree]s and not [rel_of SS] as gets coerced
in the section above so that [eauto with trans_alt] works smoothly.
|*)
Section backward.

  Context {E B : Type -> Type} {X : Type}.

(*|
Structural rules

We essentially lift the constructors to the [trans_alt] bundling, and
eliminate on the way the noise from closing up everything to [equ eq].
|*)

  Lemma trans_ret : forall (x : X),
      trans_alt (E := E) (B := B) (val x) (Ret x) Stuck.
  Proof.
    intros; constructor; auto.
  Qed.

  Lemma trans_ask : forall {Y} (e : E Y) (k : Y -> ctree E B X),
      trans_alt (ask e) (Vis e k) (β e k).
  Proof.
    intros; constructor; auto.
  Qed.

  Lemma trans_rcv : forall {Y} (e : E Y) (k : Y -> ctree E B X) y,
      trans_alt (rcv e y) (β e k) (k y).
  Proof.
    intros; constructor; auto.
  Qed.

  (* no longer true: only for epsilon labels *)
  Lemma trans_br : forall {Y} (c : B Y) x (k : Y -> ctree E B X),
      trans_alt ε (Br c k) (k x).
  Proof.
    intros *.
    eapply Transbr; [reflexivity|].
    reflexivity.   
  Qed.

  Lemma trans_step : forall (t : ctree E B X),
      trans_alt τ (Step t) t.
  Proof.
    intros.
    eapply Transstep; reflexivity.
  Qed.

  Lemma trans_guard : forall (t : ctree E B X),
      trans_alt ε (Guard t) t.
  Proof.
    intros.
    eapply Transguard; [reflexivity | auto].
  Qed.


  (* fixes: τ → ε *)
  (* this is no longer true with just (k x):  
  broadly, for these and all below, we need the transitive closure of 
  trans_alt. 
  
  *)

Ltac epop := unshelve (instantiate (1:=_)).
Ltac epop2 := unshelve (instantiate (2:=_)).

Ltac use e := unshelve (instantiate (1:=e)).


End backward.

#[global] Hint Resolve trans_br trans_guard  trans_step trans_ask trans_rcv trans_ret : core.

Section BackwardBounded.

  Context {E B : Type -> Type} {X : Type}.
  Context `{B2 -< B}.
  Context `{B3 -< B}.
  Context `{B4 -< B}.
  Variable (l : @label E X) (t t' u u' v v' w w' : ctree E B X).


  Lemma trans_br21 :
    trans_alt ε (br2 t u) t.
  Proof.
    intros *.
    apply trans_br with (x:=true). 
  Qed. 
  
  Lemma trans_br22 :
    trans_alt ε (br2 t u) u.
  Proof.
    intros *.
        apply trans_br with (x:=false). 
  Qed.


End BackwardBounded.

(*|
Forward reasoning for [trans_alt]
------------------------------
|*)

Section forward.

  Context {E B : Type -> Type} {X : Type}.

(*|
Inverting equalities between labels
|*)

  (* [val_eq_invT] no longer makes sense: [val] now has signature
     [val : R -> label E R], so two [val x], [val y] can only be compared
     when they share the return-type parameter; the type equality is
     enforced by typing rather than proved. *)

  Lemma val_eq_inv : forall (x y : X), @val E X x = val y -> x = y.
    clear B. intros * EQ.
    now inversion EQ.
  Qed.

  Lemma ask_invT : forall E Y Z e1 e2, @ask E X Y e1 = @ask E X Z e2 -> Y = Z.
    intros * EQ.
    now dependent induction EQ.
  Qed.

  Lemma ask_inv : forall E Y e1 e2, @ask E X Y e1 = @ask E X Y e2 -> e1 = e2.
    intros * EQ.
    now dependent induction EQ.
  Qed.

  Lemma rcv_invT : forall E Y Z e1 e2 v1 v2, @rcv E X Y e1 v1 = @rcv E X Z e2 v2 -> Y = Z.
    intros * EQ.
    now dependent induction EQ.
  Qed.

  Lemma rcv_inv : forall E Y e1 e2 v1 v2, @rcv E X Y e1 v1 = @rcv E X Y e2 v2 -> e1 = e2 /\ v1 = v2.
    intros * EQ.
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
      trans_alt l (Ret x : ctree E B X) u ->
      Seq u (α Stuck) /\ l = val x.
  Proof.
    intros * TR; inv TR; inv_equ.
    intuition.
  Qed.

  Lemma trans_ret_inv : forall x l (u : ctree E B X),
      trans_alt l (Ret x) u ->
      u ≅ Stuck /\ l = val x.
  Proof.
    intros * TR; inv TR; inv_equ.
    intuition.
  Qed.

  Lemma trans_vis_inv' : forall {Y} (e : E Y) (k : _ -> ctree E B X) l u,
      trans_alt l (Vis e k) u ->
      Seq u (β e k) /\ l = ask e.
  Proof.
    intros * TR.
    inv TR; inv_equ.
    split; auto.
    constructor; intros ?; symmetry; eauto.
  Qed.

  Lemma trans_vis_inv : forall {Y} (e : E Y) k l (u : ctree E B X),
      trans_alt l (Vis e k) u ->
      False.
  Proof.
    intros * TR.
    inv TR; inv_equ.
  Qed.

  Lemma trans_passive_inv' : forall {Y} (e : E Y) (k : Y -> ctree E B X) l u,
      trans_alt l (β e k) u ->
      exists x, Seq u (α k x) /\ l = rcv e x.
  Proof.
    intros * TR.
    cbn in TR; dependent induction TR.
    eexists; split; eauto.
    constructor; symmetry; eauto.
  Qed.

  Lemma trans_passive_inv : forall {Y} (e : E Y) (k : Y -> ctree E B X) l (u : ctree E B X),
      trans_alt l (β e k) u ->
      exists x, u ≅ (k x) /\ l = rcv e x.
  Proof.
    intros * TR.
    apply trans_passive_inv' in TR as (? & ? & ?).
    inv H; eauto.
  Qed.


  Lemma trans_step_inv' : forall l (t : ctree E B X) u,
      trans_alt l (Step t) u ->
      Seq u t /\ l = τ.
  Proof.
    intros * TR.
    inv TR; inv_equ; split; auto.
    now rewrite H0,H2.
  Qed.

  Lemma trans_step_inv : forall l (t u : ctree E B X),
      trans_alt l (Step t) u ->
      u ≅ t /\ l = τ.
  Proof.
    intros * TR.
    apply trans_step_inv' in TR as [? ?]; split; auto.
    now inv H.
  Qed.
  Lemma trans_stuck_inv : forall l u,
      trans_alt l (Stuck : ctree E B X) u ->
      False.
  Proof.
    intros * TR.
    cbn in TR; dependent induction TR; inv_equ.
  Qed.

(*|
Ad-hoc rules for pre-defined finite branching
|*)

  Variable (l : @label E X) (t u v w : ctree E B X).
  Context `{B2 -< B} `{B3 -< B} `{B4 -< B}.


(*|
Inversion rules for [trans_alt] based on the value of the label
-----------------------------------------------------------
In general, these would require to introduce the relation that
only steps through the non-observable internal br.
I'll skip them for now and introduce them if they turn out to be
useful.
|*)

  Lemma trans_val_inv' :
    forall t u (x : X),
      trans_alt (val x) t u ->
      Seq u (α (Stuck : ctree E B X)).
  Proof.
    intros * TR.
    remember (val x) as ox.
    revert x Heqox.
    cbn in TR; induction TR; intros ? Heqox; try now inv Heqox.
    all: eauto.
  Qed.

  Lemma trans_val_inv :
    forall (t u : ctree E B X) (x : X),
      trans_alt (val x) t u ->
      u ≅ Stuck.
  Proof.
    now intros * TR; apply trans_val_inv' in TR; inv TR.
  Qed.

  Lemma wtrans_val_inv : forall (x : X),
      wtrans (val x) u Stuck ->
      exists t, wtrans τ u t /\ trans_alt (val x) t Stuck.
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
    (trans_alt l t u \/ (l = τ /\ @Seq E B X t u)).
Proof.
  intros [] * TR; cbn in *; intuition.
Qed.

Lemma etrans_case {E B X} : forall l (t u : ctree E B X),
    etrans l t u ->
    (trans_alt l t u \/ (l = τ /\ t ≅ u)).
Proof.
  intros [] * TR; cbn in *; intuition.
  inv H; intuition.
Qed.

Lemma etrans_ret_inv' {E B X} : forall x l t,
    etrans l (Ret x) t ->
    (l = τ /\ @Seq E B X t (α Ret x)) \/ (l = val x /\ Seq t (α Stuck)).
Proof.
  intros ? [] ? step; cbn in step.
  - intuition auto with *; try (eapply trans_ret in step; now apply step).
    apply trans_ret_inv' in H; intuition.
  - eapply trans_ret_inv' in step; intuition.
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
    inv H; intuition auto with *.
  - eapply trans_ret_inv in step; intuition.
  - eapply trans_ret_inv in step; intuition.
  - eapply trans_ret_inv in step; intuition.
  - eapply trans_ret_inv in step; intuition.
Qed.

Lemma passive_τ_trans {E B X Y} e (g : X -> ctree E B Y) u :
  trans_alt τ (β e g) u ->
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

Lemma transs_τ_passive {E B X Y} e (g : X -> ctree E B Y) u :
  (trans_alt τ)^* (β e g) u ->
  Seq u (β e g).
Proof.
  intros TR.
  eapply passive_τ_wtrans.
  now apply wtrans_τ.
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

  Definition is_stuck : @S E B X -> Prop :=
    fun t => forall l u, ~ (trans_alt l t u).

  #[global] Instance Seq_is_stuck : Proper (Seq ==> iff) is_stuck.
  Proof.
    intros ? ? EQ; split; intros ST; red; intros * ABS.
    rewrite <- EQ in ABS; eapply ST; eauto.
    rewrite EQ in ABS; eapply ST; eauto.
  Qed.

  Lemma etrans_is_stuck_inv' v v' l :
    is_stuck v ->
    etrans l v v' ->
    l = τ /\ Seq v v'.
  Proof.
    intros * ST TR.
    edestruct @etrans_case'; eauto.
    apply ST in H; tauto.
  Qed.

  Lemma etrans_is_stuck_inv (v v' : ctree E B X) l :
    is_stuck v ->
    etrans l v v' ->
    (l = τ /\ v ≅ v').
  Proof.
    intros * ST TR.
    edestruct @etrans_case; eauto.
    apply ST in H; tauto.
  Qed.

  Lemma transs_is_stuck_inv' v v' :
    is_stuck v ->
    (trans_alt τ)^* v v' ->
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
    (trans_alt τ)^* v v' ->
    v ≅ v'.
  Proof.
    intros * ST TR.
    eapply transs_is_stuck_inv' in TR; eauto.
    now inv TR.
  Qed.

  Lemma wtrans_is_stuck_inv t u l :
    is_stuck t ->
    wtrans l t u ->
    (l = τ /\ Seq t u).
  Proof.
    intros * ST TR.
    destruct TR as [? [? ?] ?].
    apply transs_is_stuck_inv' in H; auto.
    rewrite H in ST.
    inv H.
    - apply etrans_is_stuck_inv' in H0 as [-> ?]; auto.
      inv H.
      rewrite EQ0 in ST; apply transs_is_stuck_inv' in H1; auto.
      intuition.
      rewrite EQ, EQ0; auto.
    - pose proof etrans_is_stuck_inv' _ _ ST H0 as [-> ?]; auto.
      split; auto.
      rewrite <-H in H1.
      apply transs_τ_passive in H1.
      rewrite H1. auto.
  Qed.

  (* Constructions *) 
  Lemma stuck_is_stuck :
     is_stuck Stuck.
  Proof.
    repeat intro; eapply trans_stuck_inv; eauto.
  Qed.


  Lemma spinS_is_not_stuck :
    ~ (is_stuck spinS).
  Proof.
    red; intros * abs.
    apply (abs τ spinS).
    rewrite ctree_eta at 1; cbn.
    apply trans_step.
  Qed.

  Lemma vis_is_not_stuck {Y} (e : E Y) (k : Y -> _) :
    ~ is_stuck (Vis e k).
  Proof.
    red; intros * abs.
    eapply (abs (ask e)).
    apply trans_ask.
  Qed.

  Lemma passive_is_not_stuck {Y} `{Inhabited Y} (e : E Y) (k : Y -> _) :
    ~ is_stuck (β e k).
  Proof.
    red; intros * abs.
    eapply (abs (rcv e inhabitant)).
    apply trans_rcv.
  Qed.

  Lemma passive_void_is_stuck (e : E void) (k : void -> _) :
    is_stuck (β e k).
  Proof.
    red; intros * abs.
    apply trans_passive_inv' in abs as ([] & _ & _).
  Qed.

End stuck.

Section not_stuck.

  Context {E B : Type -> Type} {X : Type}.

  Definition not_stuck t :=
    exists l' t', @trans_alt E B X l' t t'.

  #[global] Instance seq_not_stuck : Proper (Seq ==> iff) not_stuck.
  Proof.
    intros ? ? EQ; split; intros (l' & t' & TR).
    rewrite EQ in TR; red; eauto.
    rewrite <- EQ in TR; red; eauto.
  Qed.

  #[global] Instance equ_not_stuck : Proper (equ eq ==> iff) not_stuck.
  Proof.
    intros ? ? EQ; split; intros (l' & t' & TR).
    rewrite EQ in TR; red; eauto.
    rewrite <- EQ in TR; red; eauto.
  Qed.

  (* Converse is classically true *)
  Lemma not_stuck_is_stuck :
    forall t, not_stuck t -> ~ is_stuck t.
  Proof.
    intros t (l' & t' & NS) IS; eapply IS; eauto.
  Qed.

  Lemma ret_not_stuck x:
    not_stuck (Ret x).
  Proof.
    red; eauto.
  Qed.
 
  Lemma vis_not_stuck {Y} (e : E Y) k:
    not_stuck (Vis e k).
  Proof.
    red; eauto.
  Qed.
  
  Lemma step_not_stuck t:
    not_stuck (Step t).
  Proof.
    red; eauto.
  Qed.
  
  Lemma passive_not_stuck {Y} `{Inhabited Y} (e : E Y) k:
    not_stuck (β e k).
  Proof.
    red; eauto.
    Unshelve.
    exact inhabitant.
  Qed.
  
  Lemma br_not_stuck {Y} (b : B Y) (k : Y -> ctree _ _ _):
    (exists x, not_stuck (k x)) ->
    not_stuck (Br b k).
  Proof.
    intros (y & l' & t' & TR).
    red; eauto.
    exists ε, (α k y).
    now econstructor. 
  Qed.
   
  
End not_stuck.  
#[global] Hint Unfold not_stuck : core.
  
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
      (trans_alt τ)^* (Ret x) t ->
      @Seq E B X t (α Ret x).
  Proof.
    intros * [[|] step].
    - cbn in *; now symmetry.
    - destruct step.
      apply trans_ret_inv' in H; intuition congruence.
  Qed.

  Lemma trans_τ_str_ret_inv : forall x (t : ctree E B X),
      (trans_alt τ)^* (Ret x) t ->
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
    apply transs_is_stuck_inv in step3; [| apply stuck_is_stuck].
    intuition auto with *.
  Qed.

  Lemma wtrans_val_inv' : forall (x : X) t u,
      wtrans (val x) t u ->
      exists t', @wtrans E B X τ t t' /\ @trans_alt E B X (val x) t' u /\ Seq u Stuck.
  Proof.
    intros * TR.
    destruct TR as [t2 [t1 step1 step2] step3].
    exists t1; split.
    apply wtrans_τ; auto.
    clear step1.
    pose proof trans_val_inv' step2.
    rewrite H in step3.
    apply transs_is_stuck_inv' in step3; auto using stuck_is_stuck.
    split; [| rewrite <- step3; auto].
    rewrite H in step2. rewrite <- step3.
    auto.
  Qed.

End wtrans.

(*|
Forward and backward rules for [trans_alt] w.r.t. [bind]
----------------------------------------------------
trans_alt l (t >>= k) u -> (trans_alt l t t' /\ u ≅ t' >>= k) \/ (trans_alt (ret x) t stuck /\ trans_alt l (k x) u)
l <> val x -> trans_alt l t u -> trans_alt l (t >>= k) (u >>= k)
trans_alt (val x) t stuck -> trans_alt l (k x) u -> trans_alt l (bind t k) u.
|*)

Lemma trans_bind_l_τ {E B X Y} (t : ctree E B X) (k : X -> ctree E B Y) (u : ctree E B X) :
  trans_alt τ (Active t) (Active u) ->
  trans_alt τ (Active (x <- t;; k x)) (Active (x <- u;; k x)).
Proof.
  intros TR; unfold trans_alt in TR; cbn in TR; dependent destruction TR.
  eapply Transstep.
  - rewrite H, bind_step; reflexivity.
  - rewrite H0; reflexivity.
Qed.

Lemma trans_bind_l_ε {E B X Y} (t : ctree E B X) (k : X -> ctree E B Y) (u : ctree E B X) :
  trans_alt ε (Active t) (Active u) ->
  trans_alt ε (Active (x <- t;; k x)) (Active (x <- u;; k x)).
Proof.
  intros TR; unfold trans_alt in TR; cbn in TR; dependent destruction TR.
  - eapply Transbr.
    + rewrite H, bind_br; reflexivity.
    + rewrite H0; reflexivity.
  - eapply Transguard.
    + rewrite H, bind_guard; reflexivity.
    + rewrite H0; reflexivity.
Qed.

Lemma trans_bind_l_ask {E B X Y Z} (t : ctree E B X) (k : X -> ctree E B Y)
  (e : E Z) (g : Z -> ctree E B X) :
  trans_alt (ask e) (Active t) (Passive e g) ->
  trans_alt (ask e) (Active (x <- t;; k x)) (Passive e (fun z => x <- g z;; k x)).
Proof.
  intros TR; unfold trans_alt in TR; cbn in TR; dependent destruction TR.
  econstructor.
  rewrite H, bind_vis; reflexivity.
Qed.

Lemma trans_bind_r {E B X Y} (t : ctree E B X) (k : X -> ctree E B Y)
  (u : @S E B Y) (x : X) (l : @label E Y) :
  trans_alt (val x) (Active t) (Active (Stuck : ctree E B X)) ->
  trans_alt l (Active (k x)) u ->
  trans_alt l (Active (y <- t;; k y)) u.
Proof.
  intros TR1 TR2; unfold trans_alt in *; cbn in *; dependent destruction TR1.
  assert (SQ : Seq (Active (y <- t;; k y)) (Active (k x))) by
        (constructor; now rewrite H, bind_ret_l).
  rewrite SQ. exact TR2.
Qed.

Lemma trans_bind_inv {E B X Y} (t : ctree E B X) (k : X -> ctree E B Y)
  (u : @S E B Y) (l : @label E Y) :
  trans_alt l (Active (x <- t;; k x)) u ->
  (exists x, t ≅ Ret x /\ trans_alt l (Active (k x)) u)
  \/ (l = τ /\ exists t', trans_alt τ (Active t) (Active t')
      /\ u ⩸ (Active (x <- t';; k x)))
  \/ (l = ε /\ exists t', trans_alt ε (Active t) (Active t')
      /\ u ⩸ (Active (x <- t';; k x)))
  \/ (exists Z (e : E Z) (g : Z -> ctree E B X),
      l = ask e /\ trans_alt (ask e) (Active t) (Passive e g)
      /\ u ⩸ (Passive e (fun z => x <- g z;; k x))).
Proof.
  intros TR; unfold trans_alt in TR; cbn in TR; dependent destruction TR.
  - apply br_equ_bind in H as [(r & EQ1 & EQ2) | (k1 & EQ1 & EQ2)].
    + left; exists r; split; auto; eapply Transbr; eauto.
    + right; right; left; split; auto; exists (k1 x); split.
      * eapply Transbr; eauto; reflexivity.
      * constructor; rewrite H0; apply EQ2.
  - apply guard_equ_bind in H as [(r & EQ1 & EQ2) | (t1 & EQ1 & EQ2)].
    + left; exists r; split; auto; eapply Transguard; eauto.
    + right; right; left; split; auto; exists t1; split.
      * eapply Transguard; eauto; reflexivity.
      * constructor; rewrite H0, <- EQ2; reflexivity.
  - apply step_equ_bind in H as [(r & EQ1 & EQ2) | (t1 & EQ1 & EQ2)].
    + left; exists r; split; auto; eapply Transstep; eauto.
    + right; left; split; auto; exists t1; split.
      * eapply Transstep; eauto; reflexivity.
      * constructor; rewrite H0, <- EQ2; reflexivity.
  - apply vis_equ_bind in H as [(r & EQ1 & EQ2) | (k1 & EQ1 & EQ2)].
    + left; exists r; split; auto; econstructor; eauto.
    + right; right; right; exists X0, e, k1; split; auto; split.
      * econstructor; eauto.
      * constructor; intros a; apply EQ2.
  - apply ret_equ_bind in H as (r1 & EQ1 & EQ2).
    left; exists r1; split; auto; eapply Transval; eauto.
Qed.

Lemma trans_bind_inv_l {E B X Y} (t : ctree E B X) (k : X -> ctree E B Y)
  (u : @S E B Y) (l : @label E Y) :
  trans_alt l (Active (x <- t;; k x)) u ->
  exists (l' : @label E X) (t' : @S E B X), trans_alt l' (Active t) t'.
Proof.
  intros TR; apply trans_bind_inv in TR as [(y & EQ & _) | [(_ & t' & TR' & _) | [(_ & t' & TR' & _) | (Z & e & g & _ & TR' & _)]]]; eauto.
  exists (val y), (Active (Stuck : ctree E B X)); eapply Transval; eauto; reflexivity.
Qed.

Lemma is_stuck_bind {E B X Y} (t : ctree E B X) (k : X -> ctree E B Y) :
  is_stuck (Active t) -> is_stuck (Active (x <- t;; k x)).
Proof.
  intros ST l u TR; apply trans_bind_inv in TR as [(y & EQ & _) | [(_ & t' & TR' & _) | [(_ & t' & TR' & _) | (Z & e & g & _ & TR' & _)]]]; try (eapply ST; eauto; fail).
  eapply (ST (val y) (Active (Stuck : ctree E B X))); eapply Transval; eauto; reflexivity.
Qed.


(* [trans_val_invT] is no longer needed: with [label] now indexed by
   the return type [R], the equality [R = R'] it used to extract is
   enforced by typing. Callers that relied on it can simply drop the
   surrounding [apply trans_val_invT ... ; subst] step. *)


Lemma trans_trigger : forall {E B X Y} (e : E X) (k : X -> ctree E B Y),
    trans_alt (ask e) (trigger e >>= k) (β e k).
Proof.
  intros.
  unfold CTree.trigger.
  rewrite unfold_bind; cbn.
  setoid_rewrite bind_ret_l.
  constructor; auto.
Qed.

Lemma trans_trigger' : forall {E B X Y} (e : E X) (t : ctree E B Y),
    trans_alt (ask e) (trigger e;; t) (β e (fun _ => t)).
Proof.
  intros.
  unfold CTree.trigger.
  rewrite unfold_bind; cbn.
  setoid_rewrite bind_ret_l.
  constructor; auto.
Qed.

Lemma trans_trigger_inv : forall {E B X Y} (e : E X) (k : X -> ctree E B Y) l u,
    trans_alt l (trigger e >>= k) u ->
    Seq u (β e k) /\ l = ask e.
Proof.
  intros * TR.
  unfold trigger in TR.
  rewrite bind_vis in TR.
  apply trans_vis_inv' in TR as [EQ ->].
  setoid_rewrite bind_ret_l in EQ.
  split; auto.
Qed.


Create HintDb trans_alt.

#[global] Hint Constructors is_val : trans_alt.
#[global] Hint Resolve
  is_val_τ
  is_val_ask
  is_val_rcv : trans_alt.

Ltac etrans := eauto with trans_alt.
#[global] Arguments trans_alt : simpl never.


(*|
Structured relations on labels
|*)

Section build_rel.

  Context {E F : Type -> Type} {X Y : Type}.

  Record lrel :=
    {
      RR: rel X Y ;
      Rask: forall [X Y], E X -> F Y -> Prop ;
      Rrcv: forall [X Y] (e : E X) (f : F Y), X -> Y -> Prop ;
    }.
  
  Variant build_rel {RL : lrel} : hrel (label E X) (label F Y) :=
    | rel_τ   : build_rel τ τ
    | rel_ask {X Y} {e : E X} {f : F Y}
        (HR : Rask RL e f) :
      build_rel (ask e) (ask f)
    | rel_rcv {X Y} {e : E X} {f : F Y} x y
        (HR : Rrcv RL e f x y) :
      build_rel (rcv e x) (rcv f y)
    | rel_ret {x : X} {y : Y}:
      RR RL x y -> build_rel (val x) (val y).
  Arguments build_rel : clear implicits.
  
  Lemma build_rel_val RL x y :
    build_rel RL (val x) (val y) -> RR RL x y.
  Proof.
    now intros H; dependent induction H.
  Qed.
  
  Lemma build_rel_ask RL A B (e : E A) (f : F B) :
    build_rel RL (ask e) (ask f) -> Rask RL e f.
  Proof.
    now intros H; dependent induction H.
  Qed.
  
  Lemma build_rel_rcv RL A B (e : E A) (f : F B) a b : 
    build_rel RL (rcv e a) (rcv f b) -> Rrcv RL e f a b.
  Proof.
    now intros H; dependent induction H.
  Qed.

  Lemma build_rel_τ RL :
    build_rel RL τ τ.
  Proof.
    constructor.
  Qed.
  
End build_rel.

Arguments lrel : clear implicits.
Arguments build_rel {E F X Y} RL.
#[global] Hint Constructors build_rel : trans_alt.
Coercion build_rel : lrel >-> hrel.

Definition upd_rel {E F X Y X' Y'}
  (RL : lrel E F X Y)
  (SS : rel X' Y') : lrel E F X' Y' :=
  {|
    RR   := SS ;
    Rask := Rask RL ;
    Rrcv := Rrcv RL
  |}.

Variant eq1 {E} : forall [X Y : Type], rel (E X) (E Y) :=
  | Eq1 X (e : E X) : eq1 e e.
Variant eq2 {E} : forall [X Y : Type], E X -> E Y -> rel X Y :=
  | Eq2 X (e : E X) x : eq2 e e x x.
Hint Resolve Eq1 : trans_alt.
Hint Resolve Eq2 : trans_alt.

Definition Leq {E} {X : Type} : lrel E E X X :=
  {|
    RR   := eq ;
    Rask := eq1 ;
    Rrcv := eq2
  |}.

Definition Lvrel {E X Y} (RR : rel X Y) : lrel E E X Y :=
   {|
    RR   := RR ;
    Rask := eq1 ;
    Rrcv := eq2
  |}.

Ltac invL :=
  match goal with
  h: build_rel _ _ _ |- _ => dependent induction h
  | h: upd_rel _ _ _ _ |- _ => dependent induction h
  end.

Definition lequiv {E F X Y} : rel (lrel E F X Y) (lrel E F X Y) :=
  fun L1 L2 => RR L1 == RR L2 /\ Rask L1 == Rask L2 /\ Rrcv L1 == Rrcv L2.

#[global] Instance lequiv_equivalence {E F X Y} : Equivalence (@lequiv E F X Y).
Proof.
  constructor.
  - split3; auto.
  - intros ?? [? []]; split3; symmetry; auto.
  - intros ??? [? []] [? []]; split3; etransitivity; eauto.
Qed.

#[global] Instance lequiv_build_rel {E F X Y} : Proper (lequiv ==> weq) (@build_rel E F X Y).
Proof.
  cbn; intros L1 L2 [EQ1 [EQ2 EQ3]] l1 l2; split; intros H.
  - inv H; etrans.
    constructor; now apply EQ2.
    constructor; now apply EQ3.
    constructor; now apply EQ1.
  - inv H; etrans.
    constructor; now apply EQ2.
    constructor; now apply EQ3.
    constructor; now apply EQ1.
Qed.

#[global] Instance lequiv_build_rel' {E F X Y} : Proper (lequiv ==> eq ==> eq ==> iff) (@build_rel E F X Y).
Proof.
  now cbn; intros; subst; eapply lequiv_build_rel.
Qed.

Definition sub_lrel {E F X Y} (L L' : lrel E F X Y) : Prop :=
  RR L <= RR L' /\ Rask L <= Rask L' /\ Rrcv L <= Rrcv L'.

Lemma sub_lrel_subrel {E F X Y} :
  Proper (sub_lrel ==> leq) (@build_rel E F X Y).
Proof.
  intros L L' (SUB1 & SUB2 & SUB3) ?? HL.
  inv HL; etrans.
  now constructor; apply SUB2.
  now constructor; apply SUB3.
  now constructor; apply SUB1.
Qed.
 
Definition flipL {E F X Y} (L : lrel E F X Y) : lrel F E Y X :=
   {| RR := flip (RR L) ;
      Rask := fun X Y => flip (@Rask _ _ _ _ L Y X) ;
      Rrcv := fun X Y f e => flip (Rrcv L e f) |}.

Lemma flipL_flip {E F X Y} (L : lrel E F X Y) :
  build_rel (flipL L) == flip (build_rel L).
Proof.
  intros f e; split; cbn; intros []; constructor; auto.
Qed. 

Lemma flipL_flipL {E F X Y} (L : lrel E F X Y) :
  flipL (flipL L) = L.
Proof.
  now destruct L.
Qed.

Lemma lequiv_flipL_sym {E X} (L : lrel E E X X) {SL : Symmetric L} :
  lequiv (flipL L) L.
Proof.
  split3; cbn.
  - intros x y; split; intro H;
      apply build_rel_val, SL; now constructor.
  - intros A B e f; split; intro H;
      apply build_rel_ask, SL; now constructor.
  - intros A B e f a b; split; intro H;
      apply build_rel_rcv, SL; now constructor.
Qed.

Lemma lequiv_sub_lrel {E F X Y} (L L' : lrel E F X Y):
  sub_lrel L L' ->
  sub_lrel (flipL L) (flipL L').
Proof.
  intros (EQV & EQA & EQR).
  split3.
  now cbn; intros; apply EQV.
  now cbn; intros; apply EQA.
  now cbn; intros; apply EQR.
Qed.
 
Lemma lequiv_flipL {E F X Y} (L L' : lrel E F X Y):
  lequiv L L' ->
  lequiv (flipL L) (flipL L').
Proof.
  intros (EQV & EQA & EQR).
  split3.
  cbn; intros; apply EQV.
  cbn; intros; apply EQA.
  cbn; intros; apply EQR.
Qed.
  
Lemma equiv_flipL {E F X Y} (L L' : lrel E F X Y):
  build_rel L == build_rel L' ->
  build_rel (flipL L) == build_rel (flipL L').
Proof.
  intros EQ e f; specialize (EQ f e); cbn in *.
  split.
  - destruct EQ as [EQ _].
    intros FL; dependent induction FL; constructor.
    cbn in *.
     assert (HL: L (ask f) (ask e)) by (now constructor); apply EQ in HL; dependent induction HL; auto.
     assert (HL: L (rcv f y) (rcv e x)) by (now constructor); apply EQ in HL; dependent induction HL; auto.
     assert (HL: L (val y) (val x)) by (now constructor); apply EQ in HL; dependent induction HL; auto.
  - destruct EQ as [_ EQ].
    intros FL; dependent induction FL; constructor.
    cbn in *.
    assert (HL: L' (ask f) (ask e)) by (now constructor); apply EQ in HL; dependent induction HL; auto.
    assert (HL: L' (rcv f y) (rcv e x)) by (now constructor); apply EQ in HL; dependent induction HL; auto.
    assert (HL: L' (val y) (val x)) by (now constructor); apply EQ in HL; dependent induction HL; auto.
Qed.

#[global] Instance flipL_reflexive {E X} (L : lrel E E X X) {LR: Reflexive L} : Reflexive (flipL L).
Proof.
  intros ?.
  now apply flipL_flip.
Qed.
  
#[global] Instance flipL_symmetric {E X} (L : lrel E E X X) {LR: Symmetric L} : Symmetric (flipL L).
Proof.
  intros l l' HL.
  apply flipL_flip.
  apply (flipL_flip L) in HL.
  now apply LR.
Qed.

#[global] Instance flipL_transitive {E X} (L : lrel E E X X) {LR: Transitive L} : Transitive (flipL L).
Proof.
  intros l1 l2 l3 HL1 HL2.
  apply flipL_flip.
  apply (flipL_flip L) in HL1,HL2.
  etransitivity; eauto.
Qed. 

#[global] Instance flipL_equivalence {E X} (L : lrel E E X X) {LR: Equivalence L} : Equivalence (flipL L).
Proof.
  split; typeclasses eauto.
Qed.

Class ReflexiveL {E X} (L : lrel E E X X) : Prop :=
  reflL : forall l, l <> ε -> build_rel L l l.

#[global] Instance flipL_reflexiveL {E X} (L : lrel E E X X) {LR: ReflexiveL L} : ReflexiveL (flipL L).
Proof.
  intros l Hne.
  apply flipL_flip.
  now apply LR.
Qed.

#[global] Instance Leq_reflexiveL {E X} : ReflexiveL (@Leq E X).
Proof.
  intros [] Hne; try easy; constructor; cbn; auto with trans_alt.
Qed.

#[global] Instance build_rel_symmetric {E X L} `{Symmetric X L} : Symmetric (@build_rel E E X X (Lvrel L)).
Proof.
  intros l l' HL.
  unfold Lvrel in *.
  dependent induction HL; constructor; cbn in *.
  dependent induction HR; constructor.
  dependent induction HR; constructor.
  now apply H.
Qed.


Lemma flipL_Leq {E X}: lequiv (flipL (@Leq E X)) Leq.
Proof.
  cbv; intuition.
  all: dependent induction H; constructor.
Qed.

(* This one is a bit ugly: we will have proper instance to
   lift [lequiv] arguments of (bi)simulations to [weq] result.
   This instance does the last bit to allow the rewriting by [lequiv]
   directly.
 *)
#[global] Instance weq_body {E B X}:
  Proper (Coinduction.lattice.weq ==> eq ==> eq ==> eq ==> iff)
    (@body (rel (S E B X) (S E B X)) _).
Proof.
  cbn; intros R L EQ ?? <- ?? <- ?? <-; split; intros H.
  all:apply EQ; auto.
Qed.


#[global] Notation htrans l u v := (hrel_of (trans_alt l) u v) (only parsing).
 