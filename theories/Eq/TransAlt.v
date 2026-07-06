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
     CTree Eq.Shallow Eq.Equ Eq.Epsilon.

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


  (* Definition ss'_gen {E F C D : Type -> Type} {X Y : Type}
    (L : rel (@label E) (@label F))
    (R Reps : rel (ctree E C X) (ctree F D Y))
    (t : ctree E C X) (u : ctree F D Y) :=

    (productive t ->
    (* t and u step together under labels related by L, assuming 
    t is "productive"; that is, not a Br *)
      forall l t', trans_alt l t t' ->
             exists l' u', trans_alt l' u u' /\ R t' u' /\ L l l')
    (* if t branches, u ε-steps to u'  *)
    /\ (forall Z (c : C Z) k,
          t ≅ Br c k ->
          forall x, exists u', epsilon u u' /\ Reps (k x) u')
    /\ (forall t',
          t ≅ Guard t' ->
          exists u', epsilon u u' /\ Reps t' u'). *)



Definition sss {R1 R2} RR := @SeqR E B _ _ (@equ E B R1 R2 RR). 

(* epsilon lifted through S *)

  Inductive epsilon_S : TransAlt.S E B R -> TransAlt.S E B R -> Prop := 
  | epsilon_id_AA t t' : epsilon t t' -> epsilon_S (Active t) (Active t')
  | epsilon_id_AP {X} t e k : forall x, epsilon t (k x) -> epsilon_S (Active t) (@Passive E B R X e k)
  | epsilon_id_PA {X} t e k : forall x, epsilon (k x) t -> epsilon_S (@Passive E B R X e k) (Active t)
  | epsilon_id_PP {X} e k1 k2 : forall x y, epsilon (k1 x) (k2 y) -> epsilon_S (@Passive E B R X e k1) (@Passive E B R X e k2)
  . 

(* question: equ constraints as before or direct constructors? *)
  Variant transR : label -> hrel S S :=

  | Transbr {X} (c : B X) t k u : 
    (* u reachable from (Br c k) *)
    t ≅ Br c k -> 
    forall x, u ≅ k x -> 
    (* forall x, epsilon_S (Active (k x)) u ->  *)
    transR ε (Active t) (Active u)
    
  | Transguard t t' u :
    t ≅ Guard t' ->   
    u ≅ t' ->   
    (* epsilon_S (Active t') u ->  *)
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

Ltac epsilon_congr := 
      repeat match goal with | [HE : epsilon_S (Active _) (Active _) |- _] => inv HE 
      | [HE : epsilon_S _ (Passive _ _) |- _] => dependent destruction HE 
      | [HE : epsilon_S (Passive _ _ ) _ |- _] => dependent destruction HE 
      | [|- epsilon_S _ _] => econstructor
      end; 
      match goal with 
      H: epsilon ?t1 ?t2 |- epsilon ?t3 ?t4 => 
       try match goal with [EQ13 : t1 ≅ t3 |- _] => rewrite <- EQ13; eauto end;  
       try match goal with [EQ31 : t3 ≅ t1 |- _] => rewrite EQ31; eauto end;  
       try match goal with [EQ24 : t2 ≅ t4 |- _] => rewrite <- EQ24; eauto end;  
       try match goal with [EQ42 : t4 ≅ t2 |- _] => rewrite EQ42; eauto end; 
       try match goal with [EQ : forall a, (?k a) ≅ ?g a |- epsilon _ (?g _)] => rewrite <- EQ; eauto end;  
       try match goal with [EQ : forall a, (?k a) ≅ ?g a |- epsilon _ (?k _)] => rewrite EQ; eauto end
    end. 
 

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

(* Class Respects_val {E F} (L : rel (@label E) (@label F)) := *)
(*   { respects_val: *)
(*     forall l l', *)
(*       L l l' -> *)
(*       is_val l <-> is_val l' }. *)

(* Class Respects_τ {E F} (L : rel (@label E) (@label F)) := *)
(*   { respects_τ: forall l l', *)
(*       L l l' -> *)
(*       l = τ <-> l' = τ }. *)

(* #[global] Instance Respects_val_eq A: @Respects_val A A eq. *)
(* split; intros; subst; reflexivity. *)
(* Defined. *)

(* #[global] Instance Respects_τ_eq A: @Respects_τ A A eq. *)
(* split; intros; subst; reflexivity. *)
(* Defined. *)

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

  (* Inductive trans_clo {R} (rel : label E R -> srel SS SS) : label E R -> srel SS SS := 
  | tc_base l t1 t2 : rel l t1 t2 -> trans_clo rel l t1 t2
  | tc_trans l1 l2 s1 s2 s3 : trans_clo l1 s1 s2 -> trans_clo l2 s2 s3 -> trans_alt  *)

  (* fixes: τ → ε *)
  (* this is no longer true with just (k x):  
  broadly, for these and all below, we need the transitive closure of 
  trans_alt. 
  
  *)

Ltac epop := unshelve (instantiate (1:=_)).
Ltac epop2 := unshelve (instantiate (2:=_)).

Ltac use e := unshelve (instantiate (1:=e)).


  (* Lemma trans_brS : forall {Y} (c : B Y) (k : _ -> ctree E B X) x,
      trans_alt ε (BrS c k) (k x).
  Proof.
    intros.
    econstructor. 
  Qed. *)

  (* Lemma trans_brS : forall {Y} (c : B Y) (k : _ -> ctree E B X) x,
      wtrans ε (BrS c k) (k x).
  Proof.
    (* has to be a better way to do this... *)
    intros.
    econstructor.
    use (Step (k x)). 
    econstructor. econstructor.
    use (α (BrS c k)).
    use O. 
    econstructor. reflexivity. 
    econstructor. reflexivity. econstructor. econstructor. reflexivity. 
    econstructor. use (1 : nat).  
    econstructor. econstructor. reflexivity. reflexivity. 
    econstructor. reflexivity. 
  Qed. *)

End backward.

#[global] Hint Resolve trans_br trans_guard  trans_step trans_ask trans_rcv trans_ret : core.

Section BackwardBounded.

  Context {E B : Type -> Type} {X : Type}.
  Context `{B2 -< B}.
  Context `{B3 -< B}.
  Context `{B4 -< B}.
  Variable (l : @label E X) (t t' u u' v v' w w' : ctree E B X).

  (* Lemma trans_brS21 :
    trans_alt ε (brS2 t u) t.
  Proof.
    intros.
    unfold brS2. 
    eapply trans_br. 
    trans_step.
  Qed.

  Lemma trans_brS22 :
    trans_alt τ (brS2 t u) u.
  Proof.
    intros.
    apply trans_br with false, trans_step.
  Qed. *)

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

  (* Lemma trans_brS31 :
    trans_alt τ (brS3 t u v) t.
  Proof.
    now apply trans_br with t31.
  Qed.

  Lemma trans_brS32 :
    trans_alt τ (brS3 t u v) u.
  Proof.
    now apply trans_br with t32.
  Qed.

  Lemma trans_brS33 :
    trans_alt τ (brS3 t u v) v.
  Proof.
    now apply trans_br with t33.
  Qed.

  Lemma trans_br31 x :
    trans_alt l t x ->
    trans_alt l (br3 t u v) x.
  Proof.
    intros * TR.
    now apply trans_br with t31.
  Qed.

  Lemma trans_br32 x :
    trans_alt l u x ->
    trans_alt l (br3 t u v) x.
  Proof.
    intros * TR.
    now apply trans_br with t32.
  Qed.

  Lemma trans_br33 x :
    trans_alt l v x ->
    trans_alt l (br3 t u v) x.
  Proof.
    intros * TR.
    now apply trans_br with t33.
  Qed.

  Lemma trans_brS41 :
    trans_alt τ (brS4 t u v w) t.
  Proof.
    eapply trans_br with t41; eauto.
  Qed.

  Lemma trans_brS42 :
    trans_alt τ (brS4 t u v w) u.
  Proof.
    eapply trans_br with t42; eauto.
  Qed.

  Lemma trans_brS43 :
    trans_alt τ (brS4 t u v w) v.
  Proof.
    eapply trans_br with t43; eauto.
  Qed.

  Lemma trans_brS44 :
    trans_alt τ (brS4 t u v w) w.
  Proof.
    eapply trans_br with t44; eauto.
  Qed.

  Lemma trans_br41 x :
    trans_alt l t x ->
    trans_alt l (br4 t u v w) x.
  Proof.
    intros * TR.
    eapply trans_br with t41; eauto.
  Qed.

  Lemma trans_br42 x :
    trans_alt l u x ->
    trans_alt l (br4 t u v w) x.
  Proof.
    intros * TR.
    eapply trans_br with t42; eauto.
  Qed.

  Lemma trans_br43 x :
    trans_alt l v x ->
    trans_alt l (br4 t u v w) x.
  Proof.
    intros * TR.
    eapply trans_br with t43; eauto.
  Qed.

  Lemma trans_br44 x :
    trans_alt l w x ->
    trans_alt l (br4 t u v w) x.
  Proof.
    intros * TR.
    eapply trans_br with t44; eauto.
  Qed. *)

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

  (* Lemma trans_br_inv : forall {Y} l (c : B Y) (k : _ -> ctree E B X) u,
      trans_alt l (Br c k) u ->
      exists n, trans_alt l (k n) u.
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
  Qed. *)

  (* Lemma trans_guard_inv : forall l (t : ctree E B X) u,
      trans_alt l (Guard t) u ->
      trans_alt l t u.
  Proof.
    intros * TR.
    inv TR; inv_equ.
    now rewrite H0.
  Qed. *)

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
(* 
  Lemma trans_brS_inv' : forall {Y} l (c : B Y) (k : _ -> ctree E B X) u,
      trans_alt l (BrS c k) u ->
      exists n, Seq u (α (k n)) /\ l = τ.
  Proof.
    intros * TR.
    eapply trans_br_inv in TR as [n ?].
    apply trans_step_inv' in H as [? ?].
    eauto.
  Qed.

  Lemma trans_brS_inv : forall {Y} l (c : B Y) k (u : ctree E B X),
      trans_alt l (BrS c k) u ->
      exists n, u ≅ k n /\ l = τ.
  Proof.
    intros * TR.
    apply trans_brS_inv' in TR as (? & H & ?); inv H; eauto.
  Qed.
 *)
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

  (* Lemma trans_br2_inv t' :
    trans_alt l (br2 t u) t' ->
    (trans_alt l t t' \/ trans_alt l u t').
  Proof.
    intros * TR; apply trans_br_inv in TR as [[] TR]; auto.
  Qed.

  Lemma trans_br3_inv t' :
    trans_alt l (br3 t u v) t' ->
    (trans_alt l t t' \/ trans_alt l u t' \/ trans_alt l v t').
  Proof.
    intros * TR; apply trans_br_inv in TR as [n TR].
    destruct n; auto.
  Qed.

  Lemma trans_br4_inv t' :
    trans_alt l (br4 t u v w) t' ->
    (trans_alt l t t' \/ trans_alt l u t' \/ trans_alt l v t' \/ trans_alt l w t').
  Proof.
    intros * TR; apply trans_br_inv in TR as [n TR].
    destruct n; auto.
  Qed.

  Lemma trans_brS2_inv (t': ctree _ _ _) :
    trans_alt l (brS2 t u) t' ->
    (l = τ /\ (t' ≅ t \/ t' ≅ u)).
  Proof.
    intros * TR; apply trans_brS_inv in TR as (? & TR & ->); split; auto.
    destruct x; auto.
  Qed.

  Lemma trans_brS2_inv' t' :
    trans_alt l (brS2 t u) t' ->
    (l = τ /\ (Seq t' t \/ Seq t' u)).
  Proof.
    intros * TR; apply trans_brS_inv' in TR as (? & TR & ->); split; auto.
    destruct x; auto.
  Qed.

  Lemma trans_brS3_inv (t': ctree _ _ _) :
    trans_alt l (brS3 t u v) t' ->
    (l = τ /\ (t' ≅ t \/ t' ≅ u \/ t' ≅ v)).
  Proof.
    intros * TR; apply trans_brS_inv in TR as (? & TR & ->); split; auto.
    destruct x; auto.
  Qed.

  Lemma trans_brS3_inv' t' :
    trans_alt l (brS3 t u v) t' ->
    (l = τ /\ (Seq t' t \/ Seq t' u \/ Seq t' v)).
  Proof.
    intros * TR; apply trans_brS_inv' in TR as (? & TR & ->); split; auto.
    destruct x; auto.
  Qed.

  Lemma trans_brS4_inv' t' :
    trans_alt l (brS4 t u v w) t' ->
    (l = τ /\ (Seq t' t \/ Seq t' u \/ Seq t' v \/ Seq t' w)).
  Proof.
    intros * TR; apply trans_brS_inv' in TR as (? & TR & ->); split; auto.
    destruct x; auto.
  Qed. *)

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
  - intuition; try (eapply trans_ret in step; now apply step).
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
    inv H; intuition.
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

  (* Lemma br_void_is_stuck (c : B void) (k : void -> _) :
    is_stuck (Br c k).
  Proof.
    red. intros * ?.
    apply trans_br_inv in H as [[] ?].
  Qed. *)

  (* Lemma br_fin0_is_stuck (c : B (fin 0)) (k : fin 0 -> _) :
    is_stuck (Br c k).
  Proof.
    red. intros * ?. 
    apply trans_br_inv in H as [? ?].
    now apply case0.
  Qed. *)

  (* Lemma spin_gen_is_stuck {Y} (x : B Y) :
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
  Qed. *)

  (* Lemma spin_is_stuck :
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
  Qed. *)

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
   
  (* Lemma brS_not_stuck {Y} (b : B Y) (k : Y -> ctree _ _ _):
    (exists x, not_stuck (k x)) ->
    not_stuck (BrS b k).
  Proof.  
    intros (y & l' & t' & TR).
    red.
    exists ε, (α k y).
  Qed. *)
  
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
    intuition.
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

(*|
Forward and backward rules for [wtrans] w.r.t. [bind]
-----------------------------------------------------
|*)

(* Lemma etrans_bind_inv {E B X Y} (t : ctree E B X) (k : X -> ctree E B Y) u l :
  etrans l (t >>= k) u ->
  (l = τ /\ exists t', etrans τ t (α t') /\ Seq u (t' >>= k)) \/
  (exists Z (e : E Z), l = ask e /\
   exists (g : Z -> ctree E B X), trans_alt (ask e) t (β e g) /\ Seq u (β e (fun x => g x >>= k))) \/
  (exists (x : X), trans_alt (val x) t Stuck /\ etrans l (k x) u).
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
  (trans_alt τ)^* (t >>= k) u ->
  (exists t', (trans_alt τ)^* t (α t') /\ Seq u (t' >>= k)) \/
  (exists (x : X), wtrans (val x) t Stuck /\ (trans_alt τ)^* (k x) u).
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
Qed. *)


(*|
Things are a bit ugly with [wtrans], we end up with three cases:
- the reduction entirely takes place in the prefix
- the computation spills over the continuation, with the label taking place
in the continuation
- the computation splills over the continuation, with the label taking place
in the prefix. This is a bit more annoying to express: we cannot necessarily
[wtrans l] all the way to a [Ret] as the end of the computation might contain
just before the [Ret] some invisible br nodes. We therefore have to introduce
the last visible state reached by [wtrans] and add a [trans_alt (val _)] afterward.
|*)
(* Lemma wtrans_bind_inv {E B X Y} (t : ctree E B X) (k : X -> ctree E B Y) u l :
  wtrans l (t >>= k) u ->
  (l = τ /\ exists t', wtrans τ t (α t') /\ Seq u (t' >>= k)) \/
  (exists Y (e : E Y), l = ask e /\ exists g, wtrans (ask e) t (β e g) /\ Seq u (β e (fun x => g x >>= k))) \/
  (exists (x : X), wtrans (val x) t Stuck /\ wtrans l (k x) u) \/
  (exists (x : X) s, l = τ /\ wtrans τ t s /\ trans_alt (val x) s Stuck /\ wtrans τ (k x) u) \/
  (exists Y (e : E Y) (x : X) s, l = ask e /\ wtrans (ask e) t s /\ trans_alt (val x) s Stuck /\ wtrans τ (k x) u).
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
      * right; right; right; left.
        apply wtrans_val_inv in TR3 as (u3 & TR2' & TR2'').
        exists x, u3.
        repeat split; auto.
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

Lemma trans_τ_inv {E B X} t u :
  @trans_alt E B X τ t u ->
  exists u', Seq u (α u').
Proof.
  intros TR; cbn in TR; dependent induction TR.
  - edestruct IHTR; auto.
    inv H1; eauto.
  - edestruct IHTR; eauto.
  - eauto.
Qed.
 
Lemma etrans_τ_inv {E B X} (t : ctree E B X) u :
  etrans τ (α t) u ->
  exists u', Seq u (α u').
Proof.
  intros [TR | TR].
  - eapply trans_τ_inv; eauto.
  - cbn in *; exists t; rewrite TR; auto.
Qed.

Lemma trans_ask_inv {E B X Y} t (e : E Y) u :
  @trans_alt E B X (ask e) t u ->
  exists g, Seq u (β e g).
Proof.
  intros TR; cbn in TR; dependent induction TR.
  - edestruct IHTR; auto.
    dependent induction H1; eauto.
  - edestruct IHTR; eauto.
  - eauto.
Qed.
  
Lemma etrans_ask_inv {E B X Y} (t : ctree E B X) (e : E Y) u :
  etrans (ask e) (α t) u ->
  exists g, Seq u (β e g).
Proof.
  intros TR; eapply trans_ask_inv; eauto.
Qed.

Lemma transs_τ_active {E B X} (t : ctree E B X) u :
  (trans_alt τ)^* (α t) u ->
  exists u', Seq u (α u').
Proof.
  intros [n TR]. revert t TR.
  induction n as [| n IH]; intros t TR.
  - cbn in TR; exists t; symmetry; eauto.
  - destruct TR as [? TR TRs].
    eapply trans_τ_inv in TR as [u' EQ].
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
  (trans_alt τ)^* t u ->
  (trans_alt τ)^* (t >>= k) (u >>= k).
Proof.
  intros [n TR].
  revert t u TR.
  induction n as [| n IH].
  - cbn; intros; exists 0%nat; cbn; inv TR; rewrite EQ; auto.
  - intros t u [v TR1 TR2].
    pose proof trans_τ_inv TR1 as (v' & EQv).
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
  pose proof etrans_τ_inv TR2 as (y & EQy).
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
  pose proof etrans_ask_inv TR2 as (y & EQy).
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
  (exists v, trans_alt l t v /\ wtrans τ v u) \/
  (exists v, trans_alt τ t v /\ wtrans l v u).
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
  trans_alt (rcv e y) u v ->
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

Lemma trans_rcv_active_inv {E B X Y} (e : E Y) (y : Y) (u : ctree E B X) v :
  trans_alt (rcv e y) (α u) v ->
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
  (l = ask e /\ exists v h, wtrans τ t (α v) /\ trans_alt (ask e) v (β e h) /\ Seq (β e h) (β e g)).  
Proof.
  intros [t2 [t1 TR1 TR2] TR3].
  apply wtrans_τ in TR1.
  pose proof wtrans_τ_active TR1 as [? EQ1].
  rewrite EQ1 in *. 
  destruct l.
  - pose proof etrans_τ_inv TR2 as [? EQ2].
    rewrite EQ2 in *.
    apply wtrans_τ in TR3.
    pose proof wtrans_τ_active TR3 as [? EQ3].
    inv EQ3.
  - cbn in TR2.
    pose proof trans_ask_inv TR2 as [h EQ].
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
    eapply trans_rcv_active_inv; eauto.
  - exfalso.
    apply trans_val_inv' in TR2.
    rewrite TR2 in TR3.
    apply wtrans_τ in TR3.
    apply wtrans_stuck in TR3 as [_ EQ].
    inv EQ.
Qed.  

Lemma pwtrans_case {E B X} (t u : ctree E B X) l:
  pwtrans l t u ->
  (exists v, trans_alt l t v /\ wtrans τ v u) \/ (exists v, trans_alt τ t v /\ wtrans l v u).
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
Qed. *)

(*|
It's a bit annoying that we need two cases in this lemma, but if
[t = Guard (Ret x)] and [u = k x], we can process the [Guard] node
by taking the [Ret] in the prefix, but we cannot process it to
reach [u] in the bound computation.
|*)

(* Lemma wtrans_bind_r_τ {E B X Y} (t : ctree E B X) (k : X -> ctree E B Y) (u : ctree E B Y) x :
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
    pose proof trans_τ_inv H as [? EQ].
    rewrite EQ in H,H0.
    eapply trans_bind_r in H; [| eauto].
    eapply wcons; eauto.
  - right; eapply wconss; [apply TR1 | clear t TR1].
    rewrite EQa in TR1'.
    pose proof trans_τ_inv TR as [? EQ].
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
  - pose proof trans_τ_inv TR as [? EQ].
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
  - pose proof trans_τ_inv TRv as [? EQ].
    rewrite EQ in *; clear v0 EQ. 
    eapply wcons.
    eapply trans_bind_r; eauto.
    eapply wconss; eauto.
    now apply trans_wtrans.
  - pose proof trans_τ_inv TRv as [? EQ].
    rewrite EQ in *; clear v0 EQ. 
    eapply wcons.
    eapply trans_bind_r; eauto.
    eapply wconss; eauto.
    now apply trans_wtrans.
Qed.     *)

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

(* [trans_val_invT] is no longer needed: with [label] now indexed by
   the return type [R], the equality [R = R'] it used to extract is
   enforced by typing. Callers that relied on it can simply drop the
   surrounding [apply trans_val_invT ... ; subst] step. *)

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
(*       apply transs_is_stuck_inv in TR1''; [| apply stuck_is_stuck]. *)
(*       rewrite <- TR1'' in TR2. *)
(*       apply wtrans_is_stuck_inv in TR2; [| apply stuck_is_stuck]. *)
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

(* Lemma trans_branch :
  forall {E B : Type -> Type} {X : Type} {Y : Type}
    [l : label E X] [t t' : ctree E B X] (c : B Y) (k : Y -> ctree E B X) (x : Y),
    trans_alt l (k x) t' ->
    trans_alt l (branch c >>= k) t'.
Proof.
  intros.
  rewrite bind_branch.
  eapply trans_br; eauto.
Qed. *)

Create HintDb trans_alt.
(* #[global] Hint Resolve
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
  : trans_alt. *)

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

#[global] Instance build_rel_symmetric {E X L} `{Symmetric X L} : Symmetric (@build_rel E E X X (Lvrel L)).
Proof.
  intros l l' HL.
  unfold Lvrel in *.
  dependent induction HL; constructor; cbn in *.
  dependent induction HR; constructor.
  dependent induction HR; constructor.
  now apply H.
Qed.

(* #[global] Instance Leq_equiv {E X} : Equivalence (build_rel (@Leq E X)).
Proof.
  split.
  - intros []; try now constructor. 
  - intros ?? H.
    inv H; try now constructor.
    cbn in HR.
    dependent induction HR; now constructor.
    dependent induction HR; now constructor.
  - intros ??? H1 H2.
    dependent induction H1; dependent induction H2; try now constructor.
    dependent induction HR; dependent induction HR0; now constructor.
    dependent induction HR; dependent induction HR0; now constructor.
    cbn in *; subst; now constructor.
Qed.   *)

(* Lemma Leq_eq {E X}: build_rel (@Leq E X) == eq.
Proof.
  split; [| intros <-; reflexivity].
  intros []; auto.
  dependent induction HR; auto.
  dependent induction HR; auto.
  cbn in H; subst; auto.
Qed. *)

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

(* Ltac simpL :=
  repeat match goal with
    | h : build_rel (flipL _) _ _ |- _ => rewrite flipL_Leq in h
    | h : build_rel Leq _ _ |- _ => apply Leq_eq in h
    | |- context[flipL Leq] => rewrite flipL_Leq
    end; subst. *)

(* (*| *)
(* [wf_val] states that a [label] is well-formed: *)
(* if it is a [val] it should be of the right type. *)
(* |*) *)
(* Definition wf_val {E} X l := forall Y (v : Y), l = @val E Y v -> X = Y. *)

(* Lemma wf_val_val {E} X (v : X) : wf_val X (@val E X v). *)
(* Proof. *)
(*   red. intros. apply val_eq_invT in H. assumption. *)
(* Qed. *)

(* Lemma wf_val_nonval {E} X (l : @label E) : ~is_val l -> wf_val X l. *)
(* Proof. *)
(*   red. intros. subst. exfalso. apply H. constructor. *)
(* Qed. *)

(* Lemma wf_val_trans {E B X} (l : @label E) t t' : *)
(*   @trans_alt E B X l t t' -> wf_val X l. *)
(* Proof. *)
(*   red. intros. subst. *)
(*   now apply trans_val_invT in H. *)
(* Qed. *)

(* Lemma wf_val_is_val_inv : forall {E} X (l : @label E), *)
(*   is_val l -> *)
(*   wf_val (E := E) X l -> *)
(*   exists (x : X), l = val x. *)
(* Proof. *)
(*   intros. *)
(*   destruct H. red in H0. *)
(*   specialize (H0 X0 x eq_refl). subst. eauto. *)
(* Qed. *)

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
(*     (trans_alt τ ⊔ srtrans)^* ⋅ trans_alt (obs (inl1 l) x) ⋅ (trans_alt τ ⊔ srtrans)^*. *)

(*   (*| Obs transition on the right, ignores left transitions and [τ] |*) *)
(*   Definition rtrans {X}(r: R X)(x: X): srel SS SS := *)
(*     (trans_alt τ ⊔ sltrans)^* ⋅ trans_alt (obs (inr1 r) x) ⋅ (trans_alt τ ⊔ sltrans)^*. *)

(* End Coproduct. *)

#[global] Notation htrans l u v := (hrel_of (trans_alt l) u v) (only parsing).

(*|
[refine_transition H]: given a transition whose concrete label is known,
derive information on the active/passive status of its destination state.

Currently very partial
|*)
(* Ltac refine_trans_in h :=
  match type of h with
  | htrans τ _ _ =>
      let u  := fresh "u" in
      let EQ := fresh "EQ" in
      pose proof trans_τ_inv h as [u EQ];
      rewrite EQ in *;
      match type of EQ with
      | Seq ?a _ => try clear a EQ
      end
  | htrans (ask ?e) _ _ =>
      let u  := fresh "u" in
      let EQ := fresh "EQ" in
      pose proof trans_ask_inv h as [u EQ];
      rewrite EQ in *;
      match type of EQ with
      | Seq ?a _ => try clear a EQ
      end
  end. *)

(* Tactic Notation "refine_trans" :=
  match goal with
  | h : htrans _ _ _ |- _ => refine_trans_in h
  end.
Tactic Notation "refine_trans" "in" ident(h) := refine_trans_in h. *)

(*|
[inv_trans] is an helper tactic to automatically
invert hypotheses involving [trans_alt].
|*)

Ltac inv_label_eq EQl :=
  match type of EQl with
    | τ        = τ     =>
        clear EQl
    | val _   = val _ =>
        apply val_eq_inv in EQl; try (inversion EQl; fail)
    | ask _   = ask _ =>
        let EQt := fresh "EQt" in
        let EQe := fresh "EQe" in
        apply ask_invT in EQl as EQt;
        symmetry in EQt;
        (* subst_hyp_in EQt h; *)
        apply ask_inv in EQl as EQe;
        try (inversion EQe; fail)
    | rcv _ _ = rcv _ _ =>
        let EQt := fresh "EQt" in
        let EQt := fresh "EQv" in
        let EQe := fresh "EQe" in
        apply rcv_invT in EQl as EQt;
        symmetry in EQt;
        (* subst_hyp_in EQt h; *)
        apply rcv_inv in EQl as [EQe EQv];
        try (inversion EQe; inversion EQv; fail)
    | _ => subst; try now inv EQl
  end.

(* Ltac inv_trans_one :=
  match goal with
  (* Ret *)
  | h : htrans _ (α Ret _) _ |- _ =>
      let EQl := fresh "EQl" in
      let EQ  := fresh "EQ" in
      (apply trans_ret_inv in h as [EQ EQl] || apply trans_ret_inv' in h as [EQ EQl]);
      try rewrite EQ in *;
      inv_label_eq EQl

  (* Step *)
  | h : htrans _ (α Step _) _ |- _ =>
      let EQl := fresh "EQl" in
      let EQ  := fresh "EQ" in
      apply trans_step_inv' in h as (EQ & EQl);
      try rewrite EQ in *;
      inv_label_eq EQl
 
  (* Br *)
  | h : htrans _ (α Br _ _) _ |- _ =>
      let TR := fresh "TR" in
      apply trans_br_inv in h as (?n & TR)
 
  | h : htrans _ (α br2 _ _) _ |- _ =>
      let TR := fresh "TR" in
      apply trans_br2_inv in h as [TR | TR]

  | h : htrans _ (α br3 _ _ _) _ |- _ =>
      let TR := fresh "TR" in
      apply trans_br3_inv in h as [TR | [TR | TR]]

  | h : htrans _ (α br4 _ _ _ _) _ |- _ =>
      let TR := fresh "TR" in
      apply trans_br4_inv in h as [TR | [TR | [TR | TR]]]

  | h : htrans _ (α brS2 _ _) _ |- _ =>
      let EQ := fresh "EQ" in
      apply trans_brS2_inv' in h as (-> & [EQ | EQ])

   | h : htrans _ (α brS3 _ _ _) _ |- _ =>
      let EQ := fresh "EQ" in
      apply trans_brS3_inv' in h as (-> & [EQ | [EQ | EQ]])
 
   | h : htrans _ (α brS4 _ _ _ _) _ |- _ =>
      let EQ := fresh "EQ" in
      apply trans_brS4_inv' in h as (-> & [EQ | [EQ | [EQ | EQ]]])
                                       
  (* Guard *)
  | h : htrans _ (α Guard _) _ |- _ =>
      apply trans_guard_inv in h
                                 
  (* Vis *)
  | h : htrans _ (α (Vis ?e ?k)) _ |- _ =>
      let EQl := fresh "EQl" in
      let EQ  := fresh "EQ" in
      apply trans_vis_inv' in h as (EQ & EQl);
      try rewrite EQ in *;
      inv_label_eq EQl

 (* Stuck *)
  | h : htrans _ (α Stuck) _ |- _ =>
      exfalso; eapply trans_stuck_inv; now apply h
 
  (* Passive *)
  | h : htrans _ (β ?e ?k) _ |- _ =>
      let EQl := fresh "EQl" in
      let EQ  := fresh "EQ" in
      apply trans_passive_inv' in h as (?x & EQ & EQl);
      try rewrite EQ in *;
      inv_label_eq EQl

  end.

Ltac inv_trans := repeat (inv_trans_one). *)

Ltac use_steps n := 
lazymatch goal with 
|- context [(str _)] => 
  repeat red; 
  
  repeat match goal with 
  
  (* ^* case *)
  | |- exists2 _, _ & _ => eexists; repeat red 
  (* base case: just ^* *)
  | |- exists n : nat, _ =>
  exists (n : nat); 
  cbn; try solve [reflexivity] end
  end. 

  (* break iter *)
  (* Unset Printing Notations.  *)
Lemma trans_star_self {E B R} (x : SS) l: (@trans_alt E B R l)^* x x.
Proof. use_steps O. Qed.   

Lemma trans_star_l {E B R} (x y : SS) l1 l2 : 
trans_alt l2 x y -> 
((@trans_alt E B R l1)^* ⋅ trans_alt l2) x y.
Proof. intros. use_steps O. assumption. Qed. 

Tactic Notation "use" ident(n) "steps" := use_steps n.
 