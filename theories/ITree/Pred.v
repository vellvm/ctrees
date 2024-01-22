(** * Leaves of an Interaction Tree *)

(* begin hide *)
From CTree Require Import
  Utils.Utils
  Logic.Kripke
  Events.Core
  ITree.Core
  ITree.Interp
  ITree.Equ.

From Coinduction Require Import coinduction.
From Coq Require Import Morphisms Basics Program.Equality.

Import Itree.
Import ITreeNotations.
(* end hide *)

(** ** Leaves of itrees *)

(** The [Leaf a t] predicate expresses that [t] has a [Ret] leaf with
    value [a].

    We provide the elementary structural lemmas to work with this
    predicate, and one main useful result relying on [Leaf]: the
    up-to bind closure [eqit_bind_clo] can be refined such that
    continuations need only be related over the leaves of the
    first operand of [bind].
    *)
Generalizable All Variables.

Inductive ELeaf `{Encode E} {A: Type} (R: A -> Prop) : itree E A -> Prop :=
 | ELeafRet: forall a t,
     observe t = RetF a ->
     R a ->
     ELeaf R t
 | ELeafTau: forall t u,
   observe t = TauF u ->
   ELeaf R u ->
   ELeaf R t
 | ELeafVis: forall (e: E) t k (x: encode e),
   observe t = VisF e k ->
   ELeaf R (k x) ->
   ELeaf R t.
#[global] Hint Constructors ELeaf : itree.

(* Codomain (image) is a subset of [R] *)
Inductive ALeaf `{Encode E} {A: Type} (R: A -> Prop) : itree E A -> Prop :=
 | ALeafRet: forall a t,
     observe t = RetF a ->
     R a ->
     ALeaf R t
 | ALeafTau: forall t u,
     observe t = TauF u ->
     ALeaf R u ->
     ALeaf R t
 | ALeafVis: forall (e: E) t k,
     observe t = VisF e k ->
     (forall (x: encode e), ALeaf R (k x)) ->
     ALeaf R t.
#[global] Hint Constructors ALeaf : itree.

(* Any countable number of [tau] away from a [Ret x], such that [R x],
   Induction lemma for [t |= EF done R] and [t |= AF done R] *)
Inductive EpsilonRet `{Encode E} {A: Type}(R: A -> Prop): itree E A -> Prop :=
| EpsilonRetRet: forall a t,
    observe t = RetF a ->
    R a ->
    EpsilonRet R t
| EpsilonRetTau: forall t u,
    observe t = TauF u ->
    EpsilonRet R u ->
    EpsilonRet R t.
#[global] Hint Constructors EpsilonRet: itree.

(* Induction lemma for [t |= AF finish R] *)
Inductive AFinish `{Encode E} {A: Type}(R: forall (e: E), encode e -> A -> Prop): itree E A -> Prop :=
| AFinishVisBase: forall t e k,    
    observe t = VisF e k ->
    (forall (v: encode e), EpsilonRet (R e v) (k v)) ->
    AFinish R t
| AFinishVisStep: forall t e k,
    observe t = VisF e k ->
    (forall (v: encode e), AFinish R (k v)) ->
    AFinish R t
| AFinishTauStep: forall t u,
    observe t = TauF u ->
    AFinish R u ->
    AFinish R t.
#[global] Hint Constructors AFinish: itree.

(*| [t |= AF φ] is semantic and requires double induction, on [AF] and inside it, in
  [ktrans]. Attempt to simplify to one induction with [AFInd] |*)
Inductive AFInd `{Encode E} {X}(φ: itree E X -> World E -> Prop): itree E X -> World E -> Prop :=
| AFIndBase: forall (t: itree E X) (w: World E),
    φ t w ->
    AFInd φ t w
| AFIndFinishBase: forall t (e: E) (v: encode e) (x: X),
    observe t = RetF x ->
    φ Itree.stuck (Finish e v x) ->
    AFInd φ t (Obs e v)
| AFIndDoneBase: forall t (x: X),
    observe t = RetF x ->
    φ Itree.stuck (Done x) ->
    AFInd φ t Pure
|AFIndVisStep: forall (t: itree E X) w e k,
    observe t = VisF e k ->
    (forall (v: encode e), AFInd φ (k v) (Obs e v)) ->
    AFInd φ t w
| AFIndTauStep: forall t u w,
    observe t = TauF u ->
    AFInd φ u w ->
    AFInd φ t w.
              
Local Open Scope itree_scope.

(** Smart constructors *)
Lemma eleaf_ret : forall `{Encode E} X (R: X -> Prop) (a: X),
    R a <->
    ELeaf R (Ret a).
Proof.
  split; intros.
  - econstructor; eauto.
  - inv H0; inv H1; auto.
Qed.

Lemma aleaf_ret : forall `{Encode E} X (R: X -> Prop) (a: X),
    R a <->
    ALeaf R (Ret a).
Proof.
  split; intros.
  - econstructor; eauto.
  - inv H0; inv H1; auto.
Qed.

Lemma epsilon_ret : forall `{Encode E} X (R: X -> Prop) (a: X),
    R a <->
    ALeaf R (Ret a).
Proof.
  split; intros.
  - econstructor; eauto.
  - inv H0; inv H1; auto.
Qed.

Lemma eleaf_tau : forall `{Encode E} X (R: X -> Prop) (a: X) (t: itree E X),
  ELeaf R t <->
  ELeaf R (Tau t).
Proof.
  split; intros.
  - econstructor; [reflexivity | eauto].
  - inv H0; inv H1; auto.
Qed.

Lemma aleaf_tau : forall `{Encode E} X (R: X -> Prop) (a: X) (t: itree E X),
  ALeaf R t <->
  ALeaf R (Tau t).
Proof.
  split; intros.
  - econstructor; [reflexivity | eauto].
  - inv H0; inv H1; auto.
Qed.

Lemma eleaf_vis : forall {X Y: Type} `{Encode E} (e : E) (k : _ -> itree E Y) (R: Y -> Prop) x,
  ELeaf R (k x) ->
  ELeaf R (Vis e k).
Proof.
  intros; eapply ELeafVis; cbn; [reflexivity | eauto].
Qed.

Lemma aleaf_vis : forall {X Y: Type} `{Encode E} (e : E) (k : _ -> itree E Y) (R: Y -> Prop),
  (forall (x: encode e), ALeaf R (k x)) ->
  ALeaf R (Vis e k).
Proof.
  intros; eapply ALeafVis; cbn; [reflexivity | eauto].
Qed.

Lemma eleaf_vis_inv : forall `{Encode E} Y (e : E) (k : encode e -> itree E Y) (R: Y -> Prop),
  ELeaf R (Vis e k) ->
  exists x, ELeaf R (k x).
Proof.
  intros * IN *; inv IN; cbn in *; try congruence.
  dependent destruction H0.
  now (exists x).
Qed.

Lemma aleaf_vis_inv : forall `{Encode E} Y (e : E) (k : encode e -> itree E Y) (R: Y -> Prop) x,
  ALeaf R (Vis e k) ->
  ALeaf R (k x).
Proof.
  intros * IN *; inv IN; cbn in *; try congruence.
  dependent destruction H0; eauto.  
Qed.

#[global] Instance aleaf_equ `{Encode E} {X}:
  Proper (pointwise_relation X eq ==> equ eq (X2:=X) ==> iff) (@ALeaf E _ X).
Proof.
  unfold Proper, respectful, pointwise_relation; intros; subst.
  split; intro Hind.
  - generalize dependent y0.
    generalize dependent y.
    induction Hind; intros y Heqr t' Heqt;
      step in Heqt; cbn in Heqt; dependent destruction Heqt; try congruence. 
    + apply ALeafRet with y0; congruence.
    + eapply ALeafTau.
      * symmetry; apply x.
      * apply IHHind; auto.
        rewrite <- H1.
        rewrite <- x1 in H0.
        inv H0; reflexivity.
    + eapply ALeafVis. 
      * symmetry; apply x.
      * intros.
        rewrite H0 in x1; dependent destruction x1.
        eapply H2; auto.
  - generalize dependent x0.
    generalize dependent x.
    induction Hind; intros x Heqr t' Heqt;
      step in Heqt; cbn in Heqt; dependent destruction Heqt; try congruence. 
    + apply ALeafRet with y0; congruence.
    + eapply ALeafTau.
      * symmetry; apply x1.
      * apply IHHind; auto.
        rewrite H1.
        rewrite <- x in H0.
        inv H0; reflexivity.
    + eapply ALeafVis. 
      * symmetry; apply x1.
      * intros.
        rewrite H0 in x; dependent destruction x.
        eapply H2; auto.
Qed.

Lemma ALeaf_stuck: forall `{Encode E} X R,
    ~ ALeaf R (stuck: itree E X).
Proof.
  intros * Hcontra.
  dependent induction Hcontra; eauto.
Qed.

