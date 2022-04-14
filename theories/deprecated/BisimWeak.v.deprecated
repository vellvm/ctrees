(* begin hide *)
From Coq Require Import
     Program
     Setoid
     Morphisms
     RelationClasses.

From ITree Require Import
	Basics.HeterogeneousRelations.

From Coinduction Require Import
	coinduction rel tactics.

From CTree Require Import
	Utils CTrees Equ Bisim.

(* end hide *)

(** Weak bisimulation of ctrees

  The relation [wbisim] captures an equivalence over [ctrees] akin to the traditional
  weak bisimulation on process algebra.

  Given the specific treatment that external events (Vis nodes in the tree) receive,
  we explicitely distinguish two kind of challenges:

  - Internal challenges correspond to a non-empty sequence of tau steps, and must be
    matched by a possibly empty sequence of tau steps.
    Transposed to the [ctree] formalism, this corresponds to crawling through
    as many [Choice] nodes as desired, but chosing specifically a _visible_ [Choice]
    node to stop, and transit to any of the successor of this node.
    The opponent then needs to find a way to answer similarly, but with the additional
    possibility to stand still.

    Electing a final node and picking one of its branches ensures that at least
    one tau step is taken, and any number of such internal steps can be taken before.
    The distinction Visible/Invisible ensures we do not compare too finely the
    computations (i.e. (P + Q) + R cannot step to (P + R)).

  - External challenges correspond to a non-tau step surrounded by arbitrary amounts
    of tau steps.
    Transposed to the [ctree] formalism, this corresponds to:
    + crawling through as many [Choice] nodes as desired until a Ret or Vis node is
      reached, let us call [t'] this new state
    + having the opponent perform the same process up to a state [u']
    + if [t'] and [u'] are related pure computations, we are good
    + if [t'] and [u'] are Vis nodes of the same event, then they must match pointwise
      a new internal challenge

*)

Section Stepping.

  Context {E : Type -> Type} {R : Type}.

  (* External stepping
    We have the following invariant:
    external t u -> t = Ret x \/ t = Vis e k
  *)
  Inductive external_ : ctree' E R -> ctree' E R -> Prop :=

  | ExternalChoice {n} b (x : Fin.t n) k t :
    		external_ (observe (k x)) t ->
    		external_ (ChoiceF b n k) t

  | ExternalRet x :
    		external_ (RetF x) (RetF x)

  | ExternalVis {X} (e : E X) k k' :
    		(forall x, k x ≅ k' x) -> (* Because [external_] stops right there, we need to close explicitly up to [equ] if we want to be stable under it *)
    		external_ (VisF e k) (VisF e k').

  Definition external u v := external_ (observe u) (observe v).

  (* Internal stepping *)
  Inductive internal_ : ctree' E R -> ctree' E R -> Prop :=

  | InternalStep b {n} (x : Fin.t n) k t :
    		internal_ (observe (k x)) t ->
    		internal_ (ChoiceF b n k) t

  | InternalStop {n} k k' x :
    		k x ≅ k' x -> (* Because [internal_] stops right there, we need to close explicitly up to [equ] if we want to be stable under it *)
    		internal_ (ChoiceF true n k) (observe (k' x)).

  Definition internal u v := internal_ (observe u) (observe v).

  (* Reflexive closure of the internal stepping *)
  Variant refl_clo {X} (R : X -> X -> Prop): X -> X -> Prop :=
  | ReflCloRefl : forall u, refl_clo R u u
  | ReflCloRel  : forall u v, R u v -> refl_clo R u v.

  Definition internal_refl := refl_clo internal.

End Stepping.
#[global] Hint Constructors refl_clo: core.
#[global] Hint Unfold internal_refl : core.

Section wbisim.

  Context {E : Type -> Type} {R1 R2 : Type} (RR : R1 -> R2 -> Prop).

	(** * [matching]
	This relation captures the local challenge that two scheduled
	trees must solve. It corresponds from the more traditional
	bisimulation world to ensuring that they can take a small step
	emmitting the same event. *)

  Variant matchingL_ (bisim : ctree E R1 -> ctree E R2 -> Prop) :
    ctree' E R1 -> ctree' E R2 -> Prop :=
  | MatchLRet x y (RET : RR x y) :
     matchingL_ bisim (RetF x) (RetF y)
  | MatchLVis {X} (e : E X) k1 k2
     (RET : forall v t',
        internal_refl (k1 v) t' ->
        exists u', internal_refl (k2 v) u' /\ bisim t' u'):
     matchingL_ bisim (VisF e k1) (VisF e k2)
  .
  Hint Constructors matchingL_ : core.
  Definition matchingL bisim u v := matchingL_ bisim (observe u) (observe v).

  Variant matchingR_ (bisim : ctree E R1 -> ctree E R2 -> Prop) :
    ctree' E R1 -> ctree' E R2 -> Prop :=
  | MatchRRet x y (RET : RR x y) :
     matchingR_ bisim (RetF x) (RetF y)
  | MatchRVis {X} (e : E X) k1 k2
     (RET : forall v t',
        internal_refl (k2 v) t' ->
        exists u', internal_refl (k1 v) u' /\ bisim u' t'):
     matchingR_ bisim (VisF e k1) (VisF e k2)
  .
  Hint Constructors matchingR_ : core.

  (* step_vis : ctree E X -> {Y : Type & e : E Y & v : Y} -> ctree E X -> Prop
    Does this lead to exactly the same thing?
  *)
  Definition matchingR bisim u v := matchingR_ bisim (observe u) (observe v).

  Variant wbisimF (wbisim : ctree E R1 -> ctree E R2 -> Prop) :
    ctree E R1 -> ctree E R2 -> Prop :=

  | WBisim u t
            (SIMFI : forall u', internal u u' ->
              exists t', internal_refl t t' /\ wbisim u' t')
            (SIMBI : forall t', internal t t' ->
              exists u', internal_refl u u' /\ wbisim u' t')
            (SIMFE : forall u', external u u' ->
              exists t', external t t' /\ matchingL wbisim u' t')
            (SIMBE : forall t', external t t' ->
              exists u', external u u' /\ matchingR wbisim u' t')
               :
      wbisimF wbisim u t.

  Hint Constructors wbisimF: core.

  Lemma matchingL_mono u v sim sim'
              (IN : matchingL sim u v)
              (LE : sim <= sim') :
        matchingL sim' u v.
  Proof.
    unfold matchingL in *.
    inv IN; auto. constructor; intros. edestruct RET as (? & ? & ?); eauto.
    eexists; split; eauto.
    apply LE; auto.
  Qed.
  Hint Resolve matchingL_mono: core.

  Lemma matchingR_mono u v sim sim'
              (IN : matchingR sim u v)
              (LE : sim <= sim') :
        matchingR sim' u v.
  Proof.
    unfold matchingR in *.
    inv IN; auto. constructor; intros. edestruct RET as (? & ? & ?); eauto.
    eexists; split; eauto.
    apply LE; auto.
  Qed.
  Hint Resolve matchingR_mono: core.

  Program Definition fwbisim : mon (ctree E R1 -> ctree E R2 -> Prop) := {| body := wbisimF |}.
  Next Obligation.
   unfold pointwise_relation, impl, bisim_.
   intros ?? INC ?? EQ.
   constructor; inversion_clear EQ; intros.
  - edestruct SIMFI as (? & ? & ?); eauto.
  - edestruct SIMBI as (? & ? & ?); eauto.
  - edestruct SIMFE as (? & ? & ?); eauto.
  - edestruct SIMBE as (? & ? & ?); eauto.
  Qed.

End wbisim.

(** associated relation *)
Definition wbisim {E R} := (gfp (@fbisim E R R eq)).
(* Notation bisim := (gfp (fbisim eq)). *)

(** associated companions  *)
Notation T_bis RR  := (t (B (fwbisim RR))).
Notation t_bis RR  := (t (fwbisim RR)).
Notation bt_bis RR := (bt (fwbisim RR)).

Infix "≈" := wbisim (at level 70).
Notation "x ≊ y" := (t_bis eq _ x y) (at level 79).
Notation "x [≊] y" := (bt_bis eq _ x y) (at level 79).

Arguments wbisim _ _ _ _/.
#[global] Hint Constructors wbisimF: core.
#[global] Hint Constructors matchingL_: core.
#[global] Hint Constructors matchingR_: core.

Lemma external_active_ : forall {E R} (t u : ctree' E R),
  external_ t u ->
  active_ u.
Proof.
  intros * INTERN.
  now induction INTERN.
Qed.

Lemma external_active : forall {E R} (t u : ctree E R),
  external t u ->
  active u.
Proof.
  intros * SCHED; red.
  now induction SCHED.
Qed.

Lemma matchingL_active_refl {E R} (RR : R -> R -> Prop)
  (eq : ctree E R -> ctree E R -> Prop) (t : ctree E R)
  `{Reflexive _ RR} `{Reflexive _ eq} :
  active t ->
  matchingL RR eq t t.
Proof.
  unfold matchingL; intros []; eauto.
Qed.

Lemma matchingR_active_refl {E R} (RR : R -> R -> Prop)
  (eq : ctree E R -> ctree E R -> Prop) (t : ctree E R)
  `{Reflexive _ RR} `{Reflexive _ eq} :
  active t ->
  matchingR RR eq t t.
Proof.
  unfold matchingR; intros []; eauto.
Qed.

(*
Lemma matchingL_active_sym {E R} (RR : R -> R -> Prop)
   (eq : ctree E R -> ctree E R -> Prop) (t u : ctree E R)
   `{Symmetric _ RR} :
   matchingR RR eq t u ->
   matchingL RR (converse eq) u t.
Proof.
  unfold matchingL, matchingR; intros []; eauto.
  constructor; intros.
  edestruct RET as (? & ? & ?); eauto.
Qed.

Lemma matchingR_active_sym {E R} (RR : R -> R -> Prop)
   (eq : ctree E R -> ctree E R -> Prop) (t u : ctree E R)
   `{Symmetric _ RR} :
   matchingR RR eq t u ->
   matchingR RR (converse eq) u t.
Proof.
  unfold matchingR; intros []; eauto.
Qed. *)

Lemma matching_active_sym {E R} (RR : R -> R -> Prop)
   (eq : ctree E R -> ctree E R -> Prop) (t u : ctree' E R)
   `{Symmetric _ RR} :
   matching RR eq t u ->
   matching RR (converse eq) u t.
Proof.
  intros []; auto.
Qed.

Section wbisim_equiv.

	Variable (E : Type -> Type) (R : Type) (RR : R -> R -> Prop).
  Notation T  := (coinduction.T (fwbisim (E := E) RR)).
  Notation t  := (coinduction.t (fwbisim (E := E) RR)).
	Notation bt := (coinduction.bt (fwbisim (E := E) RR)).


  (** [eq] is a post-fixpoint, thus [const eq] is below [t] *)
	Lemma refl_t {RRR: Reflexive RR}: const eq <= t.
	Proof.
    apply leq_t.
		intros p t ? <-. cbn.
    constructor; eauto.
    - intros t' SCHED; eauto.
      exists t'; split; auto.
      apply matchingL_active_refl; auto.
      eapply external_active; eauto.
    - intros t' SCHED.
      exists t'; split; auto.
      apply matchingR_active_refl; auto.
      eapply external_active; eauto.
	Qed.

(*
	(** converse is compatible *)
	Lemma converse_t {RRS: Symmetric RR}: converse <= t.
	Proof.
		apply leq_t. intros S t u H; cbn in *.
    destruct H. constructor; eauto.
    - intros t' SCHED.
      edestruct SIMBE as (u' & SCHED' & MATCH'); eauto.
      edestruct SIMFE as (t'' & SCHED'' & MATCH''); eauto.
      exists u'; split; auto.
      apply matching_active_sym; auto.
    - intros u' SCHED.
      edestruct SIMF as (t' & SCHED' & MATCH'); eauto.
      exists t'; split; auto.
      apply matching_active_sym; auto.
	Qed.

	(** thus wbisimilarity, [t R], [b (t R)] and [T f R] are always reflexive relations *)
	#[global] Instance Reflexive_t `{Reflexive _ RR} S: Reflexive (t S).
	Proof.  intro. now apply (ft_t refl_t). Qed.
	#[global] Instance Reflexive_T `{Reflexive _ RR} f S: Reflexive (T f S).
	Proof.  intro. now apply (fT_T refl_t). Qed.
	#[global] Instance Reflexive_bt `{Reflexive _ RR} S: Reflexive (bt S).
	Proof.  intro. now apply (fbt_bt refl_t). Qed.

	(** thus wbisimilarity, [t R], [b (t R)] and [T f R] are always symmetric relations *)
	#[global] Instance Symmetric_t `{Symmetric _ RR} S: Symmetric (t S).
	Proof.  intros ???. now apply (ft_t converse_t). Qed.
	#[global] Instance Symmetric_T `{Symmetric _ RR} f S: Symmetric (T f S).
	Proof.  intros ???. now apply (fT_T converse_t). Qed.
	#[global] Instance Symmetric_bt `{Symmetric _ RR} S: Symmetric (bt S).
	Proof.  intros ???. now apply (fbt_bt converse_t). Qed.

End wbisim_equiv.

#[global] Instance wbisim_trans {E R}: Transitive (@wbisim E R).
Proof.
  red. unfold wbisim. coinduction S IH.
  intros t u v eq1 eq2.
  step in eq1; step in eq2.
  inversion eq1 as [? ? SIMF1 SIMB1]; subst.
  inversion eq2 as [? ? SIMF2 SIMB2]; subst.
  constructor.
  - intros u' SCHED.
    apply SIMF1 in SCHED as (ou' & SCHEDu & MATCHut).
    apply SIMF2 in SCHEDu as (ov' & SCHEDv & MATCHvu).
    exists ov'; split; auto.
    inv MATCHvu.
    + inv MATCHut; auto.
    + inv MATCHut.
      dependent induction H3.
      constructor.
      intros ?.
      eapply IH; eauto.
  - intros t' SCHED.
    apply SIMB2 in SCHED as (ou' & SCHEDu & MATCHut).
    apply SIMB1 in SCHEDu as (ov' & SCHEDv & MATCHvu).
    exists ov'; split; auto.
    inv MATCHvu.
    + inv MATCHut; auto.
    + inv MATCHut.
      dependent induction H2.
      constructor.
      intros ?.
      eapply IH; eauto.
Qed.

#[global] Instance equ_schedule {E X}:
	Proper (equ eq ==> equ eq ==> iff) (@schedule E X).
Proof.
  repeat red; intros * EQ1 * EQ2; split; intros SCHED.
  - step in EQ1; step in EQ2.
    unfold schedule in *.
    hinduction SCHED before X.
    + intros. inv EQ1. apply inj_pair2 in H2. subst.
      eapply SchedChoice with x1.
      apply IHSCHED. specialize (REL x1).
      step in REL. apply REL. auto.
    + intros. inv EQ1; inv EQ2; constructor.
    + intros. inv EQ1. inv EQ2. apply inj_pair2 in H2, H3, H5, H6. subst.
      constructor. intros.
      rewrite <- REL0, <- REL. auto.
  - step in EQ1; step in EQ2.
    unfold schedule in *.
    hinduction SCHED before X.
    + intros. inv EQ1. apply inj_pair2 in H3. subst.
      eapply SchedChoice with x.
      apply IHSCHED. specialize (REL x).
      step in REL. apply REL. auto.
    + intros. inv EQ1; inv EQ2; constructor.
    + intros. inv EQ1. inv EQ2. apply inj_pair2 in H3, H4, H6, H7. subst.
      constructor. intros.
      rewrite REL0, REL. auto.
Qed.

*)
