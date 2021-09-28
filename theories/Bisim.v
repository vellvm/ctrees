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
	Utils CTrees Equ.

(* end hide *)

Section Schedule.

	(* We do not wish to observe internal non-deterministic choices.
		We therefore want to consider states, i.e. ctrees, that can
		be reached after a finite number of internal decisions, and
		are such that they are ready to expose an observation: their
		head constructor is either a Ret or a Vis.
		*)

  Context {E : Type -> Type} {R : Type}.

	(* It might be better to work with the usual pattern of tying
	  the knot afterwards, but it's a bit awkward with the closure
		up-to [equ]. To see in practice. *)

  Inductive schedule_ : ctree' E R -> ctree' E R -> Prop :=
  | SchedFork {n} (x : Fin.t n) k t :
    		schedule_ (observe (k x)) t ->
    		schedule_ (ForkF n k) t
  | SchedRet x :
    		schedule_ (RetF x) (RetF x)
  | SchedVis {X} (e : E X) k :
    		schedule_ (VisF e k) (VisF e k).

  Definition schedule u v := schedule_ (observe u) (observe v).

End Schedule.

Section bisim.

  Context {E : Type -> Type} {R1 R2 : Type} (RR : R1 -> R2 -> Prop).

	(** * [matching]
	This relation captures the local challenge that two scheduled
	trees must solve. It corresponds from the more traditional
	bisimulation world to ensuring that they can take a small step
	emmitting the same event. *)

  Variant matching (bisim : ctree E R1 -> ctree E R2 -> Prop) :
    ctree' E R1 -> ctree' E R2 -> Prop :=
  | MatchRet x y (RET : RR x y) :
     matching bisim (RetF x) (RetF y)
  | MatchVis {X} (e : E X) k1 k2 (RET : forall v, bisim (k1 v) (k2 v)):
     matching bisim (VisF e k1) (VisF e k2)
  .
  Hint Constructors matching: core.

	(* The functor is shrinked to a single constructor mirrorring
		exactly traditional definitions of bisimulations:
		for any observable state that the first process can reach,
		the second one can reach a matching one, and reciprocally.
	*)

  Variant bisimF (bisim : ctree E R1 -> ctree E R2 -> Prop) :
    ctree' E R1 -> ctree' E R2 -> Prop :=

  | BisimSched u t
            (SIMF : forall u', schedule_ u u' ->
              exists t', schedule_ t t' /\ matching bisim u' t')
            (SIMB : forall t', schedule_ t t' ->
              exists u', schedule_ u u' /\ matching bisim u' t')
               :
      bisimF bisim u t
  .
  Hint Constructors bisimF: core.

  Definition bisim_ eq : ctree E R1 -> ctree E R2 -> Prop :=
	fun t1 t2 => bisimF eq (observe t1) (observe t2).

  Lemma matching_mono u v sim sim'
              (IN : matching sim u v)
              (LE : sim <= sim') :
        matching sim' u v.
  Proof.
    inv IN; auto. constructor; intros. apply LE; auto.
  Qed.
  Hint Resolve matching_mono: core.

  Program Definition fbisim : mon (ctree E R1 -> ctree E R2 -> Prop) := {| body := bisim_ |}.
  Next Obligation.
   unfold pointwise_relation, impl, bisim_.
   intros ?? INC ?? EQ. 
   constructor; inversion_clear EQ; intros; [edestruct SIMF as (? & ? & ?)| edestruct SIMB as (? & ? & ?)]; eauto. 
  Qed.

End bisim.

(** associated relation *)
Notation bisim := (gfp (fbisim eq)).

(** associated companions  *)
Notation T_bis RR  := (t (B (fbisim RR))).
Notation t_bis RR  := (t (fbisim RR)).
Notation bt_bis RR := (bt (fbisim RR)).

Infix "≈" := bisim (at level 70).
Notation "x ≊ y" := (t_bis eq _ x y) (at level 79). 
Notation "x [≊] y" := (bt_bis eq _ x y) (at level 79). 

Arguments bisim_ _ _ _ _/.
#[global] Hint Constructors bisimF: core.
#[global] Hint Constructors matching: core.

Variant passive_ {E R} : ctree' E R -> Prop := 
  | fork_passive n k : passive_ (ForkF n k).
Definition passive {E R} t := @passive_ E R (observe t).
#[global] Hint Constructors passive_: core.

Variant active_ {E R} : ctree' E R -> Prop := 
  | ret_active x : active_ (RetF x)
  | vis_active Y (e : E Y) k : active_ (VisF e k).
Definition active {E R} t := @active_ E R (observe t).
#[global] Hint Constructors active_: core.

Lemma scheduled_active_ : forall {E R} (t u : ctree' E R),
  schedule_ t u -> 
  active_ u.
Proof.
  intros * SCHED.
  now induction SCHED.
Qed.

Lemma scheduled_active : forall {E R} (t u : ctree E R),
  schedule t u -> 
  active u.
Proof.
  intros * SCHED; red.
  now induction SCHED.
Qed.

Lemma matching_active_refl {E R} (RR : R -> R -> Prop)
   (eq : ctree E R -> ctree E R -> Prop) (t : ctree' E R) 
   `{Reflexive _ RR} `{Reflexive _ eq} :
   active_ t ->
   matching RR eq t t.
Proof.
  intros []; auto.
Qed. 

Lemma matching_active_sym {E R} (RR : R -> R -> Prop)
   (eq : ctree E R -> ctree E R -> Prop) (t u : ctree' E R) 
   `{Symmetric _ RR} :
   matching RR eq t u ->
   matching RR (converse eq) u t.
Proof.
  intros []; auto. 
Qed. 
  
Section bisim_equiv.

	Variable (E : Type -> Type) (R : Type) (RR : R -> R -> Prop).
  Notation T  := (coinduction.t (B (fbisim (E := E) RR))).
  Notation t  := (coinduction.t (fbisim (E := E) RR)).
	Notation bt := (coinduction.bt (fbisim (E := E) RR)).


  (** [eq] is a post-fixpoint, thus [const eq] is below [t] *)
	Lemma refl_t {RRR: Reflexive RR}: const eq <= t.
	Proof.
    apply leq_t. 
		intros p t ? <-. cbn. 
    constructor. 
    - intros t' SCHED.
      exists t'; split; auto.
      apply matching_active_refl; auto.
      eapply scheduled_active_; eauto.
    - intros t' SCHED.
      exists t'; split; auto.
      apply matching_active_refl; auto.
      eapply scheduled_active_; eauto.
	Qed.
		
	(** converse is compatible *)
	Lemma converse_t {RRS: Symmetric RR}: converse <= t.
	Proof.
		apply leq_t. intros S t u H; cbn in *. 
    destruct H. constructor.
    - intros t' SCHED.
      edestruct SIMB as (u' & SCHED' & MATCH'); eauto.
      exists u'; split; auto.
      apply matching_active_sym; auto.
    - intros u' SCHED.
      edestruct SIMF as (t' & SCHED' & MATCH'); eauto.
      exists t'; split; auto.
      apply matching_active_sym; auto.
	Qed.

  (** so is squaring *)
	Lemma square_t {RRR: Reflexive RR} {RRT: Transitive RR}: square <= t.
	Proof.
		apply leq_t; cbn.
		intros S t u [v [] []]; cbn in *. clear t u v. rename t0 into t, u0 into u.
    constructor.
    - intros u' SCHEDu. 
      edestruct SIMF as (t' & SCHEDt & MATCHut); eauto.
      exists t'; split; auto.

		- constructor. replace y0 with x1 in * by congruence. eauto.
		- rewrite <-H in H2.
			destruct (Vis_eq1 _ _ _ _ _ _ _ H2).
			destruct (Vis_eq2 _ _ _ _ _ _ H2) as [-> ->].
			constructor. intro x0. now exists (k2 x0).
		- rewrite <- H in H2.
			destruct (Fork_eq1 _ _ _ _ _ H2).
			destruct (Fork_eq2 _ _ _ _ H2).
			constructor. intros i. now (exists (k0 i)).
	Qed.
	
	(** thus bisimilarity, [t R], [b (t R)] and [T f R] are always bisimivalence relations *)
	#[global] Instance Equivalence_t `{Equivalence _ RR} S: Equivalence (t S).
	Proof. apply Equivalence_t. apply refl_t. apply square_t. apply converse_t. Qed.
	#[global] Instance Equivalence_T `{Equivalence _ RR} f S: Equivalence (T f S).
	Proof. apply Equivalence_T. apply refl_t. apply square_t. apply converse_t. Qed.
	#[global] Instance Equivalence_bt `{Equivalence _ RR} S: Equivalence (bt S).
	Proof. apply Equivalence_bt. apply refl_t. apply square_t. apply converse_t. Qed.

End bisim_bisimiv.



(** * Sanity checks and meta-theory to establish at some point.
	We'll have to come after more basic meta-theory of course,
	but it's good to think about those.
	*)

Module Sanity.
  Import CTree.

  Lemma schedule_spin {E R} t : schedule (@spin E R) t -> False.
  Proof.
    intros. unfold schedule in H. 
    remember (observe spin). 
    genobs t ot.
    induction H; inversion Heqc.
    cbv in *. subst. apply inj_pair2 in H2. subst. auto.
  Qed.

  Goal forall {E R}, @spin E R ≈ spin.
  Proof.
    intros. step.
    constructor; intros; exfalso; eapply schedule_spin; eauto.
  Qed.

  Lemma schedule_spin_nary {E R} n t : schedule (@spin_nary E R n) t -> False.
  Proof.
    intros. unfold schedule in H. 
    remember (observe (spin_nary n)). genobs t ot.
    induction H; inversion Heqc.
    cbv in *. subst. apply inj_pair2 in H2. subst. auto.
  Qed.

  Goal forall {E R} n m, @spin_nary E R n ≈ spin_nary m.
  Proof.
    intros. step.
    constructor; intros; exfalso; eapply schedule_spin_nary; eauto.
  Qed.

	(* TODO: we need to do some thinking about what the right
		way to represent and manipulate these finite branches.
	*)
	Definition fork2 {E X} (t u : ctree E X) :=
		(Fork 2 (fun b =>
						 match b with | Fin.F1 => t | _ => u end)).

  Definition fork3 {E X} (t u v : ctree E X) :=
		(Fork 3 (fun b =>
						 match b with
						  | Fin.F1 => t
						  | Fin.FS Fin.F1 => u
							| _ => v end)).

	Lemma fork2_assoc : forall {E X} (t u v : ctree E X),
		fork2 (fork2 t u) v ≈
		fork2 t (fork2 u v).
  Proof.
    intros. step; constructor.
    - intros.
      inv H.

	Lemma fork2_commut : forall {E X} (t u : ctree E X),
		fork2 t u ≈ fork2 u t.
	Admitted.

	(* To generalize to any arity *)
	Lemma fork_merge : forall {E X} (t u v : ctree E X),
		fork2 (fork2 t u) v ≈
		fork3 t u v.
	Admitted.

	Lemma fork_spin : forall {E X} (t : ctree E X),
		fork2 t spin ≈ t.
	Admitted.

	Lemma fork2_equ : forall {E X} (t u : ctree E X),
		t ≅ u ->
		fork2 t u ≈ t.
	Admitted.

End Sanity.

Lemma schedule_vis_inv :
  forall {E X Y} e (k : X -> ctree E Y) t,
    schedule (Vis e k) t -> t ≅ Vis e k.
Proof.
  intros * SCHED. inversion SCHED. apply inj_pair2 in H1, H2. subst.
  pstep. simpl. rewrite <- H. constructor. intros. left. apply Reflexive_paco2_equ; auto. (* TODO *)
Qed.

(* TODO: schedule is closed under [equ] properly *)
#[global] Instance equ_schedule {E X}:
	Proper (equ eq ==> equ eq ==> iff) (@schedule E X).
Proof.
  repeat red; intros * EQ1 * EQ2; split; intros SCHED.
(*
  - punfold EQ1; punfold EQ2.
    inv EQ1; inv EQ2; cbn in *; try now (intuition || inv SCHED; inv_eq H3).
    + pclearbot.
      apply schedule_vis_inv in SCHED.
      pose proof (equ_vis_invT _ _ _ _ SCHED); subst.
      pose proof (equ_vis_invE _ _ _ _ SCHED) as []; subst.
      constructor.
      pfold; constructor.
      intros; left.
      rewrite <- REL0.
      admit.
    + induction SCHED; auto.
    +
    inv SCHED; inv H3.
    induction SCHED.
*)
Admitted.

(* TODO : [equ] is a subrelation of [bisim] *)
Lemma equ_bisim : forall {E X Y} {RR: X -> Y -> Prop},
  subrelationH (@equ E _ _ RR) (@bisim E _ _ RR).
Proof.
	(*
	 intros; red.
	 pcofix CIH; intros s t EQ.
	 punfold EQ; pfold.
	 inv EQ.
	 - constructor 2; (intros ? SCHED; eexists; split; [constructor | inv SCHED; auto]).
	 - constructor 2; (intros ? SCHED; eexists; split; [constructor | apply schedule_vis_inv in SCHED; subst; pclearbot; auto]).
		 all: constructor; intros; right; apply CIH, REL.
	 - constructor 2; intros ? SCHED.
		 + pclearbot.
			 remember (Fork k1) as ft. revert k1 REL Heqft; induction SCHED; try now intuition.
			 intros; dependent destruction Heqft; pclearbot.
			 edestruct IHSCHED as (t' & SCHED' & MATCH).

	 - constructor 2; .
		 assert (u' = Vis e k1).
		 { inversion SCHED. dependent induction H1. dependent induction H2. }

 	*)
Admitted.
