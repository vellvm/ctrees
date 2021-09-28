(* begin hide *)
From Paco Require Import paco.

From Coq Require Import
     Program
     Setoid
     Morphisms
     RelationClasses.

From ITree Require Import
	Basics.HeterogeneousRelations.

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

 (* Note: we close the relation up-to [equ] *)
	(* Inductive schedule : ctree E R -> ctree E R -> Prop := *)
	(* 	| SchedFork {n} (x : Fin.t n) k t : schedule (k x) t -> schedule (Fork k) t *)
	(* 	| SchedRet x : schedule (Ret x) (Ret x) *)
	(* 	| SchedVis {X} (e : E X) k t : t ≅ Vis e k -> schedule (Vis e k) t. *)

	(* It might be better to work with the usual pattern of tying
	  the knot afterwards, but it's a bit awkward with the closure
		up-to [equ]. To see in practice. *)

  Inductive schedule_ : ctree' E R -> ctree' E R -> Prop :=
  | SchedFork {n} (x : Fin.t n) k t :
    		schedule_ (observe (k x)) t ->
    		schedule_ (ForkF k) t
  | SchedRet x :
    		schedule_ (RetF x) (RetF x)
  | SchedVis {X} (e : E X) k t :
      t ≅ Vis e k ->
      schedule_ (VisF e k) (observe t).

  Definition schedule u v := schedule_ (observe u) (observe v).

End Schedule.

Section bisim.

  Context {E : Type -> Type} {R1 R2 : Type} (RR : R1 -> R2 -> Prop).

	(** * [matching]
	This relation captures the local challenge that two scheduled
	trees must solve. It corresponds from the more traditional
	bisimulation world to ensuring that they can take a small step
	emmitting the same event. *)

  Variant matching_ (bisim : ctree E R1 -> ctree E R2 -> Prop) :
    ctree' E R1 -> ctree' E R2 -> Prop :=
  | MatchRet x y (RET : RR x y) :
     matching_ bisim (RetF x) (RetF y)
  | MatchVis {X} (e : E X) k1 k2 (RET : forall v, bisim (k1 v) (k2 v)):
     matching_ bisim (VisF e k1) (VisF e k2)
  .
  Hint Constructors matching_: core.

  Definition matching bisim u v := matching_ bisim (observe u) (observe v).

	(* The functor is shrinked to a single constructor mirrorring
		exactly traditional definitions of bisimulations:
		for any observable state that the first process can reach,
		the second one can reach a matching one, and reciprocally.
	*)

	(* Probably should use the pattern tying the knot afterwards here as well *)
  Variant bisimF (bisim : ctree E R1 -> ctree E R2 -> Prop) :
    ctree E R1 -> ctree E R2 -> Prop :=

	(* We currently believe that this constructor, initially
	meant to be used to relate silently diverging computations,
	is useless. It should be triple checked in depth.

  | BisimDiv {n m} (k : Fin.t n -> _) (k' : Fin.t m -> _)
            (REL : forall i j, bisim (k i) (k' j)) :
      bisimF bisim (Fork k) (Fork k')
  *)

  | BisimSched u t
            (SIMF : forall u', schedule u u' ->
              exists t', schedule t t' /\ matching bisim u' t')
            (SIMB : forall t', schedule t t' ->
              exists u', schedule u u' /\ matching bisim u' t')
               :
      bisimF bisim u t
  .
  Hint Constructors bisimF: core.

  Lemma matching_mono u v sim sim'
              (IN : matching sim u v)
              (LE : sim <2= sim') :
        matching sim' u v.
  Proof.
    unfold matching in *.
    inv IN; auto.
  Qed.
  Hint Resolve matching_mono: core.

  Lemma bisimF_mono u v sim sim'
        (IN: bisimF sim u v)
        (LE: sim <2= sim'):
    bisimF sim' u v.
  Proof.
    intros. induction IN; eauto.
    apply BisimSched; intros; [edestruct SIMF as (? & ? & ?)| edestruct SIMB as (? & ? & ?)]; eauto.
  Qed.
  Hint Resolve bisimF_mono : paco.

  Definition bisim := paco2 bisimF bot2.

End bisim.

#[global] Hint Constructors bisimF: core.
#[global] Hint Constructors matching_: core.

(* TODO : wrap notations in modules *)
Infix "≈[ R ]" := (bisim R) (at level 70).
Infix "≈"      := (bisim eq) (at level 70).
(* Infix "{ r }≈F[ R ]" := (bisimF R (upaco2 (bisim_ R) r)) (at level 70, only printing).
Infix "{ r }≈F" := (bisimF eq (upaco2 (bisim_ eq) r)) (at level 70, only printing).
Infix "{ r }≈gF[ R ]" := (bisimF R (gupaco2 (bisim_ R) _ r)) (at level 70, only printing).
Infix "{ r }≈gF" := (bisimF eq (gupaco2 (bisim_ eq) _ r)) (at level 70, only printing).
 *)

(** * Sanity checks and meta-theory to establish at some point.
	We'll have to come after more basic meta-theory of course,
	but it's good to think about those.
	*)

Module Sanity.
  Import CTree.

  Lemma schedule_spin {E R} t : schedule (@spin E R) t -> False.
  Proof.
    intros. unfold schedule in H. remember (observe spin). remember (observe t).
    induction H; inversion Heqc.
    cbv in *. subst. apply inj_pair2 in H2. subst. auto.
  Qed.

  Goal forall {E R}, @spin E R ≈ spin.
  Proof.
    intros. pcofix CIH. pstep.
    constructor; intros; exfalso; eapply schedule_spin; eauto.
  Qed.

  Lemma schedule_spin_nary {E R} n t : schedule (@spin_nary E R n) t -> False.
  Proof.
    intros. unfold schedule in H. remember (observe (spin_nary n)). remember (observe t).
    induction H; inversion Heqc.
    cbv in *. subst. apply inj_pair2 in H2. subst. auto.
  Qed.

  Goal forall {E R} n m, @spin_nary E R n ≈ spin_nary m.
  Proof.
    intros. pcofix CIH. pstep.
    constructor; intros; exfalso; eapply schedule_spin_nary; eauto.
  Qed.

  Goal forall {E R} n, @spin_nary E R n ≈ spin.
  Proof.
    intros. pcofix CIH. pstep.
    constructor; intros; exfalso.
    - eapply schedule_spin_nary; eauto.
    - eapply schedule_spin; eauto.
  Qed.

  (* Lemma shedule_match_refl : *)
  (*   schedule t u -> matching u u. *)

  (* TODO: we need to do some thinking about what the right
		way to represent and manipulate these finite branches.
   *)
  Definition fork2 {E X} (t u : ctree E X) :=
	(Fork (fun b : fin 2 =>
			 match b with | Fin.F1 => t | _ => u end)).

  Definition fork3 {E X} (t u v : ctree E X) :=
		(Fork (fun b : fin 3 =>
						 match b with
						  | Fin.F1 => t
						  | Fin.FS Fin.F1 => u
						  | _ => v end)).

	Lemma fork2_assoc : forall {E X} (t u v : ctree E X),
		fork2 (fork2 t u) v ≈
		fork2 t (fork2 u v).
    Proof.
      intros E X. pcofix CIH. pstep. constructor.
      - intros. exists u'. split. 2: {
          (* red in H. unfold fork2 in H. red. simpl in *. (* remember (ForkF _) in H. *) *)
          (* (* remember (observe _). revert Heqc0. revert u'. red. *) *)
          (* dependent induction H; subst. ; inv Heqc; intros. apply inj_pair2 in H2. subst. *)

          (* - clear IHschedule_. dependent induction H. eapply IHschedule_; eauto. *)
          (*   unfold fork2. admit. *)
          (* - eapply IHschedule_; eauto. *)

          admit.
        }
        red in H. inv H. apply inj_pair2 in H2. subst.
        red. destruct x.
        + inv H3. apply inj_pair2 in H1. subst. destruct x.
          * apply SchedFork with (x:=Fin.F1). auto.
          * apply SchedFork with (x0:=Fin.FS Fin.F1).
            apply SchedFork with (x0:=Fin.F1). auto.
        + clear x n.
          apply SchedFork with (x:=Fin.FS Fin.F1).
          apply SchedFork with (x:=Fin.FS Fin.F1). auto.
      - intros. exists t'. split. 2: { admit. }
        red in H. inv H. apply inj_pair2 in H2. subst.
        red. destruct x.
        + apply SchedFork with (x:=Fin.F1).
          apply SchedFork with (x:=Fin.F1). auto.
        + clear x n. inv H3. apply inj_pair2 in H1. subst. destruct x.
          * apply SchedFork with (x:=Fin.F1).
            apply SchedFork with (x:=Fin.FS Fin.F1). auto.
          * apply SchedFork with (x0:=Fin.FS Fin.F1). auto.
    Abort.

	Lemma fork2_commut : forall {E X} (t u : ctree E X),
		fork2 t u ≈ fork2 u t.
    Proof.
      intros E X. pcofix CIH. pstep. constructor.
      - intros. exists u'. split. 2: { admit. }
        inv H. apply inj_pair2 in H2. subst. destruct x.
        + apply SchedFork with (x:=Fin.FS Fin.F1). auto.
        + apply SchedFork with (x0:=Fin.F1). auto.
    Abort.

	(* To generalize to any arity *)
	Lemma fork_merge : forall {E X} (t u v : ctree E X),
		fork2 (fork2 t u) v ≈
		fork3 t u v.
	Admitted.

	Lemma fork_spin : forall {E X} (t : ctree E X),
		fork2 t spin ≈ t.
    Proof.
      intros E X. pcofix CIH. pstep. constructor.
      - intros. exists u'. split; auto. 2: { admit. }
        inv H. apply inj_pair2 in H2. subst. destruct x; auto.
        exfalso. eapply schedule_spin; eauto.
    Abort.

	Lemma fork2_equ : forall {E X} (t u : ctree E X),
		t ≅ u ->
		fork2 t u ≈ t.
    Proof.
      intros. punfold H. inversion H.
    Admitted.

End Sanity.

Lemma schedule_vis_inv :
  forall {E X Y} e (k : X -> ctree E Y) t,
    schedule (Vis e k) t -> t ≅ Vis e k.
Proof.
  intros * SCHED. inversion SCHED. apply inj_pair2 in H1, H2. subst.
  pstep. simpl. (* rewrite <- H. constructor. intros. left. apply Reflexive_paco2_equ; auto. (* TODO *) *)
  (* Qed. *)
  Admitted.

(* TODO: schedule is closed under [equ] properly *)
#[global] Instance equ_schedule {E X}:
	Proper (equ eq ==> equ eq ==> iff) (@schedule E X).
Proof.
  repeat red; intros * EQ1 * EQ2; split; intros SCHED.
  - punfold EQ1; punfold EQ2.
    red in SCHED |- *. inv EQ1; rewrite <- H0 in SCHED; clear H0.
    + inv EQ2; rewrite <- H1 in SCHED; clear H1; inv SCHED. constructor.
    + inv EQ2; rewrite <- H1 in SCHED; clear H1; inv SCHED.
(*      apply inj_pair2 in H4, H3, H7, H6. subst. pclearbot. econstructor; eauto.
    +
    rewrite <- H0 in SCHED. rewrite <- H2 in SCHED;.
    inv SCHED; constructor.
    ; try now (intuition || inv SCHED; inv_eq H3).
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
	 - constructor; intros ? SCHED. exists (Ret y). split. red. rewrite <- H. econstructor 2.
       red in SCHED. rewrite <- H0 in SCHED. inv SCHED. red. rewrite <- H3. constructor; auto.
       admit.
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
