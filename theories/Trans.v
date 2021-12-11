(*|
==========================================
Transition relations over concurrent trees
==========================================

Trees represent the dynamics of non-deterministic procesess.
In order to capture their behavioral equivalence, we follow the
process-algebra tradition and define bisimulation atop of labelled
transition system.

A node is said to be _observable_ if it is a visible event, a return
node, or an internal choice tagged as visible.
The first transition relation we introduce is [trans]: a tree can
finitely descend through unobservable choices until it reaches an
observable node. At this point, it steps following the simple rules:
- [Ret v] steps to a silently blocked state by emmiting a value
label of [v]
- [Vis e k] can step to any [k x] by emmiting an event label tagged
with both [e] and [x]
- [ChoiceV k] can step to any [k x] by emmiting a tau label

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

From Coinduction Require Import
	   coinduction rel tactics.

From CTree Require Import
	   Utils CTrees Shallow Equ.

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
Open Scope ctree.

(*|
.. coq::
|*)

Section Trans.

  Context {E : Type -> Type} {R : Type}.

	Notation S' := (ctree' E R).
	Notation S  := (ctree  E R).

	Definition SS : EqType :=
		{| type_of := S ; Eq := equ eq |}.

	Variant label : Type :=
	  | tau
	  | obs {X : Type} (e : E X) (v : X)
	  | val {X : Type} (v : X).

(*|
The transition relation over [ctree]s.
It can either:
- recursively crawl through invisible [choice] node;
- stop at a successor of a visible [choice] node, labelling the transition [tau];
- stop at a successor of a [Vis] node, labelling the transition by the event and branch taken;
- stop at a sink (implemented as a [choice] node with no successor) by stepping from a [ret v]
node, labelling the transition by the returned value.
|*)
	Inductive trans_ : label -> hrel S' S' :=

  | Stepchoice {n} (x : Fin.t n) k l t :
    trans_ l (observe (k x)) t ->
    trans_ l (ChoiceF false n k) t

  | Steptau {n} (x : Fin.t n) k t :
		k x ≅ t ->
    trans_ tau (ChoiceF true n k) (observe t)

  | Stepobs {X} (e : E X) k x t :
		k x ≅ t ->
    trans_ (obs e x) (VisF e k) (observe t)

	| Stepval r k :
    trans_ (val r) (RetF r) (ChoiceF false 0 k)
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
			* rewrite H2; eapply (Steptau x); auto.
			* replace (VisF e k1) with (observe (Vis e k1)) by reflexivity.
			  eapply (Steptau x).
				rewrite H.
				rewrite (ctree_eta t), <- H2.
				step; constructor; intros; symmetry; auto.
			* replace (ChoiceF b n0 k1) with (observe (Choice b n0 k1)) by reflexivity.
			  eapply (Steptau x).
				rewrite H.
				rewrite (ctree_eta t), <- H2.
				step; constructor; intros; symmetry; auto.
		+ replace u with (observe (go u)) by reflexivity.
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
			apply (Stepchoice x).
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

(*|
Extention of [trans] with its reflexive closure, labelled by [tau].
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
[trans tau       (ChoiceV n k) (k x)]
[trans tau       (TauV t) t]
[trans l (k x) u -> trans l (ChoiceI n k) u]
[trans l t u     -> trans l (TauI t) u]

Elimination rules for [trans]
[trans l (Ret x)       u -> l = val x /\ t ≅ stuck]
[trans l (Vis e k)     u -> exists v, l = obs e v /\ t ≅ k v]
[trans l (ChoiceV n k) u -> exists x, t' ≅ k x /\ l = tau]
[trans l (TauV t)      u -> t ≅ u /\ l = tau]
[trans l (ChoiceI n k) u -> exists x, trans l (k x) u]
[trans l (TauI t)      u -> trans l t u]

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

	Lemma trans_etrans_ l: forall p p', trans l p p' -> etrans l p p'.
	Proof. apply trans_etrans. Qed.
	Lemma trans_wtrans_ l: forall p p', trans l p p' -> wtrans l p p'.
	Proof. apply trans_wtrans. Qed.
	Lemma etrans_wtrans_ l: forall p p', etrans l p p' -> wtrans l p p'.
	Proof. apply etrans_wtrans. Qed.

	(* Global Hint Resolve trans_etrans_ trans_wtrans_: ccs. *)

	Lemma enil p: etrans tau p p.
	Proof. cbn. now right. Qed.
	Lemma wnil p: wtrans tau p p.
	Proof. apply etrans_wtrans, enil. Qed.
	(* Global Hint Resolve enil wnil: ccs. *)

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

  Lemma wtrans_tau: wtrans tau ≡ (trans tau)^*.
  Proof.
 	  unfold wtrans, etrans. ka.
	Qed.

 	Global Instance PreOrder_wtrans_tau: PreOrder (wtrans tau).
 	Proof.
    split.
    intro. apply wtrans_tau.
		now (apply (str_refl (trans tau)); cbn).
    intros ?????. apply wtrans_tau. apply (str_trans (trans tau)).
    eexists; apply wtrans_tau; eassumption.
  Qed.

(*|
Backward reasoning for [trans]
------------------------------
|*)

	Lemma trans_ret : forall x,
		  trans (val x) (Ret x) stuck.
	Proof.
    intros; constructor.
  Qed.

	Lemma trans_vis : forall {X} (e : E X) x k,
		  trans (obs e x) (Vis e k) (k x).
	Proof.
    intros; constructor; auto.
  Qed.

	Lemma trans_ChoiceI : forall (l : label) t t' n k x,
		  trans l t t' ->
      k x ≅ t ->
		  trans l (ChoiceI n k) t'.
	Proof.
		intros * TR Eq.
    apply Stepchoice with x.
    rewrite Eq; auto.
	Qed.

	Lemma trans_TauI : forall l t t',
		  trans l t t' ->
		  trans l (TauI t) t'.
	Proof.
		intros * TR; eapply trans_ChoiceI; eauto; exact Fin.F1.
	Qed.

	Lemma trans_ChoiceV : forall n k x,
		  trans tau (ChoiceV n k) (k x).
	Proof.
		intros.
    apply Steptau with x; reflexivity.
	Qed.

	Lemma trans_TauV : forall t,
		  trans tau (TauV t) t.
	Proof.
    intros; apply (trans_ChoiceV 1 (fun _ => t) Fin.F1).
	Qed.

(*|
Forward reasoning for [trans]
------------------------------
|*)

	Lemma trans_ret_inv : forall x l t,
		  trans l (Ret x) t ->
		  l = val x /\ t ≅ stuck.
	Proof.
		intros * TR; inv TR; intuition.
    rewrite ctree_eta, <- H2; auto.
    step; constructor; intros abs; inv abs.
  Qed.


	Lemma trans_vis_inv : forall {X} (e : E X) k l u,
		  trans l (Vis e k) u ->
      exists x, l = obs e x /\ u ≅ k x.
	Proof.
    intros * TR.
    inv TR.
    dependent induction H3; eexists; split; eauto.
    rewrite ctree_eta, <- H4, <- ctree_eta; symmetry; auto.
  Qed.

	Lemma trans_ChoiceI_inv : forall l n k u,
		  trans l (ChoiceI n k) u ->
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
		induction TR; intros; dependent induction Heqox; eauto.
	Qed.

	Lemma trans_TauI_inv : forall l t t',
		  trans l (TauI t) t' ->
		  trans l t t'.
	Proof.
    intros * TR; apply trans_ChoiceI_inv in TR as [_ TR]; auto.
  Qed.

	Lemma trans_ChoiceV_inv : forall l n k t',
		  trans l (ChoiceV n k) t' ->
		  exists x, t' ≅ k x /\ l = tau.
	Proof.
		intros * TR.
		cbn in *; red in TR; cbn in TR.
		dependent induction TR.
    eexists; split; auto.
		rewrite H, ctree_eta, (ctree_eta t), x; reflexivity.
	Qed.

	Lemma trans_TauV_inv : forall l t t',
		  trans l (TauV t) t' ->
		  t' ≅ t /\ l = tau.
	Proof.
		intros * TR; apply trans_ChoiceV_inv in TR as (_ & ? & ?); auto.
	Qed.

(*|
Inversion rules for [trans] based on the value of the label
-----------------------------------------------------------
In general, these would require to introduce the relation that
only steps through the non-observable internal choice.
I'll skip them for now and introduce them if they turn out to be
useful.
|*)
  Lemma trans_val_inv :
    forall (t u : ctree E R) (v : R),
      trans (val v) t u ->
      u ≅ stuck.
  Proof.
    intros * TR.
    remember (val v) as ov.
    rewrite ctree_eta; induction TR; intros; auto; try now inv Heqov.
    step; econstructor; intros abs; inv abs.
  Qed.

(*|
etrans theory
---------------
|*)

  Lemma etrans_case : forall l t u,
      etrans l t u ->
      (trans l t u \/ (l = tau /\ t ≅ u)).
  Proof.
    intros [] * TR; cbn in *; intuition.
  Qed.

	Lemma etrans_ret_inv : forall x l t,
		  etrans l (Ret x) t ->
		  (l = tau /\ t ≅ Ret x) \/ (l = val x /\ t ≅ stuck).
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
to reduce pure computations if course stuck, but so is [spin].
|*)

  Definition is_stuck : ctree E R -> Prop :=
    fun t => forall l u, ~ (trans l t u).

  #[global] Instance is_stuck_equ : Proper (equ eq ==> iff) is_stuck.
  Proof.
    intros ? ? EQ; split; intros ST; red; intros * ABS.
    rewrite <- EQ in ABS; eapply ST; eauto.
    rewrite EQ in ABS; eapply ST; eauto.
  Qed.

  Lemma etrans_is_stuck_inv : forall l t u,
      is_stuck t ->
      etrans l t u ->
      (l = tau /\ t ≅ u).
  Proof.
    intros * ST TR.
    edestruct etrans_case; eauto.
    apply ST in H; tauto.
  Qed.

  Lemma transs_is_stuck_inv : forall t u,
      is_stuck t ->
      (trans tau)^* t u ->
      t ≅ u.
  Proof.
    intros * ST TR.
    destruct TR as [[] TR]; intuition.
    destruct TR.
    apply ST in H; tauto.
  Qed.

  Lemma wtrans_is_stuck_inv : forall l t u,
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

  Lemma stuck_is_stuck :
    is_stuck stuck.
  Proof.
    red; intros * abs; inv abs; inv x.
  Qed.

  Lemma spin_is_stuck :
    is_stuck spin.
  Proof.
    red; intros * abs.
    remember spin as t.
    assert (EQ: t ≅ spin) by (subst; reflexivity); clear Heqt; revert EQ; rewrite ctree_eta.
    induction abs; auto; try now (rewrite unfold_spin; intros abs; step in abs; inv abs).
    intros EQ; apply IHabs.
    rewrite <- ctree_eta.
    rewrite unfold_spin in EQ.
    step in EQ.
    dependent induction EQ; auto.
  Qed.


(*|
wtrans theory
---------------
|*)

	Lemma wtrans_TauV : forall l t t',
		  wtrans l t t' ->
		  wtrans l (TauV t) t'.
	Proof.
		intros * TR.
		eapply wcons; eauto.
		apply trans_TauV.
	Qed.

	Lemma trans_tau_str_ret_inv : forall x t,
		  (trans tau)^* (Ret x) t ->
		  t ≅ Ret x.
	Proof.
		intros * [[|] step].
		- cbn in *; symmetry; eauto.
		- destruct step.
      apply trans_ret_inv in H; intuition congruence.
	Qed.

	Lemma wtrans_ret_inv : forall x l t,
		  wtrans l (Ret x) t ->
		  (l = tau /\ t ≅ Ret x) \/ (l = val x /\ t ≅ stuck).
	Proof.
		intros * step.
		destruct step as [? [? step1 step2] step3].
		apply trans_tau_str_ret_inv in step1.
		rewrite step1 in step2; clear step1.
		apply etrans_ret_inv in step2 as [[-> EQ] |[-> EQ]].
		rewrite EQ in step3; apply trans_tau_str_ret_inv in step3; auto.
		rewrite EQ in step3.
    apply transs_is_stuck_inv in step3; [| apply stuck_is_stuck].
    intuition.
	Qed.

End Trans.

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
      (exists (x : X), trans (val x) t stuck /\ trans l (k x) u).
Proof.
  intros TR; induction TR; intros.
  - rewrite unfold_bind in H; setoid_rewrite (ctree_eta t0).
    desobs t0.
    + right.
      exists r; split.
      constructor.
      rewrite <- H.
      apply (Stepchoice x); auto.
      rewrite <- H0; auto.
    + step in H; inv H.
    + step in H; dependent induction H.
      specialize (IHTR (k1 x) k0 u).
      destruct IHTR as [(? & ? & ? & ?) | (? & ? & ?)]; auto.
      rewrite <- ctree_eta, REL; reflexivity.
      left; split; eauto.
      exists x0; split; auto.
      apply (Stepchoice x); auto.
      right.
      exists x0; split; auto.
      apply (Stepchoice x); auto.
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
    (exists (x : X), trans (val x) t stuck /\ trans l (k x) u).
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
  (* rewrite (ctree_eta t), (ctree_eta u). *)
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
  trans (val x) t stuck ->
  trans l (k x) u ->
  trans l (t >>= k) u.
Proof.
  cbn; unfold transR; intros TR1.
  genobs t ot.
  remember (observe stuck) as oc.
  remember (val x) as v.
  revert t x Heqot Heqoc Heqv.
  induction TR1; intros; try (inv Heqv; fail).
  - rewrite (ctree_eta t0), <- Heqot; cbn; econstructor.
    eapply IHTR1; eauto.
  - dependent induction Heqv.
    rewrite (ctree_eta t), <- Heqot, unfold_bind; cbn; auto.
Qed.
