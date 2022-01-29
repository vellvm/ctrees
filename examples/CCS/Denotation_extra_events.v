(* Alternate version of denotation where the communicating combinator handles the presence of extra events *)

(*|
=================================
Denotation of [ccs] into [ctree]s
=================================

.. coq:: none
|*)

From Coq Require Export
  List
  Strings.String.

From ITree Require Import ITree.

From CTree Require Import
	Utils
	CTrees
  Trans
 	Interp
	Equ
	Bisim
  CTreesTheory
  Head.

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

From CTreeCCS Require Import
	   Syntax.

From Coinduction Require Import
	coinduction rel tactics.

(* Import CTree. *)

Import CTreeNotations.
Open Scope term_scope.

Set Implicit Arguments.
Set Contextual Implicit.

(*|
Event signature
---------------
Processes must at least be able to perform actions.
We do not encode tau steps as events but rather directly as
unary visible choice nodes.
|*)

Variant ActionE : Type -> Type :=
	| Act (a : action) : ActionE unit.

Definition ccsE E : Type -> Type := ActionE +' E.

Definition ccsT' E T := ctree' (ccsE E) T.
Definition ccsT E  := ctree (ccsE E).

Definition ccs' E := ccsT' E unit.
Definition ccs  E := ccsT E unit.

(*| Process algebra |*)
Section Combinators.

  Variable (E : Type -> Type).
  Notation ccs := (ccs E).
  Notation ccsE := (ccsE E).
  Notation ccsT := (ccsT E).

	Definition nil : ccs := CTree.stuckI.

	Definition prefix (a : action) (P: ccs) : ccs := trigger (Act a);; P.

	Definition plus (P Q : ccs) : ccs := choiceI2 P Q.

  Definition h_trigger {E F} `{E -< F} : E ~> ctree F :=
    fun _ e => trigger e.

  Definition h_restrict_ (c : chan) : ActionE ~> ctree ccsE :=
    fun _ e => let '(Act a) := e in
            match a with
            | Send c'
            | Rcv c' =>
              if (c =? c')%string then CTree.stuckI else trigger e
            end.

	Definition case_ctree {E F G} (f : E ~> ctree G) (g : F ~> ctree G)
		: E +' F ~> ctree G :=
		fun T ab => match ab with
		| inl1 a => f _ a
		| inr1 b => g _ b
		end.

  (* TODO: define basically the theory of handlers for ctrees, all the constructions are specialized to ccs right now *)

  Definition h_restrict c : ccsE ~> ctree ccsE :=
    case_ctree (h_restrict_ c) h_trigger.

  Definition restrict {X} : chan -> ccsT X -> ccsT X :=
    fun c P => interp (h_restrict c) P.

  Definition communicating : ccs -> ccs -> ccs :=
    cofix F (P : ccs) (Q : ccs) :=

      (* We construct the "heads" of both computations to get all reachable events *)
			rP <- get_head P;;
			rQ <- get_head Q;;

      (* And then proceed to:
         - collect all interleavings of visible choices and visible events
         - dismiss terminated computations, disregarding their returned values
         - when encountering two synchronizable actions, adding the communication
         as a third possibility
       *)
      match rP, rQ with
      | HRet rP, _ => Q
      | _, HRet rQ => P
      | HChoice kP, HChoice kQ =>
          choiceI2 (ChoiceV _ (fun i => F (kP i) Q))
                   (ChoiceV _ (fun i => F P (kQ i)))
      | HChoice kP, HVis e kQ =>
          choiceI2 (ChoiceV _ (fun i => F (kP i) Q))
                   (Vis e     (fun x => F P (kQ x)))
      | HVis e kP, HChoice kQ =>
          choiceI2 (Vis e     (fun x => F (kP x) Q))
                   (ChoiceV _ (fun i => F P (kQ i)))
      | HVis (inl1 eP) kP, HVis (inl1 eQ) kQ =>
          match eP, kP, eQ, kQ with
          | Act a, kP, Act b, kQ =>
              if are_opposite a b
              then
                choiceI3 (TauV (F (kP tt) (kQ tt)))
                         (trigger (inl1 (Act a));; F (kP tt) Q)
                         (trigger (inl1 (Act b));; F P (kQ tt))
              else
                choiceI2 (trigger (inl1 (Act a));; F (kP tt) Q)
                         (trigger (inl1 (Act b));; F P (kQ tt))
          end
      | HVis eP kP, HVis eQ kQ =>
          choiceI2 (Vis eP (fun x => F (kP x) Q))
                   (Vis eQ (fun x => F P (kQ x)))
      end.

  (* Definition elim_void1 {E X} (t : ctree (E +' void1) X) : ctree E X := *)
  (*   translate (fun Y e => match e with | inl1 e => e | inr1 e => (match e : void1 _ with end) end) t. *)

  (* Definition intro_void1 {E X} (t : ctree E X) : ctree (E +' void1) X := *)
  (*   translate inl1 t. *)

  (* Definition para (P Q : ccs) : ccs := *)
  (*   elim_void1 (communicating (intro_void1 P) (intro_void1 Q)). *)

(*
				-------------------------------------------------
				!(a.P || bara.Q) -τ> (P || Q) || !(a.P || bara.Q)

					Question: is !P ≈ P || !P?
  Definition bang : ccs -> ccs.
*)

End Combinators.

Notation communicating_ P Q :=
	(rP <- get_head P;;
	 rQ <- get_head Q;;
   match rP, rQ with
   | HRet rP, _ => Q
   | _, HRet rQ => P
   | HChoice kP, HChoice kQ =>
       choiceI2 (ChoiceV _ (fun i => communicating (kP i) Q))
                (ChoiceV _ (fun i => communicating P (kQ i)))
   | HChoice kP, HVis e kQ =>
       choiceI2 (ChoiceV _ (fun i => communicating (kP i) Q))
                (Vis e     (fun x => communicating P (kQ x)))
   | HVis e kP, HChoice kQ =>
       choiceI2 (Vis e     (fun x => communicating (kP x) Q))
                (ChoiceV _ (fun i => communicating P (kQ i)))
   | HVis (inl1 eP) kP, HVis (inl1 eQ) kQ =>
       match eP, kP, eQ, kQ with
       | Act a, kP, Act b, kQ =>
           if are_opposite a b
           then
             choiceI3 (TauV (communicating (kP tt) (kQ tt)))
                      (trigger (inl1 (Act a));; communicating (kP tt) Q)
                      (trigger (inl1 (Act b));; communicating P (kQ tt))
           else
             choiceI2 (trigger (inl1 (Act a));; communicating (kP tt) Q)
                      (trigger (inl1 (Act b));; communicating P (kQ tt))
       end
   | HVis eP kP, HVis eQ kQ =>
       choiceI2 (Vis eP (fun x => communicating (kP x) Q))
                (Vis eQ (fun x => communicating P (kQ x)))
   end)%ctree.

Lemma unfold_communicating : forall {E} P Q, @communicating E P Q ≅ communicating_ P Q.
Proof.
  intros.
	now step.
Qed.

#[global] Instance communicating_equ {E} :
  Proper (equ eq ==> equ eq ==> equ eq) (@communicating E).
Proof.
  unfold Proper, respectful.
  coinduction R CIH.
  intros P1 P2 EQP Q1 Q2 EQQ.
  rewrite 2 unfold_communicating.
  eapply (fbt_bt (bind_ctx_equ_t _ _)).
  apply in_bind_ctx; [apply get_head_equ; auto | intros hdP1 hdP2 eqp].
  eapply (fbt_bt (bind_ctx_equ_t _ _)).
  apply in_bind_ctx; [apply get_head_equ; auto | intros hdQ1 hdQ2 eqq].
  destruct hdP1, hdP2; try now inv eqp.
  - rewrite EQQ; reflexivity.
  - destruct hdQ1, hdQ2; try now inv eqq.
    + rewrite EQP; reflexivity.
    + dependent induction eqp.
      dependent induction eqq.
      constructor.
      intros [|].
      step; constructor; auto.
      step; constructor; auto.
    + dependent induction eqp.
      dependent induction eqq.
      constructor.
      intros [|].
      step; constructor; auto.
      step; constructor; auto.
  - destruct hdQ1, hdQ2; try now inv eqq.
    + destruct e,e0; rewrite EQP; reflexivity.
    + dependent induction eqp.
      dependent induction eqq.
      destruct e0.
      * constructor.
        intros [|].
        step; constructor; auto.
        step; constructor; auto.
      * constructor.
        intros [|].
        step; constructor; auto.
        step; constructor; auto.
    + dependent induction eqp.
      dependent induction eqq.
      destruct e0, e2.
      * destruct a, a0.
        destruct (are_opposite a a0).
        constructor.
        intros [|].
        step; constructor; auto.
        destruct t.
        eapply equ_clo_bind; [reflexivity | intros [] [] _; auto].
        eapply equ_clo_bind; [reflexivity | intros [] [] _; auto].
        constructor.
        intros [|].
        eapply equ_clo_bind; [reflexivity | intros [] [] _; auto].
        eapply equ_clo_bind; [reflexivity | intros [] [] _; auto].
      * constructor.
        intros [|].
        step; constructor; auto.
        step; constructor; auto.
      * constructor.
        intros [|].
        step; constructor; auto.
        step; constructor; auto.
      * constructor.
        intros [|].
        step; constructor; auto.
        step; constructor; auto.
Qed.

Lemma trans_communicatingL {E} : forall l (P P' Q : ctree (_ +' E) unit),
    trans l P P' ->
    trans l (communicating P Q) (communicating P' Q).
Proof.
  intros * TR.
  (* red in TR; red. *)
  pose proof (trans_get_head TR) as TRhd.
  destruct l.
  - destruct TRhd as (n & k & x & TRhd & EQ).
    rewrite unfold_communicating.
    eapply trans_bind_r; [apply TRhd |].
    (* Here, [get_hd Q] could diverge silently in all branches,
       preventing any communication from happening *)
Abort.

Definition comm {E} a : @label (_ +' E) := obs (inl1 (Act a)) tt.
Lemma trans_communicatingSynch {E} : forall a b (P P' Q Q' : ctree (_ +' E) unit),
    trans (comm a) P P' ->
    trans (comm b) Q Q' ->
    are_opposite a b ->
    trans tau (communicating P Q) (communicating P' Q').
Proof.
  intros * TRP TRQ OP.
  apply trans_get_head in TRP as (kP & TRP & EQP).
  apply trans_get_head in TRQ as (kQ & TRQ & EQQ).
  rewrite unfold_communicating.
  eapply trans_bind_r; [apply TRP |].
  eapply trans_bind_r; [apply TRQ |].
  cbn; rewrite OP.
  eapply trans_ChoiceI with (x := Fin.F1); [| reflexivity].
  rewrite EQP, EQQ.
  apply trans_TauV.
Qed.

Lemma trans_communicatingL {E} :
  forall l l' (P P' Q Q' : ctree (_ +' E) unit),
    trans l P P' ->
    trans l' Q Q' ->
    (trans l (communicating P Q) (communicating P' Q) \/
       (l' = val tt /\ Q' ≅ CTree.stuckI /\ trans l  (communicating P Q) P') \/
       (l = val tt /\ P' ≅ CTree.stuckI /\ trans l' (communicating P Q) Q')
    ).
Proof.
  intros * TRP TRQ.
  destruct l, l'.
  - left.
    apply trans_get_head in TRP.
    apply trans_get_head in TRQ.
    destruct TRP as (? & ? & ? & TRP & EQP).
    destruct TRQ as (? & ? & ? & TRQ & EQQ).
    rewrite unfold_communicating.
    cbn in *.
    do 2 (eapply trans_bind_r; [cbn; eauto |]); cbn.
    eapply (trans_ChoiceI Fin.F1); [| reflexivity].
    rewrite EQP.
    pose proof (@trans_ChoiceV _ _ x (fun i : fin x => communicating (x0 i) Q) x1); auto.
  - left.
    apply trans_get_head in TRP.
    apply trans_get_head in TRQ.
    destruct TRP as (? & ? & ? & TRP & EQP).
    destruct TRQ as (? & TRQ & EQQ).
    rewrite unfold_communicating.
    cbn in *.
    do 2 (eapply trans_bind_r; [cbn; eauto |]); cbn.
    eapply (trans_ChoiceI Fin.F1); [| reflexivity].
    rewrite EQP.
    pose proof (@trans_ChoiceV _ _ x (fun i : fin x => communicating (x0 i) Q) x1); auto.
  - right; left.
    destruct (trans_get_head TRP) as (? & ? & ? & TRP' & EQP).
    pose proof (trans_val_invT TRQ); subst X; destruct v.
    apply trans_get_head in TRQ.
    destruct TRQ as (TRQ & EQQ).
    do 2 split; auto.
    rewrite unfold_communicating.
    cbn in *.
    do 2 (eapply trans_bind_r; [cbn; eauto |]); cbn.
    auto.
  - left.
    apply trans_get_head in TRP.
    apply trans_get_head in TRQ.
    destruct TRP as (? & TRP & EQP).
    destruct TRQ as (? & ? & ? & TRQ & EQQ).
    rewrite unfold_communicating.
    cbn in *.
    do 2 (eapply trans_bind_r; [cbn; eauto |]); cbn.
    destruct e.
    + eapply (trans_ChoiceI Fin.F1); [| reflexivity].
      constructor.
      rewrite EQP; auto.
    + eapply (trans_ChoiceI Fin.F1); [| reflexivity].
      constructor.
      rewrite EQP; auto.
  - left.
    apply trans_get_head in TRP.
    apply trans_get_head in TRQ.
    destruct TRP as (? & TRP & EQP).
    destruct TRQ as (? & TRQ & EQQ).
    rewrite unfold_communicating.
    cbn in *.
    do 2 (eapply trans_bind_r; [cbn; eauto |]); cbn.
    destruct e, e0, a; try destruct a0.
    destruct (are_opposite a a0).
    eapply (trans_ChoiceI (Fin.FS Fin.F1)); [| reflexivity].
    rewrite EQP.
    destruct v.
    eapply trans_trigger'.
    all: eapply (trans_ChoiceI Fin.F1); [| reflexivity].
    all: rewrite EQP.
    all: repeat match goal with | h : unit |- _ => destruct h end.
    eapply trans_trigger'.
    all: constructor; reflexivity.
  - right; left.
    destruct (trans_get_head TRP) as (? & TRP' & EQP).
    pose proof (trans_val_invT TRQ); subst; destruct v0.
    apply trans_get_head in TRQ.
    destruct TRQ as (TRQ & EQQ).
    do 2 split; auto.
    rewrite unfold_communicating.
    cbn in *.
    do 2 (eapply trans_bind_r; [cbn; eauto |]); cbn.
    destruct e; auto.
  - right; right.
    pose proof (trans_val_invT TRP); subst; destruct v.
    destruct (trans_get_head TRP) as (TRP' & EQP).
    destruct (trans_get_head TRQ) as (? & ? & ? & TRQ' & EQQ).
    do 2 split; auto.
    rewrite unfold_communicating.
    cbn in *.
    do 2 (eapply trans_bind_r; [cbn; eauto |]); cbn; auto.
  - (* We cannot if P returns *)
    right; right.
    pose proof (trans_val_invT TRP); subst; destruct v.
    destruct (trans_get_head TRP) as (TRP' & EQP).
    destruct (trans_get_head TRQ) as (? & TRQ' & EQQ).
    do 2 split; auto.
    rewrite unfold_communicating.
    cbn in *.
    do 2 (eapply trans_bind_r; [cbn; eauto |]); cbn; auto.
   - (* We cannot if P returns *)
    right; right.
    pose proof (trans_val_invT TRP); subst; destruct v.
    destruct (trans_get_head TRP) as (TRP' & EQP).
    pose proof (trans_val_invT TRQ); subst; destruct v0.
    destruct (trans_get_head TRQ) as (TRQ' & EQQ).
    do 2 split; auto.
    rewrite unfold_communicating.
    cbn in *.
    do 2 (eapply trans_bind_r; [cbn; eauto |]); cbn; auto.
 Qed.

Lemma trans_communicatingR {E} :
  forall l l' (P P' Q Q' : ctree (_ +' E) unit),
    trans l P P' ->
    trans l' Q Q' ->
    (trans l' (communicating P Q) (communicating P Q') \/
       (l = val tt /\ P' ≅ CTree.stuckI /\ trans l' (communicating P Q) Q') \/
       (l' = val tt /\ Q' ≅ CTree.stuckI /\ trans l (communicating P Q) P')
    ).
Proof.
  intros * TRP TRQ; cbn in *.
  destruct l, l'.
  - left.
    apply trans_get_head in TRP.
    apply trans_get_head in TRQ.
    destruct TRP as (? & ? & ? & TRP & EQP).
    destruct TRQ as (? & ? & ? & TRQ & EQQ).
    cbn in *.
    rewrite unfold_communicating.
    do 2 (eapply trans_bind_r; [cbn; eauto |]); cbn.
    eapply (trans_ChoiceI (Fin.FS Fin.F1)); [| reflexivity].
    rewrite EQQ.
    pose proof (@trans_ChoiceV _ _ x2 (fun i : fin x2 => communicating P (x3 i)) x4); auto.
  - left.
    apply trans_get_head in TRP.
    apply trans_get_head in TRQ.
    destruct TRP as (? & ? & ? & TRP & EQP).
    destruct TRQ as (? & TRQ & EQQ).
    rewrite unfold_communicating.
    cbn in *.
    do 2 (eapply trans_bind_r; [cbn; eauto |]); cbn.
    eapply (trans_ChoiceI (Fin.FS Fin.F1)); [| reflexivity].
    constructor; rewrite EQQ; auto.
  - right; right.
    pose proof (trans_val_invT TRQ); subst; destruct v.
    destruct (trans_get_head TRP) as (? & ? & ? & TRP' & EQP).
    destruct (trans_get_head TRQ) as (TRQ' & EQQ).
    do 2 split; auto.
    rewrite unfold_communicating.
    cbn in *.
    do 2 (eapply trans_bind_r; [cbn; eauto |]); cbn; auto.
  - left.
    destruct (trans_get_head TRP) as (? & TRP' & EQP).
    destruct (trans_get_head TRQ) as (? & ? & ? & TRQ' & EQQ).
    rewrite unfold_communicating.
    cbn in *.
    do 2 (eapply trans_bind_r; [cbn; eauto |]); cbn; auto.
    destruct e.
    + eapply (trans_ChoiceI (Fin.FS Fin.F1)); [| reflexivity].
      rewrite EQQ; econstructor; auto.
    + eapply (trans_ChoiceI (Fin.FS Fin.F1)); [| reflexivity].
      rewrite EQQ; econstructor; auto.
  - left.
    destruct (trans_get_head TRP) as (? & TRP' & EQP).
    destruct (trans_get_head TRQ) as (? & TRQ' & EQQ).
    rewrite unfold_communicating.
    cbn in *.
    do 2 (eapply trans_bind_r; [cbn; eauto |]); cbn; auto.
    destruct e, e0, a; try destruct a0.
    destruct (are_opposite a a0).
    eapply (trans_ChoiceI (Fin.FS (Fin.FS Fin.F1))); [| reflexivity].
    rewrite EQQ.
    destruct v,v0.
    eapply trans_trigger'.
    all: eapply (trans_ChoiceI (Fin.FS Fin.F1)); [| reflexivity].
    all: rewrite EQQ.
    all: repeat match goal with | h : unit |- _ => destruct h end.
    eapply trans_trigger'.
    all: constructor; reflexivity.
  - right; right.
    pose proof (trans_val_invT TRQ); subst; destruct v0.
    destruct (trans_get_head TRP) as (? & TRP' & EQP).
    destruct (trans_get_head TRQ) as (TRQ' & EQQ).
    do 2 split; auto.
    rewrite unfold_communicating.
    cbn in *.
    do 2 (eapply trans_bind_r; [cbn; eauto |]); cbn; auto.
    destruct e; eauto.
  - right; left.
    pose proof (trans_val_invT TRP); subst; destruct v.
    destruct (trans_get_head TRP) as (TRP' & EQP).
    destruct (trans_get_head TRQ) as (? & ? & ? & TRQ' & EQQ).
    do 2 split; auto.
    rewrite unfold_communicating.
    cbn in *.
    do 2 (eapply trans_bind_r; [cbn; eauto |]); cbn; auto.
  - right; left.
    pose proof (trans_val_invT TRP); subst; destruct v.
    destruct (trans_get_head TRP) as (TRP' & EQP).
    destruct (trans_get_head TRQ) as (? & TRQ' & EQQ).
    do 2 split; auto.
    rewrite unfold_communicating.
    cbn in *.
    do 2 (eapply trans_bind_r; [cbn; eauto |]); cbn; auto.
  - right; left.
    pose proof (trans_val_invT TRP); subst; destruct v.
    pose proof (trans_val_invT TRQ); subst; destruct v0.
    destruct (trans_get_head TRP) as (TRP' & EQP).
    destruct (trans_get_head TRQ) as (TRQ' & EQQ).
    do 2 split; auto.
    rewrite unfold_communicating.
    cbn in *.
    do 2 (eapply trans_bind_r; [cbn; eauto |]); cbn; auto.
Qed.

Module CCSNotationsSem.

  Declare Scope ccs_scope.

  Notation "0" := nil: ccs_scope.
  Infix "+" := plus (at level 50, left associativity).
  Infix "∥" := communicating (at level 29, left associativity).

End CCSNotationsSem.

Import CCSNotationsSem.
Open Scope ccs_scope.

Section Theory.

  Variable (E : Type -> Type).
  Notation ccs := (ccs E).


  Lemma plsC: forall (p q : ccs), p+q ~ q+p.
  Proof.
    apply choiceI2_commut.
  Qed.

  Lemma plsA (p q r : ccs): p+(q+r) ~ (p+q)+r.
  Proof.
    symmetry; apply choiceI2_assoc.
  Qed.

  Lemma pls0p (p : ccs) : 0 + p ~ p.
  Proof.
    apply choiceI2_stuckI_l.
  Qed.

  Lemma plsp0 (p : ccs) : p + 0 ~ p.
  Proof. now rewrite plsC, pls0p. Qed.

  Lemma plsidem (p : ccs) : p + p ~ p.
  Proof.
    apply choiceI2_idem.
  Qed.

  Lemma paraC: forall (p q : ccs), p ∥ q ~ q ∥ p.
  Proof.
    coinduction ? CIH; symmetric.
    intros p q l r tr.
    cbn in *.
    rewrite unfold_communicating in tr.
  Admitted.

  Lemma para0p : forall (p : ccs), 0 ∥ p ~ p.
  Proof.
  Admitted.

  Lemma commC: forall (p q : ccs), p ∥ q ~ q ∥ p.
  Proof.
  Admitted.

End Theory.

Import CCSNotations.
Open Scope term_scope.

