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
  CTreesTheory.

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
	   Syntax
     Head.

From Coinduction Require Import
	coinduction rel tactics.

(* Import CTree. *)

Import CTreeNotations.
Open Scope ctree_scope.

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

Definition ccsE : Type -> Type := ActionE.

Definition ccsT' T := ctree' ccsE T.
Definition ccsT := ctree ccsE.

Definition ccs' := ccsT' unit.
Definition ccs  := ccsT unit.

(*| Process algebra |*)
Section Combinators.

  (* A bit annoying. The [nil] process should exhibit no behavior.
     However we do observe returned value, so [Ret tt] is not ideal
from this perspective. [stuck] seems like a good alternative, but that
would therefore require from [get_head] to catch on stuck processes and
reinterpret them as terminating ones when passing them to [communicating].
Furthermore comes the question of cutting off dead branches: if nil is [Ret tt],
failure could be modelled as stuck processes, but not otherwise.
Unless one is silent stuck, the other visible stuck...
   *)
	Definition nil : ccs := ChoiceV 0 (fun x : fin 0 => match x with end).

	Definition prefix (a : action) (P: ccs) : ccs := trigger (Act a);; P.

	Definition plus (P Q : ccs) : ccs := choiceI2 P Q.

  (* Stuck? Failure event? *)
  Definition h_restrict (c : chan) : ActionE ~> ctree ccsE :=
    fun _ e => let '(Act a) := e in
            match a with
            | Send c'
            | Rcv c' =>
                if (c =? c')%string then CTree.stuck else trigger e
            end.

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
      | HVis eP kP, HVis eQ kQ =>
          match eP, kP, eQ, kQ with
          | Act a, kP, Act b, kQ =>
              if are_opposite a b
              then
                choiceI3 (TauV (F (kP tt) (kQ tt)))
                         (trigger (Act a);; F (kP tt) Q)
                         (trigger (Act b);; F P (kQ tt))
              else
                choiceI2 (trigger (Act a);; F (kP tt) Q)
                         (trigger (Act b);; F P (kQ tt))
          end
      end.

  (* Option 1
     Difference stuck pour erreur et 0 pour 0 : get_head les traite différemment
     Pour ce qui est de la divergence d'un process, deux options :
     - toujours ternaire, une seule head dans deux branches, seulement comme dans la troisième
     - get_head parallel

   *)

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


bang p = get_head P ;;
         match hd with
         | choiceV k => choiceV k (fun i => k i || P)
         | Vis e k => Vis e k (fun i => k i || P)


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
   | HVis eP kP, HVis eQ kQ =>
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
   end)%ctree.

Lemma unfold_communicating : forall P Q, communicating P Q ≅ communicating_ P Q.
Proof.
  intros.
	now step.
Qed.

#[global] Instance communicating_equ :
  Proper (equ eq ==> equ eq ==> equ eq) communicating.
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
      constructor.
      intros [|].
      step; constructor; auto.
      step; constructor; auto.
    + dependent induction eqp.
      dependent induction eqq.
      destruct e0, e2.
      * destruct (are_opposite a a0).
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
Qed.

Lemma trans_communicatingL : forall l (P P' Q : ccs),
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

Definition comm a : label := obs (Act a) tt.
Lemma trans_communicatingSynch : forall a b (P P' Q Q' : ccs),
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

Lemma trans_communicatingL :
  forall l l' (P P' Q Q' : ccs),
    trans l P P' ->
    trans l' Q Q' ->
    (trans l (communicating P Q) (communicating P' Q) \/
       (l' = val tt /\ Q' ≅ CTree.stuck /\ trans l  (communicating P Q) P') \/
       (l = val tt /\ P' ≅ CTree.stuck /\ trans l' (communicating P Q) Q')
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
    eapply (trans_ChoiceI Fin.F1); [| reflexivity].
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
    destruct e, e0. 
    destruct (are_opposite a a0).
    + eapply (trans_ChoiceI (Fin.FS Fin.F1)); [| reflexivity].
      rewrite EQP.
      destruct v.
      eapply trans_trigger'.
    + eapply (trans_ChoiceI Fin.F1); [| reflexivity].
      rewrite EQP.
      repeat match goal with | h : unit |- _ => destruct h end.
      eapply trans_trigger'.
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

Lemma trans_communicatingR :
  forall l l' (P P' Q Q' : ccs),
    trans l P P' ->
    trans l' Q Q' ->
    (trans l' (communicating P Q) (communicating P Q') \/
       (l = val tt /\ P' ≅ CTree.stuck /\ trans l' (communicating P Q) Q') \/
       (l' = val tt /\ Q' ≅ CTree.stuck /\ trans l (communicating P Q) P')
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
    eapply (trans_ChoiceI (Fin.FS Fin.F1)); [| reflexivity].
    rewrite EQQ; econstructor; auto.
  - left.
    destruct (trans_get_head TRP) as (? & TRP' & EQP).
    destruct (trans_get_head TRQ) as (? & TRQ' & EQQ).
    rewrite unfold_communicating.
    cbn in *.
    do 2 (eapply trans_bind_r; [cbn; eauto |]); cbn; auto.
    destruct e, e0.
    destruct (are_opposite a a0).
    + eapply (trans_ChoiceI (Fin.FS (Fin.FS Fin.F1))); [| reflexivity].
      rewrite EQQ.
      destruct v,v0.
      eapply trans_trigger'.
    + eapply (trans_ChoiceI (Fin.FS Fin.F1)); [| reflexivity].
      rewrite EQQ.
      repeat match goal with | h : unit |- _ => destruct h end.
      eapply trans_trigger'.
  - right; right.
    pose proof (trans_val_invT TRQ); subst; destruct v0.
    destruct (trans_get_head TRP) as (? & TRP' & EQP).
    destruct (trans_get_head TRQ) as (TRQ' & EQQ).
    do 2 split; auto.
    rewrite unfold_communicating.
    cbn in *.
    do 2 (eapply trans_bind_r; [cbn; eauto |]); cbn; auto.
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

Notation "0" := nil: ccs_scope.
Infix "+" := plus (at level 50, left associativity).
Infix "∥" := communicating (at level 29, left associativity).

Section Theory.

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
    (* apply choiceI2_stuck_l. *)
  (* Qed. *)
  Admitted.

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
Open Scope ccs_scope.

(* fun P Q => bisim (model P) (model Q): is this weak bisimulation of CCS?

   -> : term -> term -> Prop
   -ccs> : ccs -> ccs -> Prop as
   -sem> : term -> term -> Prop := fun P Q => model P -ccs> model Q
*)

Fixpoint model (t : term) : ccs :=
	match t with
	| 0      => nil
	| a · P  => prefix a (model P)
	| TauT P => TauV (model P)
	| P ∥ Q  => communicating (model P) (model Q)
	| P ⊕ Q  => plus (model P) (model Q)
	| P ∖ c  => restrict c (model P)
	end.

(*
Variant step_ccs : ccs -> option action -> ccs -> Prop :=
| Sted_comm : forall (t : ccs) a u k,
	schedule t u ->
  u ≅ trigger (Act a);; k ->
	step_ccs t (Some a) k
| Step_tau : forall (t : ccs) u k,
	schedule t u ->
  u ≅ trigger Tau;; k ->
	step_ccs t None k.

Definition step_sem : term -> option action -> term -> Prop :=
	fun P a Q => step_ccs (model P) a (model Q).
*)

Module DenNotations.

  (* Notations for patterns *)
  Notation "'synchP' e" := (inl1 e) (at level 10).
  Notation "'actP' e" := (inr1 (inl1 e)) (at level 10).
  Notation "'deadP' e" :=  (inr1 (inr1 e)) (at level 10).

  Notation "⟦ t ⟧" := (model t).
  (* Notation "P '⊢' a '→ccs' Q" := (step_ccs P a Q) (at level 50). *)
  (* Notation "P '⊢' a '→sem' Q" := (step_sem P a Q) (at level 50). *)

End DenNotations.

Import DenNotations.
