From Coq Require Export
     Strings.String.

From ITree Require Import ITree.

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

From Coinduction Require Import
	   coinduction rel tactics.

From CTree Require Import
	   Utils
	   CTrees
     Trans
 	   Interp
	   Equ
	   Bisim
     CTreesTheory
     Head.

From CTreeCCS Require Import
	   Syntax
     Denotation.
Import CTree.
Import CTreeNotations.
Open Scope ctree_scope.
Import Head.

Set Implicit Arguments.
Set Contextual Implicit.

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
                      (trigger (Act a);; communicating (kP tt) Q)
                      (trigger (Act b);; communicating P (kQ tt))
           else
             choiceI2 (trigger (Act a);; communicating (kP tt) Q)
                      (trigger (Act b);; communicating P (kQ tt))
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
  (* - rewrite EQQ; reflexivity. *)
  - destruct hdQ1, hdQ2; try now inv eqq.
    (* + rewrite EQP; reflexivity. *)
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
    (* + destruct e,e0; rewrite EQP; reflexivity. *)
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
    trans l (communicating P Q) (communicating P' Q).
Proof.
  intros * TRP TRQ.
  destruct l, l';
    try (pose proof (trans_val_invT TRP); subst; easy);
    try (pose proof (trans_val_invT TRQ); subst; easy).
  - apply trans_get_head in TRP.
    apply trans_get_head in TRQ.
    destruct TRP as (? & ? & ? & TRP & EQP).
    destruct TRQ as (? & ? & ? & TRQ & EQQ).
    rewrite unfold_communicating.
    cbn in *.
    do 2 (eapply trans_bind_r; [cbn; eauto |]); cbn.
    eapply (trans_ChoiceI Fin.F1); [| reflexivity].
    rewrite EQP.
    pose proof (@trans_ChoiceV _ _ x (fun i : fin x => communicating (x0 i) Q) x1); auto.
  - apply trans_get_head in TRP.
    apply trans_get_head in TRQ.
    destruct TRP as (? & ? & ? & TRP & EQP).
    destruct TRQ as (? & TRQ & EQQ).
    rewrite unfold_communicating.
    cbn in *.
    do 2 (eapply trans_bind_r; [cbn; eauto |]); cbn.
    eapply (trans_ChoiceI Fin.F1); [| reflexivity].
    rewrite EQP.
    pose proof (@trans_ChoiceV _ _ x (fun i : fin x => communicating (x0 i) Q) x1); auto.
  - apply trans_get_head in TRP.
    apply trans_get_head in TRQ.
    destruct TRP as (? & TRP & EQP).
    destruct TRQ as (? & ? & ? & TRQ & EQQ).
    rewrite unfold_communicating.
    cbn in *.
    do 2 (eapply trans_bind_r; [cbn; eauto |]); cbn.
    eapply (trans_ChoiceI Fin.F1); [| reflexivity].
    constructor.
    rewrite EQP; auto.
  - apply trans_get_head in TRP.
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
Qed.

Lemma trans_communicatingR :
  forall l l' (P P' Q Q' : ccs),
    trans l P P' ->
    trans l' Q Q' ->
    trans l' (communicating P Q) (communicating P Q').
Proof.
  intros * TRP TRQ; cbn in *.
  destruct l, l';
    try (pose proof (trans_val_invT TRP); subst; easy);
    try (pose proof (trans_val_invT TRQ); subst; easy).
  - apply trans_get_head in TRP.
    apply trans_get_head in TRQ.
    destruct TRP as (? & ? & ? & TRP & EQP).
    destruct TRQ as (? & ? & ? & TRQ & EQQ).
    cbn in *.
    rewrite unfold_communicating.
    do 2 (eapply trans_bind_r; [cbn; eauto |]); cbn.
    eapply (trans_ChoiceI (Fin.FS Fin.F1)); [| reflexivity].
    rewrite EQQ.
    pose proof (@trans_ChoiceV _ _ x2 (fun i : fin x2 => communicating P (x3 i)) x4); auto.
  - apply trans_get_head in TRP.
    apply trans_get_head in TRQ.
    destruct TRP as (? & ? & ? & TRP & EQP).
    destruct TRQ as (? & TRQ & EQQ).
    rewrite unfold_communicating.
    cbn in *.
    do 2 (eapply trans_bind_r; [cbn; eauto |]); cbn.
    eapply (trans_ChoiceI (Fin.FS Fin.F1)); [| reflexivity].
    constructor; rewrite EQQ; auto.
  - destruct (trans_get_head TRP) as (? & TRP' & EQP).
    destruct (trans_get_head TRQ) as (? & ? & ? & TRQ' & EQQ).
    rewrite unfold_communicating.
    cbn in *.
    do 2 (eapply trans_bind_r; [cbn; eauto |]); cbn; auto.
    eapply (trans_ChoiceI (Fin.FS Fin.F1)); [| reflexivity].
    rewrite EQQ; econstructor; auto.
  - destruct (trans_get_head TRP) as (? & TRP' & EQP).
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
Qed.

Ltac clear_tt :=
  repeat match goal with
         | h : unit |- _ => destruct h
         end.

Lemma trans_communicating_inv :
  forall l p q r,
    trans l (communicating p q) r ->
    (exists p' q' l', trans l p p' /\ trans l' q q' /\ r ≅ (communicating p' q)) \/
      (exists q' p' l', trans l q q' /\ trans l' p p' /\ r ≅ (communicating p q')) \/
      (exists p' q' a b,
          trans (comm a) p p' /\
            trans (comm b) q q' /\
            are_opposite a b /\
            r ≅ (communicating p' q')).
Proof.
(*
  intros * TR.
  rewrite unfold_communicating in TR.
  edestruct @trans_bind_inv; [apply TR | | ]; clear TR.
  destruct H as (NOTV & ? & TR & EQ); apply trans_get_head_inv in TR; easy.
  destruct H as (hdP & TRhdP & TR).
  edestruct @trans_bind_inv; [apply TR | | ]; clear TR.
  destruct H as (NOTV & ? & TR & EQ); apply trans_get_head_inv in TR; easy.
  destruct H as (hdQ & TRhdQ & TR).
  destruct hdP; try easy.
  + destruct hdQ; try easy.
    *
      inv_trans.
      { apply trans_ChoiceV_inv in TR as (x & EQ & ->).

      inv_trans;
        apply trans_ChoiceV_inv in TR as (x & EQ & ->);
        eapply trans_HChoice in TRhdP;
        eapply trans_HChoice in TRhdQ;
        eauto 8.
    * inv_trans;
        ( apply trans_ChoiceV_inv in TR as (x & EQ & ->) ||
          apply trans_vis_inv in TR as (x & EQ & ->));
          eapply trans_HChoice in TRhdP;
          eapply trans_HVis in TRhdQ;
          eauto 8.
  + destruct hdQ.
    * apply trans_HRet in TRhdQ; destruct r0.
    * inv_trans;
        ( apply trans_ChoiceV_inv in TR as (x & EQ & ->) ||
          apply trans_vis_inv in TR as (x & EQ & ->));
        eapply trans_HVis in TRhdP;
          eapply trans_HChoice in TRhdQ;
        eauto 8.
    * destruct e, e0.
      destruct (are_opposite a a0) eqn:OP; inv_trans.
      all: ( apply trans_ChoiceV_inv in TR as (x & EQ & ->) ||
             apply trans_trigger_inv in TR as (x & EQ & ->)).
      all: eapply trans_HVis in TRhdP;
        eapply trans_HVis in TRhdQ.
      all: clear_tt.
      all: eauto 12.

      right; right; eauto 8.
      left.
      { repeat right.
        apply trans_ChoiceV_inv in TR.
        destruct TR as (x & EQ & ->).
        do 4 eexists; repeat split; eauto.
        eapply trans_HVis in TRhdP; apply TRhdP.
        eapply trans_HVis in TRhdQ; apply TRhdQ.
      }
      { left.
        apply trans_trigger_inv in TR.
        destruct TR as (x & -> & EQ).
        eexists; split; eauto.
        eapply trans_HVis in TRhdP.
        destruct x; apply TRhdP.
      }
      { right; left.
        apply trans_trigger_inv in TR.
        destruct TR as (x & -> & EQ).
        eexists; split; eauto.
        eapply trans_HVis in TRhdQ.
        destruct x; apply TRhdQ.
      }
      { left.
        apply trans_trigger_inv in TR.
        destruct TR as (x & -> & EQ).
        eexists; split; eauto.
        eapply trans_HVis in TRhdP.
        destruct x; apply TRhdP.
      }
      { right; left.
        apply trans_trigger_inv in TR.
        destruct TR as (x & -> & EQ).
        eexists; split; eauto.
        eapply trans_HVis in TRhdQ.
        destruct x; apply TRhdQ.
      }
Qed.

 *)
Admitted.

Inductive heads E X :=
| Lheads : (@head E X) -> heads E X
| Rheads : (@head E X) -> heads E X
| Sheads : (@head E X * @head E X) -> heads E X.

Definition pairing {X} (x1 : X + X) (x2 : X) : X * X :=
  match x1 with
  | inl x1 => (x1,x2)
  | inr x1 => (x2,x1)
  end.

Definition get_head_cst {E X} (hd : @head E X + @head E X) : ctree E X -> ctree E (heads E X) :=
  cofix get_head_cst (t : ctree E X) :=
    match observe t with
    | RetF x            => Ret (Sheads (pairing hd (HRet x)))
    | VisF e k          => Ret (Sheads (pairing hd (HVis e k)))
    | ChoiceF true n k  => Ret (Sheads (pairing hd (HChoice k)))
    | ChoiceF false n k => Choice false n (fun i => get_head_cst (k i))
    end.

Definition get_heads {E X} : ctree E X -> ctree E X -> ctree E (heads E X) :=
  cofix get_heads (t u : ctree E X) :=
    match observe t, observe u with
    | ChoiceF false n1 k1, ChoiceF false n2 k2 =>
        ChoiceI n1 (fun i => ChoiceI n2 (fun j => get_heads (k1 i) (k2 j)))
    | RetF x, ChoiceF false _ _     =>
        choiceI2 (Ret (Lheads (HRet x))) (get_head_cst (inl (HRet x)) u)
    | VisF e k, ChoiceF false _ _      =>
        choiceI2 (Ret (Lheads (HVis e k))) (get_head_cst (inl (HVis e k)) u)
    | ChoiceF true n k, ChoiceF false _ _ =>
        choiceI2 (Ret (Lheads (HChoice k))) (get_head_cst (inl (HChoice k)) u)
    | ChoiceF false _ _, RetF x      =>
        choiceI2 (Ret (Rheads (HRet x))) (get_head_cst (inr (HRet x)) u)
    | ChoiceF false _ _, VisF e k       =>
        choiceI2 (Ret (Rheads (HVis e k))) (get_head_cst (inr (HVis e k)) u)
    | ChoiceF false _ _, ChoiceF true n k =>
        choiceI2 (Ret (Rheads (HChoice k))) (get_head_cst (inr (HChoice k)) u)
    | RetF x, RetF y     =>
        Ret (Sheads (HRet x, HRet y))
    | VisF e k, RetF y     =>
        Ret (Sheads (HVis e k, HRet y))
    | ChoiceF true n k, RetF y     =>
        Ret (Sheads (HChoice k, HRet y))
    | RetF x, VisF e' k'     =>
        Ret (Sheads (HRet x, HVis e' k'))
    | VisF e k, VisF e' k'     =>
        Ret (Sheads (HVis e k, HVis e' k'))
    | ChoiceF true n k, VisF e' k'     =>
        Ret (Sheads (HChoice k, HVis e' k'))
    | RetF x, ChoiceF true n k'     =>
        Ret (Sheads (HRet x, HChoice k'))
    | VisF e k, ChoiceF true n k'     =>
        Ret (Sheads (HVis e k, HChoice k'))
    | ChoiceF true n k, ChoiceF true n' k'     =>
        Ret (Sheads (HChoice k, HChoice k'))
    end.

Definition communicating_synch : ccs -> ccs -> ccs :=
  cofix F (P : ccs) (Q : ccs) :=
    hds <- get_heads P Q;;
    match hds with
    | Lheads hdP =>
        match hdP with
        | HRet rP => Q
        | HChoice kP => ChoiceV _ (fun i => F (kP i) Q)
        | HVis e kP => Vis e (fun i => F (kP i) Q)
        end
    | Rheads hdQ =>
        match hdQ with
        | HRet rQ => P
        | HChoice kQ => ChoiceV _ (fun i => F P (kQ i))
        | HVis e kQ => Vis e (fun i => F P (kQ i))
        end
    | Sheads (hdP,hdQ) =>
        match hdP, hdQ with
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
        end
    end.
