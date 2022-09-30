From Coq Require Export
     Strings.String.

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

From CTree Require Import
	   CTree
     Eq
 	   Interp.Interp
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
		rP <- head P;;
		rQ <- head Q;;

    (* And then proceed to:
         - collect all interleavings of visible brs and visible events
         - dismiss terminated computations, disregarding their returned values
         - when encountering two synchronizable actions, adding the communication
         as a third possibility
     *)
    match rP, rQ with
<<<<<<< HEAD
    | HRet rP, _ => Q
    | _, HRet rQ => P
    | HChoice c kP, HChoice c' kQ =>
        chooseI2 (ChoiceV c (fun i => F (kP i) Q))
                 (ChoiceV c' (fun i => F P (kQ i)))
    | HChoice c kP, HVis e kQ =>
        chooseI2 (ChoiceV c (fun i => F (kP i) Q))
                 (Vis e     (fun x => F P (kQ x)))
    | HVis e kP, HChoice c kQ =>
        chooseI2 (Vis e     (fun x => F (kP x) Q))
                 (ChoiceV c (fun i => F P (kQ i)))
    | HVis eP kP, HVis eQ kQ =>
=======
    | ARet rP, _ => Q
    | _, ARet rQ => P
    | ABr kP, ABr kQ =>
        brD2 (BrS _ (fun i => F (kP i) Q))
                 (BrS _ (fun i => F P (kQ i)))
    | ABr kP, AVis e kQ =>
        brD2 (BrS _ (fun i => F (kP i) Q))
                 (Vis e     (fun x => F P (kQ x)))
    | AVis e kP, ABr kQ =>
        brD2 (Vis e     (fun x => F (kP x) Q))
                 (BrS _ (fun i => F P (kQ i)))
    | AVis eP kP, AVis eQ kQ =>
>>>>>>> master
        match eP, kP, eQ, kQ with
        | Act a, kP, Act b, kQ =>
            if are_opposite a b
            then
<<<<<<< HEAD
              chooseI3 (tauV (F (kP tt) (kQ tt)))
                       (trigger (Act a);; F (kP tt) Q)
                       (trigger (Act b);; F P (kQ tt))
            else
              chooseI2 (trigger (Act a);; F (kP tt) Q)
=======
              brD3 (Step (F (kP tt) (kQ tt)))
                       (trigger (Act a);; F (kP tt) Q)
                       (trigger (Act b);; F P (kQ tt))
            else
              brD2 (trigger (Act a);; F (kP tt) Q)
>>>>>>> master
                       (trigger (Act b);; F P (kQ tt))
        end
    end.

Notation communicating_ P Q :=
	(rP <- head P;;
	 rQ <- head Q;;
   match rP, rQ with
<<<<<<< HEAD
   | HRet rP, _ => Q
   | _, HRet rQ => P
   | HChoice c kP, HChoice c' kQ =>
       chooseI2 (ChoiceV c  (fun i => communicating (kP i) Q))
                (ChoiceV c' (fun i => communicating P (kQ i)))
   | HChoice c kP, HVis e kQ =>
       chooseI2 (ChoiceV c (fun i => communicating (kP i) Q))
                (Vis e     (fun x => communicating P (kQ x)))
   | HVis e kP, HChoice c kQ =>
       chooseI2 (Vis e     (fun x => communicating (kP x) Q))
                (ChoiceV c (fun i => communicating P (kQ i)))
   | HVis eP kP, HVis eQ kQ =>
=======
   | ARet rP, _ => Q
   | _, ARet rQ => P
   | ABr kP, ABr kQ =>
       brD2 (BrS _ (fun i => communicating (kP i) Q))
                (BrS _ (fun i => communicating P (kQ i)))
   | ABr kP, AVis e kQ =>
       brD2 (BrS _ (fun i => communicating (kP i) Q))
                (Vis e     (fun x => communicating P (kQ x)))
   | AVis e kP, ABr kQ =>
       brD2 (Vis e     (fun x => communicating (kP x) Q))
                (BrS _ (fun i => communicating P (kQ i)))
   | AVis eP kP, AVis eQ kQ =>
>>>>>>> master
       match eP, kP, eQ, kQ with
       | Act a, kP, Act b, kQ =>
           if are_opposite a b
           then
<<<<<<< HEAD
             chooseI3 (tauV (communicating (kP tt) (kQ tt)))
                      (trigger (Act a);; communicating (kP tt) Q)
                      (trigger (Act b);; communicating P (kQ tt))
           else
             chooseI2 (trigger (Act a);; communicating (kP tt) Q)
=======
             brD3 (Step (communicating (kP tt) (kQ tt)))
                      (trigger (Act a);; communicating (kP tt) Q)
                      (trigger (Act b);; communicating P (kQ tt))
           else
             brD2 (trigger (Act a);; communicating (kP tt) Q)
>>>>>>> master
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
  apply in_bind_ctx; [apply head_equ; auto | intros hdP1 hdP2 eqp].
  eapply (fbt_bt (bind_ctx_equ_t _ _)).
  apply in_bind_ctx; [apply head_equ; auto | intros hdQ1 hdQ2 eqq].
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
        intros [| |].
        step; constructor; auto.
        upto_bind_eq; auto.
        upto_bind_eq; auto.
        constructor.
        intros [|].
        upto_bind_eq; auto.
        upto_bind_eq; auto.
Qed.

Lemma trans_communicatingL : forall l (P P' Q : ccs),
    trans l P P' ->
    trans l (communicating P Q) (communicating P' Q).
Proof.
  intros * TR.
  (* red in TR; red. *)
  pose proof (trans_head TR) as TRhd.
  destruct l.
  - destruct TRhd as (? & c & k & x & TRhd & EQ).
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
  apply trans_head in TRP as (kP & TRP & EQP).
  apply trans_head in TRQ as (kQ & TRQ & EQQ).
  rewrite unfold_communicating.
  eapply trans_bind_r; [apply TRP |].
  eapply trans_bind_r; [apply TRQ |].
  cbn; rewrite OP.
<<<<<<< HEAD
  eapply trans_choiceI with (x := t31); [| reflexivity].
=======
  eapply trans_brD with (x := Fin.F1); [| reflexivity].
>>>>>>> master
  rewrite EQP, EQQ.
  apply trans_step.
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
<<<<<<< HEAD
  - apply trans_get_head in TRP.
    apply trans_get_head in TRQ. 
    destruct TRP as (? & ? & ? & ? & TRP & EQP).
    destruct TRQ as (? & ? & ? & ? & TRQ & EQQ).
    rewrite unfold_communicating.
    cbn in *.
    do 2 (eapply trans_bind_r; [cbn; eauto |]); cbn.
    eapply (trans_choiceI _ _ true); [| reflexivity].
    rewrite EQP.
    destruct x0; repeat try destruct s.
    all: remember c as c'; destruct c;
      pose proof (@trans_choiceV _ _ _ _ _ (subevent _ c') (fun t => communicating (x1 t) Q) x2); auto.
  - apply trans_get_head in TRP.
    apply trans_get_head in TRQ.
    destruct TRP as (? & ? & ? & ? & TRP & EQP).
=======
  - apply trans_head in TRP.
    apply trans_head in TRQ.
    destruct TRP as (? & ? & ? & TRP & EQP).
    destruct TRQ as (? & ? & ? & TRQ & EQQ).
    rewrite unfold_communicating.
    cbn in *.
    do 2 (eapply trans_bind_r; [cbn; eauto |]); cbn.
    eapply (trans_brD _ Fin.F1); [| reflexivity].
    rewrite EQP.
    pose proof (@trans_brS _ _ x (fun i : fin x => communicating (x0 i) Q) x1); auto.
  - apply trans_head in TRP.
    apply trans_head in TRQ.
    destruct TRP as (? & ? & ? & TRP & EQP).
>>>>>>> master
    destruct TRQ as (? & TRQ & EQQ).
    rewrite unfold_communicating.
    cbn in *.
    do 2 (eapply trans_bind_r; [cbn; eauto |]); cbn.
<<<<<<< HEAD
    eapply (trans_choiceI _ _ true); [| reflexivity].
    rewrite EQP.
    destruct x0; repeat try destruct s.
    all: remember c as c'; destruct c;
      pose proof (@trans_choiceV _ _ _ _ _ (subevent _ c') (fun t => communicating (x1 t) Q) x2); auto.
  - apply trans_get_head in TRP.
    apply trans_get_head in TRQ.
=======
    eapply (trans_brD _ Fin.F1); [| reflexivity].
    rewrite EQP.
    pose proof (@trans_brS _ _ x (fun i : fin x => communicating (x0 i) Q) x1); auto.
  - apply trans_head in TRP.
    apply trans_head in TRQ.
>>>>>>> master
    destruct TRP as (? & TRP & EQP).
    destruct TRQ as (? & ? & ? & ? & TRQ & EQQ).
    rewrite unfold_communicating.
    cbn in *.
    do 2 (eapply trans_bind_r; [cbn; eauto |]); cbn.
<<<<<<< HEAD
    eapply (trans_choiceI _ _ true); [| reflexivity].
=======
    eapply (trans_brD _ Fin.F1); [| reflexivity].
>>>>>>> master
    constructor.
    rewrite EQP; auto.
  - apply trans_head in TRP.
    apply trans_head in TRQ.
    destruct TRP as (? & TRP & EQP).
    destruct TRQ as (? & TRQ & EQQ).
    rewrite unfold_communicating.
    cbn in *.
    do 2 (eapply trans_bind_r; [cbn; eauto |]); cbn.
    destruct e, e0.
    destruct (are_opposite a a0).
<<<<<<< HEAD
    + eapply (trans_choiceI _ _ t32); [| reflexivity].
      rewrite EQP.
      destruct v.
      eapply trans_trigger'.
    + eapply (trans_choiceI _ _ true); [| reflexivity].
=======
    + eapply (trans_brD _ (Fin.FS Fin.F1)); [| reflexivity].
      rewrite EQP.
      destruct v.
      eapply trans_trigger'.
    + eapply (trans_brD _ Fin.F1); [| reflexivity].
>>>>>>> master
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
<<<<<<< HEAD
  - apply trans_get_head in TRP.
    apply trans_get_head in TRQ.
    destruct TRP as (? & ? & ? & ? & TRP & EQP).
    destruct TRQ as (? & ? & ? & ? & TRQ & EQQ).
    cbn in *.
    rewrite unfold_communicating.
    do 2 (eapply trans_bind_r; [cbn; eauto |]); cbn.
    eapply (trans_choiceI _ _ false); [| reflexivity].
    rewrite EQQ.
    destruct x4; repeat try destruct s.
    all: remember c as c'; destruct c;
      pose proof (@trans_choiceV _ _ _ _ _ (subevent _ c') (fun t => communicating P (x5 t)) x6); auto.
  - apply trans_get_head in TRP.
    apply trans_get_head in TRQ.
    destruct TRP as (? & ? & ? & ? & TRP & EQP).
=======
  - apply trans_head in TRP.
    apply trans_head in TRQ.
    destruct TRP as (? & ? & ? & TRP & EQP).
    destruct TRQ as (? & ? & ? & TRQ & EQQ).
    cbn in *.
    rewrite unfold_communicating.
    do 2 (eapply trans_bind_r; [cbn; eauto |]); cbn.
    eapply (trans_brD _ (Fin.FS Fin.F1)); [| reflexivity].
    rewrite EQQ.
    pose proof (@trans_brS _ _ x2 (fun i : fin x2 => communicating P (x3 i)) x4); auto.
  - apply trans_head in TRP.
    apply trans_head in TRQ.
    destruct TRP as (? & ? & ? & TRP & EQP).
>>>>>>> master
    destruct TRQ as (? & TRQ & EQQ).
    rewrite unfold_communicating.
    cbn in *.
    do 2 (eapply trans_bind_r; [cbn; eauto |]); cbn.
<<<<<<< HEAD
    eapply (trans_choiceI _ _ false); [| reflexivity].
    constructor; rewrite EQQ; auto.
  - destruct (trans_get_head TRP) as (? & TRP' & EQP).
    destruct (trans_get_head TRQ) as (? & ? & ? & ? & TRQ' & EQQ).
    rewrite unfold_communicating.
    cbn in *.
    do 2 (eapply trans_bind_r; [cbn; eauto |]); cbn; auto.
    eapply (trans_choiceI _ _ false); [| reflexivity].
=======
    eapply (trans_brD _ (Fin.FS Fin.F1)); [| reflexivity].
    constructor; rewrite EQQ; auto.
  - destruct (trans_head TRP) as (? & TRP' & EQP).
    destruct (trans_head TRQ) as (? & ? & ? & TRQ' & EQQ).
    rewrite unfold_communicating.
    cbn in *.
    do 2 (eapply trans_bind_r; [cbn; eauto |]); cbn; auto.
    eapply (trans_brD _ (Fin.FS Fin.F1)); [| reflexivity].
>>>>>>> master
    rewrite EQQ; econstructor; auto.
  - destruct (trans_head TRP) as (? & TRP' & EQP).
    destruct (trans_head TRQ) as (? & TRQ' & EQQ).
    rewrite unfold_communicating.
    cbn in *.
    do 2 (eapply trans_bind_r; [cbn; eauto |]); cbn; auto.
    destruct e, e0.
    destruct (are_opposite a a0).
<<<<<<< HEAD
    + eapply (trans_choiceI _ _ t33); [| reflexivity].
      rewrite EQQ.
      destruct v,v0.
      eapply trans_trigger'.
    + eapply (trans_choiceI _ _ false); [| reflexivity].
=======
    + eapply (trans_brD _ (Fin.FS (Fin.FS Fin.F1))); [| reflexivity].
      rewrite EQQ.
      destruct v,v0.
      eapply trans_trigger'.
    + eapply (trans_brD _ (Fin.FS Fin.F1)); [| reflexivity].
>>>>>>> master
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
  destruct H as (NOTV & ? & TR & EQ); apply trans_head_inv in TR; easy.
  destruct H as (hdP & TRhdP & TR).
  edestruct @trans_bind_inv; [apply TR | | ]; clear TR.
  destruct H as (NOTV & ? & TR & EQ); apply trans_head_inv in TR; easy.
  destruct H as (hdQ & TRhdQ & TR).
  destruct hdP; try easy.
  + destruct hdQ; try easy.
    *
      inv_trans.
      { apply trans_BrS_inv in TR as (x & EQ & ->).

      inv_trans;
        apply trans_BrS_inv in TR as (x & EQ & ->);
        eapply trans_ABr in TRhdP;
        eapply trans_ABr in TRhdQ;
        eauto 8.
    * inv_trans;
        ( apply trans_BrS_inv in TR as (x & EQ & ->) ||
          apply trans_vis_inv in TR as (x & EQ & ->));
          eapply trans_ABr in TRhdP;
          eapply trans_AVis in TRhdQ;
          eauto 8.
  + destruct hdQ.
    * apply trans_ARet in TRhdQ; destruct r0.
    * inv_trans;
        ( apply trans_BrS_inv in TR as (x & EQ & ->) ||
          apply trans_vis_inv in TR as (x & EQ & ->));
        eapply trans_AVis in TRhdP;
          eapply trans_ABr in TRhdQ;
        eauto 8.
    * destruct e, e0.
      destruct (are_opposite a a0) eqn:OP; inv_trans.
      all: ( apply trans_BrS_inv in TR as (x & EQ & ->) ||
             apply trans_trigger_inv in TR as (x & EQ & ->)).
      all: eapply trans_AVis in TRhdP;
        eapply trans_AVis in TRhdQ.
      all: clear_tt.
      all: eauto 12.

      right; right; eauto 8.
      left.
      { repeat right.
        apply trans_BrS_inv in TR.
        destruct TR as (x & EQ & ->).
        do 4 eexists; repeat split; eauto.
        eapply trans_AVis in TRhdP; apply TRhdP.
        eapply trans_AVis in TRhdQ; apply TRhdQ.
      }
      { left.
        apply trans_trigger_inv in TR.
        destruct TR as (x & -> & EQ).
        eexists; split; eauto.
        eapply trans_AVis in TRhdP.
        destruct x; apply TRhdP.
      }
      { right; left.
        apply trans_trigger_inv in TR.
        destruct TR as (x & -> & EQ).
        eexists; split; eauto.
        eapply trans_AVis in TRhdQ.
        destruct x; apply TRhdQ.
      }
      { left.
        apply trans_trigger_inv in TR.
        destruct TR as (x & -> & EQ).
        eexists; split; eauto.
        eapply trans_AVis in TRhdP.
        destruct x; apply TRhdP.
      }
      { right; left.
        apply trans_trigger_inv in TR.
        destruct TR as (x & -> & EQ).
        eexists; split; eauto.
        eapply trans_AVis in TRhdQ.
        destruct x; apply TRhdQ.
      }
Qed.

 *)
Admitted.

<<<<<<< HEAD
Inductive heads E C X :=
| Lheads : (@head E C X) -> heads E C X
| Rheads : (@head E C X) -> heads E C X
| Sheads : (@head E C X * @head E C X) -> heads E C X.
=======
Inductive hactions E X :=
| Lactions : (@haction E X) -> hactions E X
| Ractions : (@haction E X) -> hactions E X
| Sactions : (@haction E X * @haction E X) -> hactions E X.
>>>>>>> master

Definition pairing {X} (x1 : X + X) (x2 : X) : X * X :=
  match x1 with
  | inl x1 => (x1,x2)
  | inr x1 => (x2,x1)
  end.

<<<<<<< HEAD
Definition get_head_cst {E C X} (hd : @head E C X + @head E C X) : ctree E C X -> ctree E C (heads E C X) :=
  cofix get_head_cst (t : ctree E C X) :=
    match observe t with
    | RetF x            => Ret (Sheads (pairing hd (HRet x)))
    | VisF e k          => Ret (Sheads (pairing hd (HVis e k)))
    | ChoiceF true c k  => Ret (Sheads (pairing hd (HChoice c k)))
    | ChoiceF false c k => Choice false c (fun i => get_head_cst (k i))
    end.

Definition get_heads {E X} : ctree E ccsC X -> ctree E ccsC X -> ctree E ccsC (heads E ccsC X) :=
  cofix get_heads (t u : ctree E ccsC X) :=
    match observe t, observe u with
    | ChoiceF false c1 k1, ChoiceF false c2 k2 =>
        ChoiceI c1 (fun i => ChoiceI c2 (fun j => get_heads (k1 i) (k2 j)))
    | RetF x, ChoiceF false _ _     =>
        chooseI2 (Ret (Lheads (HRet x))) (get_head_cst (inl (HRet x)) u)
    | VisF e k, ChoiceF false _ _      =>
        chooseI2 (Ret (Lheads (HVis e k))) (get_head_cst (inl (HVis e k)) u)
    | ChoiceF true c k, ChoiceF false _ _ =>
        chooseI2 (Ret (Lheads (HChoice c k))) (get_head_cst (inl (HChoice c k)) u)
    | ChoiceF false _ _, RetF x      =>
        chooseI2 (Ret (Rheads (HRet x))) (get_head_cst (inr (HRet x)) u)
    | ChoiceF false _ _, VisF e k       =>
        chooseI2 (Ret (Rheads (HVis e k))) (get_head_cst (inr (HVis e k)) u)
    | ChoiceF false _ _, ChoiceF true c k =>
        chooseI2 (Ret (Rheads (HChoice c k))) (get_head_cst (inr (HChoice c k)) u)
=======
Definition action_cst {E X} (hd : @haction E X + @haction E X) : ctree E X -> ctree E (hactions E X) :=
  cofix action_cst (t : ctree E X) :=
    match observe t with
    | RetF x            => Ret (Sactions (pairing hd (ARet x)))
    | VisF e k          => Ret (Sactions (pairing hd (AVis e k)))
    | BrF true n k  => Ret (Sactions (pairing hd (ABr k)))
    | BrF false n k => Br false n (fun i => action_cst (k i))
    end.

Definition heads {E X} : ctree E X -> ctree E X -> ctree E (hactions E X) :=
  cofix heads (t u : ctree E X) :=
    match observe t, observe u with
    | BrF false n1 k1, BrF false n2 k2 =>
        BrD n1 (fun i => BrD n2 (fun j => heads (k1 i) (k2 j)))
    | RetF x, BrF false _ _     =>
        brD2 (Ret (Lactions (ARet x))) (action_cst (inl (ARet x)) u)
    | VisF e k, BrF false _ _      =>
        brD2 (Ret (Lactions (AVis e k))) (action_cst (inl (AVis e k)) u)
    | BrF true n k, BrF false _ _ =>
        brD2 (Ret (Lactions (ABr k))) (action_cst (inl (ABr k)) u)
    | BrF false _ _, RetF x      =>
        brD2 (Ret (Ractions (ARet x))) (action_cst (inr (ARet x)) u)
    | BrF false _ _, VisF e k       =>
        brD2 (Ret (Ractions (AVis e k))) (action_cst (inr (AVis e k)) u)
    | BrF false _ _, BrF true n k =>
        brD2 (Ret (Ractions (ABr k))) (action_cst (inr (ABr k)) u)
>>>>>>> master
    | RetF x, RetF y     =>
        Ret (Sactions (ARet x, ARet y))
    | VisF e k, RetF y     =>
<<<<<<< HEAD
        Ret (Sheads (HVis e k, HRet y))
    | ChoiceF true c k, RetF y     =>
        Ret (Sheads (HChoice c k, HRet y))
=======
        Ret (Sactions (AVis e k, ARet y))
    | BrF true n k, RetF y     =>
        Ret (Sactions (ABr k, ARet y))
>>>>>>> master
    | RetF x, VisF e' k'     =>
        Ret (Sactions (ARet x, AVis e' k'))
    | VisF e k, VisF e' k'     =>
<<<<<<< HEAD
        Ret (Sheads (HVis e k, HVis e' k'))
    | ChoiceF true c k, VisF e' k'     =>
        Ret (Sheads (HChoice c k, HVis e' k'))
    | RetF x, ChoiceF true c k'     =>
        Ret (Sheads (HRet x, HChoice c k'))
    | VisF e k, ChoiceF true c k'     =>
        Ret (Sheads (HVis e k, HChoice c k'))
    | ChoiceF true c k, ChoiceF true c' k'     =>
        Ret (Sheads (HChoice c k, HChoice c' k'))
=======
        Ret (Sactions (AVis e k, AVis e' k'))
    | BrF true n k, VisF e' k'     =>
        Ret (Sactions (ABr k, AVis e' k'))
    | RetF x, BrF true n k'     =>
        Ret (Sactions (ARet x, ABr k'))
    | VisF e k, BrF true n k'     =>
        Ret (Sactions (AVis e k, ABr k'))
    | BrF true n k, BrF true n' k'     =>
        Ret (Sactions (ABr k, ABr k'))
>>>>>>> master
    end.

Definition communicating_synch : ccs -> ccs -> ccs :=
  cofix F (P : ccs) (Q : ccs) :=
    hds <- heads P Q;;
    match hds with
    | Lactions hdP =>
        match hdP with
<<<<<<< HEAD
        | HRet rP => Q
        | HChoice c kP => ChoiceV c (fun i => F (kP i) Q)
        | HVis e kP => Vis e (fun i => F (kP i) Q)
=======
        | ARet rP => Q
        | ABr kP => BrS _ (fun i => F (kP i) Q)
        | AVis e kP => Vis e (fun i => F (kP i) Q)
>>>>>>> master
        end
    | Ractions hdQ =>
        match hdQ with
<<<<<<< HEAD
        | HRet rQ => P
        | HChoice c kQ => ChoiceV c (fun i => F P (kQ i))
        | HVis e kQ => Vis e (fun i => F P (kQ i))
=======
        | ARet rQ => P
        | ABr kQ => BrS _ (fun i => F P (kQ i))
        | AVis e kQ => Vis e (fun i => F P (kQ i))
>>>>>>> master
        end
    | Sactions (hdP,hdQ) =>
        match hdP, hdQ with
<<<<<<< HEAD
        | HRet rP, _ => Q
        | _, HRet rQ => P
        | HChoice c kP, HChoice c' kQ =>
            chooseI2 (ChoiceV c  (fun i => F (kP i) Q))
                     (ChoiceV c' (fun i => F P (kQ i)))
        | HChoice c kP, HVis e kQ =>
            chooseI2 (ChoiceV c (fun i => F (kP i) Q))
                     (Vis e     (fun x => F P (kQ x)))
        | HVis e kP, HChoice c kQ =>
            chooseI2 (Vis e     (fun x => F (kP x) Q))
                     (ChoiceV c (fun i => F P (kQ i)))
        | HVis eP kP, HVis eQ kQ =>
=======
        | ARet rP, _ => Q
        | _, ARet rQ => P
        | ABr kP, ABr kQ =>
            brD2 (BrS _ (fun i => F (kP i) Q))
                     (BrS _ (fun i => F P (kQ i)))
        | ABr kP, AVis e kQ =>
            brD2 (BrS _ (fun i => F (kP i) Q))
                     (Vis e     (fun x => F P (kQ x)))
        | AVis e kP, ABr kQ =>
            brD2 (Vis e     (fun x => F (kP x) Q))
                     (BrS _ (fun i => F P (kQ i)))
        | AVis eP kP, AVis eQ kQ =>
>>>>>>> master
            match eP, kP, eQ, kQ with
            | Act a, kP, Act b, kQ =>
                if are_opposite a b
                then
<<<<<<< HEAD
                  chooseI3 (tauV (F (kP tt) (kQ tt)))
                           (trigger (Act a);; F (kP tt) Q)
                           (trigger (Act b);; F P (kQ tt))
                else
                  chooseI2 (trigger (Act a);; F (kP tt) Q)
=======
                  brD3 (Step (F (kP tt) (kQ tt)))
                           (trigger (Act a);; F (kP tt) Q)
                           (trigger (Act b);; F P (kQ tt))
                else
                  brD2 (trigger (Act a);; F (kP tt) Q)
>>>>>>> master
                           (trigger (Act b);; F P (kQ tt))
            end
        end
    end.
