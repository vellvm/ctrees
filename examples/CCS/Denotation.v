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

Import CTree.

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

Definition ccs' := ccsT' void.
Definition ccs  := ccsT void.

Definition comm a : label := obs (Act a) tt.

(*| Process algebra |*)
Section Combinators.

	Definition nil : ccs := ChoiceV 0 (fun x : fin 0 => match x with end).

	Definition prefix (a : action) (P: ccs) : ccs := trigger (Act a);; P.

	Definition plus (P Q : ccs) : ccs := choiceI2 P Q.

  (* Stuck? Failure event? *)
  Definition h_new (c : chan) : ActionE ~> ctree ccsE :=
    fun _ e => let '(Act a) := e in
            match a with
            | Send c'
            | Rcv c' =>
                if (c =? c')%string then stuckI else trigger e
            end.

  Definition new : chan -> ccs -> ccs :=
    fun c P => interp (h_new c) P.

  Definition para : ccs -> ccs -> ccs :=
    cofix F (P : ccs) (Q : ccs) :=
      choiceI3
        (rP <- get_head P;;
         match rP with
         | HRet rP => match rP with end
         | HChoice kP => ChoiceV _ (fun i => F (kP i) Q)
         | HVis e kP => Vis e (fun i => F (kP i) Q)
         end)

        (rQ <- get_head Q;;
         match rQ with
         | HRet rQ => match rQ with end
         | HChoice kQ => ChoiceV _ (fun i => F P (kQ i))
         | HVis e kQ => Vis e (fun i => F P (kQ i))
         end)

        (rP <- get_head P;;
         rQ <- get_head Q;;
         match rP, rQ with
         | HVis eP kP, HVis eQ kQ =>
             match eP, kP, eQ, kQ with
             | Act a, kP, Act b, kQ =>
                 if are_opposite a b
                 then
                   TauV (F (kP tt) (kQ tt))
                 else
                   stuckI
             end
         | _, _ => stuckI
         end).

(*|
We would like to define [bang] directly as in the following.
Unfortunately, it is not syntactically guarded and convincing Coq
seems challenging.
We therefore instead define a more general function [parabang] expressing
at once the parallel composition of a process [p] with a server of [q].
The usual [bang p] is then defined as [parabang p p].
|*)
  Fail Definition bang : ccs -> ccs :=
    cofix bang (p : ccs ) : ccs := para (bang p) p.

  Definition parabang : ccs ->ccs -> ccs :=
    cofix pB (p : ccs ) (q:ccs) : ccs :=

      choiceI4

           (* Communication by p *)
           (rp <- get_head p;;
            match rp with
            | HRet rp => match rp with end
            | HChoice kp => ChoiceV _ (fun i =>  pB (kp i) q )
            | HVis e kp => Vis e (fun i => pB (kp i) q)
            end)

           (* Communication by a fresh copy of q *)
           (rq <- get_head q;;
            match rq with
            | HRet rq => match rq with end
            | HChoice kq => ChoiceV _ (fun i => (pB  (para p (kq i)) q))
            | HVis e kq => Vis e (fun i => (pB  (para p (kq i)) q))
            end)

           (* Communication between p and a fresh copy of q *)
           (rp <- get_head p;;
            rq <- get_head q;;
            match rp, rq with
            | HVis ep kp, HVis eq kq =>
                match ep, kp, eq, kq with
                | Act a, kp, Act b, kq =>
                    if are_opposite a b
                    then
                      TauV (pB (para (kp tt) (kq tt)) q)
                    else
                      stuckI
                end

            | _, _ => stuckI
            end)

           (* Communication between two fresh copies of q *)
           (rq1 <- get_head q;;
            rq2 <- get_head q;;
            match rq1, rq2 with
            | HVis eq1 kq1, HVis eq2 kq2 =>
                match eq1, kq1, eq2, kq2 with
                | Act a, kq1, Act b, kq2 =>
                    if are_opposite a b
                    then
                      TauV (pB (para p (para (kq1 tt) (kq2 tt))) q)
                    else
                      stuckI
                end

            | _, _ => stuckI
            end).

  Definition bang (P : ccs) : ccs := parabang P P.

  (* Parameter bang: ccs -> ccs. *)
  (* Axiom unfold_bang: forall p, bang p ≅ para (bang p) p. *)



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

Module CCSNotationsSem.

  Declare Scope ccs_scope.

  Notation "0" := nil: ccs_scope.
  Infix "+" := plus (at level 50, left associativity) : ccs_scope.
  (* Infix "∥" := communicating (at level 29, left associativity). *)
  Infix "∥" := para (at level 29, left associativity) : ccs_scope.
  Notation "! x" := (bang x) : ccs_scope.

End CCSNotationsSem.

Import CCSNotationsSem.
Open Scope ccs_scope.

#[global] Instance equ_clos_sb_proper {E R} RR :
  Proper (gfp (@fequ E R R eq) ==> equ eq ==> iff) (sb RR).
Proof.
  unfold Proper, respectful; intros * eq1 * eq2.
  split; intros bis.
  - destruct bis as [F B]; cbn in *.
    split.
    + intros ? ? TR.
      rewrite <- eq1 in TR.
      apply F in TR as [].
      eexists.
      rewrite <- eq2; eauto.
      eauto.
    + intros ? ? TR.
      rewrite <- eq2 in TR.
      apply B in TR as [].
      eexists.
      rewrite <- eq1; eauto.
      eauto.
  - destruct bis as [F B]; cbn in *.
    split.
    + intros ? ? TR.
      rewrite eq1 in TR.
      apply F in TR as [].
      eexists.
      rewrite eq2; eauto.
      eauto.
    + intros ? ? TR.
      rewrite eq2 in TR.
      apply B in TR as [].
      eexists.
      rewrite eq1; eauto.
      eauto.
Qed.

Lemma trans_prefix_inv : forall l a p p',
    trans l (prefix a p) p' ->
    p' ≅ p /\ l = comm a.
Proof.
  intros * tr.
  apply trans_trigger_inv in tr as (? & ? & ->).
  destruct x; split; auto.
Qed.

Lemma trans_prefix : forall a p,
    trans (comm a) (prefix a p) p.
Proof.
  intros; eapply trans_trigger.
Qed.

(** ** prefix *)
Lemma ctx_prefix_st a: unary_ctx (prefix a) <= st.
Proof.
  apply Coinduction, by_Symmetry. apply unary_sym.
  rewrite <-b_T.
  intro R. apply (leq_unary_ctx (prefix a)). intros p q Hpq.
  intros l p' pp'.
  apply trans_prefix_inv in pp' as (EQ & ->).
  eexists.
  apply trans_prefix.
  rewrite EQ; auto.
Qed.

(** ** prefix *)
Lemma ctx_prefix_tequ a: unary_ctx (prefix a) <= (t_equ eq).
Proof.
  apply Coinduction.
  intro R.
  apply (leq_unary_ctx (prefix a)).
  intros p q Hpq.
  cbn in *.
  constructor.
  intros [].
  fold (@bind ccsE _ _ (Ret tt) (fun _ => p)).
  fold (@bind ccsE _ _ (Ret tt) (fun _ => q)).
  rewrite 2 unfold_bind; cbn.
  apply (b_T (fequ eq)).
  apply Hpq.
Qed.

#[global] Instance prefix_st a: forall R, Proper (st R ==> st R) (prefix a) := unary_proper_t (@ctx_prefix_st a).

#[global] Instance prefix_tequ a: forall R, Proper (t_equ eq R ==> t_equ eq R) (prefix a) := unary_proper_t (@ctx_prefix_tequ a).

Definition can_comm (c : chan) (a : @label ccsE) : bool :=
  match a with
  | obs (Act a) _ =>
      match a with
      | Send c'
      | Rcv c' => if (c =? c')%string then false else true
      end
  | _ => true
  end.

Lemma trans_new_inv : forall l c p p',
    trans l (new c p) p' ->
    exists q, can_comm c l = true /\ trans l p q /\ p' ≅ new c q.
Proof.
  intros * tr.
  unfold new in tr.
  (* TODO, theory for interp *)
Admitted.

Lemma trans_new : forall l c p p',
    trans l p p' ->
    can_comm c l = true ->
    trans l (new c p) (new c p').
Proof.
  intros * tr.
  (* TODO, theory for interp *)
Admitted.

#[global] Instance equ_clos_sT_proper {E R} RR f : Proper (gfp (@fequ E R R eq) ==> equ eq ==> iff) (T sb f RR).
Proof.
  intros ? ? eq1 ? ? eq2; split; intros H.
  apply (fT_T equ_clos_st); econstructor; [symmetry; eauto | | eauto]; assumption.
  apply (fT_T equ_clos_st); econstructor; [eauto | | symmetry; eauto]; assumption.
Qed.

(** ** name restriction *)
Lemma ctx_new_st a: unary_ctx (new a) <= st.
Proof.
  apply Coinduction, by_Symmetry. apply unary_sym.
  intro R. apply (leq_unary_ctx (new a)). intros p q Hpq l p0 Hp0.
  apply trans_new_inv in Hp0 as (? & comm & tr & EQ).
  destruct (proj1 Hpq _ _ tr) as [???].
  eexists.
  apply trans_new; eauto.
  rewrite EQ.
  now apply unary_proper_Tctx, (id_T sb).
Qed.

(** ** name restriction *)
Lemma ctx_new_tequ a: unary_ctx (new a) <= t_equ eq.
Proof.
  apply Coinduction.
  intro R. apply (leq_unary_ctx (new a)). intros p q Hpq.
Admitted.

#[global] Instance new_st a: forall R, Proper (st R ==> st R) (new a) := unary_proper_t (@ctx_new_st a).

#[global] Instance new_tequ a: forall R, Proper (t_equ eq R ==> t_equ eq R) (new a) := unary_proper_t (@ctx_new_tequ a).

Lemma trans_plus_inv : forall l p q r,
    trans l (p + q) r ->
    (exists p', trans l p p' /\ r ≅ p') \/
    (exists q', trans l q q' /\ r ≅ q').
Proof.
  intros * tr.
  apply trans_ChoiceI_inv in tr as ([|] & tr); eauto.
Qed.

Lemma trans_ChoiceV' {E X} : forall n (k : fin n -> ctree E X) x u,
    u ≅ k x ->
		trans tau (ChoiceV n k) u.
Proof.
	intros * eq; rewrite eq; apply trans_ChoiceV.
Qed.

Lemma trans_plusL : forall l p p' q,
    trans l p p' ->
    trans l (p + q) p'.
Proof.
  intros * tr.
  now apply trans_choiceI21.
Qed.

Lemma trans_plusR : forall l p q q',
    trans l q q' ->
    trans l (p + q) q'.
Proof.
  intros * tr.
  now apply trans_choiceI22.
Qed.

(** ** choice *)
Lemma ctx_plus_t: binary_ctx plus <= st.
Proof.
  apply Coinduction, by_Symmetry. apply binary_sym.
  intro R. apply (leq_binary_ctx plus).
  intros * [F1 B1] * [F2 B2] ? * tr.
  apply trans_plus_inv in tr as [(? & tr & EQ) | (? & tr & EQ)].
  - apply F1 in tr as [? tr ?].
    eexists.
    apply trans_plusL; eauto.
    rewrite EQ.
    now apply (id_T sb).
  - apply F2 in tr as [? tr ?].
    eexists.
    apply trans_plusR; eauto.
    rewrite EQ.
    now apply (id_T sb).
Qed.
#[global] Instance plus_t:
  forall R, Proper (st R ==> st R ==> st R) plus := binary_proper_t ctx_plus_t.

Notation para_ p q :=
  (choiceI3
    (rp <- get_head p;;
     match rp with
     | HRet rp => match rp with end
     | HChoice kp => ChoiceV _ (fun i => para (kp i) q)
     | HVis e kp => Vis e (fun i => para (kp i) q)
     end)

    (rq <- get_head q;;
     match rq with
     | HRet rq => match rq with end
     | HChoice kq => ChoiceV _ (fun i => para p (kq i))
     | HVis e kq => Vis e (fun i => para p (kq i))
     end)

    (rp <- get_head p;;
     rq <- get_head q;;
     match rp, rq with
     | HVis ep kp, HVis eq kq =>
         match ep, kp, eq, kq with
         | Act a, kp, Act b, kq =>
             if are_opposite a b
             then
               TauV (para (kp tt) (kq tt))
             else
               stuckI
         end
     | _, _ => stuckI
     end))%ctree.

Lemma unfold_para : forall p q, para p q ≅ para_ p q.
Proof.
  intros.
	now step.
Qed.

#[global] Instance para_equ :
  Proper (equ eq ==> equ eq ==> equ eq) para.
Proof.
  unfold Proper, respectful.
  coinduction R CIH.
  intros p1 p2 EQp q1 q2 EQq.
  rewrite 2 unfold_para.
  constructor.
  intros i.
  destruct i; [| destruct i].
  - eapply (ft_t (bind_ctx_equ_t _ _)).
    apply in_bind_ctx; [apply get_head_equ; auto | intros hdp1 hdp2 eqp].
    inv eqp; auto.
    step; constructor; auto.
    step; constructor; auto.
  - eapply (ft_t (bind_ctx_equ_t _ _)).
    apply in_bind_ctx; [apply get_head_equ; auto | intros hdp1 hdp2 eqp].
    inv eqp; auto.
    step; constructor; auto.
    step; constructor; auto.
  - eapply (ft_t (bind_ctx_equ_t _ _)).
    apply in_bind_ctx; [apply get_head_equ; auto | intros hdp1 hdp2 eqp].
    eapply (ft_t (bind_ctx_equ_t _ _)).
    apply in_bind_ctx; [apply get_head_equ; auto | intros hdq1 hdq2 eqq].
    inv eqp; auto.
    inv eqq; auto.
    destruct e, e0, (are_opposite a a0); auto.
    step; constructor; auto.
Qed.

Lemma trans_paraSynch : forall a b (p p' q q' : ccs),
    trans (comm a) p p' ->
    trans (comm b) q q' ->
    are_opposite a b ->
    trans tau (p ∥ q) (p' ∥ q').
Proof.
  intros * TRp TRq Op.
  apply trans_get_head in TRp as (kp & TRp & Eqp).
  apply trans_get_head in TRq as (kq & TRq & Eqq).
  rewrite unfold_para.
  apply trans_choiceI33.
  eapply trans_bind_r; [apply TRp |].
  eapply trans_bind_r; [apply TRq |].
  cbn; rewrite Op.
  rewrite Eqp, Eqq.
  apply trans_TauV.
Qed.

Lemma trans_paraL :
  forall l (p p' q : ccs),
    trans l p p' ->
    trans l (p ∥ q) (p' ∥ q).
Proof.
  intros * TRp.
  rewrite unfold_para.
  apply trans_choiceI31.
  destruct l.
  - apply trans_get_head in TRp.
    destruct TRp as (? & ? & ? & TRp & Eqp).
    eapply trans_bind_r; eauto; cbn.
    econstructor.
    rewrite Eqp; reflexivity.
  - apply trans_get_head in TRp.
    destruct TRp as (? & TRp & Eqp).
    eapply trans_bind_r; eauto; cbn.
    constructor.
    rewrite Eqp; reflexivity.
  - pose proof (trans_val_invT TRp); subst; easy.
Qed.

Lemma trans_paraR :
  forall l (p q q' : ccs),
    trans l q q' ->
    trans l (p ∥ q) (p ∥ q').
Proof.
  intros * TRq.
  rewrite unfold_para.
  apply trans_choiceI32.
  destruct l.
  - apply trans_get_head in TRq.
    destruct TRq as (? & ? & ? & TRq & Eqq).
    eapply trans_bind_r; eauto; cbn.
    econstructor.
    rewrite Eqq; reflexivity.
  - apply trans_get_head in TRq.
    destruct TRq as (? & TRq & Eqq).
    eapply trans_bind_r; eauto; cbn.
    constructor.
    rewrite Eqq; reflexivity.
  - pose proof (trans_val_invT TRq); subst; easy.
Qed.

Lemma trans_para_inv :
  forall l p q r,
    trans l (p ∥ q) r ->
    (exists p', trans l p p' /\ r ≅ (p' ∥ q)) \/
    (exists q', trans l q q' /\ r ≅ (p ∥ q')) \/
    (exists p' q' a b,
          trans (comm a) p p' /\
            trans (comm b) q q' /\
            are_opposite a b /\
            l = tau /\
            r ≅ (p' ∥ q')).
Proof.
  intros * TR.
  rewrite unfold_para in TR.
  apply trans_ChoiceI_inv in TR as (x & TR).
  destruct x; [| destruct x].
  - left.
    edestruct @trans_bind_inv; [apply TR | | ]; clear TR.
    destruct H as (NOTV & ? & TR & EQ); apply trans_get_head_inv in TR; easy.
    destruct H as (hdp & TRhdp & TR).
    destruct hdp; try easy.
    * apply trans_ChoiceV_inv in TR as (x & EQ & ->).
      eapply trans_HChoice in TRhdp.
      eexists; split; eauto.
    * apply trans_vis_inv in TR as (x & EQ & ->).
      eapply trans_HVis in TRhdp.
      eexists; split; eauto.
  - right; left.
    edestruct @trans_bind_inv; [apply TR | | ]; clear TR.
    destruct H as (NOTV & ? & TR & EQ); apply trans_get_head_inv in TR; easy.
    destruct H as (hdq & TRhdq & TR).
    destruct hdq; try easy.
    * apply trans_ChoiceV_inv in TR as (x & EQ & ->).
      eapply trans_HChoice in TRhdq.
      eexists; split; eauto.
    * apply trans_vis_inv in TR as (x & EQ & ->).
      eapply trans_HVis in TRhdq.
      eexists; split; eauto.
  - right; right.
    edestruct @trans_bind_inv; [apply TR | | ]; clear TR.
    destruct H as (NOTV & ? & TR & EQ); apply trans_get_head_inv in TR; easy.
    destruct H as (hdp & TRhdp & TR).
    edestruct @trans_bind_inv; [apply TR | | ]; clear TR.
    destruct H as (NOTV & ? & TR & EQ); apply trans_get_head_inv in TR; easy.
    destruct H as (hdq & TRhdq & TR).
    destruct hdp; try easy.
    exfalso; eapply stuckI_is_stuck; eassumption.
    destruct hdq; try easy.
    exfalso; eapply stuckI_is_stuck; eassumption.
    destruct e, e0, (are_opposite a a0) eqn:?.
    2:exfalso; eapply stuckI_is_stuck; eassumption.
    apply trans_TauV_inv in TR as [? ->].
    eapply trans_HVis in TRhdp.
    eapply trans_HVis in TRhdq.
    do 4 eexists.
    repeat split; eauto.
Qed.

Ltac trans_para_invT H :=
  apply trans_para_inv in H as
      [(?p' & ?TRp & ?EQ) |
        [(?q' & ?TRq & ?EQ) |
          (?p' & ?q' & ?a & ?b & ?TRp & ?TRq & ?Op & ? & ?EQ) ]]; subst.

(** ** parallel composition *)
Lemma ctx_para_t: binary_ctx para <= st.
Proof.
  apply Coinduction, by_Symmetry. apply binary_sym.
  intro R. apply (leq_binary_ctx para).
  intros * [F1 B1] * [F2 B2] ? * tr.
  trans_para_invT tr.
  - apply F1 in TRp as [? tr ?].
    eexists.
    apply trans_paraL; eauto.
    rewrite EQ.
    apply (fTf_Tf sb). apply (in_binary_ctx para).
    now apply (id_T sb).
    now apply (b_T sb).
  - apply F2 in TRq as [? tr ?].
    eexists.
    apply trans_paraR; eauto.
    rewrite EQ.
    apply (fTf_Tf sb). apply (in_binary_ctx para).
    now apply (b_T sb).
    now apply (id_T sb).
  - apply F1 in TRp as [? trp ?].
    apply F2 in TRq as [? trq ?].
    eexists.
    eapply trans_paraSynch; eauto.
    rewrite EQ.
    apply (fTf_Tf sb). apply (in_binary_ctx para); now apply (id_T sb).
Qed.
#[global] Instance para_t: forall R, Proper (st R ==> st R ==> st R) para := binary_proper_t ctx_para_t.
#[global] Instance para_T f: forall R, Proper (T sb f R ==> T sb f R ==> T sb f R) para := binary_proper_T ctx_para_t.


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
    apply choiceI2_stuckV_l.
  Qed.

  Lemma plsp0 (p : ccs) : p + 0 ~ p.
  Proof. now rewrite plsC, pls0p. Qed.

  Lemma plsidem (p : ccs) : p + p ~ p.
  Proof.
    apply choiceI2_idem.
  Qed.

  #[global] Instance are_opposite_sym : Symmetric are_opposite.
  Proof.
    unfold are_opposite, eqb_action, op; cbn.
    intros [] [] Op; intuition.
    all:rewrite eqb_sym; auto.
  Qed.

  Lemma paraC: forall (p q : ccs), p ∥ q ~ q ∥ p.
  Proof.
    coinduction ? CIH; symmetric.
    intros p q l r tr.
    trans_para_invT tr.
    - eexists.
      eapply trans_paraR; eauto.
      rewrite EQ; auto.
    - eexists.
      eapply trans_paraL; eauto.
      rewrite EQ; auto.
    - eexists.
      eapply trans_paraSynch; eauto.
      symmetry; auto.
      rewrite EQ; auto.
  Qed.

  Lemma para0p : forall (p : ccs), 0 ∥ p ~ p.
  Proof.
    coinduction R CIH.
    intros.
    split.
    - intros l q tr.
      trans_para_invT tr; try now exfalso; eapply stuckV_is_stuck; eauto.
      eexists; eauto.
      rewrite EQ; auto.
    - intros l q tr.
      eexists.
      apply trans_paraR; eauto.
      cbn; auto.
  Qed.

  Lemma parap0 : forall (p : ccs), p ∥ 0 ~ p.
  Proof.
    intros; rewrite paraC; apply para0p.
  Qed.

  Lemma paraA : forall (p q r : ccs), p ∥ (q ∥ r) ~ (p ∥ q) ∥ r.
  Proof.
    coinduction ? CIH; intros.
    split.
    - intros l s tr.
      trans_para_invT tr.
      + eexists.
        do 2 apply trans_paraL; eauto.
        rewrite EQ; auto.
      + trans_para_invT TRq.
        * eexists.
          apply trans_paraL, trans_paraR; eauto.
          rewrite EQ, EQ0; auto.
        * eexists.
          apply trans_paraR; eauto.
          rewrite EQ, EQ0; auto.
        * eexists.
          eapply trans_paraSynch; eauto.
          eapply trans_paraR; eauto.
          rewrite EQ, EQ0; auto.
      + trans_para_invT TRq.
        * eexists.
          eapply trans_paraL, trans_paraSynch; eauto.
          rewrite EQ, EQ0; auto.
        * eexists.
          eapply trans_paraSynch; eauto.
          eapply trans_paraL; eauto.
          rewrite EQ, EQ0; auto.
        * inv H.
    - intros l s tr; cbn.
      trans_para_invT tr.
      + trans_para_invT TRp.
        * eexists.
          apply trans_paraL; eauto.
          rewrite EQ, EQ0; auto.
        * eexists.
          apply trans_paraR, trans_paraL; eauto.
          rewrite EQ, EQ0; auto.
        * eexists.
          eapply trans_paraSynch; eauto.
          eapply trans_paraL; eauto.
          rewrite EQ, EQ0; auto.
      + eexists.
        eapply trans_paraR, trans_paraR; eauto.
        rewrite EQ; auto.
      + trans_para_invT TRp.
        * eexists.
          eapply trans_paraSynch; eauto.
          eapply trans_paraR; eauto.
          rewrite EQ, EQ0; auto.
        * eexists.
          eapply trans_paraR, trans_paraSynch; eauto.
          rewrite EQ, EQ0; auto.
        * inv H.
  Qed.

End Theory.

Notation parabang_ p q :=
  (choiceI4

           (* Communication by p *)
           (rp <- get_head p;;
            match rp with
            | HRet rp => match rp with end
            | HChoice kp => ChoiceV _ (fun i => parabang (kp i) q )
            | HVis e kp => Vis e (fun i => parabang (kp i) q)
            end)

           (* Communication by a fresh copy of q *)
           (rq <- get_head q;;
            match rq with
            | HRet rq => match rq with end
            | HChoice kq => ChoiceV _ (fun i => (parabang (para p (kq i)) q))
            | HVis e kq => Vis e (fun i => (parabang (para p (kq i)) q))
            end)

           (* Communication between p and a fresh copy of q *)
           (rp <- get_head p;;
            rq <- get_head q;;
            match rp, rq with
            | HVis ep kp, HVis eq kq =>
                match ep, kp, eq, kq with
                | Act a, kp, Act b, kq =>
                    if are_opposite a b
                    then
                      TauV (parabang (para (kp tt) (kq tt)) q)
                    else
                      stuckI
                end

            | _, _ => stuckI
            end)

           (* Communication between two fresh copies of q *)
           (rq1 <- get_head q;;
            rq2 <- get_head q;;
            match rq1, rq2 with
            | HVis eq1 kq1, HVis eq2 kq2 =>
                match eq1, kq1, eq2, kq2 with
                | Act a, kq1, Act b, kq2 =>
                    if are_opposite a b
                    then
                      TauV (parabang (para p (para (kq1 tt) (kq2 tt))) q)
                    else
                      stuckI
                end

            | _, _ => stuckI
            end))%ctree.

Lemma unfold_parabang : forall p q, parabang p q ≅ parabang_ p q.
Proof.
  intros.
	now step.
Qed.

Lemma unfold_bang : forall p, !p ≅ parabang_ p p.
Proof.
  intros; unfold bang. apply unfold_parabang.
Qed.

#[global] Instance parabang_equ :
  Proper (equ eq ==> equ eq ==> equ eq) parabang.
Proof.
  unfold Proper, respectful.
  coinduction R CIH.
  intros p1 p2 EQp q1 q2 EQq.
  rewrite 2 unfold_parabang.
  constructor.
  intros i.
  destruct i; [| destruct i; [| destruct i]].
  - eapply (ft_t (bind_ctx_equ_t _ _)).
    apply in_bind_ctx; [apply get_head_equ; auto | intros hdp1 hdp2 eqp].
    inv eqp; auto.
    step; constructor; auto.
    step; constructor; auto.
  - eapply (ft_t (bind_ctx_equ_t _ _)).
    apply in_bind_ctx; [apply get_head_equ; auto | intros hdp1 hdp2 eqp].
    inv eqp; auto.
    step; constructor; intros ?.
    apply CIH; auto; rewrite EQp, H; reflexivity.
    step; constructor; intros ?.
    apply CIH; auto; rewrite EQp, H; reflexivity.
  - eapply (ft_t (bind_ctx_equ_t _ _)).
    apply in_bind_ctx; [apply get_head_equ; auto | intros hdp1 hdp2 eqp].
    eapply (ft_t (bind_ctx_equ_t _ _)).
    apply in_bind_ctx; [apply get_head_equ; auto | intros hdq1 hdq2 eqq].
    inv eqp; auto.
    inv eqq; auto.
    destruct e, e0, (are_opposite a a0); auto.
    step; constructor; intros ?.
    apply CIH; auto.
    rewrite H,H0; reflexivity.
  - eapply (ft_t (bind_ctx_equ_t _ _)).
    apply in_bind_ctx; [apply get_head_equ; auto | intros hdp1 hdp2 eqp].
    eapply (ft_t (bind_ctx_equ_t _ _)).
    apply in_bind_ctx; [apply get_head_equ; auto | intros hdq1 hdq2 eqq].
    inv eqp; auto.
    inv eqq; auto.
    destruct e, e0, (are_opposite a a0); auto.
    step; constructor; intros ?.
    apply CIH; auto.
    rewrite EQp, H,H0; reflexivity.
Qed.

(* Lemma trans_bang : forall p l p', *)
(*     trans l (!p) p' -> False. *)
(*     (* trans l (!p ∥ p) p' -> *) *)
(* Proof. *)
(*   intros * TR. *)
(*   rewrite unfold_bang in TR; *)
(*     apply trans_ChoiceI_inv in TR as [[|? [|? [| ? x]]] TR]. *)
(*   -  *)


Lemma trans_vis' {E R X} : forall (e : E X) x (k : X -> ctree E R) u,
    u ≅ k x ->
		trans (obs e x) (Vis e k) u.
Proof.
	intros * eq; rewrite eq; apply trans_vis.
Qed.

Ltac copy h :=
  let foo := fresh "cpy" in
  assert (foo := h).

Lemma trans_parabangL : forall p l p' q,
    trans l p p' ->
    trans l (parabang p q) (parabang p' q).
Proof.
  intros * TR.
  pose proof trans_get_head TR.
  rewrite unfold_parabang.
  apply trans_choiceI41.
  destruct l;
    repeat match goal with
           | h : Logic.ex _ |- _ => destruct h
           | h : Logic.and _ _ |- _ => destruct h
           end.
  - eapply trans_bind_r; eauto. cbn.
    rewrite H0; econstructor; reflexivity.
  - eapply trans_bind_r; eauto. cbn.
    rewrite H0; econstructor; reflexivity.
  - apply trans_val_invT in TR; subst; easy.
Qed.

Lemma trans_parabangR : forall p l q q',
    trans l q q' ->
    trans l (parabang p q) (parabang (p ∥ q') q).
Proof.
  intros * TR.
  pose proof trans_get_head TR.
  rewrite unfold_parabang.
  apply trans_choiceI42.
  destruct l;
    repeat match goal with
           | h : Logic.ex _ |- _ => destruct h
           | h : Logic.and _ _ |- _ => destruct h
           end.
  - eapply trans_bind_r; eauto. cbn.
    econstructor; rewrite H0; reflexivity.
  - eapply trans_bind_r; eauto. cbn.
    rewrite H0; econstructor; reflexivity.
  - apply trans_val_invT in TR; subst; easy.
Qed.

Lemma para_parabang : forall p q r,
    parabang (p ∥ q) r ~ p ∥ parabang q r.
Proof.
  coinduction ? CIH.
  intros; split.

  - intros l s TR.
    rewrite unfold_parabang in TR.
    apply trans_ChoiceI_inv in TR as [[|? [|? [| ? x]]] TR].
    + apply trans_bind_inv in TR.
      destruct TR as [(NV & ? & TR & ?) | (? & TR1 & TR2)]; [apply trans_get_head_inv in TR; easy|].
      destruct x; try easy.
      * apply trans_ChoiceV_inv in TR2 as (x & EQ & ->).
        pose proof trans_HChoice _ TR1 x.
        trans_para_invT H.
        ** eexists.
           apply trans_paraL; eauto.
           rewrite EQ, EQ0; auto.
        ** eexists.
           apply trans_paraR.
           apply trans_parabangL; eauto.
           rewrite EQ,EQ0; auto.
        ** eexists.
           eapply trans_paraSynch; eauto.
           apply trans_parabangL; eauto.
           rewrite EQ,EQ0; auto.
      * apply trans_vis_inv in TR2 as (x & EQ & ->).
        pose proof trans_HVis _ TR1 (i := x).
        trans_para_invT H; try easy.
        ** eexists.
           apply trans_paraL; eauto.
           rewrite EQ, EQ0; auto.
        ** eexists.
           apply trans_paraR.
           apply trans_parabangL; eauto.
           rewrite EQ,EQ0; auto.

    + apply trans_bind_inv in TR.
      destruct TR as [(NV & ? & TR & ?) | (? & TR1 & TR2)]; [apply trans_get_head_inv in TR; easy|].
      destruct x; try easy.
      * apply trans_ChoiceV_inv in TR2 as (x & EQ & ->).
        pose proof trans_HChoice _ TR1 x.
        eexists.
        apply trans_paraR.
        apply trans_parabangR; eauto.
        rewrite EQ.
        rewrite !CIH.
        rewrite paraA; auto.
      * apply trans_vis_inv in TR2 as (x & EQ & ->).
        pose proof trans_HVis _ TR1 (i := x).
        eexists.
        apply trans_paraR.
        apply trans_parabangR; eauto.
        rewrite EQ.
        rewrite !CIH.
        rewrite paraA; auto.

    + apply trans_bind_inv in TR.
      destruct TR as [(NV & ? & TR & ?) | (? & TR1 & TR2)]; [apply trans_get_head_inv in TR; easy|].
      apply trans_bind_inv in TR2.
      destruct TR2 as [(NV & ? & TR & ?) | (? & TR2 & TR3)]; [apply trans_get_head_inv in TR; easy|].
      destruct x, x0; try easy; try now (exfalso; eapply stuckI_is_stuck; eauto).
      destruct e, e0, (are_opposite a a0); try now (exfalso; eapply stuckI_is_stuck; eauto).
      apply trans_TauV_inv in TR3.
      eexists.

Admitted.

Lemma ctx_parabang_t: binary_ctx parabang <= st.
Proof.
Admitted.
#[global] Instance parabang_t: forall R, Proper (st R ==> st R ==> st R) parabang := binary_proper_t ctx_parabang_t.
#[global] Instance parabang_T f: forall R, Proper (T sb f R ==> T sb f R ==> T sb f R) parabang := binary_proper_T ctx_parabang_t.

Lemma parabang_aux : forall p q,
    parabang (p ∥ q) q ~ parabang p q.
Proof.
  coinduction ? CIH.
  split.
  - intros l r TR.
    rewrite unfold_parabang in TR.
    apply trans_ChoiceI_inv in TR as [[|? [|? [| ? x]]] TR].

    + (* (p || q) fait un pas *)
      apply trans_bind_inv in TR.
      destruct TR as [(NV & ? & TR & ?) | (? & TR1 & TR2)]; [apply trans_get_head_inv in TR; easy|].
      destruct x; try easy.
      * apply trans_ChoiceV_inv in TR2 as (x & EQ & ->).
        pose proof trans_HChoice _ TR1.
        specialize (H x).
        trans_para_invT H.
        ** rewrite EQ0 in EQ.
           eexists.
           apply trans_parabangL; eauto.
           rewrite EQ; auto.
        ** rewrite EQ0 in EQ.
           eexists.
           apply trans_parabangR; eauto.
           rewrite EQ; auto.
        ** rewrite EQ0 in EQ.
           pose proof trans_get_head TRp as (kp & TRph & EQp).
           pose proof trans_get_head TRq as (kq & TRqh & EQq).
           eexists.
           rewrite unfold_parabang.
           apply trans_choiceI43.
           eapply trans_bind_r; [apply TRph | ].
           eapply trans_bind_r; [apply TRqh | ].
           cbn; rewrite Op.
           apply trans_TauV.
           rewrite EQ, EQp, EQq.
           auto.
      * apply trans_vis_inv in TR2 as (x & EQ & ->).
        pose proof trans_HVis _ TR1 (i := x).
        trans_para_invT H; try easy.
        ** rewrite EQ0 in EQ.
           eexists.
           apply trans_parabangL; eauto.
           rewrite EQ; auto.
        ** rewrite EQ0 in EQ.
           eexists.
           apply trans_parabangR; eauto.
           rewrite EQ; auto.

    + (* a copy of q steps *)
      apply trans_bind_inv in TR.
      destruct TR as [(NV & ? & TR & ?) | (? & TR1 & TR2)]; [apply trans_get_head_inv in TR; easy|].
      destruct x; try easy.
      * apply trans_ChoiceV_inv in TR2 as (x & EQ & ->).
        pose proof trans_HChoice _ TR1 x.
        eexists.
        apply trans_parabangR; eauto.
        rewrite EQ.
        rewrite <- paraA.
        rewrite (paraC q (k x)).
        rewrite paraA.
        auto.
      * apply trans_vis_inv in TR2 as (x & EQ & ->).
        pose proof trans_HVis _ TR1 (i := x).
        eexists.
        apply trans_parabangR; eauto.
        rewrite EQ.
        rewrite <- paraA.
        rewrite (paraC q (k x)).
        rewrite paraA.
        auto.

    + (* (p || q) communicates with a copy of q *)
      apply trans_bind_inv in TR.
      destruct TR as [(NV & ? & TR & ?) | (? & TR1 & TR2)]; [apply trans_get_head_inv in TR; easy|].
      apply trans_bind_inv in TR2.
      destruct TR2 as [(NV & ? & ?TR & ?) | (? & TR2 & TR3)]; [apply trans_get_head_inv in TR; easy|].
      destruct x, x0; try easy; try now (exfalso; eapply stuckI_is_stuck; eauto).
      destruct e,e0, (are_opposite a a0) eqn: Op; try now (exfalso; eapply stuckI_is_stuck; eauto).
      apply trans_TauV_inv in TR3 as [EQ ->].
      pose proof trans_HVis _ TR1 (i := tt) as TRp.
      pose proof trans_HVis _ TR2 (i := tt) as TRq.
      trans_para_invT TRp; [| | easy].
      * rewrite EQ0 in EQ.
        pose proof trans_get_head TRp as (kq & TRph & EQp).
        rewrite EQp in EQ.
        eexists.
        rewrite unfold_parabang.
        apply trans_choiceI43.
        eapply trans_bind_r; eauto.
        eapply trans_bind_r; eauto.
        cbn; rewrite Op.
        apply trans_TauV.
        rewrite EQ.
        rewrite <- paraA.
        rewrite (paraC q (k0 tt)).
        rewrite paraA.
        auto.
      * rewrite EQ0 in EQ.
        pose proof trans_get_head TRq0 as (kq & TRqh & EQp).
        eexists.
        rewrite unfold_parabang.
        apply trans_choiceI44.
        eapply trans_bind_r; [apply TRqh |].
        eapply trans_bind_r; [apply TR2 |].
        cbn; rewrite Op.
        apply trans_TauV.
        rewrite EQ, EQp.
        rewrite <- paraA.
        reflexivity.

    + (* two copies of q communicate *)
      apply trans_bind_inv in TR.
      destruct TR as [(NV & ? & TR & ?) | (? & TR1 & TR2)]; [apply trans_get_head_inv in TR; easy|].
      apply trans_bind_inv in TR2.
      destruct TR2 as [(NV & ? & ?TR & ?) | (? & TR2 & TR3)]; [apply trans_get_head_inv in TR; easy|].
      destruct x0, x1; try easy; try now (exfalso; eapply stuckI_is_stuck; eauto).
      destruct e,e0, (are_opposite a a0) eqn: Op; try now (exfalso; eapply stuckI_is_stuck; eauto).
      apply trans_TauV_inv in TR3 as [EQ ->].
      pose proof trans_HVis _ TR1 (i := tt) as TRp.
      pose proof trans_HVis _ TR2 (i := tt) as TRq.
      eexists.
      rewrite unfold_parabang.
      apply trans_choiceI44.
      eapply trans_bind_r; [apply TR1 |].
      eapply trans_bind_r; [apply TR2 |].
      cbn; rewrite Op.
      apply trans_TauV.
      rewrite EQ.
      rewrite <- paraA.
      rewrite (paraC q _).
      rewrite 2 paraA.
      auto.

  - intros l r TR.
    rewrite unfold_parabang in TR.
    apply trans_ChoiceI_inv in TR as [[|? [|? [| ? x]]] TR].
    + apply trans_bind_inv in TR.
      destruct TR as [(NV & ? & TR & ?) | (? & TR1 & TR2)]; [apply trans_get_head_inv in TR; easy|].
      destruct x; try easy.
      * apply trans_ChoiceV_inv in TR2 as (? & EQ & ->).
        pose proof trans_HChoice _ TR1 as TRq.
        eexists.
        apply trans_parabangL, trans_paraL; eauto.
        cbn; rewrite EQ.
        auto.
      * apply trans_vis_inv in TR2 as (? & EQ & ->).
        pose proof trans_HVis _ TR1 (i := x) as TRq.
        eexists.
        apply trans_parabangL, trans_paraL; eauto.
        cbn; rewrite EQ.
        auto.

    + apply trans_bind_inv in TR.
      destruct TR as [(NV & ? & TR & ?) | (? & TR1 & TR2)]; [apply trans_get_head_inv in TR; easy|].
      destruct x; try easy.
      * apply trans_ChoiceV_inv in TR2 as (? & EQ & ->).
        pose proof trans_HChoice _ TR1 as TRq.
        eexists.
        apply trans_parabangL, trans_paraR; eauto.
        cbn; rewrite EQ;
        auto.
      * apply trans_vis_inv in TR2 as (? & EQ & ->).
        pose proof trans_HVis _ TR1 (i := x) as TRq.
        eexists.
        apply trans_parabangL, trans_paraR; eauto.
        cbn; rewrite EQ.
        auto.

    + apply trans_bind_inv in TR.
      destruct TR as [(NV & ? & TR & ?) | (? & TR1 & TR2)]; [apply trans_get_head_inv in TR; easy|].
      apply trans_bind_inv in TR2.
      destruct TR2 as [(NV & ? & ?TR & ?) | (? & TR2 & TR3)]; [apply trans_get_head_inv in TR; easy|].
      destruct x, x0; try easy; try now (exfalso; eapply stuckI_is_stuck; eauto).
      destruct e,e0, (are_opposite a a0) eqn: Op; try now (exfalso; eapply stuckI_is_stuck; eauto).
      apply trans_TauV_inv in TR3 as [EQ ->].
      pose proof trans_HVis _ TR1 (i := tt) as TRp.
      pose proof trans_HVis _ TR2 (i := tt) as TRq.
      eexists.
      eapply trans_parabangL, trans_paraSynch; eauto.
      cbn; rewrite EQ.
      reflexivity.

    + apply trans_bind_inv in TR.
      destruct TR as [(NV & ? & TR & ?) | (? & TR1 & TR2)]; [apply trans_get_head_inv in TR; easy|].
      apply trans_bind_inv in TR2.
      destruct TR2 as [(NV & ? & ?TR & ?) | (? & TR2 & TR3)]; [apply trans_get_head_inv in TR; easy|].
      destruct x0, x1; try easy; try now (exfalso; eapply stuckI_is_stuck; eauto).
      destruct e,e0, (are_opposite a a0) eqn: Op; try now (exfalso; eapply stuckI_is_stuck; eauto).
      apply trans_TauV_inv in TR3 as [EQ ->].
      pose proof trans_HVis _ TR1 (i := tt) as TRp.
      pose proof trans_HVis _ TR2 (i := tt) as TRq.
      eexists.
      rewrite unfold_parabang.
      apply trans_choiceI44.
      eapply trans_bind_r; [apply TR1 |].
      eapply trans_bind_r; [apply TR2 |].
      cbn; rewrite Op.
      apply trans_TauV.
      cbn; rewrite EQ.
      rewrite <- paraA.
      rewrite (paraC q _).
      rewrite ! paraA.
      auto.
Qed.

Lemma parabang_eq : forall p q,
    parabang p q ~ p ∥ !q.
Proof.
  coinduction ? CIH.
  intros p q; split.

  - intros l p' TR.
    rewrite unfold_parabang in TR.
    apply trans_ChoiceI_inv in TR as [[|? [|? [| ? x]]] TR].
    + (* p moved *)
      apply trans_bind_inv in TR.
      destruct TR as [(NV & ? & TR & ?) | (? & TR1 & TR2)]; [apply trans_get_head_inv in TR; easy|].
      destruct x; try easy.
      * apply trans_ChoiceV_inv in TR2 as (x & EQ & ->).
        pose proof trans_HChoice _ TR1.
        exists (k x ∥ !q).
        apply trans_paraL; auto.
        rewrite EQ; auto.
      * apply trans_vis_inv in TR2 as (x & EQ & ->).
        epose proof trans_HVis _ TR1 (i := x).
        exists (k x ∥ !q).
        apply trans_paraL; auto.
        rewrite EQ; auto.

    + (* a copy of q moved *)
      apply trans_bind_inv in TR.
      destruct TR as [(NV & ? & TR & ?) | (? & TR1 & TR2)]; [apply trans_get_head_inv in TR; easy|].
      destruct x; try easy.
      * apply trans_ChoiceV_inv in TR2 as (x & EQ & ->).
        pose proof trans_HChoice _ TR1.
        exists (p ∥ parabang (k x) q).
        apply trans_paraR.
        rewrite unfold_bang at 1.
        apply trans_choiceI41.
        eapply trans_bind_r; eauto; cbn.
        eapply trans_ChoiceV'; reflexivity.
        rewrite EQ.
        rewrite para_parabang; auto.
      * apply trans_vis_inv in TR2 as (x & EQ & ->).
        exists (p ∥ parabang (k x) q).
        apply trans_paraR.
        rewrite unfold_bang at 1.
        apply trans_choiceI41.
        eapply trans_bind_r; eauto; cbn.
        eapply trans_vis'; reflexivity.
        rewrite EQ.
        rewrite para_parabang; auto.

    + (* p communicated with a copy of q moved *)
      apply trans_bind_inv in TR.
      destruct TR as [(NV & ? & TR & ?) | (? & TR1 & TR2)]; [apply trans_get_head_inv in TR; easy|].
      apply trans_bind_inv in TR2.
      destruct TR2 as [(NV & ? & TR & ?) | (? & TR2 & TR3)]; [apply trans_get_head_inv in TR; easy|].
      destruct x, x0; try easy; try (exfalso; eapply stuckI_is_stuck; now eauto).
      destruct e, e0, (are_opposite a a0) eqn:?; try (exfalso; eapply stuckI_is_stuck; now eauto).
      apply trans_TauV_inv in TR3 as (EQ & ->).
      pose proof trans_HVis _ TR1 (i := tt).
      pose proof trans_HVis _ TR2 (i := tt).
      (* exists (p ∥ parabang (k x) q). *)
      eexists.
      eapply trans_paraSynch; eauto.
      rewrite unfold_bang at 1.
      apply trans_choiceI41.
      eapply trans_bind_r; eauto; cbn.
      eapply trans_vis'; reflexivity.
      rewrite EQ.
      rewrite para_parabang; auto.

    + (* two copies of q communicated *)
      apply trans_bind_inv in TR.
      destruct TR as [(NV & ? & TR & ?) | (? & TR1 & TR2)]; [apply trans_get_head_inv in TR; easy|].
      apply trans_bind_inv in TR2.
      destruct TR2 as [(NV & ? & TR & ?) | (? & TR2 & TR3)]; [apply trans_get_head_inv in TR; easy|].
      destruct x0, x1; try easy; try (exfalso; eapply stuckI_is_stuck; now eauto).
      destruct e, e0, (are_opposite a a0) eqn:?; try (exfalso; eapply stuckI_is_stuck; now eauto).
      apply trans_TauV_inv in TR3 as (EQ & ->).
      pose proof trans_HVis _ TR1 (i := tt).
      pose proof trans_HVis _ TR2 (i := tt).
      eexists.
      eapply trans_paraR; eauto.
      rewrite unfold_bang at 1.
      apply trans_choiceI43.
      eapply trans_bind_r; [apply TR1 | ].
      eapply trans_bind_r; [apply TR2 | ].
      cbn; rewrite Heqb.
      apply trans_TauV.
      rewrite EQ.
      rewrite para_parabang; auto.

  - intros l p' TR.
    (* Challenge issued by [p ∥ !q] *)
    trans_para_invT TR.
    + (* [p] has moved *)
      cbn.
      (* We unfortunately need to duplicate the proof: we can only instantiate [u'] once we know [l].
         But essentially, the first of the four transitions by [parabang p q] simulates the move.
       *)
      destruct l.
      * apply trans_get_head in TRp.
        destruct TRp as (? & ? & ? & TRp & Eqp).
        rewrite Eqp in EQ; clear p'0 Eqp.
        exists (parabang (x0 x1) q).
        rewrite unfold_parabang.
        apply trans_choiceI41.
        eapply trans_bind_r; eauto; cbn.
        eapply (Steptau x1).
        reflexivity.
        rewrite EQ; auto.
      * apply trans_get_head in TRp.
        destruct TRp as (? & TRp & Eqp).
        rewrite Eqp in EQ; clear p'0 Eqp.
        exists (parabang (x v) q).
        rewrite unfold_parabang.
        apply trans_choiceI41.
        eapply trans_bind_r; eauto; cbn.
        constructor; auto.
        rewrite EQ; auto.
      * apply trans_val_invT in TRp; subst; easy.

    + (* [!q] has moved *)
      cbn.
      (* We need to exhibit that [q'] is essentially some [q''] in parallel with a [!q] *)
      rewrite unfold_bang in TRq.
      apply trans_ChoiceI_inv in TRq as [[|? [|? [| ? x]]] TR].

      * (* q has moved *)
        apply trans_bind_inv in TR.
        destruct TR as [(NV & ? & TR & ?) | (? & TR1 & TR2)]; [apply trans_get_head_inv in TR; easy|].
        destruct x; try easy.
        {
          apply trans_ChoiceV_inv in TR2 as (? & ? & ->).
          exists (parabang (p ∥ k x) q).
          rewrite unfold_parabang.
          apply trans_choiceI42.
          eapply trans_bind_r; eauto.
          cbn.
          eapply trans_ChoiceV'; reflexivity.
          rewrite EQ, H.
          rewrite 2 CIH.
          rewrite <- paraA.
          reflexivity.
        }
        {
          apply trans_vis_inv in TR2 as (? & ? & ->).
          exists (parabang (p ∥ k x) q).
          rewrite unfold_parabang.
          apply trans_choiceI42.
          eapply trans_bind_r; eauto.
          cbn.
          eapply trans_vis'; reflexivity.
          rewrite EQ, H.
          rewrite 2 CIH.
          rewrite <- paraA.
          reflexivity.
        }

      * (* a copy of q has moved *)
        apply trans_bind_inv in TR.
        destruct TR as [(NV & ? & TR & ?) | (? & TR1 & TR2)]; [apply trans_get_head_inv in TR; easy|].
        destruct x; try easy.
        {
          apply trans_ChoiceV_inv in TR2 as (? & ? & ->).
          pose proof trans_HChoice _ TR1 as TR1'.
          rewrite H in EQ; clear q' H.
          eexists.
          specialize (TR1' x).
          rewrite unfold_parabang.
          apply trans_choiceI42.
          eapply trans_bind_r; eauto.
          cbn. eapply trans_ChoiceV'. reflexivity.
          rewrite EQ.
          rewrite (paraC q).
          rewrite parabang_aux.
          rewrite 2 CIH.
          rewrite paraA.
          reflexivity.
        }
        {
          apply trans_vis_inv in TR2 as (? & ? & ->).
          pose proof trans_HVis _ TR1 (i := x) as TR1'.
          rewrite H in EQ; clear q' H.
          eexists.
          rewrite unfold_parabang.
          apply trans_choiceI42.
          eapply trans_bind_r; eauto.
          cbn. eapply trans_vis'. reflexivity.
          rewrite EQ.
          rewrite (paraC q).
          rewrite parabang_aux.
          rewrite 2 CIH.
          rewrite paraA.
          reflexivity.
        }

      * (* two copies of q communicate *)
        apply trans_bind_inv in TR.
        destruct TR as [(NV & ? & TR & ?) | (? & TR1 & TR2)]; [apply trans_get_head_inv in TR; easy|].
        apply trans_bind_inv in TR2.
        destruct TR2 as [(NV & ? & TR & ?) | (? & TR2 & TR3)]; [apply trans_get_head_inv in TR; easy|].
        destruct x, x0; try easy; try (exfalso; eapply stuckI_is_stuck; now eauto).
        destruct e, e0, (are_opposite a a0) eqn:?; try (exfalso; eapply stuckI_is_stuck; now eauto).
        apply trans_TauV_inv in TR3 as (EQ' & ->).
        rewrite EQ' in EQ; clear q' EQ'.
        pose proof trans_HVis _ TR1 (i := tt).
        pose proof trans_HVis _ TR2 (i := tt).
        eexists.
        rewrite unfold_parabang.
        apply trans_choiceI44.
        eapply trans_bind_r; [apply TR1 | ].
        eapply trans_bind_r; [apply TR2 | ].
        cbn; rewrite Heqb.
        apply trans_TauV.
        rewrite EQ.
        rewrite !CIH.
        rewrite !paraA.
        reflexivity.

      * (* two copies of q communicate *)
        apply trans_bind_inv in TR.
        destruct TR as [(NV & ? & TR & ?) | (? & TR1 & TR2)]; [apply trans_get_head_inv in TR; easy|].
        apply trans_bind_inv in TR2.
        destruct TR2 as [(NV & ? & TR & ?) | (? & TR2 & TR3)]; [apply trans_get_head_inv in TR; easy|].
        destruct x0, x1; try easy; try (exfalso; eapply stuckI_is_stuck; now eauto).
        destruct e, e0, (are_opposite a a0) eqn:?; try (exfalso; eapply stuckI_is_stuck; now eauto).
        apply trans_TauV_inv in TR3 as (EQ' & ->).
        rewrite EQ' in EQ; clear q' EQ'.
        pose proof trans_HVis _ TR1 (i := tt).
        pose proof trans_HVis _ TR2 (i := tt).
        eexists.
        rewrite unfold_parabang.
        apply trans_choiceI44.
        eapply trans_bind_r; [apply TR1 | ].
        eapply trans_bind_r; [apply TR2 | ].
        cbn; rewrite Heqb.
        apply trans_TauV.
        rewrite EQ.
        rewrite (paraC q).
        rewrite parabang_aux.
        rewrite !CIH.
        rewrite !paraA.
        reflexivity.

    + (* p and !p communicate *)
      pose proof trans_get_head TRp as (kp & TRhp & EQp).
      (* pose proof trans_get_head TRq as (kq & TRhq & EQq). *)
      rewrite EQp in EQ,TRp; clear p'0 EQp.
      (* rewrite EQq in EQ,TRq; clear q' EQq. *)
      rewrite unfold_bang in TRq.
      apply trans_ChoiceI_inv in TRq as [[|? [|? [| ? ?]]] TR].

      * apply trans_bind_inv in TR.
        destruct TR as [(NV & ? & TR & ?) | (? & TR1 & TR2)]; [apply trans_get_head_inv in TR; easy|].
        destruct x; try easy.
        (* Weird stuff here *)
        pose proof trans_vis_inv TR2 as (? & ? & ?).
        destruct e.
        unfold comm in H0.
        dependent induction H0.
        eexists.
        rewrite unfold_parabang.
        apply trans_choiceI43.
        eapply trans_bind_r; [apply TRhp | ].
        eapply trans_bind_r; [apply TR1 | ].
        cbn. rewrite Op.
        apply trans_TauV.
        cbn; rewrite EQ,H.
        rewrite !CIH.
        rewrite paraA; auto.

      * apply trans_bind_inv in TR.
        destruct TR as [(NV & ? & TR & ?) | (? & TR1 & TR2)]; [apply trans_get_head_inv in TR; easy|].
        destruct x; try easy.
        (* Weird stuff here *)
        pose proof trans_vis_inv TR2 as (? & ? & ?).
        destruct e.
        unfold comm in H0.
        dependent induction H0.
        eexists.
        rewrite unfold_parabang.
        apply trans_choiceI43.
        eapply trans_bind_r; [apply TRhp | ].
        eapply trans_bind_r; [apply TR1 | ].
        cbn. rewrite Op.
        apply trans_TauV.
        cbn; rewrite EQ,H.
        rewrite (paraC q).
        rewrite parabang_aux.
        rewrite !CIH.
        rewrite paraA; auto.

      * apply trans_bind_inv in TR.
        destruct TR as [(NV & ? & TR & ?) | (? & TR1 & TR2)]; [apply trans_get_head_inv in TR; easy|].
        apply trans_bind_inv in TR2.
        destruct TR2 as [(NV & ? & TR & ?) | (? & TR2 & TR3)]; [apply trans_get_head_inv in TR; easy|].
        destruct x, x0; try easy; try (exfalso; eapply stuckI_is_stuck; now eauto).
        destruct e,e0, (are_opposite a0 a1).
        exfalso; now eauto.
        exfalso; eapply stuckI_is_stuck; now eauto.

      * apply trans_bind_inv in TR.
        destruct TR as [(NV & ? & TR & ?) | (? & TR1 & TR2)]; [apply trans_get_head_inv in TR; easy|].
        apply trans_bind_inv in TR2.
        destruct TR2 as [(NV & ? & TR & ?) | (? & TR2 & TR3)]; [apply trans_get_head_inv in TR; easy|].
        destruct x, x0; try easy; try (exfalso; eapply stuckI_is_stuck; now eauto).
        destruct e,e0, (are_opposite a0 a1).
        exfalso; now eauto.
        exfalso; eapply stuckI_is_stuck; now eauto.
Qed.

Lemma unfold_bang' : forall p,
    !p ~ !p ∥ p.
Proof.
  intros; unfold bang at 1.
  rewrite parabang_eq. rewrite paraC; reflexivity.
Qed.

Import CCSNotations.
Open Scope term_scope.

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
	| P ∥ Q  => para (model P) (model Q)
	| P ⊕ Q  => plus (model P) (model Q)
	| P ∖ c  => new c (model P)
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
