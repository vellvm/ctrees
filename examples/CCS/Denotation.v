(*|
=================================
Denotation of [ccs] into [ctree]s
=================================

.. coq:: none
|*)

From Coq Require Export
     List
     Strings.String.
From Coq Require Import RelationClasses Program.

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

From CTree Require Import
	   CTree
     Eq
 	   Interp.Interp
     Head.

Import CTree.

Import CTreeNotations.
Open Scope ctree_scope.

(*|
Event signature
---------------
Processes must at least be able to perform actions.
We do not encode tau steps as events but rather directly as unary stepping branches.
|*)

Variant ActionE : Type -> Type :=
	| Act (a : action) : ActionE unit.

Notation ccsE := ActionE.

Definition ccsT' T := ctree' ccsE T.
Definition ccsT := ctree ccsE.

Definition ccs' := ccsT' void.
Definition ccs  := ccsT void.

Definition comm a : label := obs (Act a) tt.

(*|
Process algebra
|*)
Section Combinators.

	Definition nil : ccs := BrS 0 (fun x : fin 0 => match x with end).

	Definition prefix (a : action) (P: ccs) : ccs := trigger (Act a);; P.

	Definition plus (P Q : ccs) : ccs := brD2 P Q.

  Definition h_new (c : chan) : ActionE ~> ctree ccsE :=
    fun _ e => let '(Act a) := e in
            match a with
            | Send c'
            | Rcv c' =>
                if (c =? c')%string then stuckD else trigger e
            end.
  #[global] Arguments h_new c [T] _.

  Definition new : chan -> ccs -> ccs :=
    fun c P => interp (h_new c) P.

  Definition para : ccs -> ccs -> ccs :=
    cofix F (P : ccs) (Q : ccs) :=
      brD3
        (rP <- head P;;
         match rP with
         | ARet rP => match rP with end
         | ABr kP => BrS _ (fun i => F (kP i) Q)
         | AVis e kP => Vis e (fun i => F (kP i) Q)
         end)

        (rQ <- head Q;;
         match rQ with
         | ARet rQ => match rQ with end
         | ABr kQ => BrS _ (fun i => F P (kQ i))
         | AVis e kQ => Vis e (fun i => F P (kQ i))
         end)

        (rP <- head P;;
         rQ <- head Q;;
         match rP, rQ with
         | AVis eP kP, AVis eQ kQ =>
             match eP, kP, eQ, kQ with
             | Act a, kP, Act b, kQ =>
                 if are_opposite a b
                 then
                   Step (F (kP tt) (kQ tt))
                 else
                   stuckD
             end
         | _, _ => stuckD
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

  Definition parabang : ccs -> ccs -> ccs :=
    cofix pB (p : ccs) (q:ccs) : ccs :=

      brD4

        (* Communication by p *)
        (rp <- head p;;
         match rp with
         | ARet rp => match rp with end
         | ABr kp => BrS _ (fun i =>  pB (kp i) q )
         | AVis e kp => Vis e (fun i => pB (kp i) q)
         end)

        (* Communication by a fresh copy of q *)
        (rq <- head q;;
         match rq with
         | ARet rq => match rq with end
         | ABr kq => BrS _ (fun i => (pB  (para p (kq i)) q))
         | AVis e kq => Vis e (fun i => (pB  (para p (kq i)) q))
         end)

        (* Communication between p and a fresh copy of q *)
        (rp <- head p;;
         rq <- head q;;
         match rp, rq with
         | AVis ep kp, AVis eq kq =>
             match ep, kp, eq, kq with
             | Act a, kp, Act b, kq =>
                 if are_opposite a b
                 then
                   Step (pB (para (kp tt) (kq tt)) q)
                 else
                   stuckD
             end

         | _, _ => stuckD
         end)

        (* Communication between two fresh copies of q *)
        (rq1 <- head q;;
         rq2 <- head q;;
         match rq1, rq2 with
         | AVis eq1 kq1, AVis eq2 kq2 =>
             match eq1, kq1, eq2, kq2 with
             | Act a, kq1, Act b, kq2 =>
                 if are_opposite a b
                 then
                   Step (pB (para p (para (kq1 tt) (kq2 tt))) q)
                 else
                   stuckD
             end

         | _, _ => stuckD
         end).

  Definition bang (P : ccs) : ccs := parabang P P.

End Combinators.

Module CCSNotationsSem.

  Declare Scope ccs_scope.

  Notation "0" := nil: ccs_scope.
  Infix "+" := plus (at level 50, left associativity) : ccs_scope.
  Infix "∥" := para (at level 29, left associativity) : ccs_scope.
  Notation "! x" := (bang x) : ccs_scope.

End CCSNotationsSem.

Import CCSNotationsSem.
Open Scope ccs_scope.

#[global] Instance equ_clos_sb_goal {E R} RR :
  Proper (equ eq ==> equ eq ==> flip impl) (@sb E R RR).
Proof.
  cbn; unfold Proper, respectful; intros * eq1 * eq2 bis.
  destruct bis as [F B]; cbn in *.
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

#[global] Instance equ_clos_sb_ctx {E R} RR :
  Proper (gfp (@fequ E R R eq) ==> equ eq ==> impl) (sb RR).
Proof.
  cbn; unfold Proper, respectful; intros * eq1 * eq2 bis.
  destruct bis as [F B]; cbn in *.
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
Lemma ctx_prefix_tequ a: unary_ctx (prefix a) <= (et eq).
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

#[global] Instance prefix_tequ a: forall R, Proper (et eq R ==> et eq R) (prefix a) := unary_proper_t (@ctx_prefix_tequ a).

Definition can_comm (c : chan) (a : @label ccsE) : bool :=
  match a with
  | obs (Act a) _ =>
      match a with
      | Send c'
      | Rcv c' => if (c =? c')%string then false else true
      end
  | _ => true
  end.

Lemma trans_trigger_inv' : forall {E X} (e : E X) l u,
		trans l (trigger e) u ->
    exists x, u ≅ Ret x /\ l = obs e x.
Proof.
  intros * TR.
  unfold trigger in TR.
  now apply trans_vis_inv in TR.
Qed.

Lemma trans_hnew_inv : forall a l c p,
    trans l (h_new c (Act a)) p ->
    l = obs (Act a) tt /\ can_comm c l /\ p ≅ Ret tt.
Proof.
  intros * tr.
  cbn in *; destruct a; cbn in *; destruct (c =? c0) eqn:comm; cbn in *.
  all: try (exfalso; eapply stuckD_is_stuck, tr).
  all: unfold can_comm; apply trans_trigger_inv' in tr as ([] & ? & ?); subst; rewrite comm; eauto.
Qed.

Lemma trans_vis' {E R X} : forall (e : E X) x (k : X -> ctree E R) u,
    u ≅ k x ->
		trans (obs e x) (Vis e k) u.
Proof.
	intros * eq; rewrite eq; apply trans_vis.
Qed.

Lemma new_tau : forall c t, new c (Guard t) ≅ Guard (Guard (new c t)).
Proof.
  intros; unfold new; now rewrite interp_tau.
Qed.

Ltac eq2bisim H :=
  match type of H with
  | ?u = ?t => let eq := fresh "EQ" in assert (eq : u ~ t) by (subst; reflexivity); clear H
  end.

#[global] Instance interp_equ {E F R} (h : E ~> ctree F) :
  Proper (equ eq ==> equ eq) (interp h (T := R)).
Proof.
  unfold Proper, respectful.
  coinduction ? CIH.
  intros t u eq.
  step in eq; inv eq; auto.
  - rewrite 2 unfold_interp, <-H0, <-H; auto.
  - rewrite 2 unfold_interp.
    (* Can we make the up-to bind here nicer to use? *)
    rewrite <- H0, <-H.
    simpl Monad.bind.
    upto_bind_eq.
    constructor; intros ?.
    auto.
  - rewrite 2 unfold_interp, <-H0, <-H. cbn*.
    constructor; intros ?.
    step.
    cbn*; constructor; intros ?.
    auto.
Qed.

#[global] Instance new_equ c :
  Proper (equ eq ==> equ eq) (new c).
Proof.
  apply interp_equ.
Qed.

Lemma trans_new : forall l c p p',
    trans l p p' ->
    can_comm c l = true ->
    exists q, trans l (new c p) q /\ q ~ new c p'.
Proof.
  intros * tr comm.
  do 3 red in tr.
  genobs p obsp; genobs p' op'.
  revert p p' Heqobsp Heqop'.
  induction tr; intros.
  - edestruct IHtr as (q & tr' & eq); eauto.
    exists q; split; auto.
    unfold new; rewrite unfold_interp, <- Heqobsp.
    cbn; unfold Utils.mbr, MonadBr_ctree, br.
    eapply trans_bind_r with x.
    eapply trans_brD; [|reflexivity].
    apply trans_ret.
    apply trans_guard.
    apply tr'.
  - eexists; split.
    unfold new; rewrite unfold_interp, <- Heqobsp.
    cbn; unfold Utils.mbr, MonadBr_ctree, br.
    eapply trans_bind_l.
    intros abs; inv abs.
    apply trans_brS with (x := x).
    rewrite bind_ret_l, sb_guard.
    rewrite H.
    unfold new; rewrite 2 unfold_interp, Heqop'.
    reflexivity.
  - destruct e, a.
    all: cbn in *; destruct (c =? c0) eqn:comm'; inv comm.
    + eexists; split.
      unfold new; rewrite unfold_interp, <- Heqobsp.
      cbn; unfold Utils.mbr, MonadBr_ctree, br.
      eapply trans_bind_l.
      intros abs; inv abs.
      rewrite comm'.
      unfold trigger.
      eapply trans_vis'.
      reflexivity.
      rewrite bind_ret_l, sb_guard, H.
      unfold new; rewrite 2 unfold_interp, Heqop'.
      reflexivity.
    + eexists; split.
      unfold new; rewrite unfold_interp, <- Heqobsp.
      cbn; unfold Utils.mbr, MonadBr_ctree, br.
      eapply trans_bind_l.
      intros abs; inv abs.
      rewrite comm'.
      unfold trigger.
      eapply trans_vis'.
      reflexivity.
      rewrite bind_ret_l, sb_guard, H.
      unfold new; rewrite 2 unfold_interp, Heqop'.
      reflexivity.
  - tauto.
Qed.

Lemma trans_new_inv_aux : forall l T U,
    trans_ l T U ->
    forall c p q,
      (go T ≅ new c p \/ go T ≅ Guard (new c p)) ->
      go U ≅ q ->
      exists q', can_comm c l = true /\ trans l p q' /\ q ≅ Guard (new c q').
Proof.
  intros * tr c.
  induction tr; intros * EQ1 EQ2.
  - destruct EQ1 as [EQ1 | EQ1].
    + unfold new in EQ1; rewrite unfold_interp in EQ1.
      unfold trans, transR.
      cbn.
      desobs p; try now step in EQ1; inv EQ1.
      * destruct e,a; cbn in *.
        ** destruct (c =? c0); cbn in *.
           *** step in EQ1; dependent induction EQ1; inv x0.
           *** step in EQ1; inv EQ1.
        ** destruct (c =? c0); cbn in *.
           *** step in EQ1; dependent induction EQ1; inv x0.
           *** step in EQ1; inv EQ1.
      * cbn in EQ1.
        destruct vis; try now step in EQ1; inv EQ1.
        unfold Utils.mbr, MonadBr_ctree, br in EQ1.
        cbn in * |-.
        rewrite unfold_bind in EQ1; cbn in EQ1.
        epose proof equ_br_invT _ _ EQ1 as [<- _].
        epose proof equ_br_invE _ _ EQ1 x as eqx.
        cbn in * |-; rewrite bind_ret_l in eqx.
        setoid_rewrite <- ctree_eta in IHtr.
        setoid_rewrite eqx in IHtr.
        edestruct (IHtr (k0 x)) as (q' & comm & tr' & EQ); [right; reflexivity | reflexivity |].
        exists q'; repeat split; auto.
        eapply trans_brD with (x := x).
        eauto.
        reflexivity.
        rewrite <- EQ, EQ2; auto.
    + epose proof equ_br_invT _ _ EQ1 as [? _]; subst.
      epose proof equ_br_invE _ _ EQ1 x as eqx.
      clear EQ1.
      edestruct IHtr as (q' & comm & tr' & EQ); [| eassumption |].
      left; rewrite eqx, <- ctree_eta; reflexivity.
      exists q'; repeat split; auto.
  - destruct EQ1 as [EQ1 | EQ1]; [ | step in EQ1; inv EQ1].
    unfold new in EQ1; rewrite unfold_interp in EQ1.
    unfold trans,transR; cbn.
    desobs p; try now step in EQ1; inv EQ1.
    + cbn in *.
      destruct e,a; cbn in *; destruct (c =? c0) eqn:EQ; now step in EQ1; inv EQ1.
    + cbn in *.
      unfold Utils.mbr, MonadBr_ctree, br in EQ1.
      destruct vis; try now step in EQ1; inv EQ1.
      rewrite unfold_bind in EQ1; cbn in EQ1.
      epose proof equ_br_invT _ _ EQ1 as [<- _].
      epose proof equ_br_invE _ _ EQ1 x as eqx; clear EQ1.
      rewrite bind_ret_l in eqx.
      rewrite H in eqx.
      rewrite <- ctree_eta in EQ2.
      rewrite EQ2 in eqx.
      clear k t EQ2 H.
      exists (k0 x); repeat split.
      apply trans_brS.
      auto.
  - destruct EQ1 as [EQ1 | EQ1]; [ | step in EQ1; inv EQ1].
    unfold new in EQ1; rewrite unfold_interp in EQ1.
    unfold trans,transR; cbn.
    desobs p; try now step in EQ1; inv EQ1.
    cbn in *.
    destruct e0,a; cbn in *; destruct (c =? c0) eqn:EQ; try now step in EQ1; inv EQ1.
    all:unfold trigger in EQ1; rewrite unfold_bind in EQ1; cbn in EQ1; setoid_rewrite bind_ret_l in EQ1.
    all:epose proof equ_vis_invT _ _ _ _ EQ1; subst.
    all:epose proof equ_vis_invE _ _ _ _ EQ1 as [-> eqx]; clear EQ1.
    all:rewrite EQ.
    all:specialize (eqx x).
    all:rewrite H in eqx; rewrite <- ctree_eta in EQ2; rewrite EQ2 in eqx.
    all: exists (k0 x); repeat split; auto.
    all: apply trans_vis.
  - tauto.
Qed.

Lemma trans_new_inv : forall l c p p',
    trans l (new c p) p' ->
    exists q, can_comm c l = true /\ trans l p q /\ p' ≅ Guard (new c q).
Proof.
  intros; eapply trans_new_inv_aux; eauto.
  eapply trans_brD with (x := Fin.F1); eauto.
  symmetry; apply ctree_eta.
Qed.

Lemma trans_new_inv' : forall l c p p',
    trans l (new c p) p' ->
    exists q, can_comm c l = true /\ trans l p q /\ p' ~ new c q.
Proof.
  intros; edestruct trans_new_inv as (? & ? & ? & ?); eauto.
  eexists; repeat split; eauto.
  rewrite H2, sb_guard; reflexivity.
Qed.

(** ** name restriction *)
Lemma ctx_new_st a: unary_ctx (new a) <= st.
Proof.
  apply Coinduction, by_Symmetry. apply unary_sym.
  intro R. apply (leq_unary_ctx (new a)). intros p q Hpq l p0 Hp0.
  apply trans_new_inv in Hp0 as (? & comm & tr & EQ).
  destruct (proj1 Hpq _ _ tr) as [???].
  eapply trans_new in H as (q' & tr' & eq'); eauto.
  exists q'; eauto.
  rewrite EQ.
  rewrite eq'.
  rewrite sb_guard.
  apply unary_proper_Tctx, (id_T sb).
  auto.
Qed.

#[global] Instance new_st a: forall R, Proper (st R ==> st R) (new a) := unary_proper_t (@ctx_new_st a).

Lemma trans_plus_inv : forall l p q r,
    trans l (p + q) r ->
    (exists p', trans l p p' /\ r ≅ p') \/
      (exists q', trans l q q' /\ r ≅ q').
Proof.
  intros * tr.
  apply trans_brD_inv in tr as ([|] & tr); eauto.
Qed.

Lemma trans_brS' {E X} : forall n (k : fin n -> ctree E X) x u,
    u ≅ k x ->
		trans tau (BrS n k) u.
Proof.
	intros * eq; rewrite eq; apply trans_brS.
Qed.

Lemma trans_plusL : forall l p p' q,
    trans l p p' ->
    trans l (p + q) p'.
Proof.
  intros * tr.
  now apply trans_brD21.
Qed.

Lemma trans_plusR : forall l p q q',
    trans l q q' ->
    trans l (p + q) q'.
Proof.
  intros * tr.
  now apply trans_brD22.
Qed.

(** ** br *)
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
  (brD3
     (rp <- head p;;
      match rp with
      | ARet rp => match rp with end
      | ABr kp => BrS _ (fun i => para (kp i) q)
      | AVis e kp => Vis e (fun i => para (kp i) q)
      end)

     (rq <- head q;;
      match rq with
      | ARet rq => match rq with end
      | ABr kq => BrS _ (fun i => para p (kq i))
      | AVis e kq => Vis e (fun i => para p (kq i))
      end)

     (rp <- head p;;
      rq <- head q;;
      match rp, rq with
      | AVis ep kp, AVis eq kq =>
          match ep, kp, eq, kq with
          | Act a, kp, Act b, kq =>
              if are_opposite a b
              then
                Step (para (kp tt) (kq tt))
              else
                stuckD
          end
      | _, _ => stuckD
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
  - upto_bind; [apply head_equ; auto | intros hdp1 hdp2 eqp].
    inv eqp; auto.
    step; constructor; auto.
    step; constructor; auto.
  - upto_bind; [apply head_equ; auto | intros hdp1 hdp2 eqp].
    inv eqp; auto.
    step; constructor; auto.
    step; constructor; auto.
  - upto_bind; [apply head_equ; auto | intros hdp1 hdp2 eqp].
    upto_bind; [apply head_equ; auto | intros hdq1 hdq2 eqq].
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
  apply trans_head in TRp as (kp & TRp & Eqp).
  apply trans_head in TRq as (kq & TRq & Eqq).
  rewrite unfold_para.
  apply trans_brD33.
  eapply trans_bind_r; [apply TRp |].
  eapply trans_bind_r; [apply TRq |].
  cbn; rewrite Op.
  rewrite Eqp, Eqq.
  apply trans_step.
Qed.

Lemma trans_paraL :
  forall l (p p' q : ccs),
    trans l p p' ->
    trans l (p ∥ q) (p' ∥ q).
Proof.
  intros * TRp.
  rewrite unfold_para.
  apply trans_brD31.
  destruct l.
  - apply trans_head in TRp.
    destruct TRp as (? & ? & ? & TRp & Eqp).
    eapply trans_bind_r; eauto; cbn.
    econstructor.
    rewrite Eqp; reflexivity.
  - apply trans_head in TRp.
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
  apply trans_brD32.
  destruct l.
  - apply trans_head in TRq.
    destruct TRq as (? & ? & ? & TRq & Eqq).
    eapply trans_bind_r; eauto; cbn.
    econstructor.
    rewrite Eqq; reflexivity.
  - apply trans_head in TRq.
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
  apply trans_brD_inv in TR as (x & TR).
  destruct x; [| destruct x].
  - left.
    edestruct @trans_bind_inv; [apply TR | | ]; clear TR.
    destruct H as (NOTV & ? & TR & EQ); apply trans_head_inv in TR; easy.
    destruct H as (hdp & TRhdp & TR).
    destruct hdp; try easy.
    * apply trans_brS_inv in TR as (x & EQ & ->).
      eapply trans_ABr in TRhdp.
      eexists; split; eauto.
    * apply trans_vis_inv in TR as (x & EQ & ->).
      eapply trans_AVis in TRhdp.
      eexists; split; eauto.
  - right; left.
    edestruct @trans_bind_inv; [apply TR | | ]; clear TR.
    destruct H as (NOTV & ? & TR & EQ); apply trans_head_inv in TR; easy.
    destruct H as (hdq & TRhdq & TR).
    destruct hdq; try easy.
    * apply trans_brS_inv in TR as (x & EQ & ->).
      eapply trans_ABr in TRhdq.
      eexists; split; eauto.
    * apply trans_vis_inv in TR as (x & EQ & ->).
      eapply trans_AVis in TRhdq.
      eexists; split; eauto.
  - right; right.
    edestruct @trans_bind_inv; [apply TR | | ]; clear TR.
    destruct H as (NOTV & ? & TR & EQ); apply trans_head_inv in TR; easy.
    destruct H as (hdp & TRhdp & TR).
    edestruct @trans_bind_inv; [apply TR | | ]; clear TR.
    destruct H as (NOTV & ? & TR & EQ); apply trans_head_inv in TR; easy.
    destruct H as (hdq & TRhdq & TR).
    destruct hdp; try easy.
    exfalso; eapply stuckD_is_stuck; eassumption.
    destruct hdq; try easy.
    exfalso; eapply stuckD_is_stuck; eassumption.
    destruct e, e0, (are_opposite a a0) eqn:?.
    2:exfalso; eapply stuckD_is_stuck; eassumption.
    apply trans_step_inv in TR as [? ->].
    eapply trans_AVis in TRhdp.
    eapply trans_AVis in TRhdq.
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
    apply brD2_commut.
  Qed.

  Lemma plsA (p q r : ccs): p+(q+r) ~ (p+q)+r.
  Proof.
    symmetry; apply brD2_assoc.
  Qed.

  Lemma pls0p (p : ccs) : 0 + p ~ p.
  Proof.
    apply brD2_stuckS_l.
  Qed.

  Lemma plsp0 (p : ccs) : p + 0 ~ p.
  Proof. now rewrite plsC, pls0p. Qed.

  Lemma plsidem (p : ccs) : p + p ~ p.
  Proof.
    apply brD2_idem.
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
      trans_para_invT tr; try now exfalso; eapply stuckS_is_stuck; eauto.
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
  (brD4

     (* Communication by p *)
     (rp <- head p;;
      match rp with
      | ARet rp => match rp with end
      | ABr kp => BrS _ (fun i => parabang (kp i) q )
      | AVis e kp => Vis e (fun i => parabang (kp i) q)
      end)

     (* Communication by a fresh copy of q *)
     (rq <- head q;;
      match rq with
      | ARet rq => match rq with end
      | ABr kq => BrS _ (fun i => (parabang (para p (kq i)) q))
      | AVis e kq => Vis e (fun i => (parabang (para p (kq i)) q))
      end)

     (* Communication between p and a fresh copy of q *)
     (rp <- head p;;
      rq <- head q;;
      match rp, rq with
      | AVis ep kp, AVis eq kq =>
          match ep, kp, eq, kq with
          | Act a, kp, Act b, kq =>
              if are_opposite a b
              then
                Step (parabang (para (kp tt) (kq tt)) q)
              else
                stuckD
          end

      | _, _ => stuckD
      end)

     (* Communication between two fresh copies of q *)
     (rq1 <- head q;;
      rq2 <- head q;;
      match rq1, rq2 with
      | AVis eq1 kq1, AVis eq2 kq2 =>
          match eq1, kq1, eq2, kq2 with
          | Act a, kq1, Act b, kq2 =>
              if are_opposite a b
              then
                Step (parabang (para p (para (kq1 tt) (kq2 tt))) q)
              else
                stuckD
          end

      | _, _ => stuckD
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
  - upto_bind; [apply head_equ; auto | intros hdp1 hdp2 eqp].
    inv eqp; auto.
    step; constructor; auto.
    step; constructor; auto.
  - upto_bind; [apply head_equ; auto | intros hdp1 hdp2 eqp].
    inv eqp; auto.
    step; constructor; intros ?.
    apply CIH; auto; rewrite EQp, H; reflexivity.
    step; constructor; intros ?.
    apply CIH; auto; rewrite EQp, H; reflexivity.
  - upto_bind; [apply head_equ; auto | intros hdp1 hdp2 eqp].
    upto_bind; [apply head_equ; auto | intros hdq1 hdq2 eqq].
    inv eqp; auto.
    inv eqq; auto.
    destruct e, e0, (are_opposite a a0); auto.
    step; constructor; intros ?.
    apply CIH; auto.
    rewrite H,H0; reflexivity.
  - upto_bind; [apply head_equ; auto | intros hdp1 hdp2 eqp].
    upto_bind; [apply head_equ; auto | intros hdq1 hdq2 eqq].
    inv eqp; auto.
    inv eqq; auto.
    destruct e, e0, (are_opposite a a0); auto.
    step; constructor; intros ?.
    apply CIH; auto.
    rewrite EQp, H,H0; reflexivity.
Qed.

Lemma trans_parabangL : forall p l p' q,
    trans l p p' ->
    trans l (parabang p q) (parabang p' q).
Proof.
  intros * TR.
  pose proof trans_head TR.
  rewrite unfold_parabang.
  apply trans_brD41.
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
  pose proof trans_head TR.
  rewrite unfold_parabang.
  apply trans_brD42.
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

Lemma trans_parabangSL : forall a b p p' q q',
    are_opposite a b ->
    trans (comm a) p p' ->
    trans (comm b) q q' ->
    trans tau (parabang p q) (parabang (p' ∥ q') q).
Proof.
  intros * Op TR1 TR2.
  pose proof trans_head TR1 as (? & TRh1 & EQ1).
  pose proof trans_head TR2 as (? & TRh2 & EQ2).
  rewrite unfold_parabang.
  apply trans_brD43.
  eapply trans_bind_r; [apply TRh1 | ].
  eapply trans_bind_r; [apply TRh2 | ].
  cbn; rewrite Op.
  rewrite EQ1,EQ2.
  apply trans_step.
Qed.

Lemma trans_parabangSR : forall a b p q q' q'',
    are_opposite a b ->
    trans (comm a) q q' ->
    trans (comm b) q q'' ->
    trans tau (parabang p q) (parabang (p ∥ (q' ∥ q'')) q).
Proof.
  intros * Op TR1 TR2.
  pose proof trans_head TR1 as (? & TRh1 & EQ1).
  pose proof trans_head TR2 as (? & TRh2 & EQ2).
  rewrite unfold_parabang.
  apply trans_brD44.
  eapply trans_bind_r; [apply TRh1 | ].
  eapply trans_bind_r; [apply TRh2 | ].
  cbn; rewrite Op.
  rewrite EQ1,EQ2.
  apply trans_step.
Qed.

Lemma trans_parabang_inv : forall l p q r,
    trans l (parabang p q) r ->
    (exists p', trans l p p' /\ r ≅ parabang p' q) \/
      (exists q', trans l q q' /\ r ≅ parabang (p ∥ q') q) \/
      (exists a b p' q', trans (comm a) p p' /\
                      trans (comm b) q q' /\
                      are_opposite a b /\
                      l = tau /\
                      r ≅ parabang (p' ∥ q') q) \/
      (exists a b q' q'', trans (comm a) q q' /\
                       trans (comm b) q q'' /\
                       are_opposite a b /\
                       l = tau /\
                       r ≅ parabang (p ∥ (q' ∥ q'')) q).
Proof.
  intros * TR.
  rewrite unfold_parabang in TR.
  apply trans_brD_inv in TR as [[|? [|? [| ? x]]] TR].
  - left.
    apply trans_bind_inv in TR.
    destruct TR as [(NV & ? & TR & ?) | (? & TR1 & TR2)]; [apply trans_head_inv in TR; easy|].
    destruct x; try easy.
    apply trans_brS_inv in TR2 as (x & EQ & ->).
    pose proof trans_ABr TR1 x.
    eauto.
    apply trans_vis_inv in TR2 as (x & EQ & ->).
    pose proof trans_AVis TR1 (i := x).
    eauto.
  - right; left.
    apply trans_bind_inv in TR.
    destruct TR as [(NV & ? & TR & ?) | (? & TR1 & TR2)]; [apply trans_head_inv in TR; easy|].
    destruct x; try easy.
    apply trans_brS_inv in TR2 as (x & EQ & ->).
    pose proof trans_ABr TR1 x.
    eauto.
    apply trans_vis_inv in TR2 as (x & EQ & ->).
    pose proof trans_AVis TR1 (i := x).
    eauto.
  - right; right; left.
    apply trans_bind_inv in TR.
    destruct TR as [(NV & ? & TR & ?) | (? & TR1 & TR2)]; [apply trans_head_inv in TR; easy|].
    apply trans_bind_inv in TR2.
    destruct TR2 as [(NV & ? & TR & ?) | (? & TR2 & TR3)]; [apply trans_head_inv in TR; easy|].
    destruct x, x0; try easy; try now (exfalso; eapply stuckD_is_stuck; eauto).
    destruct e, e0, (are_opposite a a0) eqn:?; try easy; try now (exfalso; eapply stuckD_is_stuck; eauto).
    apply trans_step_inv in TR3 as (? & ->).
    pose proof trans_AVis TR1 (i := tt).
    pose proof trans_AVis TR2 (i := tt).
    eauto 10.
  - right; right; right.
    apply trans_bind_inv in TR.
    destruct TR as [(NV & ? & TR & ?) | (? & TR1 & TR2)]; [apply trans_head_inv in TR; easy|].
    apply trans_bind_inv in TR2.
    destruct TR2 as [(NV & ? & TR & ?) | (? & TR2 & TR3)]; [apply trans_head_inv in TR; easy|].
    destruct x0, x1; try easy; try now (exfalso; eapply stuckD_is_stuck; eauto).
    destruct e, e0, (are_opposite a a0) eqn:?; try easy; try now (exfalso; eapply stuckD_is_stuck; eauto).
    apply trans_step_inv in TR3 as (? & ->).
    pose proof trans_AVis TR1 (i := tt).
    pose proof trans_AVis TR2 (i := tt).
    eauto 10.
Qed.

Ltac trans_parabang_invT TR :=
  apply trans_parabang_inv in TR as
      [(?p' & ?TRp' & ?EQ) |
        [(?q' & ?TRq' & ?EQ) |
          [(?a & ?b & ?p' & ?q' & ?TRp' & ?TRq' & ?Op & ?EQl & ?EQ) |
            (?a & ?b & ?q' & ?q'' & ?TRq' & ?TRq'' & ?Op & ?EQl & ?EQ)]]]; subst.

Ltac pbL := apply trans_parabangL.
Ltac pbR := apply trans_parabangR.
Ltac pbSL := eapply trans_parabangSL.
Ltac pbSR := eapply trans_parabangSR.

Ltac pL := apply trans_paraL.
Ltac pR := apply trans_paraR.
Ltac pS := eapply trans_paraSynch.

Lemma para_parabang : forall p q r,
    parabang (p ∥ q) r ~ p ∥ parabang q r.
Proof.
  coinduction ? CIH.
  intros; split.
  - intros l s TR.
    trans_parabang_invT TR.
    + trans_para_invT TRp'.
      * eexists.
        pL; eauto.
        rewrite EQ, EQ0; auto.
      * eexists.
        pR;pbL; eauto.
        rewrite EQ,EQ0; auto.
      * eexists.
        pS; eauto.
        pbL; eauto.
        rewrite EQ,EQ0; auto.
    + eexists.
      pR; pbR; eauto.
      rewrite EQ, !CIH, paraA; auto.

    + trans_para_invT TRp'.
      * eexists.
        pS; eauto.
        pbR; eauto.
        rewrite EQ,EQ0, !CIH, !paraA; eauto.
      * eexists.
        pR; pbSL; eauto.
        rewrite EQ,EQ0, !CIH, !paraA; eauto.
      * easy.

    + eexists.
      pR; pbSR; eauto.
      rewrite EQ, !CIH, !paraA; eauto.

  - intros l s TR.
    trans_para_invT TR.
    + eexists.
      pbL;pL; eauto.
      cbn; rewrite EQ; auto.

    + trans_parabang_invT TRq.
      * eexists.
        pbL;pR; eauto.
        cbn; rewrite EQ, EQ0; auto.
      * eexists.
        pbR; eauto.
        cbn; rewrite EQ,EQ0,!CIH,!paraA; auto.
      * eexists.
        pbSL; eauto.
        pR; eauto.
        cbn; rewrite EQ,EQ0,!CIH,!paraA; auto.
      * eexists.
        pbSR; eauto.
        cbn; rewrite EQ,EQ0,!CIH,!paraA; auto.

    + trans_parabang_invT TRq.
      * eexists.
        pbL;pS; eauto.
        cbn; rewrite EQ, EQ0; auto.
      * eexists.
        pbSL; eauto.
        pL; eauto.
        cbn; rewrite EQ,EQ0,!CIH,!paraA; auto.
      * easy.
      * easy.
Qed.

Lemma ctx_parabang_t: binary_ctx parabang <= st.
Proof.
  apply Coinduction, by_Symmetry. apply binary_sym.
  intro R. apply (leq_binary_ctx parabang).
  intros * [F1 B1] * [F2 B2] ? * tr.
  trans_parabang_invT tr.
  - apply F1 in TRp' as [? tr ?].
    eexists.
    pbL; eauto.
    rewrite EQ.
    apply (fTf_Tf sb). apply (in_binary_ctx parabang).
    now apply (id_T sb).
    now apply (b_T sb).
  - apply F2 in TRq' as [? tr ?].
    eexists.
    pbR; eauto.
    rewrite EQ.
    apply (fTf_Tf sb). apply (in_binary_ctx parabang).
    apply (fT_T ctx_para_t).
    apply (in_binary_ctx para).
    now apply (b_T sb).
    now apply (id_T sb).
    now apply (b_T sb).
  - apply F1 in TRp' as [? trp ?].
    apply F2 in TRq' as [? trq ?].
    eexists.
    pbSL; eauto.
    rewrite EQ.
    apply (fTf_Tf sb). apply (in_binary_ctx parabang).
    apply (fT_T ctx_para_t).
    apply (in_binary_ctx para).
    now apply (id_T sb).
    now apply (id_T sb).
    now apply (b_T sb).
  - apply F2 in TRq' as [? trp ?].
    apply F2 in TRq'' as [? trq ?].
    eexists.
    pbSR; eauto.
    rewrite EQ.
    apply (fTf_Tf sb). apply (in_binary_ctx parabang).
    apply (fT_T ctx_para_t), (in_binary_ctx para).
    now apply (b_T sb).
    apply (fT_T ctx_para_t), (in_binary_ctx para).
    now apply (id_T sb).
    now apply (id_T sb).
    now apply (b_T sb).
Qed.
#[global] Instance parabang_t: forall R, Proper (st R ==> st R ==> st R) parabang := binary_proper_t ctx_parabang_t.
#[global] Instance parabang_T f: forall R, Proper (T sb f R ==> T sb f R ==> T sb f R) parabang := binary_proper_T ctx_parabang_t.

Lemma parabang_aux : forall p q,
    parabang (p ∥ q) q ~ parabang p q.
Proof.
  coinduction ? CIH.
  split.
  - intros l r TR.
    trans_parabang_invT TR.

    + trans_para_invT TRp'.
      * eexists.
        pbL; eauto.
        rewrite EQ,EQ0; eauto.
      * eexists.
        pbR; eauto.
        rewrite EQ,EQ0; eauto.
      * eexists.
        pbSL; eauto.
        rewrite EQ,EQ0; eauto.

    + eexists.
      pbR; eauto.
      rewrite EQ.
      rewrite <- paraA.
      rewrite (paraC q).
      rewrite paraA.
      auto.

    + trans_para_invT TRp'.
      * eexists.
        pbSL; eauto.
        rewrite EQ, EQ0.
        rewrite <- paraA.
        rewrite (paraC q).
        rewrite paraA.
        auto.
      * eexists.
        pbSR; eauto.
        rewrite EQ, EQ0.
        rewrite <- paraA; auto.
      * easy.

    + eexists.
      pbSR; eauto.
      rewrite EQ.
      rewrite <- paraA.
      rewrite (paraC q).
      rewrite ! paraA.
      auto.

  - intros l p' TR.
    trans_parabang_invT TR.

    + eexists.
      pbL;pL; eauto.
      cbn; rewrite EQ; eauto.

    + eexists.
      pbL;pR; eauto.
      cbn; rewrite EQ; eauto.

    + eexists.
      pbL;pS; eauto.
      cbn; rewrite EQ; eauto.

    + eexists.
      pbSL; eauto.
      pR; eauto.
      cbn; rewrite EQ, !paraA; eauto.

Qed.

Lemma parabang_eq : forall p q,
    parabang p q ~ p ∥ !q.
Proof.
  coinduction ? CIH.
  intros p q; split.

  - intros l p' TR.
    trans_parabang_invT TR.

    + eexists.
      pL; eauto.
      rewrite EQ; eauto.

    + eexists.
      pR; pbL; eauto.
      rewrite EQ; eauto.
      rewrite para_parabang; auto.

    + eexists.
      pS; eauto.
      pbL; eauto.
      rewrite EQ; eauto.
      rewrite para_parabang; auto.

    + eexists.
      pR; pbSL; eauto.
      rewrite EQ; eauto.
      rewrite para_parabang; auto.

  - intros l p' TR.
    trans_para_invT TR.

    + eexists.
      pbL; eauto.
      cbn; rewrite EQ; eauto.

    + trans_parabang_invT TRq.
      * eexists.
        pbR; eauto.
        cbn; rewrite EQ,EQ0; eauto.
        rewrite !CIH, !paraA; eauto.
      * eexists.
        pbR; eauto.
        cbn; rewrite EQ,EQ0; eauto.
        rewrite (paraC q), parabang_aux.
        rewrite !CIH, !paraA; eauto.
      * eexists.
        pbSR; eauto.
        cbn; rewrite EQ,EQ0; eauto.
        rewrite !CIH, !paraA; eauto.
      * eexists.
        pbSR; eauto.
        cbn; rewrite EQ,EQ0; eauto.
        rewrite (paraC q), parabang_aux.
        rewrite !CIH, !paraA; eauto.

    + trans_parabang_invT TRq.
      * eexists.
        pbSL; eauto.
        cbn; rewrite EQ,EQ0; eauto.
        rewrite !CIH, !paraA; eauto.
      * eexists.
        pbSL; eauto.
        cbn; rewrite EQ,EQ0; eauto.
        rewrite (paraC q), parabang_aux.
        rewrite !CIH, !paraA; eauto.
      * easy.
      * easy.
Qed.

Lemma unfold_bang' : forall p,
    !p ~ !p ∥ p.
Proof.
  intros; unfold bang at 1.
  rewrite parabang_eq. rewrite paraC; reflexivity.
Qed.

Import CCSNotations.
Open Scope term_scope.

Fixpoint model (t : term) : ccs :=
	match t with
	| 0      => nil
	| a · P  => prefix a (model P)
	| TauT P => Step (model P)
	| P ∥ Q  => para (model P) (model Q)
	| P ⊕ Q  => plus (model P) (model Q)
	| P ∖ c  => new c (model P)
	| !P    => bang (model P)
	end.

Module DenNotations.

  (* Notations for patterns *)
  Notation "'synchP' e" := (inl1 e) (at level 10).
  Notation "'actP' e" := (inr1 (inl1 e)) (at level 10).
  Notation "'deadP' e" :=  (inr1 (inr1 e)) (at level 10).

  Notation "⟦ t ⟧" := (model t).

End DenNotations.

Import DenNotations.
