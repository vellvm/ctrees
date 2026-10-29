(*|
=================================
Denotation of [ccs] into [ctree]s
=================================

.. coq:: none
|*)
Unset Universe Checking.

From Stdlib Require Export
     List
     Strings.String.
From Stdlib Require Import RelationClasses Program.

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
From CTree Require Import Head.

From CTree Require Import
     CTree
     Eq
     Eq.SBisim
     Interp.Fold
     Interp.FoldCTree.

Import CTree.

Import CTreeNotations.
Open Scope ctree_scope.

(*|
Event signature
---------------
Processes must at least be able to perform actions.
We do not encode tau steps as events but rather directly as
unary visible br nodes.
|*)

Variant ActionE : Type -> Type :=
  | Act (a : action) : ActionE unit.

Notation ccsE := ActionE.
Notation ccsC := (B2 +' B3 +' B4).

Definition ccsT' T := ctree' ccsE ccsC T.
Definition ccsT := ctree ccsE ccsC.

Definition ccs' := ccsT' void.
Definition ccs  := ccsT void.

Definition comm a : label ccsE void := ask (Act a).

(*| Process algebra |*)
Section Combinators.

  Definition nil : ccs := Stuck.

  Definition prefix (a : action) (P: ccs) : ccs :=
    trigger (Act a);; P.

  Definition plus (P Q : ccs) : ccs := br2 P Q.

  Definition h_new (c : chan) : ActionE ~> ctree ccsE ccsC :=
    fun _ e => let '(Act a) := e in
            match a with
            | Send c'
            | Rcv c' =>
                if (c =? c')%string then Stuck else trigger e
            end.
  #[global] Arguments h_new c [T] _.

  Definition new : chan -> ccs -> ccs :=
    fun c P => interp (h_new c) P.

  Definition para : ccs -> ccs -> ccs :=
    cofix F (P : ccs) (Q : ccs) :=
      br3
        (rP <- head P;;
         match rP with
         | ARet rP => match rP with end
         | AStep t => Step (F t Q)
         | AVis e kP => Vis e (fun i => F (kP i) Q)
         end)

        (rQ <- head Q;;
         match rQ with
         | ARet rQ => match rQ with end
         | AStep t => Step (F P t)
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
                   Stuck
             end
         | _, _ => Stuck
         end).

(*|
We would like to define [bang] directly as in the following.
Unfortunately, it is not syntactically guarded and convincing Rocq
seems challenging.
We therefore instead define a more general function [parabang] expressing
at once the parallel composition of a process [p] with a server of [q].
The usual [bang p] is then defined as [parabang p p].
|*)
  Fail Definition bang : ccs -> ccs :=
    cofix bang (p : ccs ) : ccs := para (bang p) p.

  Definition parabang : ccs -> ccs -> ccs :=
    cofix pB (p : ccs) (q:ccs) : ccs :=
      br4
        (* Communication by p *)
        (rp <- head p;;
         match rp with
         | ARet rp => match rp with end
         | AStep t => Step (pB t q)
         | AVis e kp => Vis e (fun i => pB (kp i) q)
         end)

        (* Communication by a fresh copy of q *)
        (rq <- head q;;
         match rq with
         | ARet rq  => match rq with end
         | AStep t  => Step (pB  (para p t) q)
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
                   Stuck
             end

         | _, _ => Stuck
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
                   Stuck
             end

         | _, _ => Stuck
         end).

  Definition bang (P : ccs) : ccs := parabang P P.

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

Lemma trans_prefix_inv : forall l a p p',
    trans l (prefix a p) p' ->
    p' ⩸ (β (Act a) (fun _ => p)) /\ l = comm a.
Proof.
  intros * tr.
  now apply trans_trigger_inv in tr.
Qed.

Lemma trans_prefix : forall a p,
    trans (comm a) (prefix a p) (β (Act a) (fun _ => p)).
Proof.
  intros; apply trans_trigger'.
Qed.

(* TO MOVE *)
Ltac ssplit := split; [| split].
Ltac eex := do 2 eexists.

(** ** hnew *)
Definition can_comm {X} (c : chan) (a : label ccsE X) : bool :=
  match a with
  | ask (Act a) =>
      match a with
      | Send c'
      | Rcv c' => if (c =? c')%string then false else true
      end
  | _ => true
  end.

Lemma trans_hnew_inv : forall a l c p,
    trans l (h_new c (Act a)) p ->
    l = ask (Act a) /\ can_comm c l /\ p ⩸ (β (Act a) (fun x => Ret x)).
Proof.
  intros * tr.
  cbn in *; destruct a; cbn in *; destruct (c =? c0) eqn:comm; cbn in *.
  all : try now apply trans_stuck_inv in tr.
  all: unfold can_comm; apply trans_vis_inv' in tr as (? & ->); rewrite comm; auto.
Qed.

Lemma new_guard : forall c t, new c (Guard t) ≅ Guard (new c t).
Proof.
  intros; unfold new; now rewrite interp_guard.
Qed.

#[global] Instance new_equ c :
  Proper (equ eq ==> equ eq) (new c).
Proof.
  apply interp_equ.
Qed.

(*| [mapS f s] applies a process operation [f] to a state: either directly to a
running process, or to every continuation of a waiting one. |*)
Definition mapS {E B X Y} (f : ctree E B X -> ctree E B Y) (s : S E B X) : S E B Y :=
  match s with
  | Active t => α f t
  | Passive e k => β e (fun x => f (k x))
  end.

#[global] Instance mapS_Seq {E B X Y} (f : ctree E B X -> ctree E B Y) `{Proper _ (equ eq ==> equ eq) f} :
  Proper (Seq ==> Seq) (mapS f).
Proof.
  intros s s' EQ; destruct EQ; constructor; [| intros]; now apply H.
Qed.

Lemma sbisim_passive_eq {E C X Y} (e : E Y) (k k' : Y -> ctree E C X) :
  (forall y, k y ≃ k' y) -> sbisimeq (β e k) (β e k').
Proof.
  intros H. step. split; intros l s TR; apply trans_passive_inv' in TR as (y & EQ & ->).
  - exists (rcv e y), (α k' y). split; [etrans | split; [| constructor; constructor]].
    rewrite EQ. apply H.
  - exists (rcv e y), (α k y). split; [etrans | split; [| constructor; constructor]].
    rewrite EQ. apply H.
Qed.

Lemma trans_new : forall l c (p : ccs) p',
    trans l p p' ->
    can_comm c l = true ->
    exists q, trans l (new c p) q /\ sbisimeq q (mapS (new c) p').
Proof.
  intros [| ? e | ? e v | []] c p p' TR COMM.
  - refine_trans in TR. exists (α Guard (new c u)). split.
    + now apply trans_tau_interp.
    + apply sbisim_guard.
  - refine_trans in TR. destruct e as [a].
    assert (H : trans (ask (Act a)) (h_new c (Act a)) (β (Act a) (fun x => Ret x))).
    { destruct a as [c' | c']; cbn in *; destruct (c =? c'); try discriminate; apply trans_ask. }
    eexists; split; [eapply trans_ask_interp_ask; [exact TR | exact H] |].
    apply sbisim_passive_eq; intros; rewrite bind_ret_l. apply sbisim_guard.
  - now apply trans_rcv_active_inv in TR.
Qed.

Lemma trans_new_inv : forall l c (p : ccs) p',
    trans l (new c p) p' ->
    exists q, can_comm c l = true /\ trans l p q /\ p' ⩸ (mapS (fun t => Guard (new c t)) q).
Proof.
  intros l c p p' TR.
  enough (G : forall st, trans l st p' -> forall T (p : ccs), st = Active T -> T ≅ new c p ->
    exists q, can_comm c l = true /\ trans l p q /\ p' ⩸ (mapS (fun t => Guard (new c t)) q))
    by (eapply G; [exact TR | reflexivity | reflexivity]).
  clear p TR. intros st TR. hnf in TR; induction TR; intros T p Hs EQ; inv Hs; try discriminate.
  all: try destruct r.
  all: rewrite H in EQ; unfold new in EQ; rewrite (ctree_eta p) in EQ; setoid_rewrite (ctree_eta p); desobs p;
    rewrite ?interp_ret, ?interp_stuck, ?interp_vis, ?interp_guard, ?interp_step, ?interp_br' in EQ;
    try now (step in EQ; inv EQ).
  all: try (destruct e as [[c'|c']]; cbn in EQ; destruct (c =? c'); rewrite ?bind_stuck, ?bind_trigger in EQ;
            now (step in EQ; inv EQ)).
  - destruct (equ_br_invT _ _ _ _ EQ). apply equ_br_invE in EQ as [_ EQ].
    edestruct (IHTR t' (Guard (k0 x)) eq_refl) as (q & COMM & TRq & EQq).
    { unfold new. rewrite interp_guard, H0. apply EQ. }
    exists q; repeat split; auto. eapply trans_br with (y := x). now apply trans_guard_inv in TRq.
  - apply equ_guard_inv in EQ.
    edestruct (IHTR t' t eq_refl EQ) as (q & COMM & TRq & EQq).
    exists q; repeat split; auto.
  - apply equ_step_inv in EQ.
    exists (α t); repeat split; [apply trans_step |]. cbn; constructor. now rewrite H0.
  - destruct e0 as [[c'|c']]; cbn in EQ; destruct (c =? c') eqn:Hc; rewrite ?bind_stuck, ?bind_trigger in EQ;
      try now (step in EQ; inv EQ).
    all: destruct e as [a]; apply equ_vis_invE in EQ as [Ha EQ]; inv Ha.
    all: eexists; split; [cbn; now rewrite Hc | split; [apply trans_ask |]].
    all: constructor; intros; now rewrite EQ.
Qed.

Lemma trans_new_inv' : forall l c (p : ccs) p',
    trans l (new c p) p' ->
    exists q, can_comm c l = true /\ trans l p q /\ sbisimeq p' (mapS (new c) q).
Proof.
  intros * TR. apply trans_new_inv in TR as (q & COMM & TR & EQ).
  exists q; repeat split; auto. rewrite EQ. destruct q; cbn.
  - apply sbisim_guard.
  - apply sbisim_passive_eq; intros; apply sbisim_guard.
Qed.

Lemma trans_plus_inv : forall l p q r,
    trans l (p + q) r ->
    (exists p', trans l p p' /\ r ⩸ p') \/
      (exists q', trans l q q' /\ r ⩸ q').
Proof.
  intros * tr.
  apply trans_br_inv in tr as ([|] & tr); eauto.
Qed.

Lemma trans_plusL : forall l (p : ccs) p' q,
    trans l p p' ->
    trans l (p + q) p'.
Proof.
  intros * tr.
  now apply trans_br21.
Qed.

Lemma trans_plusR : forall l p (q : ccs) q',
    trans l q q' ->
    trans l (p + q) q'.
Proof.
  intros * tr.
  now apply trans_br22.
Qed.

Notation para_ p q :=
  (br3
     (rp <- head p;;
      match rp with
      | ARet rp => match rp with end
      | AStep t => Step (para t q)
      | AVis e kp => Vis e (fun i => para (kp i) q)
      end)

     (rq <- head q;;
      match rq with
      | ARet rq => match rq with end
      | AStep t => Step (para p t)
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
                Stuck
          end
      | _, _ => Stuck
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
  destruct i.
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

Lemma trans_paraSynch : forall a b (p q : ccs) kp kq,
    trans (comm a) p (β (Act a) kp) ->
    trans (comm b) q (β (Act b) kq) ->
    are_opposite a b ->
    trans τ (p ∥ q) (kp tt ∥ kq tt).
Proof.
  intros * TRp TRq Op.
  eapply (trans_head_ask (F := ccsE) (C := ccsC)) in TRp as (kp' & TRp & EQp); dependent destruction EQp.
  eapply (trans_head_ask (F := ccsE) (C := ccsC)) in TRq as (kq' & TRq & EQq); dependent destruction EQq.
  rewrite unfold_para.
  apply trans_br33.
  eapply trans_bind_r; [apply TRp |].
  eapply trans_bind_r; [apply TRq |].
  cbn; rewrite Op, EQ, EQ0.
  apply trans_step.
Qed.

Lemma trans_paraL :
  forall l (p q : ccs) p',
    trans l p p' ->
    trans l (p ∥ q) (mapS (fun p => p ∥ q) p').
Proof.
  intros * TRp.
  eapply (trans_head (F := ccsE) (C := ccsC)) in TRp.
  rewrite unfold_para. apply trans_br31.
  destruct l as [| ? e | | []]; [| | easy].
  - destruct TRp as (u & TRp & EQ); inv EQ.
    eapply trans_bind_r; [apply TRp |]. cbn. rewrite EQ0. apply trans_step.
  - destruct TRp as (k & TRp & EQ); dependent destruction EQ.
    eapply trans_bind_r; [apply TRp |]. cbn. setoid_rewrite EQ. apply trans_ask.
Qed.

Lemma trans_paraR :
  forall l (p q : ccs) q',
    trans l q q' ->
    trans l (p ∥ q) (mapS (fun q => p ∥ q) q').
Proof.
  intros * TRq.
  eapply (trans_head (F := ccsE) (C := ccsC)) in TRq.
  rewrite unfold_para. apply trans_br32.
  destruct l as [| ? e | | []]; [| | easy].
  - destruct TRq as (u & TRq & EQ); inv EQ.
    eapply trans_bind_r; [apply TRq |]. cbn. rewrite EQ0. apply trans_step.
  - destruct TRq as (k & TRq & EQ); dependent destruction EQ.
    eapply trans_bind_r; [apply TRq |]. cbn. setoid_rewrite EQ. apply trans_ask.
Qed.

Ltac head_bind_inv TR hd TRhd :=
  let h := fresh "TRh" in
  apply trans_bind_inv in TR as [(_ & ? & h & _) | [(? & ? & _ & ? & h & _) | (hd & TRhd & TR)]];
  [ apply trans_head_inv in h; inv h | apply trans_head_inv in h; inv h | ].

Lemma trans_para_inv :
  forall l (p q : ccs) r,
    trans l (p ∥ q) r ->
    (exists p', trans l p p' /\ r ⩸ (mapS (fun p => p ∥ q) p')) \/
      (exists q', trans l q q' /\ r ⩸ (mapS (fun q => p ∥ q) q')) \/
      (exists a b kp kq,
          trans (comm a) p (β (Act a) kp) /\
            trans (comm b) q (β (Act b) kq) /\
            are_opposite a b /\
            l = τ /\
            r ⩸ (α (kp tt ∥ kq tt))).
Proof.
  intros * TR.
  rewrite unfold_para in TR.
  apply trans_br_inv in TR as (x & TR).
  destruct x.
  - left. head_bind_inv TR hdp TRhdp.
    destruct hdp as [[] | t | ? e kp].
    + apply trans_step_inv' in TR as (EQ & ->). apply trans_ABr in TRhdp. eauto.
    + apply trans_vis_inv' in TR as (EQ & ->). apply trans_AVis in TRhdp. eauto.
  - right; left. head_bind_inv TR hdq TRhdq.
    destruct hdq as [[] | t | ? e kq].
    + apply trans_step_inv' in TR as (EQ & ->). apply trans_ABr in TRhdq. eauto.
    + apply trans_vis_inv' in TR as (EQ & ->). apply trans_AVis in TRhdq. eauto.
  - right; right. head_bind_inv TR hdp TRhdp. head_bind_inv TR hdq TRhdq.
    destruct hdp as [[] | t | ? [a] kp]; try now apply trans_stuck_inv in TR.
    destruct hdq as [[] | t | ? [b] kq]; try now apply trans_stuck_inv in TR.
    cbn in TR; destruct (are_opposite a b) eqn:Op; [| now apply trans_stuck_inv in TR].
    apply trans_step_inv' in TR as (EQ & ->).
    apply trans_AVis in TRhdp, TRhdq.
    do 4 eexists; repeat split; eauto.
Qed.

Ltac trans_para_invT H :=
  apply trans_para_inv in H as
      [(?p' & ?TRp & ?EQ) |
        [(?q' & ?TRq & ?EQ) |
          (?a & ?b & ?kp & ?kq & ?TRp & ?TRq & ?Op & ? & ?EQ) ]]; subst.

Notation parabang_ p q :=
  (br4

     (* Communication by p *)
     (rp <- head p;;
      match rp with
      | ARet rp => match rp with end
      | AStep t => Step (parabang t q)
      | AVis e kp => Vis e (fun i => parabang (kp i) q)
      end)

     (* Communication by a fresh copy of q *)
     (rq <- head q;;
      match rq with
      | ARet rq => match rq with end
      | AStep t => Step (parabang (para p t) q)
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
                Stuck
          end

      | _, _ => Stuck
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
                Stuck
          end

      | _, _ => Stuck
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

  destruct i.
  - upto_bind; [apply head_equ; auto | intros hdp1 hdp2 eqp].
    inv eqp; auto.
    step; constructor; auto.
    step; constructor; auto.
  - upto_bind; [apply head_equ; auto | intros hdp1 hdp2 eqp].
    inv eqp; auto.
    step; constructor.
    apply CIH; auto; rewrite EQp, H; reflexivity.
    step; constructor; intros ?.
    apply CIH; auto; rewrite EQp, H; reflexivity.
  - upto_bind; [apply head_equ; auto | intros hdp1 hdp2 eqp].
    upto_bind; [apply head_equ; auto | intros hdq1 hdq2 eqq].
    inv eqp; auto.
    inv eqq; auto.
    destruct e, e0, (are_opposite a a0); auto.
    step; constructor.
    apply CIH; auto.
    rewrite H,H0; reflexivity.
  - upto_bind; [apply head_equ; auto | intros hdp1 hdp2 eqp].
    upto_bind; [apply head_equ; auto | intros hdq1 hdq2 eqq].
    inv eqp; auto.
    inv eqq; auto.
    destruct e, e0, (are_opposite a a0); auto.
    step; constructor.
    apply CIH; auto.
    rewrite EQp, H,H0; reflexivity.
Qed.

Lemma trans_parabangL : forall l (p q : ccs) p',
    trans l p p' ->
    trans l (parabang p q) (mapS (fun p => parabang p q) p').
Proof.
  intros * TRp.
  eapply (trans_head (F := ccsE) (C := ccsC)) in TRp.
  rewrite unfold_parabang. apply trans_br41.
  destruct l as [| ? e | | []]; [| | easy].
  - destruct TRp as (u & TRp & EQ); inv EQ.
    eapply trans_bind_r; [apply TRp |]. cbn. rewrite EQ0. apply trans_step.
  - destruct TRp as (k & TRp & EQ); dependent destruction EQ.
    eapply trans_bind_r; [apply TRp |]. cbn. setoid_rewrite EQ. apply trans_ask.
Qed.

Lemma trans_parabangR : forall l (p q : ccs) q',
    trans l q q' ->
    trans l (parabang p q) (mapS (fun q' => parabang (p ∥ q') q) q').
Proof.
  intros * TRq.
  eapply (trans_head (F := ccsE) (C := ccsC)) in TRq.
  rewrite unfold_parabang. apply trans_br42.
  destruct l as [| ? e | | []]; [| | easy].
  - destruct TRq as (u & TRq & EQ); inv EQ.
    eapply trans_bind_r; [apply TRq |]. cbn. rewrite EQ0. apply trans_step.
  - destruct TRq as (k & TRq & EQ); dependent destruction EQ.
    eapply trans_bind_r; [apply TRq |]. cbn. setoid_rewrite EQ. apply trans_ask.
Qed.

Lemma trans_parabangSL : forall a b (p q : ccs) kp kq,
    are_opposite a b ->
    trans (comm a) p (β (Act a) kp) ->
    trans (comm b) q (β (Act b) kq) ->
    trans τ (parabang p q) (parabang (kp tt ∥ kq tt) q).
Proof.
  intros * Op TR1 TR2.
  eapply (trans_head_ask (F := ccsE) (C := ccsC)) in TR1 as (k1 & TR1 & EQ1); dependent destruction EQ1.
  eapply (trans_head_ask (F := ccsE) (C := ccsC)) in TR2 as (k2 & TR2 & EQ2); dependent destruction EQ2.
  rewrite unfold_parabang.
  apply trans_br43.
  eapply trans_bind_r; [apply TR1 |].
  eapply trans_bind_r; [apply TR2 |].
  cbn; rewrite Op, EQ, EQ0.
  apply trans_step.
Qed.

Lemma trans_parabangSR : forall a b (p q : ccs) kq1 kq2,
    are_opposite a b ->
    trans (comm a) q (β (Act a) kq1) ->
    trans (comm b) q (β (Act b) kq2) ->
    trans τ (parabang p q) (parabang (p ∥ (kq1 tt ∥ kq2 tt)) q).
Proof.
  intros * Op TR1 TR2.
  eapply (trans_head_ask (F := ccsE) (C := ccsC)) in TR1 as (k1 & TR1 & EQ1); dependent destruction EQ1.
  eapply (trans_head_ask (F := ccsE) (C := ccsC)) in TR2 as (k2 & TR2 & EQ2); dependent destruction EQ2.
  rewrite unfold_parabang.
  apply trans_br44.
  eapply trans_bind_r; [apply TR1 |].
  eapply trans_bind_r; [apply TR2 |].
  cbn; rewrite Op, EQ, EQ0.
  apply trans_step.
Qed.

Lemma trans_parabang_inv : forall l (p q : ccs) r,
    trans l (parabang p q) r ->
    (exists p', trans l p p' /\ r ⩸ (mapS (fun p => parabang p q) p')) \/
      (exists q', trans l q q' /\ r ⩸ (mapS (fun q' => parabang (p ∥ q') q) q')) \/
      (exists a b kp kq, trans (comm a) p (β (Act a) kp) /\
                      trans (comm b) q (β (Act b) kq) /\
                      are_opposite a b /\
                      l = τ /\
                      r ⩸ (α parabang (kp tt ∥ kq tt) q)) \/
      (exists a b kq1 kq2, trans (comm a) q (β (Act a) kq1) /\
                       trans (comm b) q (β (Act b) kq2) /\
                       are_opposite a b /\
                       l = τ /\
                       r ⩸ (α parabang (p ∥ (kq1 tt ∥ kq2 tt)) q)).
Proof.
  intros * TR.
  rewrite unfold_parabang in TR.
  apply trans_br_inv in TR as [[] TR].
  - left. head_bind_inv TR hdp TRhdp.
    destruct hdp as [[] | t | ? e kp].
    + apply trans_step_inv' in TR as (EQ & ->). apply trans_ABr in TRhdp. eauto.
    + apply trans_vis_inv' in TR as (EQ & ->). apply trans_AVis in TRhdp. eauto.
  - right; left. head_bind_inv TR hdq TRhdq.
    destruct hdq as [[] | t | ? e kq].
    + apply trans_step_inv' in TR as (EQ & ->). apply trans_ABr in TRhdq. eauto.
    + apply trans_vis_inv' in TR as (EQ & ->). apply trans_AVis in TRhdq. eauto.
  - right; right; left. head_bind_inv TR hdp TRhdp. head_bind_inv TR hdq TRhdq.
    destruct hdp as [[] | t | ? [a] kp]; try now apply trans_stuck_inv in TR.
    destruct hdq as [[] | t | ? [b] kq]; try now apply trans_stuck_inv in TR.
    cbn in TR; destruct (are_opposite a b) eqn:Op; [| now apply trans_stuck_inv in TR].
    apply trans_step_inv' in TR as (EQ & ->).
    apply trans_AVis in TRhdp, TRhdq.
    exists a, b, kp, kq; repeat split; auto.
  - right; right; right. head_bind_inv TR hd1 TRhd1. head_bind_inv TR hd2 TRhd2.
    destruct hd1 as [[] | t | ? [a] k1]; try now apply trans_stuck_inv in TR.
    destruct hd2 as [[] | t | ? [b] k2]; try now apply trans_stuck_inv in TR.
    cbn in TR; destruct (are_opposite a b) eqn:Op; [| now apply trans_stuck_inv in TR].
    apply trans_step_inv' in TR as (EQ & ->).
    apply trans_AVis in TRhd1, TRhd2.
    exists a, b, k1, k2; repeat split; auto.
Qed.

Ltac trans_parabang_invT TR :=
  apply trans_parabang_inv in TR as
      [(?p' & ?TRp' & ?EQ) |
        [(?q' & ?TRq' & ?EQ) |
          [(?a & ?b & ?kp & ?kq & ?TRp' & ?TRq' & ?Op & ?EQl & ?EQ) |
            (?a & ?b & ?kq1 & ?kq2 & ?TRq' & ?TRq'' & ?Op & ?EQl & ?EQ)]]]; subst.

Ltac pbL := apply trans_parabangL.
Ltac pbR := apply trans_parabangR.
Ltac pbSL := eapply trans_parabangSL.
Ltac pbSR := eapply trans_parabangSR.

Ltac pL := apply trans_paraL.
Ltac pR := apply trans_paraR.
Ltac pS := eapply trans_paraSynch.

Ltac inv_ccs_trans :=
  match goal with
  | h : hrel_of (trans _) (Active (prefix _ _)) _ |- _ => apply trans_prefix_inv in h as (?EQ & ->)
  | h : hrel_of (trans _) (Active (new _ _)) _ |- _ => apply trans_new_inv in h as (?q & ?EQ & ?tr & ?EQ')
  | h : hrel_of (trans _) (Active (plus _ _)) _ |- _ => apply trans_plus_inv in h as [(?q & ?tr & ?EQ) | (?q & ?tr & ?EQ)]
  | h : hrel_of (trans _) (Active (para _ _)) _ |- _ => trans_para_invT h
  | h : hrel_of (trans _) (Active (parabang _ _)) _ |- _ => trans_parabang_invT h
  | h : hrel_of (trans _) (Active (bang _)) _ |- _ => trans_parabang_invT h
  | _ => idtac
  end.
Hint Resolve trans_prefix trans_new trans_plusL trans_plusR trans_paraSynch trans_paraL trans_paraR
             trans_parabangL trans_parabangR trans_parabangSL trans_parabangSR
  : ccs.
Ltac ccs_trans := eauto with ccs.

(** ** prefix  *)
#[global] Instance prefix_st a: forall (R : Chain (sb Leq)),
    Proper ((fun p q : ccs => elem R p q) ==> (fun p q : ccs => elem R p q)) (prefix a).
Proof.
  intros R p q H.
  apply (b_chain R); split; intros l s TR; apply trans_prefix_inv in TR as (EQ & ->);
    (eexists; eexists; split; [apply trans_prefix | split; [| constructor; constructor]]);
    rewrite EQ; apply (b_chain R); split; intros l' s' TR';
    apply trans_passive_inv' in TR' as ([] & EQ' & ->);
    (eexists; eexists; split; [etrans | split; [rewrite EQ'; auto | constructor; constructor]]).
Qed.

(** ** name restriction *)
Lemma sbisim_mapS_guard {E C X} (f : ctree E C X -> ctree E C X) s :
  sbisimeq (mapS (fun t => Guard (f t)) s) (mapS f s).
Proof.
  destruct s; cbn; [apply sbisim_guard | apply sbisim_passive_eq; intros; apply sbisim_guard].
Qed.

Lemma new_chain c : forall (R : Chain (@sb ccsE ccsE ccsC ccsC void void Leq)),
  (forall p q : ccs, elem R p q -> elem R (new c p) (new c q)) /\
  (forall X (e : ccsE X) (k k' : X -> ccs), elem R (β e k) (β e k') ->
     elem R (β e (fun x => new c (k x))) (β e (fun x => new c (k' x)))).
Proof.
  intros R; pattern (elem R); revert R; apply tower.
  - intros T HT; split; intros * H R TR; destruct (HT R TR) as [HT1 HT2]; [apply HT1 | apply HT2]; apply H, TR.
  - intros R [IH1 IH2]; split.
    + intros p q [F B]; split; intros l s TR.
      * apply trans_new_inv in TR as (q0 & COMM & TR0 & EQ).
        apply F in TR0 as TR1; destruct TR1 as (l' & q1 & TR1 & HR & HL).
        apply Leq_eq in HL; subst l'.
        destruct (trans_new _ _ _ _ TR1 COMM) as (q2 & TR2 & EQ2).
        exists l, q2; split; [exact TR2 | split; [| reflexivity]].
        rewrite EQ, EQ2, sbisim_mapS_guard.
        destruct l as [| ? e | | []].
        -- refine_trans in TR0. refine_trans in TR1. cbn. now apply IH1.
        -- refine_trans in TR0. refine_trans in TR1. cbn. now apply IH2.
        -- now apply trans_rcv_active_inv in TR0.
      * apply trans_new_inv in TR as (q0 & COMM & TR0 & EQ).
        apply B in TR0 as TR1; destruct TR1 as (l' & q1 & TR1 & HR & HL).
        rewrite flipL_Leq in HL; apply Leq_eq in HL; subst l'.
        destruct (trans_new _ _ _ _ TR1 COMM) as (q2 & TR2 & EQ2).
        exists l, q2; split; [exact TR2 | split; [| rewrite flipL_Leq; reflexivity]].
        unfold flip in *. rewrite EQ, EQ2, sbisim_mapS_guard.
        destruct l as [| ? e | | []].
        -- refine_trans in TR0. refine_trans in TR1. cbn. now apply IH1.
        -- refine_trans in TR0. refine_trans in TR1. cbn. now apply IH2.
        -- now apply trans_rcv_active_inv in TR0.
    + intros X e k k' [F B]; split; intros l s TR.
      * apply trans_passive_inv' in TR as (x & EQ & ->).
        destruct (F _ _ (trans_rcv e k x)) as (l' & s' & TR' & HR & HL).
        apply Leq_eq in HL; subst l'.
        apply trans_passive_inv' in TR' as (y & EQ' & EQl). dependent destruction EQl.
        eexists _, _; split; [apply trans_rcv | split; [| reflexivity]].
        rewrite EQ. apply IH1. now rewrite <- EQ'.
      * apply trans_passive_inv' in TR as (x & EQ & ->).
        destruct (B _ _ (trans_rcv e k' x)) as (l' & s' & TR' & HR & HL).
        rewrite flipL_Leq in HL; apply Leq_eq in HL; subst l'.
        apply trans_passive_inv' in TR' as (y & EQ' & EQl). dependent destruction EQl.
        eexists _, _; split; [apply trans_rcv | split; [| rewrite flipL_Leq; reflexivity]].
        unfold flip in *. rewrite EQ. apply IH1. now rewrite <- EQ'.
Qed.

#[global] Instance ctx_new_st c: forall (R : Chain (sb Leq)),
    Proper ((fun p q : ccs => elem R p q) ==> (fun p q : ccs => elem R p q)) (new c).
Proof.
  intros R p q H. now apply new_chain.
Qed.

(** ** plus  *)
#[global] Instance ctx_plus_t : forall (R : Chain (sb Leq)),
  Proper ((fun p q : ccs => elem R p q) ==> (fun p q : ccs => elem R p q) ==> (fun p q : ccs => elem R p q)) plus.
Proof.
  intros R; cbn; pattern (elem R); revert R; apply tower.
  - intros T HT p q Hpq r s Hrs R TR. apply (HT R TR); [apply Hpq | apply Hrs]; exact TR.
  - intros R IH p q [Fp Bp] r s [Fr Br]; split; intros l t TR.
    + apply trans_plus_inv in TR as [(t0 & TR & EQ) | (t0 & TR & EQ)].
      * apply Fp in TR as (l' & t' & TR & HR & HL). exists l', t'; rewrite EQ; split; [now apply trans_plusL | auto].
      * apply Fr in TR as (l' & t' & TR & HR & HL). exists l', t'; rewrite EQ; split; [now apply trans_plusR | auto].
    + apply trans_plus_inv in TR as [(t0 & TR & EQ) | (t0 & TR & EQ)].
      * apply Bp in TR as (l' & t' & TR & HR & HL). exists l', t'. unfold flip in *; rewrite EQ; split; [now apply trans_plusL | auto].
      * apply Br in TR as (l' & t' & TR & HR & HL). exists l', t'. unfold flip in *; rewrite EQ; split; [now apply trans_plusR | auto].
Qed.

(** ** parallel composition *)

(*| We observe that the chain-level context lemma for [∥] fails for [sb] in the
new state-based system. Therefore we define [sbm] to sort this out: a normal
synchronization uses up a question and its answer from each side in one [τ]
step, while [sb] counts them as two steps, so [sbm] below plays a question
together with all its answers as one move; its bisimilarity coincides with [≃]
([sbm_sbisim], [sbisim_sbm]) and [∥] is compatible with its chain
([ctx_para_m]). |*)
Section AnswerGame.
  Context {E C : Type -> Type} {X : Type}.

  Definition ssm (R : rel (ctree E C X) (ctree E C X)) (t u : ctree E C X) : Prop :=
    (forall s, trans τ t s -> exists t' (u' : ctree E C X), s ⩸ (α t') /\ trans τ u u' /\ R t' u') /\
    (forall v s, trans (val v) t s -> trans (val v) u Stuck) /\
    (forall Y (e : E Y) s, trans (ask e) t s ->
       exists k k', s ⩸ (β e k) /\ trans (ask e) u (β e k') /\ forall y, R (k y) (k' y)).

  Lemma ssm_mon (R R' : rel (ctree E C X) (ctree E C X)) t u :
    (forall a b, R a b -> R' a b) -> ssm R t u -> ssm R' t u.
  Proof.
    intros LE [A1 [A2 A3]]; repeat split; auto.
    - intros s TR; destruct (A1 _ TR) as (t' & u' & ? & ? & ?); exists t', u'; auto.
    - intros * TR; destruct (A3 _ _ _ TR) as (k & k' & ? & ? & ?); exists k, k'; auto.
  Qed.

  Program Definition sbm : mon (rel (ctree E C X) (ctree E C X)) :=
    {| body R t u := ssm R t u /\ ssm (flip R) u t |}.
  Next Obligation.
    split; eapply ssm_mon; try eassumption; unfold flip; auto.
  Qed.

  Definition sbmbisim := gfp sbm.

End AnswerGame.

Lemma chain_passive {E C X Y} {R : Chain (@sb E E C C X X Leq)} (e : E Y) (k k' : Y -> ctree E C X) :
  (forall y, elem R (k y) (k' y)) -> elem R (β e k) (β e k').
Proof.
  intros H. apply (b_chain R). split; intros l s TR; apply trans_passive_inv' in TR as (y & EQ & ->);
    (eexists _, _; split; [apply trans_rcv | split]).
  - rewrite EQ; apply H.
  - reflexivity.
  - unfold flip; rewrite EQ; apply H.
  - rewrite flipL_Leq; reflexivity.
Qed.

Lemma sbm_sbisim {E C X} : forall (t u : ctree E C X), sbmbisim t u -> t ≃ u.
Proof.
  unfold sbisimT. coinduction R CIH. intros t u H. step in H.
  destruct H as [[A1 [A2 A3]] [B1 [B2 B3]]].
  split; intros l s TR.
  - destruct l as [| ? e | ? e y | v].
    + destruct (A1 _ TR) as (t' & u' & EQ & TR' & HR).
      exists τ, (α u'); split; [exact TR' | split; [rewrite EQ; now apply CIH | reflexivity]].
    + destruct (A3 _ _ _ TR) as (k & k' & EQ & TR' & HR).
      exists (ask e), (β e k'); split; [exact TR' | split; [rewrite EQ; apply chain_passive; intros; apply CIH, HR | reflexivity]].
    + now apply trans_rcv_active_inv in TR.
    + pose proof (A2 _ _ TR) as TR'. exists (val v), (α Stuck); split; [exact TR' | split; [| reflexivity]].
      apply trans_val_inv' in TR; rewrite TR. apply Chain_Stuck.
  - destruct l as [| ? e | ? e y | v].
    + destruct (B1 _ TR) as (t' & u' & EQ & TR' & HR).
      exists τ, (α u'); split; [exact TR' | split; [unfold flip; rewrite EQ; apply CIH, HR | rewrite flipL_Leq; reflexivity]].
    + destruct (B3 _ _ _ TR) as (k & k' & EQ & TR' & HR).
      exists (ask e), (β e k'); split; [exact TR' | split; [unfold flip; rewrite EQ; apply chain_passive; intros; apply CIH, HR | rewrite flipL_Leq; reflexivity]].
    + now apply trans_rcv_active_inv in TR.
    + pose proof (B2 _ _ TR) as TR'. exists (val v), (α Stuck); split; [exact TR' | split; [| rewrite flipL_Leq; reflexivity]].
      apply trans_val_inv' in TR; unfold flip; rewrite TR. apply Chain_Stuck.
Qed.

Lemma sbisim_sbm_passive {E C X Y} (e : E Y) (k k' : Y -> ctree E C X) :
  sbisimeq (β e k) (β e k') -> forall y, k y ≃ k' y.
Proof.
  intros HR y. step in HR. destruct HR as [F _].
  destruct (F _ _ (trans_rcv e k y)) as (l' & s' & TR & HR' & HL).
  apply Leq_eq in HL; subst l'. apply trans_passive_inv' in TR as (y' & EQ & EQl). dependent destruction EQl.
  unfold sbisimT. now rewrite EQ in HR'.
Qed.

Lemma ssm_sbisim {E C X} (R : rel (ctree E C X) (ctree E C X)) (t u : ctree E C X) :
  (forall t' u', t' ≃ u' -> R t' u') -> ss Leq sbisimeq (α t) (α u) -> ssm R t u.
Proof.
  intros CIH F; repeat split.
  - intros s TR. destruct (trans_τ_inv TR) as (t' & EQ). rewrite EQ in TR.
    apply F in TR as (l' & s' & TR' & HR & HL). apply Leq_eq in HL; subst l'.
    destruct (trans_τ_inv TR') as (u' & EQ'). rewrite EQ' in TR', HR.
    exists t', u'; repeat split; auto.
  - intros v s TR. apply F in TR as (l' & s' & TR' & HR & HL). apply Leq_eq in HL; subst l'.
    now rewrite <- (trans_val_inv' TR').
  - intros Y e s TR. destruct (trans_ask_inv TR) as (k & EQ). rewrite EQ in TR.
    apply F in TR as (l' & s' & TR' & HR & HL). apply Leq_eq in HL; subst l'.
    destruct (trans_ask_inv TR') as (k' & EQ'). rewrite EQ' in TR', HR.
    exists k, k'; repeat split; auto. intros y; apply CIH.
    exact (sbisim_sbm_passive e k k' HR y).
Qed.

Lemma sbisim_sbm {E C X} : forall (t u : ctree E C X), t ≃ u -> sbmbisim t u.
Proof.
  unfold sbmbisim. coinduction R CIH. intros t u H.
  step in H. destruct H as [F B]. split.
  - apply ssm_sbisim; auto.
  - apply ssm_sbisim.
    + intros; apply CIH; now symmetry.
    + rewrite flipL_Leq in B. revert B. apply (Hbody (ss Leq)). intros ? ? H; now symmetry.
Qed.

#[global] Instance para_equ_l (q : ccs) : Proper (equ eq ==> equ eq) (fun p : ccs => p ∥ q).
Proof. intros ? ? H; now rewrite H. Qed.

#[global] Instance para_equ_r (p : ccs) : Proper (equ eq ==> equ eq) (fun q : ccs => p ∥ q).
Proof. intros ? ? H; now rewrite H. Qed.

Lemma para_ssm (R : rel ccs ccs) :
  (forall p q r s, R p q -> R r s -> R (p ∥ r) (q ∥ s)) ->
  forall p q r s, ssm R p q -> ssm R r s -> R p q -> R r s -> ssm R (p ∥ r) (q ∥ s).
Proof.
  intros CTX p q r s [Ap1 [_ Ap3]] [Ar1 [_ Ar3]] Hpq Hrs; repeat split.
  - intros s0 TR. unfold comm in *. trans_para_invT TR.
    + destruct (Ap1 _ TRp) as (t' & u' & EQ' & TR' & HR).
      exists (t' ∥ r), (u' ∥ s); repeat split.
      * rewrite EQ, EQ'; reflexivity.
      * apply (trans_paraL _ _ s) in TR'; exact TR'.
      * now apply CTX.
    + destruct (Ar1 _ TRq) as (t' & u' & EQ' & TR' & HR).
      exists (p ∥ t'), (q ∥ u'); repeat split.
      * rewrite EQ, EQ'; reflexivity.
      * apply (trans_paraR _ q) in TR'; exact TR'.
      * now apply CTX.
    + destruct (Ap3 _ _ _ TRp) as (k1 & k1' & EQ1 & TR1 & HR1).
      destruct (Ar3 _ _ _ TRq) as (k2 & k2' & EQ2 & TR2 & HR2).
      dependent destruction EQ1. dependent destruction EQ2.
      exists (k1 tt ∥ k2 tt), (k1' tt ∥ k2' tt); repeat split.
      * rewrite EQ, EQ0, EQ1; reflexivity.
      * eapply trans_paraSynch; [exact TR1 | exact TR2 | exact Op].
      * now apply CTX.
  - intros [].
  - intros Y e s0 TR. trans_para_invT TR.
    + destruct (Ap3 _ _ _ TRp) as (k & k' & EQ' & TR' & HR).
      exists (fun y => k y ∥ r), (fun y => k' y ∥ s); repeat split.
      * rewrite EQ, EQ'; reflexivity.
      * apply (trans_paraL _ _ s) in TR'; exact TR'.
      * intros; now apply CTX.
    + destruct (Ar3 _ _ _ TRq) as (k & k' & EQ' & TR' & HR).
      exists (fun y => p ∥ k y), (fun y => q ∥ k' y); repeat split.
      * rewrite EQ, EQ'; reflexivity.
      * apply (trans_paraR _ q) in TR'; exact TR'.
      * intros; now apply CTX.
    + discriminate.
Qed.

Lemma ctx_para_m : forall (R : Chain (@sbm ccsE ccsC void)) (p q r s : ccs),
    elem R p q -> elem R r s -> elem R (p ∥ r) (q ∥ s).
Proof.
  intros R. pattern (elem R). revert R. apply tower.
  - intros T HT p q r s Hpq Hrs R' TR. apply (HT R' TR); [apply Hpq | apply Hrs]; exact TR.
  - intros R IH p q r s Hpq Hrs.
    pose proof (b_chain R _ _ Hpq) as Hpq'. pose proof (b_chain R _ _ Hrs) as Hrs'.
    destruct Hpq as [Fp Bp], Hrs as [Fr Br]. split.
    + apply para_ssm; auto.
    + apply para_ssm; auto. intros; apply IH; auto.
Qed.

#[global] Instance para_sbisim : Proper (sbisimT Leq ==> sbisimT Leq ==> sbisimT Leq) para.
Proof.
  intros p q Hpq r s Hrs. apply sbm_sbisim.
  apply sbisim_sbm in Hpq, Hrs. unfold sbmbisim in *.
  now apply (gfp_prop (fun x => forall p q r s : ccs, x p q -> x r s -> x (p ∥ r) (q ∥ s)) ctx_para_m).
Qed.

Section Theory.

  Lemma plsC: forall (p q : ccs), p+q ≃ q+p.
  Proof.
    apply br2_commut.
  Qed.

  Lemma plsA (p q r : ccs): p+(q+r) ≃ (p+q)+r.
  Proof.
    symmetry; apply br2_assoc.
  Qed.

  Lemma pls0p (p : ccs) : 0 + p ≃ p.
  Proof.
    apply br2_stuck_l.
  Qed.

  Lemma plsp0 (p : ccs) : p + 0 ≃ p.
  Proof. now rewrite plsC, pls0p. Qed.

  Lemma plsidem (p : ccs) : p + p ≃ p.
  Proof.
    apply br2_idem.
  Qed.

  #[global] Instance are_opposite_sym : Symmetric are_opposite.
  Proof.
    unfold are_opposite, eqb_action, op; cbn.
    intros [] [] Op; intuition.
    all:rewrite eqb_sym; auto.
  Qed.

  Lemma paraC: forall (p q : ccs), p ∥ q ≃ q ∥ p.
  Proof.
    unfold sbisimT. coinduction r CIH; symmetric.
    intros p q l s TR.
    trans_para_invT TR.
    - eexists _, _; split; [apply trans_paraR; eauto | split; [| reflexivity]].
      rewrite EQ; destruct p' as [p' | ? e k]; cbn; [apply CIH | apply chain_passive; intros; apply CIH].
    - eexists _, _; split; [apply trans_paraL; eauto | split; [| reflexivity]].
      rewrite EQ; destruct q' as [q' | ? e k]; cbn; [apply CIH | apply chain_passive; intros; apply CIH].
    - eexists _, _; split; [eapply trans_paraSynch; eauto; now symmetry | split; [| reflexivity]].
      rewrite EQ; apply CIH.
  Qed.

  Lemma para0p : forall (p : ccs), 0 ∥ p ≃ p.
  Proof.
    unfold sbisimT. coinduction R CIH. intros p. split.
    - intros l s TR. trans_para_invT TR; try now apply trans_stuck_inv in TRp.
      exists l, q'; split; [auto | split; [| reflexivity]].
      rewrite EQ; destruct q'; cbn; [apply CIH | apply chain_passive; intros; apply CIH].
    - intros l s TR. exists l, (mapS (fun q => 0 ∥ q) s).
      split; [now apply trans_paraR | split; [| rewrite flipL_Leq; reflexivity]].
      unfold flip; destruct s; cbn; [apply CIH | apply chain_passive; intros; apply CIH].
  Qed.

  Lemma parap0 : forall (p : ccs), p ∥ 0 ≃ p.
  Proof.
    intros; rewrite paraC; apply para0p.
  Qed.

  Lemma paraA : forall (p q r : ccs), p ∥ (q ∥ r) ≃ (p ∥ q) ∥ r.
  Proof.
    unfold sbisimT. coinduction R CIH; intros; split.
    - intros l s TR. unfold comm in *.
      trans_para_invT TR.
      + eexists _, _; split; [apply trans_paraL, trans_paraL, TRp | split; [| reflexivity]].
        rewrite EQ; destruct p'; cbn; [apply CIH | apply chain_passive; intros; apply CIH].
      + trans_para_invT TRq.
        * eexists _, _; split; [apply trans_paraL, trans_paraR, TRp | split; [| reflexivity]].
          rewrite EQ, EQ0; destruct p'; cbn; [apply CIH | apply chain_passive; intros; apply CIH].
        * eexists _, _; split; [apply trans_paraR, TRq | split; [| reflexivity]].
          rewrite EQ, EQ0; destruct q'0; cbn; [apply CIH | apply chain_passive; intros; apply CIH].
        * assert (TRpq : trans (comm a) (p ∥ q) (β (Act a) (fun i => p ∥ kp i)))
            by (apply (trans_paraR _ p) in TRp; exact TRp).
          eexists _, _; split; [eapply trans_paraSynch; [exact TRpq | exact TRq | exact Op] | split; [| reflexivity]].
          rewrite EQ, EQ0; cbn; apply CIH.
      + unfold comm in TRq. trans_para_invT TRq.
        * rename EQ into EQs. refine_trans in TRp0. dependent destruction EQ0.
          eexists _, _; split; [apply trans_paraL; eapply trans_paraSynch; [exact TRp | exact TRp0 | exact Op] | split; [| reflexivity]].
          rewrite EQs; cbn. rewrite (EQ tt). apply CIH.
        * rename EQ into EQs. refine_trans in TRq. dependent destruction EQ0.
          assert (TRpq : trans (comm a) (p ∥ q) (β (Act a) (fun i => kp i ∥ q)))
            by (apply (trans_paraL _ _ q) in TRp; exact TRp).
          eexists _, _; split; [eapply trans_paraSynch; [exact TRpq | exact TRq | exact Op] | split; [| reflexivity]].
          rewrite EQs; cbn. rewrite (EQ tt). apply CIH.
        * discriminate.
    - intros l s TR. unfold comm in *. unfold flip.
      trans_para_invT TR.
      + trans_para_invT TRp.
        * eexists _, _; split; [apply trans_paraL, TRp | split; [| rewrite flipL_Leq; reflexivity]].
          rewrite EQ, EQ0; destruct p'0; cbn; [apply CIH | apply chain_passive; intros; apply CIH].
        * eexists _, _; split; [apply trans_paraR, trans_paraL, TRq | split; [| rewrite flipL_Leq; reflexivity]].
          rewrite EQ, EQ0; destruct q'; cbn; [apply CIH | apply chain_passive; intros; apply CIH].
        * assert (TRqr : trans (comm b) (q ∥ r) (β (Act b) (fun i => kq i ∥ r)))
            by (apply (trans_paraL _ _ r) in TRq; exact TRq).
          eexists _, _; split; [eapply trans_paraSynch; [exact TRp | exact TRqr | exact Op] | split; [| rewrite flipL_Leq; reflexivity]].
          rewrite EQ, EQ0; cbn; apply CIH.
      + eexists _, _; split; [apply trans_paraR, trans_paraR, TRq | split; [| rewrite flipL_Leq; reflexivity]].
        rewrite EQ; destruct q'; cbn; [apply CIH | apply chain_passive; intros; apply CIH].
      + unfold comm in TRp. rename EQ into EQs. trans_para_invT TRp.
        * refine_trans in TRp. dependent destruction EQ.
          assert (TRqr : trans (comm b) (q ∥ r) (β (Act b) (fun i => q ∥ kq i)))
            by (apply (trans_paraR _ q) in TRq; exact TRq).
          eexists _, _; split; [eapply trans_paraSynch; [exact TRp | exact TRqr | exact Op] | split; [| rewrite flipL_Leq; reflexivity]].
          rewrite EQs; cbn. rewrite (EQ tt). apply CIH.
        * refine_trans in TRq0. dependent destruction EQ.
          eexists _, _; split; [apply trans_paraR; eapply trans_paraSynch; [exact TRq0 | exact TRq | exact Op] | split; [| rewrite flipL_Leq; reflexivity]].
          rewrite EQs; cbn. rewrite (EQ tt). apply CIH.
        * discriminate.
  Qed.

End Theory.

Variant liftS {E C X} (R : rel (ctree E C X) (ctree E C X)) : rel (S E C X) (S E C X) :=
| liftS_act t u : R t u -> liftS R (Active t) (Active u)
| liftS_pas {Y} (e : E Y) k k' : (forall y, R (k y) (k' y)) -> liftS R (Passive e k) (Passive e k').

Lemma ss_ssm {E C X} (R : rel (ctree E C X) (ctree E C X)) (t u : ctree E C X) :
  (forall l s, trans l t s -> exists s0 s', s ⩸ s0 /\ trans l u s' /\ liftS R s0 s') -> ssm R t u.
Proof.
  intros H; repeat split.
  - intros s TR. destruct (H _ _ TR) as (s0 & s' & EQ & TR' & HL).
    destruct HL as [t0 u0 HR | Y e k k' HR].
    + exists t0, u0; auto.
    + exfalso. destruct (trans_τ_inv TR) as (x & EQx). rewrite EQ in EQx. inv EQx.
  - intros v s TR. destruct (H _ _ TR) as (s0 & s' & EQ & TR' & HL).
    now rewrite <- (trans_val_inv' TR').
  - intros Y e s TR. destruct (H _ _ TR) as (s0 & s' & EQ & TR' & HL).
    destruct (trans_ask_inv TR) as (g & EQg).
    destruct HL as [t0 u0 HR | Z f k k' HR].
    + exfalso. rewrite EQ in EQg. inv EQg.
    + rewrite EQ in EQg. dependent destruction EQg.
      exists k, k'; repeat split; auto.
Qed.

Lemma ssm_step {E C X} (R : rel (ctree E C X) (ctree E C X)) (t u : ctree E C X) l s :
  ssm R t u -> trans l t s -> (forall v, l <> val v) ->
  exists s0 s', s ⩸ s0 /\ trans l u s' /\ liftS R s0 s'.
Proof.
  intros [A1 [_ A3]] TR NV. destruct l as [| ? e | ? e y | v].
  - destruct (A1 _ TR) as (t' & u' & EQ & TR' & HR). exists (α t'), (α u'); repeat split; auto. now constructor.
  - destruct (A3 _ _ _ TR) as (k & k' & EQ & TR' & HR). exists (β e k), (β e k'); repeat split; auto. now constructor.
  - now apply trans_rcv_active_inv in TR.
  - now destruct (NV v).
Qed.

Lemma liftS_mapS {E C X} (R : rel (ctree E C X) (ctree E C X)) f g s s' :
  liftS R s s' -> (forall x y, R x y -> R (f x) (g y)) -> liftS R (mapS f s) (mapS g s').
Proof.
  intros HL FG; destruct HL; constructor; auto.
Qed.

#[global] Instance parabang_equ_l (q : ccs) : Proper (equ eq ==> equ eq) (fun p : ccs => parabang p q).
Proof. intros ? ? H; now rewrite H. Qed.

#[global] Instance parabang_equ_r (p q : ccs) : Proper (equ eq ==> equ eq) (fun r : ccs => parabang (p ∥ r) q).
Proof. intros ? ? H; now rewrite H. Qed.

Lemma parabang_ssm (R : rel ccs ccs) :
  (forall p q r s, R p q -> R r s -> R (p ∥ r) (q ∥ s)) ->
  (forall p q r s, R p q -> R r s -> R (parabang p r) (parabang q s)) ->
  forall p q r s, ssm R p q -> ssm R r s -> R p q -> R r s -> ssm R (parabang p r) (parabang q s).
Proof.
  intros CTXp CTXb p q r s Hp Hr Hpq Hrs. apply ss_ssm. intros l s0 TR.
  destruct l as [| ? e | ? e y | []]; [| | now apply trans_rcv_active_inv in TR].
  all: unfold comm in *; trans_parabang_invT TR.
  all: try discriminate.
  all: try (destruct (ssm_step _ _ _ _ _ Hp TRp' ltac:(now intros [])) as (s1 & s1' & EQ1 & TR1 & HL1);
            exists (mapS (fun x => parabang x r) s1), (mapS (fun x => parabang x s) s1'); repeat split;
            [rewrite EQ, EQ1; reflexivity | now apply trans_parabangL | apply liftS_mapS; auto]).
  all: try (destruct (ssm_step _ _ _ _ _ Hr TRq' ltac:(now intros [])) as (s1 & s1' & EQ1 & TR1 & HL1);
            exists (mapS (fun x => parabang (p ∥ x) r) s1), (mapS (fun x => parabang (q ∥ x) s) s1'); repeat split;
            [rewrite EQ, EQ1; reflexivity | now apply trans_parabangR | apply liftS_mapS; auto]).
  - destruct Hp as [_ [_ Ap3]], Hr as [_ [_ Ar3]].
    destruct (Ap3 _ _ _ TRp') as (k1 & k1' & EQ1 & TR1 & HR1).
    destruct (Ar3 _ _ _ TRq') as (k2 & k2' & EQ2 & TR2 & HR2).
    dependent destruction EQ1. dependent destruction EQ2.
    exists (α parabang (k1 tt ∥ k2 tt) r), (α parabang (k1' tt ∥ k2' tt) s); repeat split.
    + rewrite EQ, EQ0, EQ1; reflexivity.
    + eapply trans_parabangSL; [exact Op | exact TR1 | exact TR2].
    + constructor; auto.
  - destruct Hr as [_ [_ Ar3]].
    destruct (Ar3 _ _ _ TRq') as (k1 & k1' & EQ1 & TR1 & HR1).
    destruct (Ar3 _ _ _ TRq'') as (k2 & k2' & EQ2 & TR2 & HR2).
    dependent destruction EQ1. dependent destruction EQ2.
    exists (α parabang (p ∥ (k1 tt ∥ k2 tt)) r), (α parabang (q ∥ (k1' tt ∥ k2' tt)) s); repeat split.
    + rewrite EQ, EQ0, EQ1; reflexivity.
    + eapply trans_parabangSR; [exact Op | exact TR1 | exact TR2].
    + constructor; auto.
Qed.

Lemma ctx_parabang_m : forall (R : Chain (@sbm ccsE ccsC void)) (p q r s : ccs),
    elem R p q -> elem R r s -> elem R (parabang p r) (parabang q s).
Proof.
  intros R. pattern (elem R). revert R. apply tower.
  - intros T HT p q r s Hpq Hrs R' TR. apply (HT R' TR); [apply Hpq | apply Hrs]; exact TR.
  - intros R IH p q r s Hpq Hrs.
    pose proof (b_chain R _ _ Hpq) as Hpq'. pose proof (b_chain R _ _ Hrs) as Hrs'.
    destruct Hpq as [Fp Bp], Hrs as [Fr Br]. split.
    + apply parabang_ssm; auto. apply ctx_para_m.
    + apply parabang_ssm; auto.
      * intros; now apply ctx_para_m.
      * intros; apply IH; auto.
Qed.

#[global] Instance parabang_sbisim : Proper (sbisimT Leq ==> sbisimT Leq ==> sbisimT Leq) parabang.
Proof.
  intros p q Hpq r s Hrs. apply sbm_sbisim.
  apply sbisim_sbm in Hpq, Hrs. unfold sbmbisim in *.
  now apply (gfp_prop (fun x => forall p q r s : ccs, x p q -> x r s -> x (parabang p r) (parabang q s)) ctx_parabang_m).
Qed.

#[global] Instance bang_sbisim : Proper (sbisimT Leq ==> sbisimT Leq) bang.
Proof.
  intros p q H. unfold bang. now rewrite H.
Qed.

Lemma sbisimT_step {E C X} (t t' : ctree E C X) l s :
  t ≃ t' -> trans l t s -> exists s', trans l t' s' /\ sbisimeq s s'.
Proof.
  intros H TR. step in H. destruct H as [F _].
  apply F in TR as (l' & s' & TR' & HR & HL). apply Leq_eq in HL; subst l'. eauto.
Qed.

Lemma ssm_sbisim_clos (R : rel ccs ccs) :
  (forall t t' u u', t ≃ t' -> u ≃ u' -> R t' u' -> R t u) ->
  forall t t' u u', t ≃ t' -> u ≃ u' -> ssm R t' u' -> ssm R t u.
Proof.
  intros CLO t t' u u' Ht Hu H. apply ss_ssm. intros l s TR.
  destruct l as [| ? e | ? e y | []]; [| | now apply trans_rcv_active_inv in TR].
  all: destruct (sbisimT_step _ _ _ _ Ht TR) as (s1 & TR1 & HS1).
  all: destruct (ssm_step _ _ _ _ _ H TR1 ltac:(now intros [])) as (s0 & s2 & EQ0 & TR2 & HL).
  all: symmetry in Hu; destruct (sbisimT_step _ _ _ _ Hu TR2) as (s3 & TR3 & HS3).
  - destruct (trans_τ_inv TR) as (x & EQx). destruct (trans_τ_inv TR3) as (y & EQy).
    destruct HL as [a b HR | Z f k k' HR].
    + exists (α x), (α y); repeat split; [exact EQx | rewrite <- EQy; exact TR3 | constructor].
      eapply CLO; [| | exact HR].
      * rewrite EQx, EQ0 in HS1. exact HS1.
      * rewrite EQy in HS3. symmetry; exact HS3.
    + exfalso. destruct (trans_τ_inv TR2) as (z & EQz). inv EQz.
  - destruct (trans_ask_inv TR) as (g & EQg). destruct (trans_ask_inv TR3) as (g' & EQg').
    destruct (trans_ask_inv TR1) as (g1 & EQg1).
    destruct HL as [a b HR | Z f k k' HR].
    + exfalso. destruct (trans_ask_inv TR2) as (z & EQz). inv EQz.
    + rewrite EQ0 in EQg1. dependent destruction EQg1.
      exists (β e g), (β e g'); repeat split; [exact EQg | rewrite <- EQg'; exact TR3 | constructor; intros z].
      eapply CLO; [| | exact (HR z)].
      * rewrite EQg, EQ0 in HS1. exact (sbisim_sbm_passive _ _ _ HS1 z).
      * rewrite EQg' in HS3. symmetry. exact (sbisim_sbm_passive _ _ _ HS3 z).
Qed.

Lemma sbm_chain_sbisim : forall (R : Chain (@sbm ccsE ccsC void)) (t t' u u' : ccs),
    t ≃ t' -> u ≃ u' -> elem R t' u' -> elem R t u.
Proof.
  intros R. pattern (elem R). revert R. apply tower.
  - intros T HT t t' u u' Ht Hu H R' TR. eapply (HT R' TR); eauto. apply H, TR.
  - intros R IH t t' u u' Ht Hu [F B]. split.
    + eapply ssm_sbisim_clos; eauto.
    + eapply ssm_sbisim_clos; [| exact Hu | exact Ht | exact B].
      unfold flip; intros; eapply IH; eauto.
Qed.

#[global] Instance sbm_chain_sbisim_goal {R : Chain (@sbm ccsE ccsC void)} :
  Proper (sbisimT Leq ==> sbisimT Leq ==> flip impl) (elem R).
Proof.
  intros t t' Ht u u' Hu H. eapply sbm_chain_sbisim; eauto.
Qed.

Lemma mapS_mapS {E C X} (f g : ctree E C X -> ctree E C X) s :
  mapS f (mapS g s) = mapS (fun x => f (g x)) s.
Proof. now destruct s. Qed.

Lemma liftS_mapS_eq {E C X} (R : rel (ctree E C X) (ctree E C X)) f g (s : S E C X) :
  (forall x, R (f x) (g x)) -> liftS R (mapS f s) (mapS g s).
Proof. intros H; destruct s; constructor; auto. Qed.

Lemma para_parabang : forall p q r,
    parabang (p ∥ q) r ≃ p ∥ parabang q r.
Proof.
  intros p q r. apply sbm_sbisim. revert p q r. unfold sbmbisim.
  coinduction R CIH. intros p q r. split; apply ss_ssm; intros l s TR;
    (destruct l as [| ? e | ? e y | []]; [| | now apply trans_rcv_active_inv in TR]).
  all: unfold comm in *.
  1-2: trans_parabang_invT TR.
  all: try discriminate.
  - trans_para_invT TRp'.
    + exists (mapS (fun x => parabang (x ∥ q) r) p'0), (mapS (fun x => x ∥ parabang q r) p'0); repeat split.
      * rewrite EQ, EQ0, mapS_mapS; reflexivity.
      * now apply trans_paraL.
      * apply liftS_mapS_eq; intros; apply CIH.
    + exists (mapS (fun x => parabang (p ∥ x) r) q'), (mapS (fun x => p ∥ parabang x r) q'); repeat split.
      * rewrite EQ, EQ0, mapS_mapS; reflexivity.
      * pose proof (trans_paraR _ p _ _ (trans_parabangL _ _ r _ TRq)) as T. rewrite mapS_mapS in T. exact T.
      * apply liftS_mapS_eq; intros; apply CIH.
    + exists (α parabang (kp tt ∥ kq tt) r), (α kp tt ∥ parabang (kq tt) r); repeat split.
      * rewrite EQ, EQ0; reflexivity.
      * apply (trans_paraSynch a b p (parabang q r) kp (fun x => parabang (kq x) r));
          [exact TRp | exact (trans_parabangL _ _ r _ TRq) | exact Op].
      * constructor; apply CIH.
  - exists (mapS (fun x => parabang ((p ∥ q) ∥ x) r) q'), (mapS (fun x => p ∥ parabang (q ∥ x) r) q'); repeat split.
    + exact EQ.
    + pose proof (trans_paraR _ p _ _ (trans_parabangR _ q r _ TRq')) as T. rewrite mapS_mapS in T. exact T.
    + apply liftS_mapS_eq; intros. rewrite <- paraA. apply CIH.
  - unfold comm in TRp'. rename EQ into EQs. trans_para_invT TRp'.
    + refine_trans in TRp. dependent destruction EQ.
      exists (α parabang ((u tt ∥ q) ∥ kq tt) r), (α u tt ∥ parabang (q ∥ kq tt) r); repeat split.
      * rewrite EQs, (EQ tt); reflexivity.
      * apply (trans_paraSynch a b p (parabang q r) u (fun x => parabang (q ∥ kq x) r));
          [exact TRp | exact (trans_parabangR _ q r _ TRq') | exact Op].
      * constructor. rewrite <- paraA. apply CIH.
    + refine_trans in TRq. dependent destruction EQ.
      exists (α parabang ((p ∥ u tt) ∥ kq tt) r), (α p ∥ parabang (u tt ∥ kq tt) r); repeat split.
      * rewrite EQs, (EQ tt); reflexivity.
      * exact (trans_paraR _ p _ _ (trans_parabangSL a b q r u kq Op TRq TRq')).
      * constructor. rewrite <- paraA. apply CIH.
    + discriminate.
  - exists (α parabang ((p ∥ q) ∥ (kq1 tt ∥ kq2 tt)) r), (α p ∥ parabang (q ∥ (kq1 tt ∥ kq2 tt)) r); repeat split.
    + exact EQ.
    + exact (trans_paraR _ p _ _ (trans_parabangSR a b q r kq1 kq2 Op TRq' TRq'')).
    + constructor. rewrite <- paraA. apply CIH.
  - trans_para_invT TRp'.
    + exists (mapS (fun x => parabang (x ∥ q) r) p'0), (mapS (fun x => x ∥ parabang q r) p'0); repeat split.
      * rewrite EQ, EQ0, mapS_mapS; reflexivity.
      * now apply trans_paraL.
      * apply liftS_mapS_eq; intros; apply CIH.
    + exists (mapS (fun x => parabang (p ∥ x) r) q'), (mapS (fun x => p ∥ parabang x r) q'); repeat split.
      * rewrite EQ, EQ0, mapS_mapS; reflexivity.
      * pose proof (trans_paraR _ p _ _ (trans_parabangL _ _ r _ TRq)) as T. rewrite mapS_mapS in T. exact T.
      * apply liftS_mapS_eq; intros; apply CIH.
    + discriminate.
  - exists (mapS (fun x => parabang ((p ∥ q) ∥ x) r) q'), (mapS (fun x => p ∥ parabang (q ∥ x) r) q'); repeat split.
    + exact EQ.
    + pose proof (trans_paraR _ p _ _ (trans_parabangR _ q r _ TRq')) as T. rewrite mapS_mapS in T. exact T.
    + apply liftS_mapS_eq; intros. rewrite <- paraA. apply CIH.
  - trans_para_invT TR.
    + exists (mapS (fun x => x ∥ parabang q r) p'), (mapS (fun x => parabang (x ∥ q) r) p'); repeat split.
      * exact EQ.
      * pose proof (trans_parabangL _ _ r _ (trans_paraL _ _ q _ TRp)) as T. rewrite mapS_mapS in T. exact T.
      * apply liftS_mapS_eq; intros; apply CIH.
    + trans_parabang_invT TRq.
      * exists (mapS (fun x => p ∥ parabang x r) p'), (mapS (fun x => parabang (p ∥ x) r) p'); repeat split.
        -- rewrite EQ, EQ0, mapS_mapS; reflexivity.
        -- pose proof (trans_parabangL _ _ r _ (trans_paraR _ p _ _ TRp')) as T. rewrite mapS_mapS in T. exact T.
        -- apply liftS_mapS_eq; intros; apply CIH.
      * exists (mapS (fun x => p ∥ parabang (q ∥ x) r) q'0), (mapS (fun x => parabang ((p ∥ q) ∥ x) r) q'0); repeat split.
        -- rewrite EQ, EQ0, mapS_mapS; reflexivity.
        -- now apply trans_parabangR.
        -- apply liftS_mapS_eq; intros. unfold flip. rewrite <- paraA. apply CIH.
      * exists (α p ∥ parabang (kp tt ∥ kq tt) r), (α parabang ((p ∥ kp tt) ∥ kq tt) r); repeat split.
        -- rewrite EQ, EQ0; reflexivity.
        -- exact (trans_parabangSL a b (p ∥ q) r (fun x => p ∥ kp x) kq Op (trans_paraR _ p _ _ TRp') TRq').
        -- constructor. unfold flip. rewrite <- paraA. apply CIH.
      * exists (α p ∥ parabang (q ∥ (kq1 tt ∥ kq2 tt)) r), (α parabang ((p ∥ q) ∥ (kq1 tt ∥ kq2 tt)) r); repeat split.
        -- rewrite EQ, EQ0; reflexivity.
        -- exact (trans_parabangSR a b (p ∥ q) r kq1 kq2 Op TRq' TRq'').
        -- constructor. unfold flip. rewrite <- paraA. apply CIH.
    + unfold comm in TRq. rename EQ into EQs. trans_parabang_invT TRq.
      * refine_trans in TRp'. dependent destruction EQ.
        exists (α kp tt ∥ parabang (u tt) r), (α parabang (kp tt ∥ u tt) r); repeat split.
        -- rewrite EQs, (EQ tt); reflexivity.
        -- exact (trans_parabangL _ _ r _ (trans_paraSynch a b p q kp u TRp TRp' Op)).
        -- constructor. unfold flip. apply CIH.
      * refine_trans in TRq'. dependent destruction EQ.
        exists (α kp tt ∥ parabang (q ∥ u tt) r), (α parabang ((kp tt ∥ q) ∥ u tt) r); repeat split.
        -- rewrite EQs, (EQ tt); reflexivity.
        -- exact (trans_parabangSL a b (p ∥ q) r (fun x => kp x ∥ q) u Op (trans_paraL _ _ q _ TRp) TRq').
        -- constructor. unfold flip. rewrite <- paraA. apply CIH.
      * discriminate.
      * discriminate.
  - trans_para_invT TR.
    + exists (mapS (fun x => x ∥ parabang q r) p'), (mapS (fun x => parabang (x ∥ q) r) p'); repeat split.
      * exact EQ.
      * pose proof (trans_parabangL _ _ r _ (trans_paraL _ _ q _ TRp)) as T. rewrite mapS_mapS in T. exact T.
      * apply liftS_mapS_eq; intros; apply CIH.
    + trans_parabang_invT TRq; try discriminate.
      * exists (mapS (fun x => p ∥ parabang x r) p'), (mapS (fun x => parabang (p ∥ x) r) p'); repeat split.
        -- rewrite EQ, EQ0, mapS_mapS; reflexivity.
        -- pose proof (trans_parabangL _ _ r _ (trans_paraR _ p _ _ TRp')) as T. rewrite mapS_mapS in T. exact T.
        -- apply liftS_mapS_eq; intros; apply CIH.
      * exists (mapS (fun x => p ∥ parabang (q ∥ x) r) q'0), (mapS (fun x => parabang ((p ∥ q) ∥ x) r) q'0); repeat split.
        -- rewrite EQ, EQ0, mapS_mapS; reflexivity.
        -- now apply trans_parabangR.
        -- apply liftS_mapS_eq; intros. unfold flip. rewrite <- paraA. apply CIH.
    + discriminate.
Qed.

Lemma sbm_chain_refl (R : Chain (@sbm ccsE ccsC void)) (t : ccs) : elem R t t.
Proof. apply (gfp_chain R). apply sbisim_sbm. reflexivity. Qed.

Lemma parabang_aux : forall p q,
    parabang (p ∥ q) q ≃ parabang p q.
Proof.
  intros p q. apply sbm_sbisim. revert p q. unfold sbmbisim.
  coinduction R CIH. intros p q. split; apply ss_ssm; intros l s TR;
    (destruct l as [| ? e | ? e y | []]; [| | now apply trans_rcv_active_inv in TR]).
  all: unfold comm in *; trans_parabang_invT TR; try discriminate.
  all: try (exists (mapS (fun x => parabang ((p ∥ q) ∥ x) q) q'), (mapS (fun x => parabang (p ∥ x) q) q'); repeat split;
         [exact EQ | now apply trans_parabangR | apply liftS_mapS_eq; intros x; rewrite <- paraA, (paraC q), paraA; apply CIH]).
  all: try (exists (mapS (fun x => parabang x q) p'), (mapS (fun x => parabang (x ∥ q) q) p'); repeat split;
         [exact EQ | pose proof (trans_parabangL _ _ q _ (trans_paraL _ _ q _ TRp')) as T; rewrite mapS_mapS in T; exact T
         | apply liftS_mapS_eq; intros; apply CIH]).
  all: try (exists (mapS (fun x => parabang (p ∥ x) q) q'), (mapS (fun x => parabang (p ∥ x) q) q'); repeat split;
         [exact EQ | pose proof (trans_parabangL _ _ q _ (trans_paraR _ p _ _ TRq')) as T; rewrite mapS_mapS in T; exact T
         | apply liftS_mapS_eq; intros; apply sbm_chain_refl]).
  1,4: trans_para_invT TRp'; try discriminate.
  all: try (exists (mapS (fun x => parabang (x ∥ q) q) p'0), (mapS (fun x => parabang x q) p'0); repeat split;
         [rewrite EQ, EQ0, mapS_mapS; reflexivity | now apply trans_parabangL | apply liftS_mapS_eq; intros; apply CIH]).
  all: try (exists (mapS (fun x => parabang (p ∥ x) q) q'), (mapS (fun x => parabang (p ∥ x) q) q'); repeat split;
         [rewrite EQ, EQ0, mapS_mapS; reflexivity | now apply trans_parabangR | apply liftS_mapS_eq; intros; apply sbm_chain_refl]).
  - exists (α parabang (kp tt ∥ kq tt) q), (α parabang (kp tt ∥ kq tt) q); repeat split.
    + rewrite EQ, EQ0; reflexivity.
    + exact (trans_parabangSL a b p q kp kq Op TRp TRq).
    + constructor; apply sbm_chain_refl.
  - unfold comm in TRp'. rename EQ into EQs. trans_para_invT TRp'.
    + refine_trans in TRp. dependent destruction EQ.
      exists (α parabang ((u tt ∥ q) ∥ kq tt) q), (α parabang (u tt ∥ kq tt) q); repeat split.
      * rewrite EQs, (EQ tt); reflexivity.
      * exact (trans_parabangSL a b p q u kq Op TRp TRq').
      * constructor. rewrite <- paraA, (paraC q), paraA. apply CIH.
    + refine_trans in TRq. dependent destruction EQ.
      exists (α parabang ((p ∥ u tt) ∥ kq tt) q), (α parabang (p ∥ (u tt ∥ kq tt)) q); repeat split.
      * rewrite EQs, (EQ tt); reflexivity.
      * exact (trans_parabangSR a b p q u kq Op TRq TRq').
      * constructor. rewrite <- paraA. apply sbm_chain_refl.
    + discriminate.
  - exists (α parabang ((p ∥ q) ∥ (kq1 tt ∥ kq2 tt)) q), (α parabang (p ∥ (kq1 tt ∥ kq2 tt)) q); repeat split.
    + exact EQ.
    + exact (trans_parabangSR a b p q kq1 kq2 Op TRq' TRq'').
    + constructor. rewrite <- paraA, (paraC q), paraA. apply CIH.
  - exists (α parabang (kp tt ∥ kq tt) q), (α parabang (kp tt ∥ kq tt) q); repeat split.
    + exact EQ.
    + exact (trans_parabangL _ _ q _ (trans_paraSynch a b p q kp kq TRp' TRq' Op)).
    + constructor; apply sbm_chain_refl.
  - exists (α parabang (p ∥ (kq1 tt ∥ kq2 tt)) q), (α parabang ((p ∥ kq1 tt) ∥ kq2 tt) q); repeat split.
    + exact EQ.
    + exact (trans_parabangSL a b (p ∥ q) q (fun x => p ∥ kq1 x) kq2 Op (trans_paraR _ p _ _ TRq') TRq'').
    + constructor. unfold flip. rewrite <- paraA. apply sbm_chain_refl.
Qed.

Lemma parabang_eq : forall p q,
    parabang p q ≃ p ∥ !q.
Proof.
  intros p q. apply sbm_sbisim. revert p q. unfold sbmbisim.
  coinduction R CIH. intros p q. split; apply ss_ssm; intros l s TR;
    (destruct l as [| ? e | ? e y | []]; [| | now apply trans_rcv_active_inv in TR]).
  all: unfold comm, bang in *.
  1,2: trans_parabang_invT TR; try discriminate.
  all: try (exists (mapS (fun x => parabang x q) p'), (mapS (fun x => x ∥ parabang q q) p'); repeat split;
         [exact EQ | now apply trans_paraL | apply liftS_mapS_eq; intros; apply CIH]).
  all: try (exists (mapS (fun x => parabang (p ∥ x) q) q'), (mapS (fun x => p ∥ parabang x q) q'); repeat split;
         [exact EQ | pose proof (trans_paraR _ p _ _ (trans_parabangL _ _ q _ TRq')) as T; rewrite mapS_mapS in T; exact T
         | apply liftS_mapS_eq; intros; apply (gfp_chain R), sbisim_sbm, para_parabang]).
  - exists (α parabang (kp tt ∥ kq tt) q), (α kp tt ∥ parabang (kq tt) q); repeat split.
    + exact EQ.
    + exact (trans_paraSynch a b p (parabang q q) kp (fun x => parabang (kq x) q) TRp' (trans_parabangL _ _ q _ TRq') Op).
    + constructor; apply (gfp_chain R), sbisim_sbm, para_parabang.
  - exists (α parabang (p ∥ (kq1 tt ∥ kq2 tt)) q), (α p ∥ parabang (kq1 tt ∥ kq2 tt) q); repeat split.
    + exact EQ.
    + exact (trans_paraR _ p _ _ (trans_parabangSL a b q q kq1 kq2 Op TRq' TRq'')).
    + constructor; apply (gfp_chain R), sbisim_sbm, para_parabang.
  - trans_para_invT TR.
    + exists (mapS (fun x => x ∥ parabang q q) p'), (mapS (fun x => parabang x q) p'); repeat split;
        [exact EQ | now apply trans_parabangL | apply liftS_mapS_eq; intros; apply CIH].
    + trans_parabang_invT TRq.
      * exists (mapS (fun x => p ∥ parabang x q) p'), (mapS (fun x => parabang (p ∥ x) q) p'); repeat split.
        -- rewrite EQ, EQ0, mapS_mapS; reflexivity.
        -- now apply trans_parabangR.
        -- apply liftS_mapS_eq; intros; apply (gfp_chain R), sbisim_sbm, para_parabang.
      * exists (mapS (fun x => p ∥ parabang (q ∥ x) q) q'0), (mapS (fun x => parabang (p ∥ x) q) q'0); repeat split.
        -- rewrite EQ, EQ0, mapS_mapS; reflexivity.
        -- now apply trans_parabangR.
        -- apply liftS_mapS_eq; intros; apply (gfp_chain R), sbisim_sbm.
           rewrite para_parabang, (paraC q), parabang_aux; reflexivity.
      * exists (α p ∥ parabang (kp tt ∥ kq tt) q), (α parabang (p ∥ (kp tt ∥ kq tt)) q); repeat split.
        -- rewrite EQ, EQ0; reflexivity.
        -- exact (trans_parabangSR a b p q kp kq Op TRp' TRq').
        -- constructor; apply (gfp_chain R), sbisim_sbm, para_parabang.
      * exists (α p ∥ parabang (q ∥ (kq1 tt ∥ kq2 tt)) q), (α parabang (p ∥ (kq1 tt ∥ kq2 tt)) q); repeat split.
        -- rewrite EQ, EQ0; reflexivity.
        -- exact (trans_parabangSR a b p q kq1 kq2 Op TRq' TRq'').
        -- constructor; apply (gfp_chain R), sbisim_sbm.
           rewrite para_parabang, (paraC q), parabang_aux; reflexivity.
    + unfold comm in TRq. rename EQ into EQs. trans_parabang_invT TRq; try discriminate.
      * refine_trans in TRp'. dependent destruction EQ.
        exists (α kp tt ∥ parabang (u tt) q), (α parabang (kp tt ∥ u tt) q); repeat split.
        -- rewrite EQs, (EQ tt); reflexivity.
        -- exact (trans_parabangSL a b p q kp u Op TRp TRp').
        -- constructor; apply (gfp_chain R), sbisim_sbm, para_parabang.
      * refine_trans in TRq'. dependent destruction EQ.
        exists (α kp tt ∥ parabang (q ∥ u tt) q), (α parabang (kp tt ∥ u tt) q); repeat split.
        -- rewrite EQs, (EQ tt); reflexivity.
        -- exact (trans_parabangSL a b p q kp u Op TRp TRq').
        -- constructor; apply (gfp_chain R), sbisim_sbm.
           rewrite para_parabang, (paraC q), parabang_aux; reflexivity.
  - trans_para_invT TR; try discriminate.
    + exists (mapS (fun x => x ∥ parabang q q) p'), (mapS (fun x => parabang x q) p'); repeat split;
        [exact EQ | now apply trans_parabangL | apply liftS_mapS_eq; intros; apply CIH].
    + trans_parabang_invT TRq; try discriminate.
      * exists (mapS (fun x => p ∥ parabang x q) p'), (mapS (fun x => parabang (p ∥ x) q) p'); repeat split.
        -- rewrite EQ, EQ0, mapS_mapS; reflexivity.
        -- now apply trans_parabangR.
        -- apply liftS_mapS_eq; intros; apply (gfp_chain R), sbisim_sbm, para_parabang.
      * exists (mapS (fun x => p ∥ parabang (q ∥ x) q) q'0), (mapS (fun x => parabang (p ∥ x) q) q'0); repeat split.
        -- rewrite EQ, EQ0, mapS_mapS; reflexivity.
        -- now apply trans_parabangR.
        -- apply liftS_mapS_eq; intros; apply (gfp_chain R), sbisim_sbm.
           rewrite para_parabang, (paraC q), parabang_aux; reflexivity.
Qed.

Lemma unfold_bang' : forall p,
    !p ≃ !p ∥ p.
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
  (* Notation "P '⊢' a '→ccs' Q" := (step_ccs P a Q) (at level 50). *)
  (* Notation "P '⊢' a '→sem' Q" := (step_sem P a Q) (at level 50). *)

End DenNotations.

Import DenNotations.
