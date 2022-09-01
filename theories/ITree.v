From Paco Require Import paco.

From CTree Require Import
	   CTree Eq Interp.Internalize.

(* Universe issue, TO FIX *)
Unset Universe Checking.
Unset Auto Template Polymorphism.

From ITree Require Import
	   ITree Eq Interp InterpFacts.

From Coq Require Import
	   Morphisms Program.
Open Scope ctree.

Set Implicit Arguments.
Set Contextual Implicit.

Definition h_embed {E C} : E ~> ctree E C :=
  fun _ e => CTree.trigger e.
Definition embed' {E} : itree E ~> ctree E (C01) := interp h_embed.

Definition embed {E C} : itree (C +' E) ~> ctree E (C01 +' C) :=
  fun _ t => internalize (embed' t).

Notation "t '-' l '→' u" := (trans l t u)
                              (at level 50, only printing,
                                format "t  '-' l '→'  u").

Notation "t '-' l '→' u" := (transR l t u)
                              (at level 50, only printing,
                                format "t  '-' l '→'  u").

(* Definition embed {E X} : itree E X -> ctree E X := *)
(* 	cofix _embed t := *)
(* 	 match observe t with *)
(* 	| RetF x => CTrees.Ret x *)
(* 	| TauF t => CTrees.TauI (_embed t) *)
(* 	| VisF e k => CTrees.Vis e (fun x => _embed (k x)) *)
(* 	 end. *)

(* Notation "'_embed' ot" := *)
(* 	(match ot with *)
(* 	| RetF x => CTrees.Ret x *)
(* 	| TauF t => CTrees.TauI (embed t) *)
(* 	| VisF e k => CTrees.Vis e (fun x => embed (k x)) *)
(*  end) (at level 50, only parsing). *)

(* Lemma unfold_embed {E X} (t : itree E X) : *)
(* 	equ eq (embed t) (_embed (observe t)). *)
(* Proof. *)
(*   now step. *)
(* Qed. *)

#[local] Notation iobserve  := observe.
#[local] Notation _iobserve := _observe.
#[local] Notation cobserve  := CTreeDefinitions.observe.
#[local] Notation _cobserve := CTreeDefinitions._observe.
#[local] Notation iRet x    := (Ret x).
#[local] Notation iVis e k  := (Vis e k).
#[local] Notation iTau t    := (Tau t).
#[local] Notation cRet x    := (CTreeDefinitions.Ret x).
#[local] Notation cTauI t   := (CTreeDefinitions.tauI t).
#[local] Notation cVis e k  := (CTreeDefinitions.Vis e k).

(** Unfolding of [interp]. *)
Definition _interp {E F C R} `{C1 -< C} (f : E ~> ctree F C) (ot : itreeF E R _)
  : ctree F C R :=
  match ot with
  | RetF r => CTreeDefinitions.Ret r
  | TauF t => cTauI (interp f t)
  | VisF e k => CTree.bind (f _ e) (fun x => cTauI (interp f (k x)))
  end.

Lemma unfold_interp_ctree {E F C X} `{C1 -< C} (h: E ~> ctree F C) (t : itree E X):
  (interp h t ≅ _interp h (iobserve t))%ctree.
Proof.
  revert t.
  coinduction R CIH.
  intros; cbn*.
  Opaque CTree.bind.
  unfold cobserve; cbn.
  destruct (iobserve t) eqn:ot; try now cbn; auto.
  match goal with
    |- equb _ _ (_cobserve ?t) (_cobserve ?u) =>
      fold (cobserve t);
      fold (cobserve u)
  end.
  Transparent CTree.bind.
  cbn.
  rewrite Equ.bind_map.
  apply (fbt_bt (@bind_ctx_equ_t F _ X0 X0 X X eq eq) R), in_bind_ctx.
  reflexivity.
  intros ? ? <-.
  constructor; intros ?.
  reflexivity.
Qed.

Lemma embed_eq {E C X}:
	Proper (eq_itree eq ==> equ eq) (@embed E C X).
Proof.
	unfold Proper, respectful.
	coinduction r CIH.
	intros t u bisim. unfold embed, embed', internalize.
  rewrite 2 unfold_interp_ctree.
  rewrite 2 Interp.unfold_interp.
	punfold bisim.
	inv bisim; pclearbot; try easy.
	- Opaque CTree.bind.
          unfold cobserve; cbn.
          destruct (iobserve t) eqn:ot; try now cbn; auto.
          Transparent CTree.bind.
          upto_bind_eq.
          constructor; intros ?.
          apply CIH; auto.
        - unfold cobserve; cbn.
          upto_bind_eq.
          constructor; intros ?.
          rewrite 2 Interp.unfold_interp.
          cbn.
          step; cbn*.
          constructor; intros ?.
          step; cbn*.
          constructor; intros ?.
          apply CIH, REL.
Qed.

From Coq Require Import Datatypes.

(* This is actually not trivial.
   There are two ways to encode itrees' taus:
   - If we use tauI, then I believe we have eutt mapping to sbisim I believe.
   Proving so however is tricky: [eutt] has a weird behavior that consists of
   being allowed to either look at taus (tau/tau rule) or ignore them (asymmetric rules).
   In contrast, [sbisim] can only ignore [tauI]. In the Tau/Tau case, it's therefore quite
   unclear how the proof should proceed: fundamentally, the rule is useful in [eutt] if and
   only if the computations are both [spin] from now on --- in all other cases it can be
   replaced by two asymmetric rules.
   And as it turns out, if it is indeed [spin] against [spin], then [sbisim] relate [spinI]
   against itself as well.
   But how do we turn this into a proof?
   - If we use tauV, then [eutt] certainly does not map against sbisim --- actually, it maps
   against [equ] as well in this case. However, I think it should map against [wbisim], but
   that remains to be proved.

 *)

Notation embed_ t :=
  match iobserve t with
  | RetF r => cRet r
  | TauF t => cTauI (cTauI (embed t))
  | VisF (inl1 e) k =>
      match e,k with
      | c, k => ChoiceV c (fun x => cTauI (cTauI (cTauI (embed (k x)))))
      end
  | VisF (inr1 e) k => CTreeDefinitions.vis e (fun x => cTauI (cTauI (cTauI (embed (k x)))))
  end.

Lemma unfold_embed {E C X} (t : itree (C +' E) X) : (embed t ≅ embed_ t)%ctree.
Proof.
  unfold embed, embed', internalize at 1.
  rewrite unfold_interp_ctree, Interp.unfold_interp.
  cbn.
  destruct (iobserve t) eqn:EQ; cbn; auto.
  - step; cbn.
    constructor; intros ?.
    step; cbn.
    reflexivity.
  - destruct e.
    + cbn.
      rewrite Equ.unfold_bind at 1.
      cbn.
      step; cbn; constructor; intros ?.
      rewrite Equ.bind_ret_l.
      step; cbn; constructor; intros ?.
      rewrite Interp.unfold_interp; cbn.
      rewrite Equ.unfold_bind at 1.
      step; cbn; constructor; intros ?.
      rewrite Equ.bind_ret_l.
      step; cbn; constructor; intros ?.
      auto.
    + cbn.
      rewrite Equ.unfold_bind at 1.
      cbn.
      step; cbn; constructor; intros ?.
      rewrite Equ.bind_ret_l.
      step; cbn; constructor; intros ?.
      rewrite Interp.unfold_interp; cbn.
      rewrite Equ.unfold_bind at 1.
      step; cbn; constructor; intros ?.
      rewrite Equ.bind_ret_l.
      step; cbn; constructor; intros ?.
      auto.
Qed.

Lemma trans_embed_inv E C X : forall (t1 : itree (C +' E) X) l t2',
    trans l (embed t1) t2' ->
    (exists r : X, (t2' ≅ stuckI)%ctree /\ l = val r)
    \/ exists t2, (t2' ~ embed t2)%ctree.
Proof.
  unfold trans.
  intros * TR.
  cbn in TR; red in TR.
  remember (embed t1) as et1.
  cut (
      ((et1 ≅ embed t1)%ctree \/ (et1 ≅ cTauI (embed t1))%ctree) ->
      (exists r : X, (t2' ≅ stuckI)%ctree /\ l = val r)
      \/ exists t2 : itree (C +' E) X, t2' ~ embed t2).
  intros H; eapply H; eauto; left; subst; auto.
  clear Heqet1.
  revert t1.
  dependent induction TR.
  - intros ? EQ.
    destruct EQ as [EQ | EQ].
    + rewrite (unfold_embed t1) in EQ.
      step in EQ.
      rewrite <- x in EQ.
      destruct (iobserve t1) eqn:EQ1; try now inv EQ.
      * dependent induction EQ.
        specialize (REL x0).
        specialize (IHTR _ t2' (k x0) eq_refl).
        edestruct IHTR; eauto.
      * destruct e.
        inv EQ.
        inv EQ.
    + step in EQ.
      rewrite <- x in EQ.
      clear x et1.
      dependent induction EQ.
      specialize (REL x0).
      specialize (IHTR _ t2' (k x0) eq_refl).
      edestruct IHTR; eauto.
  - intros * EQ.
    assert (t2' ≅ t)%ctree by (step; now rewrite x).
    setoid_rewrite H0.
    clear t2' x H0.
    setoid_rewrite <- H.
    clear t H.
    destruct EQ as [EQ | EQ].
    + rewrite (ctree_eta et1), <- x1 in EQ;
        clear et1 x1.
      rewrite unfold_embed in EQ.
      destruct (iobserve t1) eqn:EQ1; try now step in EQ; inv EQ.
      destruct e; [| step in EQ; inv EQ].
      step in EQ; dependent induction EQ.
      setoid_rewrite (REL x0).
      right.
      eexists; rewrite !sb_tauI.
      reflexivity.
    + rewrite (ctree_eta et1), <- x1 in EQ;
        clear et1 x1.
      step in EQ; inv EQ.

  - intros * EQ.
    assert (t2' ≅ t)%ctree by (step; now rewrite x).
    setoid_rewrite H0.
    clear t2' x H0.
    setoid_rewrite <- H.
    clear t H.
    destruct EQ as [EQ | EQ].
    + rewrite (ctree_eta et1), <- x1 in EQ;
        clear et1 x1.
      rewrite unfold_embed in EQ.
      destruct (iobserve t1) eqn:EQ1; try now step in EQ; inv EQ.
      destruct e0.
      step in EQ; inv EQ.
      step in EQ; dependent induction EQ.
      setoid_rewrite (REL x0).
      right; eexists.
      rewrite !sb_tauI.
      reflexivity.
    + rewrite (ctree_eta et1), <- x1 in EQ;
        clear et1 x1.
      step in EQ; inv EQ.

  - intros * EQ.
    assert (t2' ≅ ChoiceI choice0 k)%ctree by (step; now rewrite x).
    setoid_rewrite H.
    clear t2' x H.
    destruct EQ as [EQ | EQ].
    + rewrite (ctree_eta et1), <- x0 in EQ.
      clear et1 x0.
      rewrite unfold_embed in EQ.
      destruct (iobserve t1) eqn:EQ1; try now step in EQ; inv EQ.
      * dependent induction EQ.
        left; eexists; split; eauto.
        rewrite choiceStuckI_always_stuck; reflexivity.
      * destruct e; step in EQ; inv EQ.
    + step in EQ; rewrite <- x0 in EQ; inv EQ.
Qed.


(*
  t1  ≈  u1

 [t1] -r> stuck
--------------
 [u1] -r> stuck

 *)

Lemma bar E C X : forall (t1 u1 : itree (C +' E) X) l t2',
    trans l (embed t1) t2' ->
    t1 ≈ u1 ->
    (exists t2 u2,
        trans l (embed u1) (embed u2) /\
          (t2' ~ embed t2)%ctree /\
          t2 ≈ u2) \/
      ((t2' ≅ stuckI)%ctree /\
         trans l (embed u1) stuckI).
Proof.
  intros * TR.
  edestruct trans_embed_inv as [(r & STUCK & EQ) | (t2 & EQ)]; eauto.
  - subst l. rewrite STUCK in TR.
    right; split; auto.
    clear t2' STUCK.
    revert u1 H.
    unfold trans in TR; cbn in TR; red in TR.
    remember (embed t1) as et1.
  (*   intros u1 EUTT. *)
  (*     (* match type of Heqot1 with *) *)
  (*     (* | ?u = ?t => let eq := fresh "EQ" in assert (eq : u ~ t) by (subst; reflexivity); clear Heqot1 *) *)
  (*     (* end. *) *)
  (*   cut ( *)
  (*       ((et1 ≅ embed t1)%ctree \/ (et1 ≅ cTauI (embed t1))%ctree) -> *)
  (*       trans (val r) (embed u1) CTree.stuckI *)
  (*     ). *)
  (*   intros H; apply H; left; subst; auto. *)
  (*   clear Heqet1. *)
  (*       (* eq2equ Heqot1. *) *)
  (*   revert u1 t1 EUTT. *)
  (*   dependent induction TR; intros * EUTT EQ. *)
  (*   + specialize (IHTR _ _ eq_refl eq_refl eq_refl). *)
  (*     destruct EQ as [EQ | EQ]. *)
  (*     * rewrite ctree_eta, <- x, unfold_embed in EQ. *)
  (*       eapply IHTR. *)
  (*       reflexivity. *)
  (*       destruct (iobserve t1) eqn:EQ'; try now step in EQ; inv EQ. *)
  (*       ** step in EQ; dependent induction EQ. *)
  (*          specialize (REL x0). *)
  (*          right; rewrite REL. *)
  (*          step. *)
  (*          constructor. *)
  (*          intros ?. *)
  (*          admit. *)
  (*     * step in EQ; dependent induction EQ. *)
  (*       rewrite itree_eta, EQ', tau_eutt in EUTT. *)
  (*       eapply IHTR. *)
  (*       auto. *)
  (*       reflexivity. *)
  (*       auto. *)
  (*       specialize (REL x0). *)

  (*       apply REL. *)
  (*       rewrite unfold_embed in TR. *)
  (*       cbn in TR; red in TR. *)
  (*       dependent induction TR; intros * EQ. *)
  (*   + destruct (iobserve t1) eqn:EQ'; try now inv x. *)
  (*     dependent induction EQ. *)
  (*     rewrite unfold_embed. *)
  (*     inv EQ. *)
  (*     * apply trans_ret. *)



  (*   revert TR. *)
  (*   punfold H. *)
  (*   cbn in H; red in H. *)
  (*   dependent induction H. *)
  (*   + rewrite 2 unfold_embed, <- x, <- x0. *)
  (*     intros TRANS. *)
  (*     apply trans_ret_inv in TRANS as [EQ _]. *)
  (*     apply val_eq_inv in EQ; subst. *)
  (*     apply trans_ret. *)
  (*   + rewrite 2 unfold_embed, <- x, <- x0. *)
  (*     intros TRANS. *)
  (*     apply *)
  (*     apply trans_ret_inv in TRANS as [EQ _]. *)
  (*     apply val_eq_inv in EQ; subst. *)
  (*     apply trans_ret. *)


  (*   punfold H; red in H; cbn in H. *)
  (*   revert u1 H. *)
  (*   rewrite unfold_embed in TR. *)
  (*   cbn in TR; red in TR. *)
  (*   dependent induction TR; intros * EQ. *)
  (*   + destruct (iobserve t1) eqn:EQ'; try now inv x. *)
  (*     dependent induction EQ. *)
  (*     rewrite unfold_embed. *)
  (*     inv EQ. *)
  (*     * apply trans_ret. *)

  (* cbn in TR; red in TR. *)
  (* remember (embed t1) as et1. *)
  (* eq2equ Heqet1. *)
  (* rewrite ctree_eta in EQ. *)
  (* setoid_rewrite (ctree_eta t2'). *)
  (* revert t1 EQ u1. *)
  (* induction TR. *)
  (* - intros * EQ * EUTT. *)
  (*   admit. *)
  (* - intros * EQ * EUTT. *)
  (*   punfold EUTT. *)
  (*   red in EUTT; cbn in EUTT. *)
  (*   rewrite unfold_embed in EQ. *)
  (*   destruct (iobserve t1) eqn:EQt1; try now step in EQ; inv EQ. *)
  (*   destruct (iobserve u1) eqn:EQu1; try now inv EUTT. *)
  (*   + destruct e. *)
Admitted.

Lemma embed_eutt {E C X}:
  Proper (eutt eq ==> sbisim) (@embed E C X).
Proof.
  unfold Proper,respectful.
  coinduction ? CIH.
  symmetric using idtac.
  - intros * HR * EQ.
    apply HR; symmetry; assumption.
  - intros t u EUTT.
    cbn; intros * TR.
    rewrite unfold_embed in TR.
    punfold EUTT; red in EUTT.
    remember (iobserve u) as ou.
    revert u Heqou.
    induction EUTT.
    + subst.
      eexists; [| reflexivity].
      rewrite unfold_embed, <- Heqou; apply TR.

    + pclearbot.
      intros.
      apply trans_tauI_inv, trans_tauI_inv in TR.
      fold (eqit eq true true m1 m2) in REL.
      fold (eutt eq m1 m2) in REL.

      destruct (bar TR REL) as [(t2 & u2 & TR' & EQ2 & EUTT2) | (EQ2 & TR2)].
      * eexists.
        rewrite unfold_embed, <- Heqou.
        apply trans_tauI, trans_tauI.
        eauto.
        rewrite EQ2.
        apply CIH, EUTT2.
      * exists stuckI.
        2:setoid_rewrite EQ2; reflexivity.
        rewrite unfold_embed, <- Heqou.
        apply trans_tauI, trans_tauI.
        auto.

      + pclearbot.
        destruct e.
        * apply trans_choiceV_inv in TR as (u' & EQ & ->).
          eexists.
          rewrite unfold_embed, <- Heqou.
          apply trans_choiceV.
          rewrite EQ.
          rewrite !sb_tauI.
          auto.
        * apply trans_vis_inv in TR as (u' & EQ & ->).
          eexists.
          rewrite unfold_embed, <- Heqou.
          apply trans_vis.
          rewrite EQ.
          rewrite !sb_tauI.
          auto.

      + intros.
        apply trans_tauI_inv, trans_tauI_inv in TR.
        rewrite unfold_embed in TR.
        eapply IHEUTT in TR; eauto.

      + intros.
        destruct (iobserve u) eqn:EQ; inv Heqou.
        specialize (IHEUTT TR t0 eq_refl).
        destruct IHEUTT as [? ? ?].
        eexists; eauto.
        rewrite unfold_embed, EQ.
        apply trans_tauI, trans_tauI.
        eauto.

Qed.


(* Maybe simpler to just write a coinductive relation *)
(*Definition partial_inject {E X} : ctree E X -> itree E (option X) :=
	cofix _inject t :=
	 match CTreeDefinitions.observe t with
	| CTreeDefinitions.RetF x => Ret (Some x)
	| @ChoiceF _ _ _ _ n t =>
		(match n as x return n = x -> itree E (option X) with
					 | O => fun _ => Ret None
					 | 1 => fun pf => eq_rect_r
	 													(fun n1 : nat => (Fin.t n1 -> ctree E X) -> itree E (option X))
	 													(fun t2 : Fin.t 1 -> ctree E X => Tau (_inject (t2 Fin.F1)))
	 													pf t
					 | _ => fun _ => Ret None
		 end eq_refl)
	| CTreeDefinitions.VisF e k => Vis e (fun x => _inject (k x))
	 end.

Definition option_rel {A B : Type} (R : A -> B -> Prop) : option A -> option B -> Prop :=
	fun x y => match x, y with
	|	Some x, Some y => R x y
	| _, _ => False
	end.

(* This is probably false: no reason for the embedding to succeed. *)
Lemma partial_inject_eq {E X} :
	Proper (equ eq ==> eq_itree (option_rel eq)) (@partial_inject E X).
Admitted.*)

Variant is_detF {E C X} `{C1 -< C} (is_det : ctree E C X -> Prop) : ctree E C X -> Prop :=
| Ret_det : forall x, is_detF is_det (CTreeDefinitions.Ret x)
| Vis_det : forall {Y} (e : E Y) k,
	(forall y, is_det (k y)) ->
	is_detF is_det (CTreeDefinitions.Vis e k)
| Tau_det : forall t,
	(is_det t) ->
	is_detF is_det (CTreeDefinitions.tauI t)
.

Definition is_det {E C X} `{C1 -< C} := paco1 (@is_detF E C X _) bot1.
