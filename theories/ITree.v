From Paco Require Import paco.

From CTree Require Import
	   CTree Eq Interp.Internalize.

(* Universe issue, TO FIX *)
Unset Universe Checking.
Unset Auto Template Polymorphism.

From ITree Require Import
	   ITree Eq.Eq Interp InterpFacts.

From Coq Require Import
	   Morphisms Program.
Open Scope ctree.

Set Implicit Arguments.
Set Contextual Implicit.

Definition h_embed {E} : E ~> ctree E :=
  fun _ e => CTree.trigger e.
Definition embed' {E} : itree E ~> ctree E := interp h_embed.

Definition embed {E} : itree (ExtChoice +' E) ~> ctree E :=
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
#[local] Notation cTauI t   := (CTreeDefinitions.TauI t).
#[local] Notation cVis e k  := (CTreeDefinitions.Vis e k).

(** Unfolding of [interp]. *)
Definition _interp {E F R} (f : E ~> ctree F) (ot : itreeF E R _)
  : ctree F R :=
  match ot with
  | RetF r => CTreeDefinitions.Ret r
  | TauF t => cTauI (interp f t)
  | VisF e k => CTree.bind (f _ e) (fun x => cTauI (interp f (k x)))
  end.

Lemma unfold_interp_ctree {E F X} (h: E ~> ctree F) (t : itree E X):
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
  apply (fbt_bt (@bind_ctx_equ_t F X0 X0 X X eq eq) R), in_bind_ctx.
  reflexivity.
  intros ? ? <-.
  constructor; intros ?.
  reflexivity.
Qed.

Instance embed_eq {E X}:
	Proper (eq_itree eq ==> equ eq) (@embed E X).
Proof.
	unfold Proper, respectful.
	coinduction r CIH.
	intros t u bisim. unfold embed, embed', internalize.
  rewrite 2 unfold_interp_ctree.
  rewrite 2 Interp.unfold_interp.
	punfold bisim.
	inv bisim; pclearbot; try easy.
	- cbn*.
    constructor; intros ?.
    step.
    cbn.
    constructor; intros ?.
    now apply CIH.
	- cbn.
    upto_bind_eq.
    constructor; intros ?.
    rewrite 2 Interp.unfold_interp.
    cbn.
    step; cbn.
    constructor; intros ?.
    step; cbn.
    constructor; intros ?.
    apply CIH, REL.
Qed.

From Coq Require Import Datatypes.

(* This is actually not trivial.
   There are two ways to encode itrees' taus:
   - If we use TauI, then I believe we have eutt mapping to sbisim I believe.
   Proving so however is tricky: [eutt] has a weird behavior that consists of
   being allowed to either look at taus (tau/tau rule) or ignore them (asymmetric rules).
   In contrast, [sbisim] can only ignore [TauI]. In the Tau/Tau case, it's therefore quite
   unclear how the proof should proceed: fundamentally, the rule is useful in [eutt] if and
   only if the computations are both [spin] from now on --- in all other cases it can be
   replaced by two asymmetric rules.
   And as it turns out, if it is indeed [spin] against [spin], then [sbisim] relate [spinI]
   against itself as well.
   But how do we turn this into a proof?
   - If we use TauV, then [eutt] certainly does not map against sbisim --- actually, it maps
   against [equ] as well in this case. However, I think it should map against [wbisim], but
   that remains to be proved.

 *)

Notation embed_ t :=
  match iobserve t with
  | RetF r => cRet r
  | TauF t => cTauI (cTauI (embed t))
  | VisF (inl1 e) k =>
      match e,k with
      | ext_chose n, k => ChoiceV n (fun x => cTauI (cTauI (cTauI (embed (k x)))))
      end
  | VisF (inr1 e) k => CTreeDefinitions.vis e (fun x => cTauI (cTauI (cTauI (embed (k x)))))
  end.

Lemma unfold_embed {E X} (t : itree (_ +' E) X) : (embed t ≅ embed_ t)%ctree.
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
    + destruct e.
      cbn.
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

Lemma trans_embed_inv E X : forall (t1 : itree (ExtChoice +' E) X) l t2',
    trans l (embed t1) t2' ->
    (exists r : X, (t2' ≅ CTree.stuckI)%ctree /\ l = val r)
    \/ exists t2, (t2' ~ embed t2)%ctree.
Proof.
  unfold trans.
  intros * TR.
  cbn in TR; red in TR.
  remember (embed t1) as et1.
  cut (
      ((et1 ≅ embed t1)%ctree \/ (et1 ≅ cTauI (embed t1))%ctree) ->
      (exists r : X, (t2' ≅ CTree.stuckI)%ctree /\ l = val r)
      \/ exists t2 : itree (ExtChoice +' E) X, t2' ~ embed t2).
  intros H; eapply H; eauto; left; subst; auto.
  clear Heqet1.
  revert t1.
  dependent induction TR.
  - intros ? EQ.
    destruct EQ as [EQ | EQ].
    + rewrite unfold_embed in EQ.
      step in EQ.
      rewrite <- x in EQ.
      destruct (iobserve t1) eqn:EQ1; try now inv EQ.
      * dependent induction EQ.
        specialize (REL x0).
        specialize (IHTR _ _ eq_refl eq_refl t).
        edestruct IHTR; eauto.
      * destruct e.
        destruct e; inv EQ.
        inv EQ.
    + step in EQ.
      rewrite <- x in EQ.
      clear x et1.
      dependent induction EQ.
      specialize (REL x0).
      specialize (IHTR _ _ eq_refl eq_refl t1).
      edestruct IHTR; auto.
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
      destruct e.
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
    assert (t2' ≅ Choice false 0 k)%ctree by (step; now rewrite x).
    setoid_rewrite H.
    clear t2' x H.
    destruct EQ as [EQ | EQ].
    + rewrite (ctree_eta et1), <- x0 in EQ.
      clear et1 x0.
      rewrite unfold_embed in EQ.
      destruct (iobserve t1) eqn:EQ1; try now step in EQ; inv EQ.
      * dependent induction EQ.
        left; eexists; split; eauto.
        rewrite choiceI0_always_stuck; reflexivity.
      * destruct e; [destruct e |]; step in EQ; inv EQ.
    + step in EQ; rewrite <- x0 in EQ; inv EQ.
Qed.

Inductive productive {E X} : itree E X -> Prop :=
| prod_ret {r t} (EQ: eq_itree eq t (Ret r)) : productive t
| prod_vis {Y} {e : E Y} {k t} (EQ: eq_itree eq t (Vis e k)) : productive t
| prod_tau {u t} (EQ: eq_itree eq t (Tau u)) (PROD : productive u) : productive t.

#[global] Instance eq_itree_productive {E X} : Proper (eq_itree eq ==> flip impl) (@productive E X).
Proof.
  intros t u EQ PR.
  revert t EQ.
  induction PR; intros.
  - eapply prod_ret.
    rewrite EQ0; eauto.
  - eapply prod_vis.
    rewrite EQ0; eauto.
  - eapply prod_tau.
    rewrite EQ0; eauto.
    apply IHPR.
    reflexivity.
Qed.

Lemma embed_trans_productive_aux E X : forall l t (T u : ctree E X),
    trans l T u ->
    (equ eq T (embed t) \/ equ eq T (cTauI (embed t))) ->
    productive t.
Proof.
  intros * TR EQ.
  unfold trans in TR.
  cbn in TR; red in TR.
  CTreeDefinitions.genobs T oT.
  CTreeDefinitions.genobs u ou.
  revert T HeqoT u Heqou t EQ.
  induction TR; intros.
  - subst.
    destruct EQ as [EQ | EQ].
    + rewrite ctree_eta, <- HeqoT in EQ.
      rewrite itree_eta.
      rewrite unfold_embed in EQ.
      destruct (iobserve t0); try now step in EQ; inv EQ.
      * eapply prod_tau; [reflexivity|].
        eapply IHTR.
        reflexivity.
        reflexivity.
        step in EQ; dependent induction EQ.
        specialize (REL x).
        auto.
      * destruct e; [destruct e |]; step in EQ; inv EQ.
    + specialize (IHTR _ eq_refl _ eq_refl).
      rewrite ctree_eta, <- HeqoT in EQ.
      step in EQ; dependent induction EQ.
      specialize (REL x).
      apply IHTR.
      auto.
  - destruct EQ as [EQ | EQ].
    + rewrite itree_eta.
      rewrite ctree_eta, <- HeqoT in EQ.
      rewrite unfold_embed in EQ.
      destruct (iobserve t0); try now step in EQ; inv EQ.
      destruct e; [destruct e|]; eapply prod_vis; eauto.
    + rewrite itree_eta.
      rewrite ctree_eta, <- HeqoT in EQ.
      step in EQ; inv EQ.
  - destruct EQ as [EQ | EQ].
    + rewrite itree_eta.
      rewrite ctree_eta, <- HeqoT in EQ.
      rewrite unfold_embed in EQ.
      destruct (iobserve t0); try now step in EQ; inv EQ.
      destruct e0; [destruct e0|]; eapply prod_vis; eauto.
    + rewrite itree_eta.
      rewrite ctree_eta, <- HeqoT in EQ.
      step in EQ; inv EQ.
  - destruct EQ as [EQ | EQ].
    + rewrite itree_eta.
      rewrite ctree_eta, <- HeqoT in EQ.
      rewrite unfold_embed in EQ.
      destruct (iobserve t); try now step in EQ; inv EQ.
      eapply prod_ret; eauto.
      eapply prod_vis; eauto.
    + rewrite itree_eta.
      rewrite ctree_eta, <- HeqoT in EQ.
      step in EQ; inv EQ.
Qed.

Lemma embed_trans_productive E X : forall l t (u : ctree E X),
    trans l (embed t) u ->
    productive t.
Proof.
  intros * TR.
  eapply embed_trans_productive_aux; eauto.
Qed.

Lemma embed_eutt {E X}:
  Proper (eutt eq ==> sbisim) (@embed E X).
Proof.
  unfold Proper,respectful.
  coinduction ? CIH.
  symmetric using idtac.
  - intros * HR * EQ.
    apply HR; symmetry; assumption.
  - intros t u EUTT.
    cbn; intros * TR.
    pose proof embed_trans_productive TR as PROD.
    revert u TR EUTT.
    induction PROD.
    + intros.
      rewrite EQ in EUTT,TR.
      rewrite unfold_embed in TR; cbn in TR.
      pose proof trans_ret_inv TR as (EQ' & ->).
      punfold EUTT; cbn in EUTT; red in EUTT.
      remember (iobserve (iRet r)) as ot;
        remember (iobserve u) as ou.
      revert u Heqou.
      induction EUTT; subst; pclearbot; try now inv Heqot.
      * intros.
        inv Heqot.
        eexists.
        rewrite unfold_embed, <- Heqou.
        etrans.
        reflexivity.
      * intros.
        edestruct IHEUTT; try reflexivity.
        eexists.
        rewrite unfold_embed, <- Heqou.
        apply trans_tauI, trans_tauI.
        eauto.
        eauto.
    + intros.
      rewrite EQ in EUTT,TR.
      rewrite unfold_embed in TR; cbn in TR.
      destruct e.
      * destruct e.
        apply trans_choiceV_inv in TR; destruct TR as (? & EQ' & ->).
        punfold EUTT; cbn in EUTT; red in EUTT.
        remember (iobserve (iVis (inl1 (ext_chose n)) k)) as ot;
          remember (iobserve u) as ou.
        revert u Heqou.
        induction EUTT; subst; try now inv Heqot.
        ** intros.
           dependent induction Heqot.
           eexists.
           rewrite unfold_embed, <- Heqou.
           etrans.
           rewrite EQ'.
           rewrite !sb_tauI.
           apply CIH.
           pclearbot; apply REL.
        ** intros.
           edestruct IHEUTT; try reflexivity.
           eexists.
           rewrite unfold_embed, <- Heqou.
           apply trans_tauI, trans_tauI.
           eauto.
           eauto.
      * apply trans_vis_inv in TR; destruct TR as (? & EQ' & ->).
        punfold EUTT; cbn in EUTT; red in EUTT.
        remember (iobserve (iVis (inr1 e) k)) as ot;
          remember (iobserve u) as ou.
        revert u Heqou.
        induction EUTT; subst; try now inv Heqot.
        ** intros.
           dependent induction Heqot.
           eexists.
           rewrite unfold_embed, <- Heqou.
           etrans.
           rewrite EQ'.
           rewrite !sb_tauI.
           apply CIH.
           pclearbot; apply REL.
        ** intros.
           edestruct IHEUTT; try reflexivity.
           eexists.
           rewrite unfold_embed, <- Heqou.
           apply trans_tauI, trans_tauI.
           eauto.
           eauto.
    + intros.
      rewrite EQ in EUTT,TR.
      rewrite unfold_embed in TR; cbn in TR.
      do 2 apply trans_tauI_inv in TR.
      apply IHPROD.
      auto.
      rewrite tau_eutt in EUTT; auto.
Qed.

(*
  t1  ≈  u1

 [t1] -r> stuck
--------------
 [u1] -r> stuck

 *)

(* Lemma trans_eutt : forall E X (t1 u1 : itree (ExtChoice +' E) X) l t2', *)
(*     t1 ≈ u1 -> *)
(*     trans l (embed t1) t2' -> *)
(*     exists u2', *)
(*       trans l (embed u1) u2' /\ t2' ~ u2'. *)
(* Admitted. *)

(* Lemma trans_eutt' : forall E X (t1 u1 : itree (ExtChoice +' E) X), *)
(*     t1 ≈ u1 -> *)
(*     embed t1 ~ embed u1. *)
(*   intros. *)
(*   step. *)
(*   split; cbn; intros ? ? ?. *)
(*   edestruct trans_eutt; eauto. *)
(*   intuition; eexists; eauto. *)
(*   symmetry in H. *)
(*   edestruct trans_eutt; eauto. *)
(*   intuition; eexists; eauto. *)
(*   symmetry. eauto. *)

(* Lemma foo: (forall E X (t u : itree (_ +' E) X), embed t ~ embed u -> t ≈ u). *)
(* Admitted. *)

(* Lemma bar: forall E X (t1 u1 : itree (ExtChoice +' E) X) l t2', *)
(*     trans l (embed t1) t2' -> *)
(*     t1 ≈ u1 -> *)
(*     exists U2 t2 u2, *)
(*       trans l (embed u1) U2 /\ *)
(*         U2 ~ embed u2 /\ *)
(*         (t2' ~ embed t2)%ctree /\ *)
(*         t2 ≈ u2. *)
(* Proof. *)
(*   intros * TR EUTT. *)
(*   pose proof trans_eutt EUTT. *)
(*   step in H; destruct H as [F _]; edestruct F as [u2' TR' BIS']; eauto. *)
(*   (* pose proof trans_eutt EUTT TR as (u2' & TR' & BIS'). *) *)
(*   pose proof trans_embed_inv _ TR. *)
(*   pose proof trans_embed_inv _ TR'. *)
(*   edestruct H as [?  | (t2 & EQ2)]; cycle -1. *)
(*   edestruct H0 as [? | (u2 & EQ2')]; cycle -1. *)
(*   { *)
(*     clear H H0. *)
(*     exists u2',t2,u2; split; [| split; [| split]]; auto. *)
(*     apply foo. *)
(*     rewrite <- EQ2, <- EQ2'; auto. *)

(* Lemma bar E X : *)
(*   forall (t1 u1 : itree (ExtChoice +' E) X) l t2', *)
(*     trans l (embed t1) t2' -> *)
(*     t1 ≈ u1 -> *)
(*     (exists U2 u2, *)
(*         trans l (embed u1) U2 /\ U2 ~ (embed u2) /\ *)
(*           (t2' ~ embed t2)%ctree /\ *)
(*           t2 ≈ u2) \/ *)
(*       ((t2' ≅ CTree.stuckI)%ctree /\ *)
(*          trans l (embed u1) CTree.stuckI). *)
(* Proof. *)
(*   intros * TR EUTT. *)
(*   pose proof trans_eutt EUTT TR as (u2' & TR' & BIS'). *)
(*   (* clear EUTT. *) *)
(*   pose proof trans_embed_inv _ TR. *)
(*   pose proof trans_embed_inv _ TR'. *)
(*   edestruct H as [?  | (t2 & EQ2)]; cycle -1. *)
(*   edestruct H0 as [? | (u2 & EQ2')]; cycle -1. *)
(*   { *)
(*     left. *)
(*     clear H H0. *)


(* Lemma bar E X : forall (t1 u1 : itree (ExtChoice +' E) X) l t2', *)
(*     trans l (embed t1) t2' -> *)
(*     t1 ≈ u1 -> *)
(*     (exists t2 u2, *)
(*         trans l (embed u1) (embed u2) /\ *)
(*           (t2' ~ embed t2)%ctree /\ *)
(*           t2 ≈ u2) \/ *)
(*       ((t2' ≅ CTree.stuckI)%ctree /\ *)
(*          trans l (embed u1) CTree.stuckI). *)
(* Proof. *)
(*   intros * TR EUTT. *)
(*   pose proof trans_eutt EUTT TR as (u2' & TR' & BIS'). *)
(*   (* clear EUTT. *) *)
(*   pose proof trans_embed_inv _ TR. *)
(*   pose proof trans_embed_inv _ TR'. *)
(*   edestruct H as [?  | (t2 & EQ2)]; cycle -1. *)
(*   edestruct H0 as [? | (u2 & EQ2')]; cycle -1. *)
(*   { *)
(*     left. *)
(*     clear H H0. *)


(*     as [(r & STUCK & EQ) | (t2 & EQ)]; eauto. *)
(*   - subst l. rewrite STUCK in TR'. *)
(*     right; split; auto. *)
(*     (* clear t2' STUCK. *) *)
(*     (* revert u1 TR. *) *)
(*     (* unfold trans in TR; cbn in TR; red in TR. *) *)
(*     (* remember (embed t1) as et1. *) *)
(*     admit. *)
(*   - edestruct trans_embed_inv as [(r & STUCK & EQ) | (t2 & EQ)]; eauto. *)


(*     intros u1 EUTT. *)
(*       (* match type of Heqot1 with *) *)
(*       (* | ?u = ?t => let eq := fresh "EQ" in assert (eq : u ~ t) by (subst; reflexivity); clear Heqot1 *) *)
(*       (* end. *) *)
(*     cut ( *)
(*         ((et1 ≅ embed t1)%ctree \/ (et1 ≅ cTauI (embed t1))%ctree) -> *)
(*         trans (val r) (embed u1) CTree.stuckI *)
(*       ). *)
(*     intros H; apply H; left; subst; auto. *)
(*     clear Heqet1. *)
(*         (* eq2equ Heqot1. *) *)
(*     revert u1 t1 EUTT. *)
(*     dependent induction TR; intros * EUTT EQ. *)
(*     + specialize (IHTR _ _ eq_refl eq_refl eq_refl). *)
(*       destruct EQ as [EQ | EQ]. *)
(*       * rewrite ctree_eta, <- x, unfold_embed in EQ. *)
(*         eapply IHTR. *)
(*         reflexivity. *)
(*         destruct (iobserve t1) eqn:EQ'; try now step in EQ; inv EQ. *)
(*         ** step in EQ; dependent induction EQ. *)
(*            specialize (REL x0). *)
(*            right; rewrite REL. *)
(*            step. *)
(*            constructor. *)
(*            intros ?. *)
(*            admit. *)
(*       * step in EQ; dependent induction EQ. *)
(*         rewrite itree_eta, EQ', tau_eutt in EUTT. *)
(*         eapply IHTR. *)
(*         auto. *)
(*         reflexivity. *)
(*         auto. *)
(*         specialize (REL x0). *)

(*   (*       apply REL. *) *)
(*   (*       rewrite unfold_embed in TR. *) *)
(*   (*       cbn in TR; red in TR. *) *)
(*   (*       dependent induction TR; intros * EQ. *) *)
(*   (*   + destruct (iobserve t1) eqn:EQ'; try now inv x. *) *)
(*   (*     dependent induction EQ. *) *)
(*   (*     rewrite unfold_embed. *) *)
(*   (*     inv EQ. *) *)
(*   (*     * apply trans_ret. *) *)



(*   (*   revert TR. *) *)
(*   (*   punfold H. *) *)
(*   (*   cbn in H; red in H. *) *)
(*   (*   dependent induction H. *) *)
(*   (*   + rewrite 2 unfold_embed, <- x, <- x0. *) *)
(*   (*     intros TRANS. *) *)
(*   (*     apply trans_ret_inv in TRANS as [EQ _]. *) *)
(*   (*     apply val_eq_inv in EQ; subst. *) *)
(*   (*     apply trans_ret. *) *)
(*   (*   + rewrite 2 unfold_embed, <- x, <- x0. *) *)
(*   (*     intros TRANS. *) *)
(*   (*     apply *) *)
(*   (*     apply trans_ret_inv in TRANS as [EQ _]. *) *)
(*   (*     apply val_eq_inv in EQ; subst. *) *)
(*   (*     apply trans_ret. *) *)


(*   (*   punfold H; red in H; cbn in H. *) *)
(*   (*   revert u1 H. *) *)
(*   (*   rewrite unfold_embed in TR. *) *)
(*   (*   cbn in TR; red in TR. *) *)
(*   (*   dependent induction TR; intros * EQ. *) *)
(*   (*   + destruct (iobserve t1) eqn:EQ'; try now inv x. *) *)
(*   (*     dependent induction EQ. *) *)
(*   (*     rewrite unfold_embed. *) *)
(*   (*     inv EQ. *) *)
(*   (*     * apply trans_ret. *) *)

(*   (* cbn in TR; red in TR. *) *)
(*   (* remember (embed t1) as et1. *) *)
(*   (* eq2equ Heqet1. *) *)
(*   (* rewrite ctree_eta in EQ. *) *)
(*   (* setoid_rewrite (ctree_eta t2'). *) *)
(*   (* revert t1 EQ u1. *) *)
(*   (* induction TR. *) *)
(*   (* - intros * EQ * EUTT. *) *)
(*   (*   admit. *) *)
(*   (* - intros * EQ * EUTT. *) *)
(*   (*   punfold EUTT. *) *)
(*   (*   red in EUTT; cbn in EUTT. *) *)
(*   (*   rewrite unfold_embed in EQ. *) *)
(*   (*   destruct (iobserve t1) eqn:EQt1; try now step in EQ; inv EQ. *) *)
(*   (*   destruct (iobserve u1) eqn:EQu1; try now inv EUTT. *) *)
(*   (*   + destruct e. *) *)
(* Admitted. *)



Lemma embed_eutt {E X}:
  Proper (eutt eq ==> sbisim) (@embed E X).
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



      destruct (bar _ _ _ _ _ _ TR REL) as (U2 & t2 & u2 & TR' & EQ2 & EQ2' & EUTT2).

      eexists.
      rewrite unfold_embed.
      rewrite <- Heqou.
      apply trans_tauI, trans_tauI.
      eauto.
      rewrite EQ2'.
      rewrite EQ2.
      apply CIH.

      assert(bar: forall E X (t1 u1 : itree (ExtChoice +' E) X) l t2',
                trans l (embed t1) t2' ->
                t1 ≈ u1 ->
                exists t2 u2,
                  trans l (embed u1) (embed u2) /\
                    (t2' ~ embed t2)%ctree /\
                    t2 ≈ u2).
      admit.

      destruct (bar _ _ _ _ _ _ TR REL) as (t2 & u2 & TR' & EQ2 & EUTT2).
      * eexists.
        rewrite unfold_embed, <- Heqou.
        apply trans_tauI, trans_tauI.
        eauto.
        rewrite EQ2.
        apply CIH, EUTT2.
      * exists CTree.stuckI.
        2:setoid_rewrite EQ2; reflexivity.
        rewrite unfold_embed, <- Heqou.
        apply trans_tauI, trans_tauI.
        auto.


      destruct (bar TR REL) as [(t2 & u2 & TR' & EQ2 & EUTT2) | (EQ2 & TR2)].
      * eexists.
        rewrite unfold_embed, <- Heqou.
        apply trans_tauI, trans_tauI.
        eauto.
        rewrite EQ2.
        apply CIH, EUTT2.
      * exists CTree.stuckI.
        2:setoid_rewrite EQ2; reflexivity.
        rewrite unfold_embed, <- Heqou.
        apply trans_tauI, trans_tauI.
        auto.


    + pclearbot.
      destruct e.
      * destruct e.
        apply trans_choiceV_inv in TR as (u' & EQ & ->).
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
Definition partial_inject {E X} : ctree E X -> itree E (option X) :=
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
Admitted.

Variant is_detF {E X} (is_det : ctree E X -> Prop) : ctree E X -> Prop :=
| Ret_det : forall x, is_detF is_det (CTreeDefinitions.Ret x)
| Vis_det : forall {Y} (e : E Y) k,
	(forall y, is_det (k y)) ->
	is_detF is_det (CTreeDefinitions.Vis e k)
| Tau_det : forall t,
	(is_det t) ->
	is_detF is_det (CTreeDefinitions.TauI t)
.

Definition is_det {E X} := paco1 (@is_detF E X) bot1.
