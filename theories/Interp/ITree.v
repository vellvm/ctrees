From Paco Require Import paco.

From CTree Require Import
	   CTree Eq Interp.Internalize Interp.FoldCTree.

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
Definition embed' {E} : itree E ~> ctree E (B01) := interp h_embed.
Definition embed {E C} : itree (C +' E) ~> ctree E (B01 +' C) :=
  fun _ t => internalize (embed' t).

Notation "t '-' l '→' u" := (trans l t u)
                              (at level 50, only printing,
                                format "t  '-' l '→'  u").

Notation "t '-' l '→' u" := (transR l t u)
                              (at level 50, only printing,
                                format "t  '-' l '→'  u").

#[local] Notation iobserve  := observe.
#[local] Notation _iobserve := _observe.
#[local] Notation cobserve  := CTreeDefinitions.observe.
#[local] Notation _cobserve := CTreeDefinitions._observe.
#[local] Notation iRet x    := (Ret x).
#[local] Notation iVis e k  := (Vis e k).
#[local] Notation iTau t    := (Tau t).
#[local] Notation cRet x    := (CTreeDefinitions.Ret x).
#[local] Notation cGuard t   := (CTreeDefinitions.Guard t).
#[local] Notation cVis e k  := (CTreeDefinitions.Vis e k).

(** Unfolding of [interp]. *)
Definition _interp {E F C R} `{B1 -< C} (f : E ~> ctree F C) (ot : itreeF E R _)
  : ctree F C R :=
  match ot with
  | RetF r => CTreeDefinitions.Ret r
  | TauF t => cGuard (interp f t)
  | VisF e k => CTree.bind (f _ e) (fun x => cGuard (interp f (k x)))
  end.

Lemma unfold_interp_ctree {E F C X} `{B1 -< C} (h: E ~> ctree F C) (t : itree E X):
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

#[global] Instance embed_eq {E C X}:
	Proper (eq_itree eq ==> equ eq) (@embed E C X).
Proof.
	unfold Proper, respectful.
	coinduction r CIH.
	intros t u bisim. unfold embed, embed', internalize.
  rewrite 2 unfold_interp_ctree.
  rewrite 2 FoldCTree.unfold_interp.
	punfold bisim.
	inv bisim; pclearbot; try easy.
	- cbn*.
    constructor; intros ?.
    step.
    cbn*.
    constructor; intros ?.
    now apply CIH.
	- cbn.
    upto_bind_eq.
    constructor; intros ?.
    rewrite 2 FoldCTree.unfold_interp.
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
  | RetF r => CTreeDefinitions.Ret r
  | TauF t => cGuard (cGuard (embed t))
  | VisF (inl1 e) k =>
      match e,k with
      | c, k => brS c (fun x => cGuard (cGuard (cGuard (embed (k x)))))
      end
  | VisF (inr1 e) k => CTreeDefinitions.vis e (fun x => cGuard (cGuard (cGuard (embed (k x)))))
  end.

Lemma unfold_embed {E C X} (t : itree (C +' E) X) : (embed t ≅ embed_ t)%ctree.
Proof.
  unfold embed, embed', internalize at 1.
  rewrite unfold_interp_ctree, FoldCTree.unfold_interp.
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
      rewrite FoldCTree.unfold_interp; cbn.
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
      rewrite FoldCTree.unfold_interp; cbn.
      rewrite Equ.unfold_bind at 1.
      step; cbn; constructor; intros ?.
      rewrite Equ.bind_ret_l.
      step; cbn; constructor; intros ?.
      auto.
Qed.

Lemma trans_embed_inv E C X : forall (t1 : itree (C +' E) X) l t2',
    trans l (embed t1) t2' ->
    (exists r : X, (t2' ≅ stuckD)%ctree /\ l = val r)
    \/ exists t2, (t2' ~ @embed E C X t2)%ctree.
Proof.
  unfold trans.
  intros * TR.
  cbn in TR; red in TR.
  remember (embed t1) as et1.
  cut (
      ((et1 ≅ embed t1)%ctree \/ (et1 ≅ cGuard (embed t1))%ctree) ->
      (exists r : X, (t2' ≅ stuckD)%ctree /\ l = val r)
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
      eexists; rewrite !sb_guard.
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
      rewrite !sb_guard.
      reflexivity.
    + rewrite (ctree_eta et1), <- x1 in EQ;
        clear et1 x1.
      step in EQ; inv EQ.
  - intros * EQ.
    assert (t2' ≅ br false branch0 k)%ctree by (step; now rewrite x).
    setoid_rewrite H.
    clear t2' x H.
    destruct EQ as [EQ | EQ].
    + rewrite (ctree_eta et1), <- x0 in EQ.
      clear et1 x0.
      rewrite unfold_embed in EQ.
      destruct (iobserve t1) eqn:EQ1; try now step in EQ; inv EQ.
      * dependent induction EQ.
        left; eexists; split; eauto.

        rewrite brD0_always_stuck; reflexivity.
      * destruct e; step in EQ; inv EQ.
    + step in EQ; rewrite <- x0 in EQ; inv EQ.
Qed.

(* TODO THIS IS REDUNDANT WITH THE DEF IN FOLDCTREE! *)
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

Lemma embed_trans_productive_aux E C X : forall l t (T u : ctree E (B01 +' C) X),
    trans l T u ->
    (equ eq T (embed t) \/ equ eq T (cGuard (embed t))) ->
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
      * destruct e; step in EQ; inv EQ.
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
      destruct e; eapply prod_vis; eauto.
    + rewrite itree_eta.
      rewrite ctree_eta, <- HeqoT in EQ.
      step in EQ; inv EQ.
  - destruct EQ as [EQ | EQ].
    + rewrite itree_eta.
      rewrite ctree_eta, <- HeqoT in EQ.
      rewrite unfold_embed in EQ.
      destruct (iobserve t0); try now step in EQ; inv EQ.
      destruct e0; eapply prod_vis; eauto.
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

Lemma embed_trans_productive E C X : forall l t (u : ctree E (B01 +' C) X),
    trans l (embed t) u ->
    productive t.
Proof.
  intros * TR.
  eapply embed_trans_productive_aux; eauto.
Qed.

Lemma embed_eutt {E C X}:
  Proper (eutt eq ==> sbisim eq) (@embed E C X).
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
        do 2 eexists; split; [|split].
        rewrite unfold_embed, <- Heqou.
        etrans.
        all: reflexivity.
      * intros.
        edestruct IHEUTT; try reflexivity.
        destruct H as (? & ? & ? & ->).
        do 2 eexists; split; [|split].
        rewrite unfold_embed, <- Heqou.
        apply trans_guard, trans_guard; eauto.
        assumption.
        reflexivity.
    + intros.
      rewrite EQ in EUTT,TR.
      rewrite unfold_embed in TR; cbn in TR.
      destruct e.
      * apply trans_brS_inv in TR; destruct TR as (? & EQ' & ->).
        punfold EUTT; cbn in EUTT; red in EUTT.
        remember (iobserve (iVis (inl1 c) k)) as ot;
          remember (iobserve u) as ou.
        revert u Heqou.
        induction EUTT; subst; try now inv Heqot.
        ** intros.
           dependent induction Heqot.
           do 2 eexists; split; [|split].
           rewrite unfold_embed, <- Heqou.
           etrans.
           rewrite EQ'.
           rewrite !sb_guard.
           apply CIH.
           pclearbot; apply REL.
           reflexivity.
        ** intros.
           edestruct IHEUTT; try reflexivity.
           destruct H as (? & ? & ? & ->).
           do 2 eexists; split; [|split].
           rewrite unfold_embed, <- Heqou.
           apply trans_guard, trans_guard.
           eauto.
           assumption.
           reflexivity.
      * apply trans_vis_inv in TR; destruct TR as (? & EQ' & ->).
        punfold EUTT; cbn in EUTT; red in EUTT.
        remember (iobserve (iVis (inr1 e) k)) as ot;
          remember (iobserve u) as ou.
        revert u Heqou.
        induction EUTT; subst; try now inv Heqot.
        ** intros.
           dependent induction Heqot.
           do 2 eexists; split; [|split].
           rewrite unfold_embed, <- Heqou.
           etrans.
           rewrite EQ'.
           rewrite !sb_guard.
           apply CIH.
           pclearbot; apply REL.
           reflexivity.
        ** intros.           
           edestruct IHEUTT; try reflexivity.
           destruct H as (? & ? & ? & ->).
           do 2 eexists; split; [|split].
           rewrite unfold_embed, <- Heqou.
           apply trans_guard, trans_guard.
           eauto.
           assumption.
           reflexivity.
    + intros.
      rewrite EQ in EUTT,TR.
      rewrite unfold_embed in TR; cbn in TR.
      do 2 apply trans_guard_inv in TR.
      apply IHPROD.
      auto.
      rewrite tau_eutt in EUTT; auto.
Qed.

(* Other things to consider if time permitted:
   - partial inverse
   - embedded itrees are internally deterministic
 *)

(* Maybe simpler to just write a coinductive relation *)
(*Definition partial_inject {E X} : ctree E X -> itree E (option X) :=
	cofix _inject t :=
	 match CTreeDefinitions.observe t with
	| CTreeDefinitions.RetF x => Ret (Some x)
	| @BrF _ _ _ _ n t =>
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

Variant is_detF {E C X} `{B1 -< C} (is_det : ctree E C X -> Prop) : ctree E C X -> Prop :=
| Ret_det : forall x, is_detF is_det (CTreeDefinitions.Ret x)
| Vis_det : forall {Y} (e : E Y) k,
	(forall y, is_det (k y)) ->
	is_detF is_det (CTreeDefinitions.Vis e k)
| Tau_det : forall t,
	(is_det t) ->
	is_detF is_det (CTreeDefinitions.Guard t).

Definition is_det {E C X} `{B1 -< C} := paco1 (@is_detF E C X _) bot1.
