Unset Universe Checking.

From Paco Require Import paco.

From CTree Require Import
	   CTree Eq Interp.Internalize Interp.FoldCTree.

(* Universe issue, TO FIX *)
Unset Universe Checking.
Unset Auto Template Polymorphism.

From ITree Require Import
	   ITree Eq Interp InterpFacts.

From Stdlib Require Import
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
Definition _interp {E F C R} (f : E ~> ctree F C) (ot : itreeF E R _)
  : ctree F C R :=
  match ot with
  | RetF r => CTreeDefinitions.Ret r
  | TauF t => cGuard (interp f t)
  | VisF e k => CTree.bind (f _ e) (fun x => cGuard (interp f (k x)))
  end.

Lemma unfold_interp_ctree {E F C X} (h: E ~> ctree F C) (t : itree E X):
  (interp h t ≅ _interp h (iobserve t))%ctree.
Proof.
  revert t.
  coinduction R CIH.
  intros; cbn.
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
  apply fequ_bind_chain_eq.
  intros ?.
  now constructor.
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
	- cbn.
    constructor.
    now apply CIH.
  - cbn.
    apply fequ_bind_chain_eq; intros.
    rewrite 2 FoldCTree.unfold_interp.
    cbn; constructor.
    step; cbn; constructor.
    apply CIH, REL.
Qed.

From Stdlib Require Import Datatypes.

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
  | TauF t => cGuard (embed t)
  | VisF (inl1 e) k =>
      match e,k with
      | c, k => brS c (fun x => cGuard (cGuard (embed (k x))))
      end
  | VisF (inr1 e) k => CTreeDefinitions.vis e (fun x => cGuard (cGuard (embed (k x))))
  end.

Lemma unfold_embed {E C X} (t : itree (C +' E) X) : (embed t ≅ embed_ t)%ctree.
Proof.
  unfold embed, embed', internalize at 1.
  rewrite unfold_interp_ctree, FoldCTree.unfold_interp.
  cbn.
  destruct (iobserve t) eqn:EQ; cbn; auto.
  - destruct e.
    + cbn.
      rewrite Equ.unfold_bind at 1.
      cbn.
      step; cbn; constructor; intros ?.
      rewrite Equ.bind_step.
      step; cbn; constructor.
      rewrite Equ.bind_ret_l.
      step; cbn; constructor.
      step; cbn; constructor.
      reflexivity.
    + cbn.
      rewrite Equ.unfold_bind at 1.
      cbn.
      step; cbn; constructor; intros ?.
      rewrite Equ.bind_ret_l.
      step; cbn; constructor.
      rewrite FoldCTree.unfold_interp; cbn.
      step; cbn; constructor.
      reflexivity.
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
      eapply prod_vis; reflexivity.
    + specialize (IHTR _ eq_refl _ eq_refl).
      rewrite ctree_eta, <- HeqoT in EQ.
      step in EQ; dependent induction EQ.
  - subst.
    destruct EQ as [EQ | EQ].
    + rewrite ctree_eta, <- HeqoT in EQ.
      rewrite itree_eta.
      rewrite unfold_embed in EQ.
      destruct (iobserve t0); try now step in EQ; inv EQ.
      2:eapply prod_vis; reflexivity.
      inv_equ.
      eapply prod_tau; eauto.
    + specialize (IHTR _ eq_refl _ eq_refl).
      apply IHTR.
      left.
      rewrite ctree_eta, <- HeqoT in EQ.
      now inv_equ.

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
  coinduction r CIH.
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
      remember (iobserve (iRet r0)) as ot;
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
        apply trans_guard; eauto.
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
           apply trans_guard; eauto.
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
           apply trans_guard; eauto.
           assumption.
           reflexivity.
    + intros.
      rewrite EQ in EUTT,TR.
      rewrite unfold_embed in TR; cbn in TR.
      apply trans_guard_inv in TR.
      apply IHPROD.
      auto.
      rewrite tau_eutt in EUTT; auto.
Qed.

(* Other things to consider if time permitted:
   - partial inverse
   - embedded itrees are internally deterministic
 *)
