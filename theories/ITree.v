From CTree Require Import
	CTrees Trans Equ Bisim CTreesTheory.

From ITree Require Import
	ITree Eq.

From Coq Require Import
	Morphisms Program.

From Paco Require Import paco.

From Coinduction Require Import
	   lattice coinduction rel tactics.

Open Scope ctree.

(* I'm stupid and this is the proper definition of the embedding *)
Definition h_embed {E} : E ~> ctree E :=
  fun _ e => CTree.trigger e.
Definition embed' {E} : itree E ~> ctree E := interp h_embed.

Definition embed {E X} : itree E X -> ctree E X :=
	cofix _embed t :=
	 match observe t with
	| RetF x => CTrees.Ret x
	| TauF t => CTrees.TauI (_embed t)
	| VisF e k => CTrees.Vis e (fun x => _embed (k x))
	 end.

Notation "'_embed' ot" :=
	(match ot with
	| RetF x => CTrees.Ret x
	| TauF t => CTrees.TauI (embed t)
	| VisF e k => CTrees.Vis e (fun x => embed (k x))
 end) (at level 50, only parsing).

Lemma unfold_embed {E X} (t : itree E X) :
	equ eq (embed t) (_embed (observe t)).
Proof.
  now step.
Qed.

#[local] Notation iobserve  := observe.
#[local] Notation _iobserve := _observe.
#[local] Notation cobserve  := CTrees.observe.
#[local] Notation _cobserve := CTrees._observe.
#[local] Notation iRet x    := (Ret x).
#[local] Notation iVis e k  := (Vis e k).
#[local] Notation iTau t    := (Tau t).
#[local] Notation cRet x    := (CTrees.Ret x).
#[local] Notation cTauI t   := (CTrees.TauI t).
#[local] Notation cVis e k  := (CTrees.Vis e k).

Lemma embed_eq {E X}:
	Proper (eq_itree eq ==> equ eq) (@embed E X).
Proof.
	unfold Proper, respectful.
	coinduction r CIH.
	intros t u bisim.
	rewrite 2 unfold_embed.
	punfold bisim.
	inv bisim; pclearbot; try easy.
	- constructor; intros _.
		apply CIH, REL.
	- constructor; intros.
		apply CIH, REL.
Qed.

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

Lemma embed_eutt {E X}:
  Proper (eutt eq ==> sbisim) (@embed E X).
Proof.
  unfold Proper,respectful.
  coinduction ? CIH.
  symmetric using idtac.
  - intros * HR * EQ.
    apply HR; symmetry; assumption.
  - intros * EUTT.
    cbn; intros * TR.
    rewrite unfold_embed in TR.
    punfold EUTT; red in EUTT.
    remember (iobserve y) as oy.
    induction EUTT.
    + eexists; [rewrite unfold_embed, <- Heqoy; subst; apply TR | reflexivity].
    + pclearbot.
      apply CIH in REL.
      (* This almost certainly does not hold, it essentially relies on
         `t b <= b (t b)` which I don't think is valid.
         Question for Damien: how to unfold the companion in an hypothesis at another point that Bot? 
       *)
      assert (sbt R (embed m1) (embed m2)) by admit.
      destruct H as [F _].
      apply trans_TauI_inv in TR.
      apply F in TR as [? ? ?].
      eexists.
      rewrite unfold_embed, <- Heqoy.
      apply trans_TauI.
      apply H.
      auto.
    + pclearbot.
      apply trans_vis_inv in TR as (u' & EQ & ->).
      eexists; [rewrite unfold_embed, <- Heqoy; apply trans_vis |].
      rewrite EQ.
      apply CIH, REL.
    + apply trans_TauI_inv in TR.

Admitted.

(* Maybe simpler to just write a coinductive relation *)
Definition partial_inject {E X} : ctree E X -> itree E (option X) :=
	cofix _inject t :=
	 match CTrees.observe t with
	| CTrees.RetF x => Ret (Some x)
	| @ChoiceF _ _ _ _ n t =>
		(match n as x return n = x -> itree E (option X) with
					 | O => fun _ => Ret None
					 | 1 => fun pf => eq_rect_r
	 													(fun n1 : nat => (Fin.t n1 -> ctree E X) -> itree E (option X))
	 													(fun t2 : Fin.t 1 -> ctree E X => Tau (_inject (t2 Fin.F1)))
	 													pf t
					 | _ => fun _ => Ret None
		 end eq_refl)
	| CTrees.VisF e k => Vis e (fun x => _inject (k x))
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

Lemma partial_inject_eutt {E X} :
	Proper (wbisim ==> eutt (option_rel eq)) (@partial_inject E X).
Admitted.

Variant is_detF {E X} (is_det : ctree E X -> Prop) : ctree E X -> Prop :=
| Ret_det : forall x, is_detF is_det (CTrees.Ret x)
| Vis_det : forall {Y} (e : E Y) k,
	(forall y, is_det (k y)) ->
	is_detF is_det (CTrees.Vis e k)
| Tau_det : forall t,
	(is_det t) ->
	is_detF is_det (CTrees.TauI t)
.

Definition is_det {E X} := paco1 (@is_detF E X) bot1.
