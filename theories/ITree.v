From CTree Require Import 
	CTrees Equ
	 (* Bisim *)
  .

From ITree Require Import 
	ITree Eq.

From Coq Require Import 
	Morphisms Program.

From Paco Require Import paco. 

From Coinduction Require Import 
	coinduction rel tactics.

Open Scope ctree.

(* Temporary due to bug in the reification *)
Unset Universe Checking.

Definition embed {E X} : itree E X -> ctree E X :=
	cofix _embed t := 
	 match observe t with 
	| RetF x => CTrees.Ret x
	| TauF t => CTrees.Tau (_embed t)
	| VisF e k => CTrees.Vis e (fun x => _embed (k x))
	 end. 
 
Notation "'_embed' ot" :=
	(match ot with 
	| RetF x => CTrees.Ret x
	| TauF t => CTrees.Tau (embed t)
	| VisF e k => CTrees.Vis e (fun x => embed (k x))
 end) (at level 50, only parsing). 

Lemma embed_unfold {E X} (t : itree E X) :
	equ eq (embed t) (_embed (observe t)).
Proof.
	now step.
Qed.

#[local] Notation iobserve := observe.
#[local] Notation _iobserve := _observe.
#[local] Notation cobserve := CTrees.observe.
#[local] Notation _cobserve := CTrees._observe.
#[local] Notation iRet x   := (Ret x).
#[local] Notation iVis e k := (Vis e k).
#[local] Notation iTau t   := (Tau t).
#[local] Notation cRet x   := (CTrees.Ret x).
#[local] Notation cTau t   := (CTrees.Tau t).
#[local] Notation cVis e k := (CTrees.Vis e k).

Lemma equF_vis_invT {E X Y S} (e1 : E X) (e2 : E Y) (k1 : X -> ctree E S) k2 :
  equF eq (equ eq) (CTrees.VisF e1 k1) (CTrees.VisF e2 k2) ->
  X = Y.
Proof.
  intros EQ. 
	dependent induction EQ; auto.
Qed.

Lemma equF_vis_invE {E X S} (e1 e2 : E X) (k1 k2 : X -> ctree E S) :
  equF eq (equ eq) (CTrees.VisF e1 k1) (CTrees.VisF e2 k2) ->
  e1 = e2 /\ forall x, equ eq (k1 x) (k2 x).
Proof.
  intros EQ.
	inv EQ.
	dependent destruction H; dependent destruction H4; auto.
Qed. 

Lemma equF_fork_invT {E S n m} (k1 : _ -> ctree E S) k2 :
  equF eq (equ eq) (CTrees.ForkF n k1) (CTrees.ForkF m k2) ->
  n = m.
Proof.
  intros EQ. 
	dependent induction EQ; auto.
Qed.

Lemma equF_fork_invE {E S n} (k1 : _ -> ctree E S) k2 :
  equF eq (equ eq) (CTrees.ForkF n k1) (CTrees.ForkF n k2) ->
  forall x, equ eq (k1 x) (k2 x).
Proof.
  intros EQ.
	inv EQ.
	dependent destruction H; auto.
Qed. 

Instance gfp_bt_equ {E R r} :
	 Proper (gfp (@fequ E R R eq) ==> gfp (@fequ E R R eq) ==> flip impl)
	  (bt_equ eq r).
Proof.
	unfold Proper, respectful, flip, impl.
	intros.
	pose proof (gfp_bt (fequ eq) r).	
	etransitivity; [|etransitivity]; [|apply H1 |].
	apply H2; assumption.
	apply H2; symmetry; assumption.
Qed.	

Lemma embed_eq {E X}: 
	Proper (eq_itree eq ==> equ eq) (@embed E X).
Proof.
	unfold Proper, respectful.
	coinduction r CIH.	
	intros t u bisim.
	rewrite 2 embed_unfold. 
	punfold bisim.
	inv bisim; pclearbot; try easy.
	- constructor; intros _.
		apply CIH, REL.
	- constructor; intros.
		apply CIH, REL.
Qed.

Lemma embed_eutt {E X}: 
	Proper (eutt eq ==> bisim eq) (@embed E X).
Admitted.

(* Maybe simpler to just write a coinductive relation *)
Definition partial_inject {E X} : ctree E X -> itree E (option X) :=
	cofix _inject t := 
	 match CTrees.observe t with 
	| CTrees.RetF x => Ret (Some x)
	| @ForkF _ _ _ n t => 
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
	Proper (bisim eq ==> eutt (option_rel eq)) (@partial_inject E X).
Admitted.

Variant is_detF {E X} (is_det : ctree E X -> Prop) : ctree E X -> Prop :=
| Ret_det : forall x, is_detF is_det (CTrees.Ret x)	
| Vis_det : forall {Y} (e : E Y) k,
	(forall y, is_det (k y)) ->
	is_detF is_det (CTrees.Vis e k)	
| Tau_det : forall t,
	(is_det t) ->
	is_detF is_det (CTrees.Tau t)	
.

Definition is_det {E X} := paco1 (@is_detF E X) bot1.


