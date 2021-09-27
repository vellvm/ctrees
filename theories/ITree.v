From CTree Require Import 
	CTrees Equ Bisim.

From ITree Require Import 
	ITree Eq.

From Coq Require Import 
	Morphisms.

From Paco Require Import 
	paco.

Open Scope ctree.

Definition embed {E X} : itree E X -> ctree E X :=
	cofix _embed t := 
	 match observe t with 
	| RetF x => CTrees.Ret x
	| TauF t => CTrees.Tau (_embed t)
	| VisF e k => CTrees.Vis e (fun x => _embed (k x))
	 end. 
 
(* Definition embed_' {E X} (_embed : itree E X -> ctree E X):
	 itree' E X -> ctree E X :=
		fun t =>
	 match t with 
	| RetF x => CTrees.Ret x
	| TauF t => CTrees.Tau (_embed t)
	| VisF e k => CTrees.Vis e (fun x => _embed (k x))
	 end. 

Definition embed {E X} := cofix F := fun t => @embed_' E X F (observe t). *)

Notation "'_embed' ot" :=
	(match ot with 
	| RetF x => CTrees.Ret x
	| TauF t => CTrees.Tau (embed t)
	| VisF e k => CTrees.Vis e (fun x => embed (k x))
 end) (at level 50, only parsing). 

(* 
		go {observe : itree' itree}

*)

Lemma embed_unfold {E X} : forall (t : itree E X), 
	equ eq (embed t) (_embed (observe t)).
Proof.
	(* pcofix CIH. *)
	intros. pfold. cbn.
	destruct (observe t) eqn:EQ; cbn.
	cbn.
	(* destruct (CTrees.observe (embed t)) eqn:EQ'; cbn. *)
Admitted.	




Global Instance Reflexive_equF {E R RR}:
  Reflexive RR -> Reflexive (@equF E R R RR (upaco2 (equ_ RR) bot2)).
Proof.
	repeat red; intros. reflexivity.
	destruct x; constructor; auto.
	intros; left; auto.
   pcofix CIH. pstep. intros. eapply Reflexive_equF; auto.
Qed.
	
Lemma observing : forall {E X} (t u : ctree E X),
	CTrees.observe t = CTrees.observe u -> equ eq t u.
Proof.
	intros.
	pfold; cbn; rewrite H.
	Unset Printing Notations.

	reflexivity.	

Lemma embed_eq {E X}: 
	Proper (eq_itree eq ==> equ eq) (@embed E X).
Proof.
	repeat red.
	pcofix CIH; intros t u EQ.
	punfold EQ; pstep. cbn.
	inv EQ; try discriminate.	 


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


