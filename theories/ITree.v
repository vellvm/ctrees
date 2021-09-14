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
	 match t with 
	| Ret x => CTrees.Ret x
	| Tau t => CTrees.Tau (_embed t)
	| Vis e k => CTrees.Vis e (fun x => _embed (k x))
	 end. 

Lemma embed_eq {E X}: 
	Proper (eq_itree eq ==> equ eq) (@embed E X).
Admitted.

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


