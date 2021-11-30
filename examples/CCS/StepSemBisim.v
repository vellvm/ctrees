From ITree Require Import ITree.

From CTree Require Import
	Utils
	CTrees
	Interp
	Equ
	Bisim.

From CTreeCCS Require Import 
	Syntax
	Denotation.

From Coinduction Require Import
	coinduction rel tactics.

Import CCSNotations.
Import DenNotations.
Open Scope ccs_scope.

Definition strongc : term -> term -> Prop :=
	fun P Q => ⟦P⟧ ≈ ⟦Q⟧.

Definition hide_tau : SynchE ~> ctree (ActionE +' DeadE) :=
	fun _ 'Tau => CTrees.TauI (Ret tt).

Definition h_tau : ccsE ~> ctree (ActionE +' DeadE) :=
  case_ctree hide_tau h_trigger.

Definition weakc : term -> term -> Prop :=
	fun P Q => interp h_tau ⟦P⟧ ≈ interp h_tau ⟦Q⟧.

(*
Goal weakc (TauT (↑a ⋅ 0) ⊕ ↑b ⋅ 0) (↑a ⋅ 0 ⊕ ↑b ⋅ 0).
unfold weakc, bisim.
Arguments model : simpl never.
step. constructor.
- intros. cbn in *.
	inv H; dependent induction H2; cbn in *.
	inv H3; dependent induction H1; cbn in *.
	destruct x.
	+ inv H2; dependent induction H1; cbn in *.
	  inv H3; dependent induction H1; cbn in *.
	  inv H2; dependent induction H3; cbn in *.
		specialize (H4 tt).
		
*)

(* 
Definition weak : term -> term -> Prop :=
	fun P Q => interp h ⟦P⟧ ≈ interp h ⟦Q⟧. *)


(*
P ~ P' -> Q ~ Q' -> P + Q ~ P' + Q'

bisim_bisim corresponds strong operational bisimulation
	 if you then interp Tau into "choice 1", do you get weak operational bisimulation

	 weak (τ.a + b) (a + b)  ???
	 weak (τ.a + τ.b) (τ.(a + b))  ???

*)

Definition forward (R : term -> term -> Prop) : Prop :=
	forall P a P' Q, 
		R P Q ->
		P ⊢ a →sem P' -> 
	exists Q', Q ⊢ a →sem Q' /\ R P' Q'.

Definition backward (R : term -> term -> Prop) : Prop :=
	forall P a Q Q', 
		R P Q ->
		Q ⊢ a →sem Q' -> 
	exists P', P ⊢ a →sem P' /\ R P' Q'.

Definition bisim_step : term -> term -> Prop :=
	fun P Q => exists R, forward R /\ backward R /\ R P Q.

Theorem bisim_equiv : forall P Q, strongc P Q <-> bisim_step P Q.
Proof.
	(* split.
	- admit.
	- intros (R & FOR & BACK & HR). 
		unfold bisim_bisim, bisim.
		coinduction S IH.
		cbn.
		constructor.
		+ intros * SCHED.
			unfold forward in FOR; clear BACK.
 *)
Admitted.
