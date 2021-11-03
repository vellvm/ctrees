From CTree Require Import
	Utils
	CTrees
	Interp
	Equ
	Bisim.

From CTreeCCS Require Import 
	Syntax
	Denotation
	Operational.

Import CCSNotations.
Import DenNotations.
Import OpNotations.
Open Scope ccs_scope.


Definition forward (R : term -> term -> Prop) : Prop :=
	forall P a P' Q, 
		R P Q ->
		P ⊢ a →op P' -> 
	exists Q', Q ⊢ a →sem Q' /\ R P' Q'.

Lemma complete : exists R, forward R.
Admitted.

Definition backward (R : term -> term -> Prop) : Prop :=
	forall P a Q Q', 
		R P Q ->
		Q ⊢ a →sem Q' -> 
	exists P', P ⊢ a →op P' /\ R P' Q'.

Lemma correct : exists R, backward R.
Admitted.

Lemma bisim : exists R, backward R /\ forward R.
Admitted.


