(*|
==============
Syntax for ccs
==============
Traditional syntax for ccs with replication and explicit prefix by tau for convenience.

.. coq:: none
|*)

From Coq Require Export
  List
  Strings.String.

(*|
.. coq::
|*)

Section Channels.

	Definition chan : Set := string.

	Variant action : Type :=
   | Send (c : chan) : action
   | Rcv (c : chan) : action.

	Definition op (a : action) : action :=
		match a with
		| Send c => Rcv c
		| Rcv c => Send c
		end.

	Definition eqb_action : action -> action -> bool :=
		fun a b => match a,b with
			| Send c, Send c'
			| Rcv c, Rcv c' => String.eqb c c'
			| _, _ => false
		end .

	Lemma eqb_action_refl : forall a,
		 eqb_action a a = true.
	Proof.
		intros []; cbn; auto using eqb_refl.
	Qed.

	Definition are_opposite (a b : action) : bool :=
		if eqb_action a (op b) then true else false.

End Channels.


Section Syntax.

  Inductive term : Type :=
  | DoneT : term
  | TauT (P : term)
  | ActionT (a : action) (P : term)
  | ParaT (P1 P2 : term)
  | PlusT (P1 P2 : term)
  | RestrictT (c : chan) (P : term)
  | rep (P : term).

End Syntax.

Module CCSNotations.

  Declare Scope term_scope.

  Infix "=?" := eqb_action : term_scope.
  Notation "0" := DoneT : term_scope.
  Notation "a · P" := (ActionT a P) (at level 10) : term_scope.
  Notation "P ∥ Q" := (ParaT P Q) (at level 29, left associativity) : term_scope.
  Notation "P ⊕ Q" := (PlusT P Q) (at level 28, left associativity) : term_scope.
  Notation "P ∖ c" := (RestrictT c P) (at level 10) : term_scope.
  Notation "! P" := (rep P) (right associativity, at level 20): term_scope.
  Notation "↑" := Send : term_scope.
  Notation "↓" := Rcv : term_scope.

End CCSNotations.

Import CCSNotations.
Open Scope term_scope.
Open Scope string.

Section Ex.

  Definition a := "a".
  Definition b := "b".

  Definition ex P Q : term :=
    ((↑a · P ⊕ ↑b · 0) ∥ ↓a · Q) ∖ a.

End Ex.

