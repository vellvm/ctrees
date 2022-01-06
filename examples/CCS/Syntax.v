From Coq Require Export
  List
  Strings.String.


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

  (* We consider CCS with guarded choice for now *)
  Inductive term : Type :=
  | DoneT : term
  | TauT (P : term)
  | ActionT (a : action) (P : term)
  | ParaT (P1 P2 : term)
  | PlusT (P1 P2 : term)
  | RestrictT (c : chan) (P : term).

End Syntax.

Module CCSNotations.

  Declare Scope ccs_scope.

  Infix "=?" := eqb_action : ccs_scope.
  Notation "0" := DoneT : ccs_scope.
  Notation "a · P" := (ActionT a P) (at level 10) : ccs_scope.
  (* Notation "τ ⋅ P" := (TauT P) (at level 10) : ccs_scope. *)
  Notation "P ∥ Q" := (ParaT P Q) (at level 29, left associativity) : ccs_scope.
  Notation "P ⊕ Q" := (PlusT P Q) (at level 28, left associativity) : ccs_scope.
  Notation "P ∖ c" := (RestrictT c P) (at level 10) : ccs_scope.
  Notation "↑" := Send.
  Notation "↓" := Rcv.

End CCSNotations.

Import CCSNotations.
Open Scope ccs_scope.
Open Scope string.

Section Ex.

  Definition a := "a".
  Definition b := "b".

  Definition ex P Q : term :=
    ((↑a · P ⊕ ↑b · 0) ∥ ↓a · Q) ∖ a.

End Ex.

