(*| 
Denotation of [ccs] into [ctree]s
|*)

From Coq Require Export
  List
  Strings.String.

From ITree Require Import ITree.

From CTree Require Import
	Utils
	CTrees
 	Interp
	Equ
	Bisim.

From CTreeCCS Require Import 
	Syntax.

From Coinduction Require Import
	coinduction rel tactics.

Import CTreeNotations.
Open Scope ctree_scope.

(*| Event signature 

Processes can perform actions, synchronizations, or be unresponsive
|*)

Variant ActionE : Type -> Type :=
	| Act (a : action) : ActionE unit.
Variant SynchE : Type -> Type := Tau : SynchE unit.

Variant DeadE : Type -> Type := 
	| throw : DeadE void.

Definition dead {A : Type} {E} `{DeadE -< E} : ctree E A :=
	x <- trigger throw;; match x: void with end.

Definition ccsE : Type -> Type := (ActionE +' SynchE +' DeadE).

Definition ccsT := ctree ccsE.

Definition ccs := ccsT unit.

(*| Process algebra |*)
Section Combinators.

	Definition done : ccs := Ret tt. (* Or should it be Choice 0 ? *)

	Definition prefix (a : action) (P: ccs) : ccs := trigger (Act a);; P.

	Definition plus (P Q : ccs) : ccs := Sanity.choice2 P Q.

  Definition h_trigger {E F} `{E -< F} : E ~> ctree F :=
    fun _ e => trigger e.

  Definition h_restrict_ (c : chan) : ActionE ~> ctree ccsE :=
    fun _ e => let '(Act a) := e in
            match a with
            | Send c'
            | Rcv c' =>
              if (c =? c')%string then dead else trigger e
            end.

	Definition case_ctree {E F G} (f : E ~> ctree G) (g : F ~> ctree G)
		: E +' F ~> ctree G :=
		fun T ab => match ab with
		| inl1 a => f _ a
		| inr1 b => g _ b
		end.

 (* TODO: define basically the theory of handlers for ctrees, all the constructions are specialized to ccs right now *)

  Definition h_restrict c : ccsE ~> ctree ccsE :=
    case_ctree (h_restrict_ c) h_trigger.

  Definition restrict {X} : chan -> ccsT X -> ccsT X :=
    fun c P => interp (h_restrict c) P.

	(* TO THINK : how should the head be wrapped? More concretely, leading to more dirty pattern matching in [get_hd],
	or generically, making get_hd both very generic and simpler, but leading to more work in the parallel composition operator?
	*)
	Variant head :=
	| Hdone
	| Hact (a : option action) (P : ccs).

	Variant head' {E R} :=
	| HDone'
	| HVis (obs : {X : Type & ccsE X & X -> ctree E R}).

  (* Notations for patterns *)
  Notation "'actP' e" := (inl1 e) (at level 10).
  Notation "'synchP' e" := (inr1 (inl1 e)) (at level 10).
  Notation "'deadP' e" :=  (inr1 (inr1 e)) (at level 10).

	Notation "pf ↦ k" := (eq_rect_r (fun T => T -> ccs) k pf tt) (at level 40, k at next level).

  Definition can_synch (a b : option action) : bool :=
		match a, b with | Some a, Some b => are_opposite a b | _, _ => false end.

  Definition get_hd : ccs -> ccsT head :=
    cofix get_hd (P : ccs) :=
      match observe P with
      | RetF x => Ret Hdone
      | @VisF _ _ _ T e k =>
				match e  with
				| actP e   => match e in ActionE X return X = T -> ccsT head with
											| Act a => fun pf => (Ret (Hact (Some a) (pf ↦ k)))
											end eq_refl
				| synchP e => match e in SynchE X return X = T -> ccsT head with
											| Tau => fun pf => (Ret (Hact None (pf ↦ k)))
											end eq_refl
				| deadP e  => dead
				end
      | ChoiceF n k => Choice n (fun i => get_hd (k i))
			end.

  Definition para : ccs -> ccs -> ccs :=
		cofix F (P : ccs) (Q : ccs) :=
			rP <- get_hd P;;
			rQ <- get_hd Q;;
			match rP, rQ with
			| Hdone, Hdone => done
			| Hdone, _ => Q
			| _, Hdone => P
			| Hact a P', Hact b Q' =>
				match a, b with
				| Some a, Some b =>
					if are_opposite a b
					then Sanity.choice3 (vis Tau (fun _ => F P' Q')) (vis (Act a) (fun _ => F P' Q)) (vis (Act b) (fun _ => F P Q'))
					else Sanity.choice2 (vis (Act a) (fun _ => F P' Q)) (vis (Act b) (fun _ => F P Q'))
				| Some a, None => Sanity.choice2 (vis (Act a) (fun _ => F P' Q)) (vis Tau (fun _ => F P Q'))
				| None, Some b => Sanity.choice2 (vis Tau (fun _ => F P' Q)) (vis (Act b) (fun _ => F P Q'))
				| None, None =>   Sanity.choice2 (vis Tau (fun _ => F P' Q)) (vis Tau (fun _ => F P Q'))
				end
			end	.


(*
				-------------------------------------------------
				!(a.P || bara.Q) -τ> (P || Q) || !(a.P || bara.Q)

					Question: is !P ≈ P || !P?
  Definition bang : ccs -> ccs.
*)

End Combinators.

Import CCSNotations.
Open Scope ccs_scope.

(* fun P Q => bisim (model P) (model Q): is this weak bisimulation of CCS?

   -> : term -> term -> Prop
   -ccs> : ccs -> ccs -> Prop as
   -sem> : term -> term -> Prop := fun P Q => model P -ccs> model Q
*)

Fixpoint model (t : term) : ccs :=
	match t with 
	| 0     => done
	| a ⋅ P => prefix a (model P)
	| P ∥ Q => para (model P) (model Q)
	| P ⊕ Q => plus (model P) (model Q)
	| P ∖ c => restrict c (model P)
	end.

Variant step_ccs : ccs -> option action -> ccs -> Prop :=
| Sted_comm : forall (t : ccs) a u k,
	schedule t u ->
  u ≅ trigger (Act a);; k ->
	step_ccs t (Some a) k
| Step_tau : forall (t : ccs) u k,
	schedule t u ->
  u ≅ trigger Tau;; k ->
	step_ccs t None k.

Definition step_sem : term -> option action -> term -> Prop :=
	fun P a Q => step_ccs (model P) a (model Q).

Module DenNotations.

  (* Notations for patterns *)
  Notation "'actP' e" := (inl1 e) (at level 10).
  Notation "'synchP' e" := (inr1 (inl1 e)) (at level 10).
  Notation "'deadP' e" :=  (inr1 (inr1 e)) (at level 10).

  Notation "⟦ t ⟧" := (model t).
  Notation "P '⊢' a '→ccs' Q" := (step_ccs P a Q) (at level 50).
  Notation "P '⊢' a '→sem' Q" := (step_sem P a Q) (at level 50).

End DenNotations.

Import DenNotations.

Notation "pf ↦ k" := (eq_rect_r (fun T => T -> ccs) k pf tt) (at level 40, k at next level).
Notation get_hd_ P :=
  match observe P with
  | RetF x => Ret Hdone
  | @VisF _ _ _ T e k =>
  	match e  with
		| actP e   => match e in ActionE X return X = T -> ccsT head with
									| Act a => fun pf => (Ret (Hact (Some a) (pf ↦ k)))
									end eq_refl
		| synchP e => match e in SynchE X return X = T -> ccsT head with
									| Tau => fun pf => (Ret (Hact None (pf ↦ k)))
									end eq_refl
		| deadP e  => dead
		end
  | ChoiceF n k => Choice n (fun i => get_hd (k i))
  end.

Lemma get_hd_unfold : forall P,
    get_hd P ≅ get_hd_ P.
Proof.
  intros.
	now step.
Qed.

Notation para_ P Q :=
			(rP <- get_hd P;;
			rQ <- get_hd Q;;
			match rP, rQ with
			| Hdone, Hdone => done
			| Hdone, _ => Q
			| _, Hdone => P
			| Hact a P', Hact b Q' =>
				match a, b with
				| Some a, Some b =>
					if are_opposite a b
					then Sanity.choice3 (vis Tau (fun _ => para P' Q')) (vis (Act a) (fun _ => para P' Q)) (vis (Act b) (fun _ => para P Q'))
					else Sanity.choice2 (vis (Act a) (fun _ => para P' Q)) (vis (Act b) (fun _ => para P Q'))
				| Some a, None => Sanity.choice2 (vis (Act a) (fun _ => para P' Q)) (vis Tau (fun _ => para P Q'))
				| None, Some b => Sanity.choice2 (vis Tau (fun _ => para P' Q)) (vis (Act b) (fun _ => para P Q'))
				| None, None =>   Sanity.choice2 (vis Tau (fun _ => para P' Q)) (vis Tau (fun _ => para P Q'))
				end
			end)%ctree.

Lemma para_unfold : forall P Q, para P Q ≅ para_ P Q.
Proof.
  intros.
	now step.
Qed.


