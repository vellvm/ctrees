(* begin hide *)

From Coq Require Export
  List
  Strings.String.

From ITree Require Import
	Basics.Basics
	Core.Subevent
	Interp.Handler	
	Indexed.Sum
	Events.Exception.
 
From CTree Require Import 
	Utils
	CTrees
 	Interp
	Bisim.

Import CTreeNotations.
Open Scope ctree_scope.

(* end hide *)


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

(* Event signature *)

Variant ActionE : Type -> Type :=
	| Act (a : action) : ActionE unit.
Variant SynchE : Type -> Type := Tau : SynchE unit.

Definition DeadE := exceptE unit.
Definition dead {A : Type} {E} `{DeadE -< E} : ctree E A :=
	x <- trigger (Throw tt);; match x: void with end.

Definition ccsE : Type -> Type := (ActionE +' SynchE +' DeadE).

Definition ccsT := ctree ccsE.

Definition ccs := ccsT unit.

Section Combinators.

	Definition done : ccs := Ret tt.

	Definition prefix (a : action) : ccs := trigger (Act a).

	Definition plus (P Q : ccs) : ccs := Sanity.fork2 P Q.

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

 (* TODO: define basically the theory of handlers for ctrees, all the constructions are specialized to itrees *)

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
      | ForkF k => Fork (fun i => get_hd (k i))
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
					then Sanity.fork3 (vis Tau (fun _ => F P' Q')) (vis (Act a) (fun _ => F P' Q)) (vis (Act b) (fun _ => F P Q'))
					else Sanity.fork2 (vis (Act a) (fun _ => F P' Q)) (vis (Act b) (fun _ => F P Q'))
				| Some a, None => Sanity.fork2 (vis (Act a) (fun _ => F P' Q)) (vis Tau (fun _ => F P Q'))
				| None, Some b => Sanity.fork2 (vis Tau (fun _ => F P' Q)) (vis (Act b) (fun _ => F P Q'))
				| None, None =>   Sanity.fork2 (vis Tau (fun _ => F P' Q)) (vis Tau (fun _ => F P Q'))
				end
			end	.
				
End Combinators.