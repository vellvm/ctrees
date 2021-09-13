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

Notation ccsE := (ActionE +' SynchE +' DeadE).

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
	| HDone 
	| Hsynch (P : ccs)
	| Hact (a : action) (P : ccs).

	Variant head' :=
	| HDone' 
	| HVis (obs : {X : Type & ccsE X}).

(* Construction site, currently a mess

	Variable get_hd : ccs -> ccsT head'.

  Definition para : ccs -> ccs -> ccs. 
		refine (cofix F (P : ccs) (Q : ccs) := _).
			refine (rP <- get_hd P;;
			rQ <- get_hd Q;; 
				match rP, rQ with 
				| HDone', HDone' => done
				| HDone', _ => _
				| _, _ => _
				end	
				).

			match rP, rQ with
				| HDone, HDone => done
				| HDone, HAct b Q' => vis (Act b) (fun _ => F P Q')
				| HDone, HSynch Q' => vis Synch   (fun _ => F P Q')
				| HAct a P', HDone => vis (Act a) (fun _ => F P' Q)
				| HSynch P', HDone => vis Synch   (fun _ => F P' Q)
				| HAct a P', HAct b Q' =>
					if are_opposite a b
					then
						branch3 (vis (Act a) (fun _ => F P' Q))
										(vis (Act b) (fun _ => F P Q'))
										(vis Synch   (fun _ => F P' Q'))
					else
						branch2 (vis (Act a) (fun _ => F P' Q))
										(vis (Act b) (fun _ => F P Q'))
				| HAct a P', HSynch Q' =>
					branch2 (vis (Act a) (fun _ => F P' Q))
									(vis Synch   (fun _ => F P Q'))
				| HSynch P', HAct a Q' =>
					branch2 (vis Synch   (fun _ => F P' Q))
									(vis (Act a) (fun _ => F P Q'))
				| HSynch P', HSynch Q' =>
					branch2 (vis Synch   (fun _ => F P' Q))
									(vis Synch   (fun _ => F P Q'))
				end.

  Definition get_sched_hd : ccs -> ccsT head. 
    refine (cofix get_hd (P : ccs) := _).
		
      refine (match observe P with
      | RetF x => Ret HDone
      | @VisF _ _ _ T e k => _
      | ForkF k => Fork (fun x => get_hd (k x))
			end).


			admit.
			refine .

        match e with
        | schedP e => vis e (fun x => get_hd (k x))
        | actP e =>
          match e in ActionE X return (T = X -> ccsT head) with
          | Act a => fun (Pf : T = unit) =>
                      Ret (HAct a (@eq_rect_r _ T (fun T => T -> itree ccsE unit) k unit (eq_sym Pf) tt))
          end eq_refl
        | synchP e =>
          match e in SynchE X return (T = X -> ccsT head) with
          | Synch => fun (Pf : T = unit) =>
                      Ret (HSynch (@eq_rect_r _ T (fun T => T -> itree ccsE unit) k unit (eq_sym Pf) tt))
          end eq_refl
        | deadP e => Ret HDone
        end
      end
  .

*)

End Combinators.