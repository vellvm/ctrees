(* begin hide *)
From ExtLib Require Import
     Structures.Functor
     Structures.Monad.

From ITree Require Import
	Basics.Basics.
 
From CTree Require Import 
		 Utils CTrees Bisim.

Import CTreeNotations.
Open Scope ctree_scope.

(* end hide *)

Definition translateF {E F R} (h : E ~> F) (rec: ctree E R -> ctree F R) (t : ctreeF E R _) : ctree F R  :=
	match t with
		| RetF x => Ret x
		| VisF e k => Vis (h _ e) (fun x => rec (k x))
		| ForkF n k => Fork n (fun x => rec (k x))
	end.
		
Definition translate {E F} (h : E ~> F) : ctree E ~> ctree F
	:= fun R => cofix translate_ t := translateF h translate_ (observe t).
		
Arguments translate {E F} h [T].
		
(** ** Interpret *)
		
(** An event handler [E ~> M] defines a monad morphism
		[ctree E ~> M] for any monad [M] with a loop operator. *)
		
Definition interp {E M : Type -> Type}
					 {FM : Functor M} {MM : Monad M} {IM : MonadIter M} {FoM : MonadFork M}
					 (h : E ~> M) :
			ctree E ~> M := fun R =>
			iter (fun t =>
				match observe t with
				| RetF r => ret (inr r)
				| VisF e k => fmap (fun x => inl (k x)) (h _ e)
				| @ForkF _ _ _ n k => bind (fork n) (fun x => ret (inl (k x)))
				end).
		
Arguments interp {E M FM MM IM FoM} h [T].
