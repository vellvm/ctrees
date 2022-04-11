From ExtLib Require Import
     Structures.Functor
     Structures.Monad.

From CTree Require Import
     CTree Eq.

Import ITree.Basics.Basics.Monads.
Import MonadNotation.
Open Scope monad_scope.

#[global] Instance ctree_trigger {E} : MonadTrigger E (ctree E) :=
  @CTree.trigger _.

#[global] Instance stateT_trigger {E S M} {MM : Monad M} {MT: MonadTrigger E M} :
  MonadTrigger E (stateT S M) :=
  fun _ e s => v <- mtrigger _ e;; ret (s, v).

Definition schedule {E M : Type -> Type}
					 {FM : Functor M} {MM : Monad M} {IM : MonadIter M} {FoM : MonadTrigger E M}
					 (h : forall n, M (fin n)) :
	ctree E ~> M :=
  fun R =>
		iter (fun t =>
				    match observe t with
				    | RetF r => ret (inr r)
				    | @ChoiceF _ _ _ _ n k => bind (h n) (fun x => ret (inl (k x)))
				    | VisF e k => bind (mtrigger _ e) (fun x => ret (inl (k x)))
				    end).

Definition schedule_cst {E} (h : forall n, fin n) : ctree E ~> ctree E :=
  schedule (fun n => Ret (h n)).

Definition round_robin {E} : ctree E ~> stateT nat (ctree E).
  refine (schedule
            (fun n m =>
               (* m: branch to be scheduled
                  n: arity of the new node
                *)
               match n as n' return (ctree E (nat * fin n')) with
               | O => CTree.stuckI
               | S n => (Ret (S m, @Fin.of_nat_lt (Nat.modulo m (S n)) _ _))
               end
         )).
  apply (NPeano.Nat.mod_upper_bound).
  auto with arith.
Defined.


