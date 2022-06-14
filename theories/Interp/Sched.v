From ExtLib Require Import
     Structures.Functor
     Structures.Monad.

From CTree Require Import
     Eq.

Import ITree.Basics.Basics.Monads.
Import MonadNotation.
Open Scope monad_scope.

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

Variant pureb {E X} (rec : ctree E X -> Prop) : ctree' E X -> Prop :=
  | pure_ret   (v : X) : pureb rec (RetF v)
  | pure_delay n k (REC: forall v, rec (k v)) : pureb rec (ChoiceIF n k).
#[global] Hint Constructors equb: core.

Definition pureb_ {E X} rec (t : ctree E X) := pureb rec (observe t).

Program Definition fpure {E R} : mon (ctree E R -> Prop) := {|body := pureb_|}.
Next Obligation.
  red in H0 |- *.
  inversion_clear H0; econstructor; auto.
Qed.

Definition pure {E R} := gfp (@fpure E R).

(* Definition schedule_pure {E} (hV hI : forall n, fin n) : ctree E ~> ctree E := *)
(*   schedule (fun n => Ret (h n)). *)


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
               | 1 => Ret (m, Fin.F1)
               | S (S n) => (Ret (S m, @Fin.of_nat_lt (Nat.modulo m (S (S n))) _ _))
               end
         )).
  apply (NPeano.Nat.mod_upper_bound).
  auto with arith.
Defined.
