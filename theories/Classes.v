From ExtLib Require Import
  Structures.Functor.
From CTree Require Import Utils.

(*| [iter]: A primitive for general recursion.
    Iterate a function updating an accumulator [I], until it produces
    an output [R]. |*)
Polymorphic Class MonadIter (M : Type -> Type) : Type :=
  iter : forall {R I: Type}, (I -> M (I + R)%type) -> I -> M R.

(*| [mbr] Branch monad |*)
Polymorphic Class MonadBr (M : Type -> Type) : Type :=
  mbr : forall (n: nat), M (fin (S n)).

(*| Greatest fixpoint of [k] |*)
Definition forever {M: Type -> Type} {MF: Functor M} {IT: MonadIter M} {X}
  (k: X -> M X): X -> M X  :=
  fun x => iter (fun x => fmap inl (k x)) x.

