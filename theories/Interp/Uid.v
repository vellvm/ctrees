From Coq Require Import
     Fin
     Nat
     List
     Relations.

From ITree Require Import
     Indexed.Sum
     CategoryOps.

From CTree Require Import
     CTree
     Eq.Equ
     Eq.Trans
     Interp.Fold
     Interp.FoldStateT
     Misc.Vectors
     Core.Utils.

From ExtLib Require Import
     Monad
     Functor.

From RelationAlgebra Require Import
     monoid
     kat
     kat_tac
     prop
     rel
     srel
     comparisons
     rewriting
     normalisation.

Local Open Scope fin_vector_scope.
  
Set Implicit Arguments.

Module Uid.

  (*| Unique thread identifiers |*)
  Notation uid := fin.
  (*| Thread IDs are a product of an effect [E] with a [uid] |*)
  Variant Uid (n: nat) (E: Type -> Type) : Type -> Type :=
    | Frame {X} (e: E X) (i: uid n): Uid n E X.

  Arguments Frame {n} {E} {X}.

  Definition single{E: Type -> Type}: E ~> Uid 1 E :=
    fun R e => Frame e F1.

  Definition forget{n: nat}{E: Type -> Type}: Uid n E ~> E :=
    fun R e => match e return (E _) with Frame e i => e end.
  
  (* Every ctree with no thread identifiers can be injected in the single-threaded ctree *)
  Definition inj_single {E C: Type -> Type}{X: Type}(t: ctree E C X): ctree (Uid 1 E) C X :=
    translate single t.

  Section N.
    Context {n: nat}.
    (* Can forget thread identifiers in order to interpret trees *)
    Definition inj_forget {E C: Type -> Type}{X: Type}(t: ctree (Uid n E) C X): ctree E C X :=
      translate forget t.

    Definition fold_n {E B M : Type -> Type}
               {FM : Functor M} {MM : Monad M} {IM : MonadIter M}
               (h : E ~> M) (g : bool -> B ~> M) :
      ctree (Uid n E) B ~> M := fold (fun R e => @h R (forget e)) g.

    Definition interp_n {E B M : Type -> Type}
               {FM : Functor M} {MM : Monad M} {IM : MonadIter M} {BM : MonadBr B M}
               (h : E ~> M) := fold_n h (fun b _ c => mbr b c).

  End N.    

  Arguments fold_n {n E B M FM MM IM} h g [T].
  Arguments interp_n {n E B M FM MM IM BM} h [T].

  (** Now some ETL *)
  Section Strans.
    Context {C: Type -> Type} {X: Type} (S: Type) (n: nat) `{HasStuck: B0 -< C}.
    Notation T := (ctree (Uid n (stateE S)) C X).
    Notation SS := (@Trans.SS (Uid n (stateE S)) C X).    
    Notation SP := (S -> SS -> Prop).

    (*| Finitely many [tau] and [obs Get s] labels, before getting a [obs (Put s') tt] |*)
    Definition strans(i: uid n)(s s': S): srel SS SS :=
      (cup (trans tau) (trans (obs (Frame (@Get S) i) s)))^* ⋅ trans (obs (Frame (Put s') i) tt).
  End Strans.

End Uid.

