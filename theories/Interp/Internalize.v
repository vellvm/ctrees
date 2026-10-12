From CTree Require Import
     CTree Eq Interp.Fold Interp.FoldCTree.

Set Implicit Arguments.
Set Contextual Implicit.
Set Universe Polymorphism.

Import CTreeNotations.

Section Internalize.
  Universes d q d' q'.
  Variable E : Type -> Type.
  Variable C : Type -> Type.
  Variable ExtChoice : Type -> Type.

  Definition internalize_h : ExtChoice ~> @ctree@{_ _ _ _ d' q'} E (C +' ExtChoice) :=
    fun _ e => CTree.branchS (subevent _ e).

  Definition internalize_h' : ExtChoice +' E ~> @ctree@{_ _ _ _ d' q'} E (C +' ExtChoice) :=
    fun _ e => match e with
            | inl1 e => internalize_h e
            | inr1 e => trigger e
            end.

  Definition internalize : @ctree@{_ _ _ _ d q} (ExtChoice +' E) C ~>
      @ctree@{_ _ _ _ d' q'} E (C +' ExtChoice) :=
    interp internalize_h'.

  Lemma internalize_ret {R} (r : R) : internalize (Ret r) ≅ Ret r.
  Proof.
    unfold internalize.
    rewrite FoldCTree.interp_ret.
    reflexivity.
  Qed.

  Lemma internalize_bind {R S} (t : ctree _ _ R) (k : R -> ctree _ _ S) :
    internalize (t >>= k) ≅ internalize t >>= (fun x => internalize (k x)).
  Proof.
    unfold internalize.
    rewrite FoldCTree.interp_bind.
    reflexivity.
  Qed.

End Internalize.
