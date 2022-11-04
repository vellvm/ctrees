From CTree Require Import
     CTree Eq Interp.Interp.

Set Implicit Arguments.
Set Contextual Implicit.

Import CTreeNotations.

Section Internalize.
  Variable E C : Type -> Type.
  Variable ExtBr : Type -> Type.
  Context `{B1 -< C}.

  Definition internalize_h:  ExtBr ~> ctree E (C +' ExtBr) :=
    fun _ e => (CTree.branch true (subevent _ e)).  

  Definition internalize_h' : ExtBr +' E ~> ctree E (C +' ExtBr) :=
    fun _ e => match e with
            | inl1 e => internalize_h e
            | inr1 e => trigger e
            end.

  #[local] Instance MonadBr_ctree {E C D} `{C -< D}: MonadBr C (ctree E D) :=
    fun b _ e => CTree.branch b (@subevent C D _ _ e).

  Definition internalize : ctree (ExtBr +' E) C ~> ctree E (C +' ExtBr) :=
    interpE internalize_h'.

  Lemma internalize_ret {R} (r : R) : internalize (Ret r) ≅ Ret r.
  Proof.
    unfold internalize.
    Set Printing All.
    rewrite interp_ret.
    reflexivity.
  Qed.

  Lemma internalize_bind {R S} (t : ctree _ _ R) (k : R -> ctree _ _ S) :
    internalize (t >>= k) ≅ internalize t >>= (fun x => internalize (k x)).
  Proof.
    unfold internalize.
    rewrite interp_bind.
    reflexivity.
  Qed.

End Internalize.
