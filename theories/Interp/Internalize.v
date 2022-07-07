From CTree Require Import
     CTree Eq Interp.Interp.

Set Implicit Arguments.
Set Contextual Implicit.

Import CTreeNotations.

Section Internalize.
  Variable E : Type -> Type.

  Variant ExtBr : Type -> Type :=
    | ext_chose n : ExtBr (Fin.t n).
  Arguments ext_chose n : clear implicits.

  Definition internalize_h {E} : ExtBr ~> ctree E :=
    fun _ '(ext_chose n) => CTree.br true n.

  Definition internalize_h' {E} : ExtBr +' E ~> ctree E :=
    fun _ e => match e with
            | inl1 e => internalize_h e
            | inr1 e => trigger e
            end.

  Definition internalize : ctree (ExtBr +' E) ~> ctree E :=
    interp internalize_h'.

  Lemma internalize_ret {R} (r : R) : internalize (Ret r) ≅ Ret r.
  Proof.
    unfold internalize.
    rewrite interp_ret.
    reflexivity.
  Qed.

  Lemma internalize_bind {R S} (t : ctree _ R) (k : R -> ctree _ S) :
    internalize (t >>= k) ≅ internalize t >>= (fun x => internalize (k x)).
  Proof.
    unfold internalize.
    rewrite interp_bind.
    reflexivity.
  Qed.

End Internalize.
Arguments ext_chose n : clear implicits.
