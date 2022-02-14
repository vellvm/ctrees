From ITree Require Import ITree.

From CTree Require Import
     Utils CTrees Interp.

Set Implicit Arguments.
Set Contextual Implicit.

Section Internalize.
  Variable E : Type -> Type.

  Variant ExtChoice : Type -> Type :=
    | ext_chose n : ExtChoice (Fin.t n).
  Arguments ext_chose n : clear implicits.

  Definition internalize_h {E} : ExtChoice ~> ctree E :=
    fun _ '(ext_chose n) => CTree.choice true n.

  Definition internalize_h' {E} : ExtChoice +' E ~> ctree E :=
    fun _ e => match e with
            | inl1 e => internalize_h e
            | inr1 e => trigger e
            end.

  Definition internalize : ctree (ExtChoice +' E) ~> ctree E :=
    interp internalize_h'.

End Internalize.

