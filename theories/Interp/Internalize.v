From CTree Require Import
     CTree Eq Interp.Interp.

Set Implicit Arguments.
Set Contextual Implicit.

(* Import CTreeNotations. *)

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

  Lemma internalize_ret {R} (r : R) : internalize (Ret r) ≅ Ret r.
  Proof.
    unfold internalize.
    rewrite interp_ret. (* Why is it slow? *)
    reflexivity.
  Qed.

  Lemma internalize_bind {R S} (t : ctree _ R) (k : R -> ctree _ S) :
    internalize (t >>= k) ≅ internalize t >>= (fun x => internalize (k x)).
  Proof.
    unfold internalize.
    rewrite interp_bind. (* Why is it slow? *)
    reflexivity.
  Qed.

End Internalize.
Arguments ext_chose n : clear implicits.

