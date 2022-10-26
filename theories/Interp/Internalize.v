From CTree Require Import
     CTree Eq Interp.Interp.

From ITree Require Import
     Subevent
     CategoryOps.

Set Implicit Arguments.
Set Contextual Implicit.

Import CTreeNotations.

Section Internalize.
  Variable E C : Type -> Type.
  Variable ExtBr : Type -> Type.
  Context `{B1 -< C}.

  Print Coercions.
  (* LEF: Some reason the instance resolution doesn't coerce [ExtBr >-> C +' ExtBr] *)
  Definition internalize_h:  ExtBr ~> ctree E (C +' ExtBr) :=
    fun _ e => CTree.branch true 
                         (@subevent ExtBr (sum1 C ExtBr)
                                    (@CategoryOps.ReSum_inr (forall _ : Type, Type) IFun sum1 Cat_IFun Inr_sum1 ExtBr ExtBr C
                                                            (@CategoryOps.ReSum_id (forall _ : Type, Type) IFun Id_IFun ExtBr)) _ e).


  Definition internalize_h' : ExtBr +' E ~> ctree E (C +' ExtBr) :=
    fun _ e => match e with
            | inl1 e => internalize_h e
            | inr1 e => trigger e
            end.
  
  Definition internalize : ctree (ExtBr +' E) C ~> ctree E (C +' ExtBr) :=
    interpE internalize_h'.

  Lemma internalize_ret {R} (r : R) : internalize (Ret r) ≅ Ret r.
  Proof.
    unfold internalize.
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
