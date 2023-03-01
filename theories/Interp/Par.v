From ITree Require Import
     Core.Subevent.

From CTree Require Import
     CTree
     Fold
     Eq
     Take.

Set Implicit Arguments.

Import CTreeNotations.
Local Open Scope ctree_scope.

(*| Unique thread identifiers |*)

(*| Thread IDs are a product of an effect [E] with a [uid] |*)
Variant parE : Type -> Type :=
  | Switch (i: nat): parE unit.

Definition switch {E C} `{parE -< E} (i: nat): ctree E C unit :=
  trigger (Switch i).

Definition preempt{E C X}`{B1 -< C} (i: nat)(cycles: nat)(a: ctree E C X): ctree (E +' parE) C (ctree E C X) :=
  trigger (inr1 (Switch i)) ;; translate inl1 (take cycles a).

Lemma unfold_0_preempt{E C X}`{B1 -< C}(i: nat) (t: ctree E C X):
  preempt i 0 t ≅ trigger (inr1 (Switch i)) ;; Ret t.
Proof.
  intros; unfold preempt.
  upto_bind_eq.
  rewrite unfold_0_take, translate_ret.
  reflexivity.
Qed.

Lemma unfold_Sn_preempt{E C X}`{B1 -< C}: forall (i: nat) (n: nat) (t: ctree E C X),
    preempt i (S n) t ≅ trigger (inr1 (Switch i)) ;;
    match observe t with
    | RetF x => Ret (Ret x)
    | VisF e k => Vis (inl1 e) (fun i => translate inl1 (take n (k i))) 
    | BrSF c k => Br true c (fun i => translate inl1 (take n (k i))) 
    | BrDF c k => Br false c (fun i => translate inl1 (take (S n) (k i)))
    end.
Proof.
  intros; unfold preempt.
  upto_bind_eq.
  rewrite unfold_take, unfold_translate.
  desobs t; auto; destruct vis; reflexivity.
Qed.

