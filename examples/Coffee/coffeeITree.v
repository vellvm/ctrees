From ITree Require Import ITree Eq.Eq Basics.Monad.
From CTreeCoffee Require Import propt.
From Coq Require Import Relations Morphisms Program.
Require Import Paco.paco.
Import ITreeNotations.
Open Scope itree.

Variant E : Type -> Type :=
  | Coin      : E unit
  | ReqTea    : E unit
  | ReqCoffee : E unit
  | Tea       : E unit
  | Coffee    : E unit
.

Variant C : Type -> Type :=
  | choice : C bool.

Notation state := (itree (C +' E) void).

Definition choose (t u : state) : state :=
  b <- trigger choice;;
  if b:bool then t else u.

Definition vending : state :=
  cofix F :=
    trigger Coin;;
    choose
      (trigger ReqTea;;
       vis Tea (fun _ => F))
      (trigger ReqCoffee;;
       vis Coffee (fun _ => F))
.

Definition reapoff : state :=
  cofix F :=
    choose
    (trigger Coin;;
     trigger ReqTea;;
     vis Tea (fun _ => F))
    (trigger Coin;;
     trigger ReqCoffee;;
     vis Coffee (fun _ => F))
.

Definition h_choose {E} : C ~> PropT E :=
  fun _ 'choice t => t ≅ Ret true \/ t ≅ Ret false.

Definition trigger_prop : E ~> PropT E :=
  fun R e => fun t => t = r <- trigger e ;; Ret r.

Definition ℑ : itree (C +' E) ~> PropT E :=
  fun R => interp_prop (case_ h_choose trigger_prop) _ eq.
Arguments ℑ [_] t.

Notation "P ≡ Q" := (eq1 (ℑ P) (ℑ Q)) (at level 50).

Theorem undistinguishable : vending ≡ reapoff.
Proof.
  split.
  - intros t u eq; split.
    + revert t u eq.
      pcofix CIH; intros * eq.
      punfold eq.
      red in eq; cbn in eq.
      rewrite (itree_eta t).
      genobs u ou.
      revert u Heqou.
      induction eq; intros; subst; auto.
      * exfalso.
        punfold H0. 2: apply interp_PropT__mono.
        red in H0. cbn in H0. dependent induction H0.
        cbn in *.
        red in HTA.
        subst.
        cbn in eq2. rewrite Eq.bind_bind in eq2.
      (* This is absurd, but it's hell to manipulate *)
        admit.
      * rewrite tau_eutt in H0.
        pfold.
Admitted.


