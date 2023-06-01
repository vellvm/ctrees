From Coq Require Import
     Lia
     Bool
     Nat.

From ExtLib Require Import
     Structures.Monad
     Structures.MonadState
     Data.Monads.StateMonad.

From CTree Require Import
     CTree
     Equ
     Fold
     FoldCTree
     FoldStateT
     Logic.Kripke
     Logic.Ctl.

Import CTree CTreeNotations CtlNotations.
Local Open Scope nat_scope.
Local Open Scope ctl_scope.
Local Open Scope ctree_scope.

(*| Bounded choice by pigeonhole |*)
Section ChoiceB.

  (** bound *)
  Context (n: nat).

  (** flip coin *)
  Variant choiceE: Type -> Type :=
  | Flip: choiceE bool.
  
  (** Interpret to counters of true/false flips *)
  Definition h_choiceE {B: Type -> Type} `{B0 -< B} `{B1 -< B} `{B2 -< B}: choiceE ~> ctree (stateE (nat * nat)) B :=
    fun X e =>
      '(t, f) <- get;;
      match e in choiceE Y return X = Y -> ctree (stateE (nat * nat)) B Y with
      | Flip =>
          fun _: X = bool =>
            if andb (t <=? n) (f <=? n) then
              brD2
                (put (t+1, f);;
                 Ret true)
                (put (t, f+1);;
                 Ret false)
            else
              if andb (n <? t) (n <? f) then
                stuckD
              else
                if n <? t then
                  put (t, f+1) ;;
                  Ret false
                else
                  put (t+1, f);;
                  Ret true
      end eq_refl.

End ChoiceB.

Section LawBN.
  Context {B: Type -> Type} {X: Type} {HB0: B0 -< B} {HB1: B1 -< B} {HB2: B2 -< B}.
  Notation "t , s |= φ " := (@entailsF (stateE (nat * nat)%type) B bool (nat * nat) (@handler_stateE (nat*nat)) HB0 φ t s) (in custom ctl at level 80,
                                                                                                                φ custom ctl,
                                                                                                                right associativity).
  Notation interp := (@interp choiceE B (ctree (stateE (nat *nat)) B) _ _ _ _).
  Definition beacon : ctree choiceE B bool := forever (fun _ => trigger Flip) false.

  (** Only four cases in ordering of [a,b] around a number [n] *)
  Lemma quat_nat_dec: forall (n a b: nat),
      (a <= n /\ b <= n) \/ (a <= n /\ b > n) \/ (a > n /\ b <= n) \/ (a > n /\ b > n).
  Proof. lia. Qed.

  Lemma quat_nat_bool: forall (n a b: nat),
      ((a <=? n) = true /\ (b <=? n) = true) \/
        ((a <=? n) = true /\ (n <? b) = true) \/
        ((n <? a) = true /\ (b <=? n) = true) \/
        ((n <? a) = true /\ (n <? b) = true).
  Proof.
    intros.
    destruct (quat_nat_dec n a b); destruct H; intros.
    - left; split.                      
      + destruct (PeanoNat.Nat.leb_spec0 a n); auto.
      + destruct (PeanoNat.Nat.leb_spec0 b n); auto.
    - right; left; split; inv H.
      + destruct (PeanoNat.Nat.leb_spec0 a n); auto.
      + destruct (PeanoNat.Nat.ltb_spec0 n b); auto.
    - inv H; inv H0; right; right;
        [left | right]; split.
      + destruct (PeanoNat.Nat.ltb_spec0 n a); auto.
      + destruct (PeanoNat.Nat.leb_spec0 b n); auto.
      + destruct (PeanoNat.Nat.ltb_spec0 n a); auto.
      + destruct (PeanoNat.Nat.ltb_spec0 n b); auto.
  Qed.

  (** Prove I eventually get [true] forall [n] *)
  Lemma law_big_numbers : forall (n: nat),
      <( {interp (h_choiceE n) beacon}, {(0,0)} |= AF (now {fun '(t, _) => t > 0}) )>.
  Proof.
    Opaque entailsF.
    intro n.
    induction n; unfold beacon; rewrite unfold_interp; unfold h_choiceE; cbn;
      rewrite !bind_bind; fold_subst; unfold get; rewrite bind_trigger.
    - next; right.
      Transparent entailsF. unfold entailsF. cbn.
      unfold get.
      intros.
      intros.
  Admitted.
End LawBN.
