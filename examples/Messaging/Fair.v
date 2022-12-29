From ITree Require Import
     Basics
     Subevent
     Events.State
     Indexed.Sum.

From Coq Require Import
     Nat
     List
     Logic.Eqdep
     Classes.RelationClasses
     Program.Tactics.

From Equations Require Import Equations.

From ExtLib Require Import
     RelDec
     Monad
     Option.

From Coinduction Require Import
     coinduction rel tactics.

From CTree Require Import
     CTree
     Eq
     Interp.Fold
     Interp.FoldStateT
     Interp.Log
     Interp.Network
     Logic.Ctl.

Import CTreeNotations ListNotations Log CtlNotations Monads Network.  
Local Open Scope ctree_scope.

Set Implicit Arguments.
Set Contextual Implicit.
Set Asymmetric Patterns.

Module Fair.

  (** Compose [k] with itself [i] times. *)
  Fixpoint frepeat {E C X}
           (i: nat) (k: ctree E C X): ctree E C X :=
    match i with
    | 0 => k
    | S n => k ;; frepeat n k
    end.

  (** This is not associative, consider
      (A || B) || C ~ A || (B || C)
   
      The sequence [B, C] is impossible for the left,
      as it will do [B, B, ..., B, A] by picking [B] then [C].
      But it is possible for the right, by taking the branch [B]. *)
        
  Definition parafair{E C X}
             `{BN -< C} `{B1 -< C} `{B2 -< C} `{B0 -< C}
             (a b: ctree E C X): ctree E C void :=
    CTree.forever
      (brD2
         (i <- branch false (branchN) ;;
          frepeat i a ;;
          b)
         
         (i <- branch false (branchN) ;;
          frepeat i b ;;
          a)).

  Variant ID: Type -> Type :=
    | Index: nat -> ID unit.

  Definition id{C}(n: nat): ctree ID C unit := trigger (Index n).

  (* Ignore [t], label observation equals [e] *)
  Inductive obs_eq {E C: Type -> Type}{X Y: Type} :
    E Y -> ctree E C X -> @label E -> Prop :=
  | ObsEq y : forall t e, obs_eq e t (obs e y).

  #[global] Instance proper_obs_eq_equ {E C: Type -> Type} {X Y} (e: E Y) {HasStuck: B0 -< C} :
    Proper (@equ E C X X eq ==> eq ==> iff) (@obs_eq E C X Y e).
  Proof.
    unfold Proper, respectful, impl; cbn.      
    intros x y EQ ? ? <-; split; intro OBS; inv OBS; econstructor; now rewrite EQ.
  Qed.
  (** TODO: This would be more simply stated and without [ID] 
      and [obs_eq] as

    forall l (t1 t2: ctree ID C void),
      (parafair t1 t2), l |= AG (AF (fun l t => t ≅ t1)) /\
      (parafair t1 t2), l |= AG (AF (fun l t => t ≅ t2)),
  *)

  Lemma para_fair {C}
        `{HBN: BN -< C} `{HB1: B1 -< C} `{HB2: B2 -< C} `{HB0: B0 -< C}:
    forall l (t: ctree ID C void),
      t = parafair (id 0) (id 1) ->
      t, l |= AG (AF (obs_eq (Index 0))).
  Proof.
    intros; revert l.
    unfold ag; subst; coinduction R CIH; intro l.
    split.
    (* Eventually [ID = 0] shows up *)
    - unfold parafair.
      rewrite ctl_af_ax; right.
      
      rewrite ctree_eta; cbn; fold_subst.
      unfold ax; intros; inv_trans_one.
      (* Never use [trans_bind_inv_l] it loses the target label and introduces a new one! *)
      destruct x;
        apply trans_bind_inv in TR as [(HV & t3 & TR & ?) | (l2 & TRV  & TR )].
      + apply trans_bind_inv in TR as [(HV' & t4 & TR & ?) | (l3 & TRV'  & TR' )].
        * apply trans_brD_inv in TR as (niter & TR).
          apply trans_ret_inv in TR as (ST & ->).
          exfalso; apply HV; econstructor. (* Not a val! *)
        * eapply trans_val_inv in TRV'. (* Nothing to do with TRV *)
          clear TRV'.
          (* [t3] is [id 0]^+ *)
          destruct l3; cbn in *.
          (* [0] iterations = [id 0] *)
          apply trans_bind_inv in TR' as [(HV'' & t4 & TR & ?) | (l3 & TRV'  & TR )].
          
          
  Admitted.
  
 
End Fair.
  


