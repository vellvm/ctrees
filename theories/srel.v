(*******************************************************************)
(*  This is part of RelationAlgebra, it is distributed under the   *)
(*    terms of the GNU Lesser General Public License version 3     *)
(*              (see file LICENSE for more details)                *)
(*                                                                 *)
(*  Copyright 2012: Damien Pous. (CNRS, LIP - ENS Lyon, UMR 5668)  *)
(*******************************************************************)

(** * srel: heterogeneous binary relations between setoids *)

Require Bool.
From RelationAlgebra Require Export boolean prop.
From RelationAlgebra Require Import kat rel.

Set Printing Universes.

Universe U.
Record EqType := {
    type_of:> Type@{U};
    Eq: relation type_of;
    Equivalence_Eq: Equivalence Eq
  }.
#[global] Existing Instance Equivalence_Eq.

Record srel (n m: EqType) := {
    rel_of :> hrel n m;
    srel_Eq: Proper (Eq n ==> Eq m ==> iff) rel_of
  }.
Arguments rel_of {_ _}.
#[global] Existing Instance srel_Eq.

Section s.
 Variables n m: EqType.
 Definition srel_leq (R S: srel n m): Prop := rel_of R ≦ rel_of S.  
 Definition srel_weq (R S: srel n m): Prop := rel_of R ≡ rel_of S.  
 Program Definition srel_cup (R S: srel n m): srel n m := {| rel_of := cup (rel_of R) (rel_of S) |}.
 Next Obligation. now rewrite H, H0. Qed.
 Program Definition srel_cap (R S: srel n m): srel n m := {| rel_of := cap (rel_of R) (rel_of S) |}.
 Next Obligation. now rewrite H, H0. Qed.
 Program Definition srel_neg (R: srel n m): srel n m := {| rel_of := neg (rel_of R) |}.
 Next Obligation. now rewrite H, H0. Qed.
 Program Definition srel_bot: srel n m := {| rel_of := bot |}.
 Next Obligation. tauto. Qed.
 Program Definition srel_top: srel n m := {| rel_of := top |}.
 Next Obligation. tauto. Qed.
 Canonical Structure srel_lattice_ops: lattice.ops := {|
  car := srel n m;
  leq := srel_leq;
  weq := srel_weq;
  cup := srel_cup;
  cap := srel_cap;
  neg := srel_neg;
  bot := srel_bot;
  top := srel_top
 |}.
 Arguments srel_leq _ _ /. 
 Arguments srel_weq _ _ /. 
 Arguments srel_cup _ _ /. 
 Arguments srel_cap _ _ /. 
 Arguments srel_neg _ /. 
 Arguments srel_bot /. 
 Arguments srel_top /. 
 
 #[global] Instance srel_lattice_laws: lattice.laws (BDL+STR+CNV+DIV) srel_lattice_ops.
 Proof.
   constructor; simpl; try firstorder.
   constructor; simpl; firstorder. 
   discriminate. 
 Qed.
End s.

Section RepOps.
 Implicit Types n m p : EqType.

 Program Definition srel_one n: srel n n := 
  {| rel_of := Eq n |}.

 Program Definition srel_dot n m p (x: srel n m) (y: srel m p): srel n p := 
  {| rel_of := rel_of x⋅rel_of y |}.
 Next Obligation.
   split; intros [z H1 H2].
    rewrite H in H1. rewrite H0 in H2. now exists z. 
    rewrite <-H in H1. rewrite <-H0 in H2. now exists z. 
 Qed. 

 Program Definition srel_cnv n m (x: srel n m): srel m n := 
   {| rel_of := (rel_of x) ° |}.
 Next Obligation. unfold hrel_cnv. now rewrite H, H0. Qed.
 
 Program Definition srel_ldv n m p (x: srel n m) (y: srel n p): srel m p := 
  {| rel_of := ldv _ _ _ (rel_of x) (rel_of y) |}.
 Next Obligation. unfold hrel_ldv. setoid_rewrite H. setoid_rewrite H0. reflexivity. Qed. 

 Program Definition srel_rdv n m p (x: srel m n) (y: srel p n): srel p m := 
  {| rel_of := rdv _ _ _ (rel_of x) (rel_of y) |}.
 Next Obligation. unfold hrel_rdv. setoid_rewrite H. setoid_rewrite H0. reflexivity. Qed. 

 Section i.
  Variable n: EqType.
  Variable x: srel n n.
  (** finite iterations of a relation *)
  Fixpoint iter u: srel n n := match u with O => srel_one n | S u => srel_dot _ _ _ x (iter u) end.
  Program Definition srel_str: srel n n := {| rel_of i j := exists u, rel_of (iter u) i j |}.
  Next Obligation. setoid_rewrite H. setoid_rewrite H0. reflexivity. Qed.
  Definition srel_itr: srel n n := srel_dot n n n x srel_str.
 End i.

 Arguments srel_dot [_ _ _] _ _/. 
 Arguments srel_ldv [_ _ _] _ _/. 
 Arguments srel_rdv [_ _ _] _ _/. 
 Arguments srel_cnv [_ _] _ /. 
 Arguments srel_str [_] _ /. 
 Arguments srel_itr [_] _ /. 
 Arguments srel_one {_} /. 
End RepOps.

Canonical Structure srel_monoid_ops :=  
  monoid.mk_ops EqType srel_lattice_ops srel_dot srel_one srel_itr srel_str srel_cnv srel_ldv srel_rdv.

#[global] Instance srel_monoid_laws: monoid.laws (BDL+STR+CNV+DIV) srel_monoid_ops.
Proof.
  (* assert (dot_leq: forall n m p : Type@{U}, *)
  (*  Proper (leq ==> leq ==> leq) (hrel_dot n m p)). *)
  (*  intros n m p x y H x' y' H' i k [j Hij Hjk]. exists j. apply H, Hij. apply H', Hjk. *)
  constructor; (try now left); intros. 
   apply srel_lattice_laws.
   apply (dotA (laws:=hrel_monoid_laws)).
   intros i j. split.
    intros [k ik kj]. simpl in ik; now rewrite ik. 
    intro. exists i. simpl; reflexivity. assumption. 
   apply (cnvdot_ (laws:=hrel_monoid_laws)).
   apply (cnv_invol (laws:=hrel_monoid_laws)).
   intros i j ij. now apply (cnv_leq (laws:=hrel_monoid_laws)).
   intros i j E. exists O. exact E.
   intros i k [j Hij [u Hjk]]. exists (S u). now exists j. 
   assert (E: forall i, (iter n x i: srel n n) ⋅ z ≦ z).
    induction i. simpl. intros h k [l hl lk]. simpl in hl. now rewrite hl. 
    rewrite <-H0 at 2. transitivity (x⋅((iter n x i: srel n n)⋅z)). 
     cbn. firstorder congruence. now apply (dot_leq (H:=hrel_monoid_laws)).  
    intros i j [? [? ?] ?]. eapply E. repeat eexists; eauto.
   reflexivity. 
   apply (capdotx (laws:=hrel_monoid_laws)).
   apply (ldv_spec (laws:=hrel_monoid_laws)).
   apply (rdv_spec (laws:=hrel_monoid_laws)).
Qed.

Ltac fold_srel := ra_fold srel_monoid_ops.
Tactic Notation "fold_srel" "in" hyp_list(H) := ra_fold srel_monoid_ops in H.
Tactic Notation "fold_srel" "in" "*" := ra_fold srel_monoid_ops in *.
