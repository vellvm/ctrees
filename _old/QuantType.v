From CTree Require Import
  Events.Core
  Utils.

From Coq Require Import
     Logic.FunctionalExtensionality
     Lists.List.

(** In this module from [GaloisInc/entree-spec] they define the notion of a
"quantifiable type", which is a type that can be quantified over by quantifying
over all elements of some type in a set encoding **)

(* An encoding of an easy-to-define collection of types *)
Inductive QuantEnc : Type :=
| QEnc_nat
| QEnc_prop (P:Prop)
| QEnc_sum (k1 k2:QuantEnc)
| QEnc_pair (k1 k2:QuantEnc)
| QEnc_fun (k1 k2:QuantEnc).

Fixpoint encodes_QuantEnc (k: QuantEnc) : Type :=
  match k with
  | QEnc_nat => nat
  | QEnc_prop P => P
  | QEnc_sum k1 k2 => encodes_QuantEnc k1 + encodes_QuantEnc k2
  | QEnc_pair k1 k2 => encodes_QuantEnc k1 * encodes_QuantEnc k2
  | QEnc_fun k1 k2 => encodes_QuantEnc k1 -> encodes_QuantEnc k2
  end.
Global Instance EncodingType_QuantEnc : Encode QuantEnc :=
  encodes_QuantEnc.

(* A type whose elements can be enumerated by a function from a QuantEnc that is
constructively surjective, i.e., where we can constructively find an input that
maps to any element of the output type *)
Class QuantType (A:Type) : Type :=
  { quantEnc : QuantEnc;
    quantEnum : encode quantEnc -> A;
    quantEnumInv : A -> encode quantEnc;
    quantEnumSurjective : forall a:A, quantEnum (quantEnumInv a) = a }.

#[refine] Global Instance QuantType_unit : QuantType unit :=
  { quantEnc := QEnc_prop True;
    quantEnum := fun _ => tt;
    quantEnumInv := fun _ => I; }.
  destruct a; reflexivity.
Defined.

#[refine] Global Instance QuantType_bool : QuantType bool :=
  { quantEnc := QEnc_nat;
    quantEnum := fun n => Nat.eqb n 0;
    quantEnumInv := fun b => if b then 0 else 1; }.
  destruct a; reflexivity.
Defined.

Global Instance QuantType_Prop (P:Prop) : QuantType P :=
  { quantEnc := QEnc_prop P;
    quantEnum := fun pf => pf;
    quantEnumInv := fun pf => pf;
    quantEnumSurjective := fun pf => eq_refl pf }.

Global Instance QuantType_nat : QuantType nat :=
  { quantEnc := QEnc_nat;
    quantEnum := fun n => n;
    quantEnumInv := fun n => n;
    quantEnumSurjective := fun n => eq_refl n }.

#[refine] Global Instance QuantType_sum (A B:Type) `{QuantType A} `{QuantType B} : QuantType (A + B) :=
  { quantEnc := QEnc_sum (quantEnc (A:=A)) (quantEnc (A:=B));
    quantEnum := fun s => match s with
                          | inl x => inl (quantEnum x)
                          | inr x => inr (quantEnum x)
                          end;
    quantEnumInv := fun s => match s with
                          | inl x => inl (quantEnumInv x)
                          | inr x => inr (quantEnumInv x)
                          end; }.
  destruct a; rewrite quantEnumSurjective; reflexivity.
Defined.

#[refine] Global Instance QuantType_pair (A B:Type) `{QuantType A} `{QuantType B} : QuantType (A * B) :=
  { quantEnc := QEnc_pair (quantEnc (A:=A)) (quantEnc (A:=B));
    quantEnum := fun p => (quantEnum (fst p), quantEnum (snd p));
    quantEnumInv := fun p => (quantEnumInv (fst p), quantEnumInv (snd p)) }.
intros [a b]; cbn; repeat rewrite quantEnumSurjective; reflexivity.
Defined.

#[refine] Global Instance QuantType_fun (A B:Type) `{QuantType A} `{QuantType B} : QuantType (A -> B) :=
  { quantEnc := QEnc_fun (quantEnc (A:=A)) (quantEnc (A:=B));
    quantEnum := fun f x => quantEnum (f (quantEnumInv x));
    quantEnumInv := fun f x => quantEnumInv (f (quantEnum x)) }.
intros; apply functional_extensionality. intro x.
  repeat rewrite quantEnumSurjective. reflexivity.
Defined.

(* A list can be quantified by quantifying over unit + (len, nat -> A); the
unit+ is needed in case A is not inhabited *)

Definition build_list (A:Type) len (f : nat -> A) : list A :=
  map f (seq 0 len).

#[refine] Global Instance QuantType_list (A:Type) `{QuantType A} : QuantType (list A) :=
  { quantEnc :=
      QEnc_sum (QEnc_prop True) (QEnc_pair
                                   QEnc_nat (QEnc_fun QEnc_nat (quantEnc (A:=A))));
    quantEnum :=
      fun s => match s with
               | inl _ => nil
               | inr (len, f) => build_list A len (fun x => quantEnum (f x))
               end;
    quantEnumInv :=
      fun l => match l with
               | nil => inl I
               | def::_ => inr (length l, fun i => quantEnumInv (nth _ l def))
            end }.
  exact i.
  destruct a; [ reflexivity | ].
  unfold build_list.
  set (l:= a :: a0).
  transitivity (build_list A (length l) (fun x => nth x l a));
    unfold build_list; [ apply map_ext; intro; apply quantEnumSurjective | ].
  apply (nth_ext _ _ a a);
    rewrite map_length; rewrite seq_length; [ reflexivity | ].
  intros.
  etransitivity; [ apply (map_nth (fun x : nat => nth x l a) _ 0 n) | ].
  rewrite seq_nth; [ reflexivity | assumption ].
Defined.
