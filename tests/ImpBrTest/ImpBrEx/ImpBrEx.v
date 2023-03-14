From Coq Require Import
     Strings.String.
From ExtLib Require Import
     Data.Map.FMapAList.
From CTree Require Import
     CTree.
From CTreeImp Require Import
     ImpBr.

Import CTreeNotations.
Local Open Scope ctree_scope.
Local Open Scope string_scope.

Definition ex_prog :=
  Branch
    (Branch
      (Assign "x" (Lit 1))
      (Assign "x" (Lit 2)))
    Block.

Definition ex_prog' : ctree void1 B02 nat :=
  r <- interp_imp (denote_imp ex_prog) nil;; Ret (
    match alist_find _ "x" (fst r) with
    | Some x => x
    | None => 0
    end
  ).
