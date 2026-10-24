From CTree Require Import Core.Utils Core.CTreeDefinitions Eq.Equ Eq.Trans
  Interp.FoldCTree Interp.FoldStateT Interp.Recursion Interp.ITree.
From ITree Require Import ITree InterpFacts Events.StateFacts.
From RelationAlgebra Require Import rel srel.
Import CTreeNotations EquNotations.
Local Open Scope ctree_scope.
Set Universe Checking.
Set Universe Polymorphism.

Section IndependentBudgets.
  Universes i ri qi ro qo.
  Constraint i < ri.
  Constraint ri < qi.
  Constraint qi < ro.
  Constraint ro < qo.
  Context (E : Type@{i} -> Type) (B : Type@{i} -> Type).
  Context (X : Type@{i}) (ev : E X) (choice : B X).

  Definition raised_trigger : @ctree@{i i _ _ ri qi} E B X := CTree.trigger ev.
  Definition raised_branch : @ctree@{i i _ _ ri qi} E B X := CTree.branch choice.
  Definition raised_branchS : @ctree@{i i _ _ ri qi} E B X := CTree.branchS choice.
  Definition raised_monadic_trigger : @ctree@{i i _ _ ri qi} E B X :=
    @Utils.mtrigger E (@ctree@{i i _ _ ri qi} E B) _ X ev.
  Definition raised_monadic_branch : @ctree@{i i _ _ ri qi} E B X :=
    @Utils.mbr B (@ctree@{i i _ _ ri qi} E B) _ X choice.
  Definition continuation (x : X) : @ctree@{i i _ _ ro qo} E B X :=
    CTreeDefinitions.Ret x.

  Example bind_across_budgets :
    CTree.bind raised_trigger continuation ≅ CTreeDefinitions.Vis ev continuation.
  Proof. apply Equ.bind_trigger. Qed.

  Example algebra_across_budgets
      (t u : @ctree@{i i _ _ ri qi} E B X)
      (v w : @ctree@{i i _ _ ro qo} E B X) :
    (trans τ t u -> etrans τ t u) /\ (trans τ v w -> etrans τ v w).
  Proof. split; apply trans_etrans. Qed.
End IndependentBudgets.

Section EventBelowBranch.
  Universes e b.
  Constraint e < b.
  Context (E : Type@{e} -> Type) (B : Type@{b} -> Type).
  Context (X : Type@{e}) (ev : E X).
  Definition trigger_distinct_indices : ctree E B X := CTree.trigger ev.
End EventBelowBranch.

Section BranchBelowEvent.
  Universes e b.
  Constraint b < e.
  Context (E : Type@{e} -> Type) (B : Type@{b} -> Type).
  Context (X : Type@{b}) (choice : B X).
  Definition branch_distinct_indices : ctree E B X := CTree.branch choice.
End BranchBelowEvent.
