From CTree Require Import
  CTree.Core.

From CTree Require Export
  Events.Core
  Events.IoE.

Notation fd := nat (only parsing).

Definition fresh {S}: ctree (ioE S) fd :=
  @Ctree.trigger (ioE S) (ioE S) _ _ (ReSum_refl) (ReSumRet_refl) Fresh.

Definition read {S}(f: fd): ctree (ioE S) (option S) :=
  @Ctree.trigger (ioE S) (ioE S) _ _ (ReSum_refl) (ReSumRet_refl) (Read f).

Definition write {S}(f: fd)(s: S): ctree (ioE S) bool :=
  @Ctree.trigger (ioE S) (ioE S) _ _ (ReSum_refl) (ReSumRet_refl) (Write f s).

Definition open {S}(f: fd): ctree (ioE S) bool :=
  @Ctree.trigger (ioE S) (ioE S) _ _ (ReSum_refl) (ReSumRet_refl) (Open f).

Definition close {S}(f: fd): ctree (ioE S) bool :=
  @Ctree.trigger (ioE S) (ioE S) _ _ (ReSum_refl) (ReSumRet_refl) (Close f).


