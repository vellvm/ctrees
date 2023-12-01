(*| Useful instructions: State |*)
From CTree Require Import
  CTree.Core.

From CTree Require Export
  Events.Core
  Events.StateE.

Definition get {S}: ctree (stateE S) S :=
  @Ctree.trigger (stateE S) (stateE S) _ _ (ReSum_refl) (ReSumRet_refl) Get.

Definition put {S}: S -> ctree (stateE S) unit :=
  fun (s: S) => Ctree.trigger (Put s).
