From CTree Require Import
  ITree.Core
  ITree.Interp.

From CTree Require Export
  Classes
  Events.Core
  Events.StateE.

Definition get {S}: itree (stateE S) S :=
  @Itree.trigger (stateE S) (stateE S) _ _ (ReSum_refl) (ReSumRet_refl) Get.

Definition put {S}: S -> itree (stateE S) unit := fun s => Itree.trigger (Put s).
