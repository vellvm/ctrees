From CTree Require Import
  ITree.Core.

From CTree Require Export
  Utils.Utils
  Events.NetE.

Definition send {n T}: fin' n -> T -> itree (netE n T) unit :=
  fun i p => Itree.trigger (Send i p).

Definition recv {n T}: itree (netE n T) (option T) :=
  Itree.trigger Recv.
