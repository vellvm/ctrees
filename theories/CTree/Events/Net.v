From CTree Require Import
  CTree.Core.

From CTree Require Export
  Events.NetE.

Definition send {n T}: uid n -> uid n -> T -> ctree (netE n T) unit :=
  fun i u p => Ctree.trigger (Send i u p).

Definition recv {n T}: uid n -> ctree (netE n T) (option T) :=
  fun i => Ctree.trigger (Recv i).

Notation retry := (Ret (inl tt)).
Notation exit := (Ret (inr tt)).
