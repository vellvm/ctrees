From CTree Require Import
  ITree.Core.

From CTree Require Export
  Events.NetE.

Definition send {n T}: uid n -> uid n -> T -> itree (netE n T) unit :=
  fun i u p => Itree.trigger (Send i u p).

Definition recv {n T}: uid n -> itree (netE n T) (option T) :=
  fun i => Itree.trigger (Recv i).

Notation retry := (Ret (inl tt)).
Notation exit := (Ret (inr tt)).
