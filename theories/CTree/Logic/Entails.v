From ExtLib Require Import
  Structures.MonadWriter
  Structures.Monads
  Structures.MonadState
  Data.Monads.StateMonad.

From Coq Require Import
  List
  Basics
  Fin
  Relations.Relation_Definitions
  Classes.SetoidClass
  Classes.RelationPairs.

From CTree Require Import
  CTree.Core
  CTree.Pred
  CTree.Equ
  CTree.SBisim
  CTree.Trans
  CTree.Logic.Trans
  Logic.Semantics
  Logic.Entails
  Logic.Kripke
  Events.Writer.

Generalizable All Variables.

Import Ctree CTreeNotations.
Local Open Scope ctree_scope.

Section KripkeCTreeW.
  Context {E W: Type}.
  Local Open Scope ctl_scope.

  (*| CTreeW is an interpreted tree, an automaton by indirection to [ctree_kripke] |*)
  #[refine] Global Instance ctreeW_kripke: Kripke (ctreeW W) W :=
    {|
      ktrans X '(t, w) '(t', w') :=
        ctree_kripke.(ktrans) (X:=X)
                       (t, Some (Obs (Log w) tt))
                       (t', Some (Obs (Log w') tt));
      mequ X := @sbisim (writerE W) (writerE W) _ _ X X eq
    |}.
  Proof.
    intros; now apply ctree_kripke.(ktrans_semiproper) with (t:=t) (s:=s).
  Defined.

End KripkeCTreeW.

(*
  - Uninterpreted ctree (observe uninterpreted events)
    + ctree E X * opt E (from [ctree_kripke])
  - Interpreterd (observe states)
    + stateT W (ctree (writerE W))
  - Interpreted (observe interpreted events)
    + stateT Σ (ctree (writerE (Bar E)))
 *)
Global Instance ctreeW_entails{W}: EntailsT (ctreeW W) W := {
    KripkeM := @ctreeW_kripke W;
    entails {X} (φ: CtlFormula W) (t: ctreeW W X) (w: W) :=
      entails
        (ctl_option (ctl_contramap (fun '(Obs (Log w) _) => w) φ))
        t (Some (Obs (Log w) tt))
  }.
