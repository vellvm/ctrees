From Coq Require Import
  Classes.SetoidClass
  Classes.Morphisms
  Classes.RelationPairs.

From CTree Require Import
  Logic.Kripke
  Logic.Semantics
  Logic.Congruence.

Generalizable All Variables.

Arguments CtlFormula: clear implicits.

Class EntailsT(M: Type -> Type)(W: Type) := {
    KripkeM :: Kripke M W;
    entails{X}(φ: CtlFormula W)(m: M X)(w: W): Prop
  }.
Global Hint Mode EntailsT ! +: core.

(* Entails instances for all the following.
   Base entailsF is (M X * W).
   - Uninterpreted ctree (observe uninterpreted events)
     + ctree E X * opt E
   - Interpreterd (observe states)
     + stateT Σ (ctree (writerE Σ))
   - Interpreted (observe interpreted events)
     + stateT Σ (ctree (writerE (Bar E)))
*)
Global Instance EntailsT_id `{Kripke M W}: EntailsT M W :=
  {
    entails{X}(φ: CtlFormula W)(m: M X)(w: W) :=
      entailsF φ (m, w)
  }.

