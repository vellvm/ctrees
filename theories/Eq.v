(*|
Equivalence of computations
===========================
This file reexports everything that's necessary to reason w.r.t.
[equ] (coinductive structural equality) and [sbisim] (strong bisimulation).
Tactics are redefined locally to support both relations.
|*)

From Coq Require Export Basics.

From RelationAlgebra Require Export
     rel srel.

From Coinduction Require Export
     coinduction rel tactics.

From CTree.Eq Require Export
     Shallow
     Equ
     Trans
     SBisim
     SSim
     Visible.

From CTree Require Export CTree.

(* Export CTreeNotations. *)
Export EquNotations.
Export SBisimNotations.

(*|
The [step], [step in] and [coinduction] tactics from [coinduction]
 with additional unfolding and refolding of [equ] and [sbisim]
|*)
#[global] Tactic Notation "step" :=
  __step_equ || __step_sbisim || step.

#[global] Tactic Notation "coinduction" simple_intropattern(R) simple_intropattern(H) :=
  __coinduction_equ R H || __coinduction_sbisim R H || coinduction R H.

#[global] Tactic Notation "step" "in" ident(H) :=
  __step_in_equ H || __step_in_sbisim H || step_in H.

(*|
Assuming a goal of the shape [t ~ u], initialize the two challenges
|*)
#[global] Tactic Notation "play" := __play_sbisim || __play_ssim.

(*|
Assuming an hypothesis of the shape [t ~ u], extract the forward (playL)
or backward (playR) challenge --- the e-versions looks for the hypothesis
|*)
#[global] Tactic Notation "play" "in" ident(H) := __play_ssim_in H.
#[global] Tactic Notation "playL" "in" ident(H) := __playL_sbisim H.
#[global] Tactic Notation "playR" "in" ident(H) := __playR_sbisim H.
#[global] Tactic Notation "eplay" := __eplay_ssim.
#[global] Tactic Notation "eplayL" := __eplayL_sbisim.
#[global] Tactic Notation "eplayR" := __eplayR_sbisim.

(*|
The upto [Vis] context principle for [sbisim]
|*)
#[global] Tactic Notation "upto_vis" := __upto_vis_sbisim.

(*|
The upto [bind] context principle for [equ] and [sbisim] ---
the same tactic covers both cases, whether in front of a [gfp], [t _] or [bt _].
The three variants are:
- [upto_bind]: leave you with both proof obligations, introducing an evar for the intermediate relation in the case of [equ]
- [upto_bind_eq]: meant to be use when the prefixes of the computations
are identical: assumes [reflexivity] will solve the first goal, and proceed to substitute the equality
- [upto_bind with SS]: for [equ], provides explicitly the intermediate relation
|*)
#[global] Tactic Notation "upto_bind" :=
  __eupto_bind_equ || __upto_bind_sbisim || __upto_bind_ssim.

#[global] Tactic Notation "upto_bind_eq" :=
  __upto_bind_eq_equ || __upto_bind_eq_sbisim || __upto_bind_eq_ssim.

#[global] Tactic Notation "upto_bind" "with" uconstr(SS) :=
  __upto_bind_equ SS.

(*|
Weakens equalities into respectively [equ] and [sbisim] equations ---
useful to setup inductions.
|*)
Ltac eq2equ H :=
  match type of H with
  | ?u = ?t => let eq := fresh "EQ" in assert (eq : u ≅ t) by (rewrite H; reflexivity); clear H
  end.

Ltac eq2sb H :=
  match type of H with
  | ?u = ?t => let eq := fresh "EQ" in assert (eq : u ~ t) by (rewrite H; reflexivity); clear H
  end.

#[global] Opaque wtrans.
