(*|
Equivalence of computations
===========================
This file reexports everything that's necessary to reason w.r.t.
[equ] (coinductive structural equality) and [sbisim] (strong bisimulation).
Tactics are redefined locally to support both relations.
|*)

From Stdlib Require Export Basics.

From RelationAlgebra Require Export
     rel srel.

From Coinduction Require Export all.

From CTree.Eq Require Export
     Shallow
     Equ
     Trans
     Epsilon
     SBisim
     SSim
     CSSim
     Visible.

From CTree Require Export CTree.

(* Export CTreeNotations.
   Exporting everything right now, probably completely unreasonable.
 *)
Export EquNotations.
Export SBisimNotations.
Export SSimNotations.
Export CSSimNotations.

(*|
The [step], [step in] and [coinduction] tactics from [coinduction]
 with additional unfolding and refolding of [equ] and [sbisim]
|*)

From CTree.Eq Require Import
     SSimAlt
     SBisimAlt.

Ltac __concl_is t :=
  assert_succeeds (repeat match goal with |- forall _, _ => intro end; t).

#[global] Tactic Notation "step" :=
  first [ __step_equ | __step_sbisim | __step_ssim | __step_cssim
        | __step_sbisim' | __step_sb' | __step_ssim' | step
        | match goal with |- ?G =>
            fail 1 "step: the goal is not an equ, sbisim, ssim, cssim, sbisim' or ssim' goal, nor a chain element or gfp of one:" G
          end ].

#[global] Tactic Notation "coinduction" simple_intropattern(R) simple_intropattern(H) :=
  first
    [ __concl_is ltac:(lazymatch goal with |- equ _ _ _ => idtac end);
      first [ __coinduction_equ R H
            | fail 2 "coinduction: the conclusion is an equ goal, but coinduction on equ failed" ]
    | __concl_is ltac:(lazymatch goal with |- sbisim _ _ _ => idtac end);
      first [ __coinduction_sbisim R H
            | fail 2 "coinduction: the conclusion is an sbisim goal, but coinduction on sbisim failed" ]
    | __concl_is ltac:(lazymatch goal with |- ssim _ _ _ => idtac end);
      first [ __coinduction_ssim R H
            | fail 2 "coinduction: the conclusion is an ssim goal, but coinduction on ssim failed" ]
    | __concl_is ltac:(lazymatch goal with |- cssim _ _ _ => idtac end);
      first [ __coinduction_cssim R H
            | fail 2 "coinduction: the conclusion is a cssim goal, but coinduction on cssim failed" ]
    | __concl_is ltac:(lazymatch goal with |- sbisim' _ _ _ => idtac end);
      first [ __coinduction_sbisim' R H
            | fail 2 "coinduction: the conclusion is an sbisim' goal, but coinduction on sbisim' failed" ]
    | __concl_is ltac:(lazymatch goal with |- ssim' _ _ _ => idtac end);
      first [ __coinduction_ssim' R H
            | fail 2 "coinduction: the conclusion is an ssim' goal, but coinduction on ssim' failed" ]
    | __coinduction_equ R H | __coinduction_sbisim R H | __coinduction_ssim R H | __coinduction_cssim R H
    | __coinduction_sbisim' R H | __coinduction_ssim' R H
    | coinduction R H
    | match goal with |- ?G =>
        fail 1 "coinduction: the goal is not an equ, sbisim, ssim, cssim, sbisim' or ssim' goal, nor a gfp:" G
      end ].

#[global] Tactic Notation "step" "in" ident(H) :=
  first [ __step_in_equ H | __step_in_sbisim H | __step_in_ssim H | __step_in_cssim H
        | __step_in_sbisim' H | __step_in_sb' H | __step_in_ssim' H | step_in H
        | fail "step in: the hypothesis" H "is not an equ, sbisim, ssim, cssim, sbisim' or ssim' fact, nor a chain element or gfp of one" ].

(*|
Assuming a goal of the shape [t ~ u], initialize the two challenges
|*)
#[global] Tactic Notation "play" := __play_sbisim || __play_ssim || __play_cssim.

(*|
Assuming an hypothesis of the shape [t ~ u], extract the forward (playL)
or backward (playR) challenge --- the e-versions looks for the hypothesis
|*)
#[global] Tactic Notation "play" "in" ident(H) := __play_ssim_in H || __play_cssim_in H.
#[global] Tactic Notation "playL" "in" ident(H) := __playL_sbisim H.
#[global] Tactic Notation "playR" "in" ident(H) := __playR_sbisim H.
#[global] Tactic Notation "eplay" := __eplay_ssim || __eplay_cssim.
#[global] Tactic Notation "eplayL" := __eplayL_sbisim.
#[global] Tactic Notation "eplayR" := __eplayR_sbisim.

(*|
The upto [Vis] context principle for [sbisim]
|*)
(* #[global] Tactic Notation "upto_vis" := __upto_vis_sbisim. *)

(* (*| *)
(* The upto [bind] context principle for [equ] and [sbisim] --- *)
(* the same tactic covers both cases, whether in front of a [gfp], [t _] or [bt _]. *)
(* The three variants are: *)
(* - [upto_bind]: leave you with both proof obligations, introducing an evar for the intermediate relation in the case of [equ] *)
(* - [upto_bind_eq]: meant to be use when the prefixes of the computations *)
(* are identical: assumes [reflexivity] will solve the first goal, and proceed to substitute the equality *)
(* - [upto_bind with SS]: for [equ], provides explicitly the intermediate relation *)
(* |*) *)

#[global] Tactic Notation "upto_bind" :=
  first [ __eupto_bind_equ | __eupto_bind_sbisim'
        | fail "upto_bind: the goal is not an equ or sbisim' goal (or chain element of one) relating two binds" ].

#[global] Tactic Notation "upto_bind_eq" :=
  first [ __upto_bind_equ_eq | __upto_bind_sbisim'_eq
        | fail "upto_bind_eq: the goal is not an equ or sbisim' goal (or chain element of one) relating two binds with the same prefix" ].

#[global] Tactic Notation "upto_bind" "with" uconstr(SS) :=
  first [ __upto_bind_equ SS | __upto_bind_sbisim' SS
        | fail "upto_bind with: the goal is not an equ or sbisim' goal (or chain element of one) relating two binds" ].


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
  | ?u = ?t => let eq := fresh "EQ" in assert (eq : u ≃ t) by (rewrite H; reflexivity); clear H
  end.

#[global] Opaque Trans.wtrans.
