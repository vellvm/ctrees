From CTree Require Import 
	CTrees Equ
  .

From Coinduction Require Import 
	coinduction rel tactics.

(* We work over a (coinductive) parameterized data-structure named `ctree E X`.
	 We consider two different relations over this datatype, both 
	 defined as greatest fixedpoint via the `coq-coinduction` library.

		Here is a smallish example where unification goes wrong.
	 *)
Goal forall E X, (Reflexive (@equF E X X eq (gfp (fequ eq)))).
	(* I currently have only one of the two relations in scope,
		 that is the greatest fixedpoint of the `fequ` endofunction.
		 Everything goes smoothly.
	*)
	intros.
	typeclasses eauto. 
	Restart.
	(* Explicitely, the proof search finds the following proof *)
	intros.
  apply Reflexive_equF.
	eauto.
	apply (@Equivalence_Reflexive _ _ Equivalence_equ).
	Restart.
	intros.

  From CTree Require Import Bisim.
(* But now, when both relations are in scope, instances such as `Bisim.Reflexive_t` 
	 lead to huge unification problems that eventually turn out impossible, allowing 
	 the previous proof to finally be found, but only after an excruciating time.
*)

	(* The following takes ~30s on my machine with the opam version of coinduction. The patched one solves the problem *)
	(* Time typeclasses eauto.  ~30s on my machine *)

Qed.

