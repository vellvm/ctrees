From Coinduction Require Export
     coinduction rel tactics.

From CTree Require Import CTrees.
From CTree.Eq Require Export
     Equ
     Trans
     SBisim.

Export CTreeNotations.
Export EquNotations.
Export SBisimNotations.

#[global] Tactic Notation "step" :=
  __step_equ || __step_sbisim.

#[global] Tactic Notation "coinduction" simple_intropattern(R) simple_intropattern(H) :=
  __coinduction_equ R H || __coinduction_sbisim R H.

#[global] Tactic Notation "step" "in" ident(H) :=
  __step_in_equ H || __step_in_sbisim H.

#[global] Tactic Notation "upto_vis" := __upto_vis_sbisim.

#[global] Tactic Notation "play" := __play_sbisim.
#[global] Tactic Notation "playL" "in" ident(H) := __playL_sbisim H.
#[global] Tactic Notation "playR" "in" ident(H) := __playR_sbisim H.
#[global] Tactic Notation "eplayL" := __eplayL_sbisim.
#[global] Tactic Notation "eplayR" := __eplayR_sbisim.

#[global] Tactic Notation "upto_bind" :=
  __eupto_bind_equ || __upto_bind_sbisim.

#[global] Tactic Notation "upto_bind_eq" :=
  __upto_bind_eq_equ || __upto_bind_eq_sbisim.

#[global] Tactic Notation "upto_bind" "with" uconstr(SS) :=
  __upto_bind_equ SS.

Ltac eq2equ H :=
  match type of H with
  | ?u = ?t => let eq := fresh "EQ" in assert (eq : u ≅ t) by (subst; reflexivity); clear H
  end.

Ltac eq2sb H :=
  match type of H with
  | ?u = ?t => let eq := fresh "EQ" in assert (eq : u ~ t) by (subst; reflexivity); clear H
  end.

#[global] Opaque wtrans.
