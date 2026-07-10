(*
Convenience to step/unstep in relations built using the coinduction library.
Hopefully upstreamed eventually: https://github.com/damien-pous/coinduction/pull/22
 *)

From Coinduction Require Import all.

Lemma pfp_gfp {X : Type} {L : CompleteLattice X} (b : mon X) : b (gfp b) <= gfp b.
Proof. apply b_chain. Qed.

Ltac step :=
match goal with
| |- context [gfp ?b] => apply (pfp_gfp b)
| |- context [elem ?R] => apply (b_chain R)
end.

Ltac step_in h :=
match type of h with
| context [gfp ?b] => apply (gfp_pfp b) in h
end.

Tactic Notation "step" "in" ident(h) := step_in h.

Ltac unstep :=
match goal with
| |- context [gfp ?b] => apply (gfp_pfp b)
end.

Ltac unstep_in h :=
match type of h with
| context [gfp ?b] => apply (pfp_gfp b) in h
end.

Tactic Notation "unstep" "in" ident(h) := unstep_in h.

Ltac apply_leq := match goal with 
  | [H : _ <= _ |- _]=> intros; apply H 
  | [H : leq _ _ |- _]=> intros; apply H 
end.

(* nonlinear pattern works here *)
Ltac induct_on_premise := match goal with 
| H: context [?rel _] |- context [?rel ] => induction H
end. 


Ltac monauto := (solve [
(* break `Proper`, introduce names and premises` *)
cbv; 
intros; 
(* find hypothesis matching goal and proceed by cases *)
solve [induct_on_premise; 
(* break down each case as necessary. `solve` will backtrack in a helpful way.  *)
try econstructor; 
(* use monotonicity fact itself: [sim] <= [sim'] *)
try apply_leq; 
eauto]] || fail "`monauto` could not solve this goal."). 
