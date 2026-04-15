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
