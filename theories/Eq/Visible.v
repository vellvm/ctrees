From RelationAlgebra Require Import
     monoid
     kat
     kat_tac
     prop
     rel
     srel
     comparisons
     rewriting
     normalisation.

From Coinduction Require Import
	 coinduction rel tactics.

From CTree Require Import
	 CTree Eq.Shallow Eq.Equ.

Import CTree.
Import CTreeNotations.
Import EquNotations.
Open Scope ctree.

Set Implicit Arguments.
Set Primitive Projections.

#[local] Tactic Notation "step" "in" ident(H) := __step_in_equ H.

Section Visible.

  Context {E : Type -> Type} {R : Type}.

  Notation S' := (ctree' E R).
  Notation S  := (ctree  E R).

  Definition SS : EqType :=
	{| type_of := S ; Eq := equ eq |}.

  Inductive visible_ : hrel S' S' :=
  | VisibleI {n} (x : Fin.t n) k t :
    visible_ (observe (k x)) t ->
    visible_ (BrF false n k) t

  | VisibleV {n} (x : Fin.t n) k1 k2 :
    (forall x, k1 x ≅ k2 x) ->
    visible_ (BrF true n k1) (BrF true n k2)

  | VisibleVis {X} (e : E X) k1 k2 :
    (forall x, k1 x ≅ k2 x) ->
    visible_ (VisF e k1) (VisF e k2)

  | VisibleRet r :
    visible_ (RetF r) (RetF r)
  .
  Hint Constructors visible_ : core.

  Definition visibleR : hrel S S :=
	fun u v => visible_ (observe u) (observe v).

  #[local] Instance visible__equ_aux1 t :
	Proper (going (equ eq) ==> flip impl) (visible_ t).
  Proof.
	intros x x' equ TR.
	inv equ; rename H into equ.
	step in equ.
	dependent induction TR; intros; eauto; inv equ; try invert; auto;
	  (constructor; auto; etransitivity; [apply H | symmetry; auto]).
  Qed.

  #[local] Instance visible__equ_aux2 :
	Proper (going (equ eq) ==> going (equ eq) ==> impl) visible_.
  Proof.
	intros x x' xequ y y' yequ TR. rewrite <- yequ. clear yequ y'.
	inv xequ; rename H into xequ.	step in xequ.
    revert x' xequ.
	dependent induction TR; intros; eauto; inv xequ; try invert; auto.
    2, 3: constructor; auto; intros; rewrite <- H; symmetry; auto.
    econstructor. apply IHTR. rewrite REL. reflexivity.
  Qed.

  #[global] Instance visible__equ :
	Proper (going (equ eq) ==> going (equ eq) ==> iff) visible_.
  Proof.
	intros ? ? eqt ? ? equ; split; intros TR.
	- eapply visible__equ_aux2; eauto.
	- symmetry in equ; symmetry in eqt; eapply visible__equ_aux2; eauto.
  Qed.

  #[global] Instance visible_equ :
	Proper (equ eq ==> equ eq ==> iff) visibleR.
  Proof.
	intros ? ? eqt ? ? equ; unfold visibleR.
    rewrite eqt, equ. reflexivity.
  Qed.

  Definition visible : srel SS SS := {| hrel_of := visibleR : hrel SS SS |}.
End Visible.
