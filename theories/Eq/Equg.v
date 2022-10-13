(*|
=================================
Equality up to guards over ctrees
=================================
[equg] is an equivalence relation over ctrees similar to the syntactic equality,
that also allows to skip a finite number of Guard nodes.

This is still experimental, it is only used in the proof of an iterative law for now.
.. coq:: none
|*)
From Coq Require Import RelationClasses Program.

From Coinduction Require Import
	coinduction rel tactics.

From CTree Require Import
     CTree
     Eq.Shallow
     Eq.Equ
     Eq.Trans
     Eq.SBisim.

Import CTree.

(*|
.. coq::
|*)

Section equg.

  Context {E : Type -> Type} {R1 R2 : Type} (RR : R1 -> R2 -> Prop).

  Inductive equgb (eq : ctree E R1 -> ctree E R2 -> Prop) :
    ctree' E R1 -> ctree' E R2 -> Prop :=
  | Eqg_Ret x y (REL : RR x y) : equgb eq (RetF x) (RetF y)
  | Eqg_Vis {X} (e : E X) k1 k2
      (REL : forall x, eq (k1 x) (k2 x)) :
      equgb eq (VisF e k1) (VisF e k2)
  | Eqg_GuardL t1 t2 k1
              (Hk : forall x, k1 x = t1)
              (REL : equgb eq (observe t1) t2) :
      equgb eq (BrDF 1 k1) t2
  | Eqg_GuardR t1 t2 k2
              (Hk : forall x, k2 x = t2)
              (REL : equgb eq t1 (observe t2)) :
      equgb eq t1 (BrDF 1 k2)
  | Eqg_Br b {n} (k1 : Fin.t n -> _) (k2 : Fin.t n -> _)
              (REL : forall i, eq (k1 i) (k2 i)) :
      equgb eq (BrF b n k1) (BrF b n k2)
  .
  Hint Constructors equgb: core.

  Definition equgb_ eq : ctree E R1 -> ctree E R2 -> Prop :=
	fun t1 t2 => equgb eq (observe t1) (observe t2).

  Theorem equgb_sub : forall (R R' : rel _ _), (forall x y, R x y -> R' x y) -> equgb R <= equgb R'.
  Proof.
    cbn. intros.
    induction H0.
    - constructor. apply REL.
    - constructor. auto.
    - econstructor; auto.
    - econstructor; auto.
    - constructor. auto.
  Qed.

  Program Definition fequg: mon (ctree E R1 -> ctree E R2 -> Prop) := {|body := equgb_|}.
  Next Obligation.
    unfold pointwise_relation, Basics.impl, equgb_.
    red in H0.
    genobs a oa. genobs a0 oa0.
    inversion_clear H0; eauto.
    econstructor; eauto. eapply equgb_sub; eauto.
    econstructor; eauto. eapply equgb_sub; eauto.
  Qed.

  Theorem equgb__fequg : equgb_ = fequg.
  Proof.
    reflexivity.
  Qed.

  Theorem equgb_fequg : forall (R : rel _ _) (t : ctree E R1) (t' : ctree E R2), equgb R (observe t) (observe t') = fequg R t t'.
  Proof.
    reflexivity.
  Qed.

End equg.

Definition equg {E R1 R2} R := (gfp (@fequg E R1 R2 R)).
#[global] Hint Unfold equg: core.
#[global] Hint Constructors equgb: core.
Arguments equgb_ _ _ _ _/.

Ltac fold_equg :=
  repeat
    match goal with
    | h: context[@fequg ?E ?R1 ?R2 ?RR] |- _ => fold (@equg E R1 R2 RR) in h
    | |- context[@fequg ?E ?R1 ?R2 ?RR] => fold (@equg E R1 R2 RR)
    end.

Ltac __coinduction_equg R H :=
  unfold equ; apply_coinduction; fold_equg; intros R H.

Tactic Notation "__step_equg" :=
  match goal with
  | |- context [@equg ?E ?R1 ?R2 ?RR _ _] =>
      unfold equg;
      step;
      fold (@equg E R1 R2 RR);
      simpl body
  | |- _ => step
  end.

#[local] Tactic Notation "step" := __step_equg.

#[local] Tactic Notation "coinduction" simple_intropattern(R) simple_intropattern(H) :=
  __coinduction_equg R H.

Ltac __step_in_equg H :=
  match type of H with
  | context [@equg ?E ?R1 ?R2 ?RR _ _] =>
      unfold equg in H;
      step in H;
      fold (@equg E R1 R2 RR) in H;
      simpl body in H
  end.

#[local] Tactic Notation "step" "in" ident(H) := __step_in_equg H || __step_in_equ H.

Module EqugNotations.

  Infix "(G≅)" := (equg eq) (at level 70).

(*|
The associated companions:
|*)
  Notation gt Q  := (t (fequg Q)).
  Notation gT Q  := (T (fequg Q)).
  Notation gbt Q := (bt (fequg Q)).
  Notation gbT Q := (bT (fequg Q)).
  Notation "t [G≅ Q ] u" := (gt Q _ t u) (at level 79).
  Notation "t {G≅ Q } u" := (gbt Q _ t u) (at level 79).
  Notation "t {{G≅ Q }} u" := (equgb Q (equg Q) t u) (at level 79).
  Notation "t [G≅] u" := (gt eq _ t u) (at level 79).
  Notation "t {G≅} u" := (gbt eq _ t u) (at level 79).
  Notation "t {{G≅}} u" := (equgb eq (equg eq) t u) (at level 79).

End EqugNotations.

Import EqugNotations.

Section equg_theory.

  Variable (E : Type -> Type) (R : Type) (RR : R -> R -> Prop).
  Notation gT  := (coinduction.T (fequg (E := E) RR)).
  Notation gt  := (coinduction.t (fequg (E := E) RR)).
  Notation gbt := (coinduction.bt (fequg (E := E) RR)).
(*|
This is just a hack to avoid a universe inconsistency when
 using both the relational algebra and coinduction libraries
 (we fix the type at which we'll use [eq]).
|*)
  Definition seq: relation (ctree E R) := eq.

	Lemma refl_t {RRR: Reflexive RR}: const seq <= gt.
	Proof.
		apply leq_t. intro. cbn.
		change (@eq (ctree E R)  <= equgb_ RR eq).
		intros p ? <-. cbn. desobs p; auto.
	Qed.

(*|
[converse] is compatible: up-to symmetry is valid
|*)
	Lemma converse_t {RRS: Symmetric RR}: converse <= gt.
  Proof.
    apply leq_t. intros S x y H; cbn in *.
    genobs y oy. genobs x ox. clear x Heqox y Heqoy.
    induction H; eauto.
  Qed.

  #[global] Instance Reflexive_gt `{Reflexive _ RR} S: Reflexive (gt S).
  Proof. apply (build_reflexive (ft_t refl_t S)). Qed.

  #[global] Instance Symmetric_gt `{Symmetric _ RR} S: Symmetric (gt S).
  Proof. apply (build_symmetric (ft_t converse_t S)). Qed.

  #[global] Instance Reflexive_equgb (equg : ctree E R -> ctree E R -> Prop) :
    Reflexive RR -> Reflexive equg -> Reflexive (equgb RR equg).
  Proof.
    red. destruct x; auto.
  Qed.

End equg_theory.

#[global] Hint Constructors equgb : core.
Arguments equgb_ {E R1 R2} RR eq t1 t2/.

#[global] Instance Reflexive_equg {E X}: Reflexive (@equg E X X eq).
Proof.
  apply Reflexive_gt. typeclasses eauto.
Qed.

#[global] Instance Symmetric_equg {E X}: Symmetric (@equg E X X eq).
Proof.
  apply Symmetric_gt. typeclasses eauto.
Qed.

Theorem equ_clos_gt {E X} : @equ_clos E X X <= gt eq.
Proof.
  apply Coinduction. cbn. intros.
  destruct H. cbn in HR.
  setoid_rewrite (ctree_eta t') in Equt. setoid_rewrite (ctree_eta u') in Equu.
  genobs t' ot'. genobs u' ou'.
  clear t' Heqot' u' Heqou'.
  revert t Equt u Equu. induction HR; intros; subst.
  - unfold equ in *.
    apply (gfp_fp (fequ eq) t (Ret y)) in Equt.
    cbn in Equt. inv Equt.
    apply (gfp_fp (fequ eq) (Ret y) u) in Equu.
    cbn in Equu. inv Equu.
    constructor. reflexivity.
  - step in Equt. dependent induction Equt.
    step in Equu. dependent induction Equu.
    cbn. rewrite <- x, <- x0. constructor. intros. apply (f_Tf (fequg eq)).
    econstructor. 2: apply REL. all: eauto.
  - step in Equt. dependent induction Equt.
    cbn. rewrite <- x. econstructor. intros. assert (x0 = Fin.F1). dependent induction x0. reflexivity. now apply Fin.case0. subst. reflexivity.
    apply IHHR; auto. rewrite <- (Hk Fin.F1), <- ctree_eta, REL. reflexivity.
  - step in Equu. dependent induction Equu.
    cbn. rewrite <- x. econstructor. intros. assert (x0 = Fin.F1). dependent induction x0. reflexivity. now apply Fin.case0. subst. reflexivity.
    apply IHHR; auto. rewrite <- (Hk Fin.F1), <- ctree_eta, REL. reflexivity.
  - step in Equt. dependent induction Equt.
    step in Equu. dependent induction Equu.
    cbn. rewrite <- x, <- x0. constructor. intros. apply (f_Tf (fequg eq)).
    econstructor. 2: apply REL. all: eauto.
Qed.

(*|
Dependent inversion of [equ] and [equb] equations
-------------------------------------------------
We assume [JMeq_eq] to invert easily bisimilarity of dependently typed constructors
|*)
Lemma equg_vis_invT {E X Y S} (e1 : E X) (e2 : E Y) (k1 : X -> ctree E S) k2 :
  Vis e1 k1 (G≅) Vis e2 k2 ->
  X = Y.
Proof.
  intros EQ.
	step in EQ. dependent induction EQ; auto.
Qed.

Lemma equg_vis_invE {E X S} (e1 e2 : E X) (k1 k2 : X -> ctree E S) :
  Vis e1 k1 (G≅) Vis e2 k2 ->
  e1 = e2 /\ forall x, k1 x (G≅) k2 x.
Proof.
  intros EQ; step in EQ.
	inv EQ.
	dependent destruction H2.
	dependent destruction H4.
	auto.
Qed.

Lemma equg_br_invT {E S b b' n m} (k1 : _ -> ctree E S) k2 :
  Br b n k1 (G≅) Br b' m k2 ->
  n <> 1 -> m <> 1 ->
  n = m /\ b = b'.
Proof.
  intros EQ; step in EQ.
	dependent destruction EQ; intuition.
Qed.

Lemma equg_br_invE {E S b n} (k1 : _ -> ctree E S) k2 :
  Br b n k1 (G≅) Br b n k2 ->
  n <> 1 ->
  forall x, k1 x (G≅) k2 x.
Proof.
  intros EQ; step in EQ. cbn in EQ.
	dependent induction EQ; intuition.
Qed.

Lemma equgb_vis_invT {E X Y S} (e1 : E X) (e2 : E Y) (k1 : X -> ctree E S) k2 :
  equb eq (equg eq) (VisF e1 k1) (VisF e2 k2) ->
  X = Y.
Proof.
  intros EQ.
	dependent induction EQ; auto.
Qed.

Lemma equgb_vis_invE {E X S} (e1 e2 : E X) (k1 k2 : X -> ctree E S) :
  equb eq (equg eq) (VisF e1 k1) (VisF e2 k2) ->
  e1 = e2 /\ forall x, equg eq (k1 x) (k2 x).
Proof.
  intros EQ.
	inv EQ.
	dependent destruction H; dependent destruction H4; auto.
Qed.

Lemma equgb_br_invT {E S b b' n m} (k1 : _ -> ctree E S) k2 :
  equb eq (equg eq) (BrF b n k1) (BrF b' m k2) ->
  n <> 1 -> m <> 1 ->
  n = m /\ b = b'.
Proof.
  intros EQ.
	dependent induction EQ; intuition.
Qed.

Lemma equgb_br_invE {E S b n} (k1 : _ -> ctree E S) k2 :
  equb eq (equg eq) (BrF b n k1) (BrF b n k2) ->
  n <> 1 ->
  forall x, equg eq (k1 x) (k2 x).
Proof.
  intros EQ.
	dependent induction EQ; intuition.
Qed.

#[global] Instance equg_observe {E R} :
  Proper (equg eq ==> going (equg eq)) (@observe E R).
Proof.
  constructor. step in H.
  now step.
Qed.

#[global] Instance equg_BrF {E R} b n :
  Proper (pointwise_relation _ (equg eq) ==> going (equg eq)) (@BrF E R _ b n).
Proof.
  constructor. red in H. step. econstructor; eauto.
Qed.

#[global] Instance equg_VisF {E R X} (e : E X) :
  Proper (pointwise_relation _ (equg eq) ==> going (equg eq)) (@VisF E R _ _ e).
Proof.
  constructor. red in H. step. econstructor; eauto.
Qed.

#[global] Instance observing_sub_equg E R :
  subrelation (@observing E R R eq) (equg eq).
Proof.
  repeat intro.
  step. rewrite (observing_observe H). apply Reflexive_equgb; eauto.
Qed.

#[global] Instance equ_clos_gt_goal E X RR :
  Proper (@equ E X X eq ==> equ eq ==> flip impl) (gt eq RR).
Proof.
  cbn; intros ? ? eq1 ? ? eq2 H.
  apply (ft_t equ_clos_gt); econstructor; [eauto | | symmetry; eauto]; assumption.
Qed.

#[global] Instance equ_clos_gt_ctx E X RR :
  Proper (@equ E X X eq ==> equ eq ==> impl) (gt eq RR).
Proof.
  cbn; intros ? ? eq1 ? ? eq2 H.
  apply (ft_t equ_clos_gt); econstructor; [symmetry; eauto | | eauto]; assumption.
Qed.

#[global] Instance equ_gbt_closed_goal E X {r} :
  Proper (@equ E X X eq ==> equ eq ==> flip impl) (gbt eq r).
Proof.
  repeat intro.
  apply (fbt_bt equ_clos_gt); econstructor; [eauto | | symmetry; eauto]; assumption.
Qed.

#[global] Instance equ_gbt_closed_ctx E X {r} :
  Proper (@equ E X X eq ==> equ eq ==> impl) (gbt eq r).
Proof.
  repeat intro.
  apply (fbt_bt equ_clos_gt); econstructor; [symmetry; eauto | | eauto]; assumption.
Qed.

#[global] Instance equ_clos_gT_goal E X RR f :
  Proper (@equ E X X eq ==> equ eq ==> flip impl) (gT eq f RR).
Proof.
  cbn; intros ? ? eq1 ? ? eq2 H.
  apply (fT_T equ_clos_gt); econstructor; [eauto | | symmetry; eauto]; assumption.
Qed.

#[global] Instance equ_clos_gT_ctx E X RR f :
  Proper (@equ E X X eq ==> equ eq ==> impl) (gT eq f RR).
Proof.
  cbn; intros ? ? eq1 ? ? eq2 H.
  apply (fT_T equ_clos_gt); econstructor; [symmetry; eauto | | eauto]; assumption.
Qed.

#[global] Instance equ_clos_equg_goal E X :
  Proper (@equ E X X eq ==> equ eq ==> flip impl) (equg eq).
Proof.
  cbn; intros ? ? eq1 ? ? eq2 H.
  apply (ft_t equ_clos_gt); econstructor; [eauto | | symmetry; eauto]; assumption.
Qed.

#[global] Instance equ_clos_equg_ctx E X :
  Proper (@equ E X X eq ==> equ eq ==> impl) (equg eq).
Proof.
  cbn; intros ? ? eq1 ? ? eq2 H.
  apply (ft_t equ_clos_gt); econstructor; [symmetry; eauto | | eauto]; assumption.
Qed.

Ltac _apply f :=
  match goal with
    |- context [@body ?x ?l ?y] => apply (f _ l)
  end.


(*|
Up-to bind principle
~~~~~~~~~~~~~~~~~~~~
Specialization of [bind_ctx] to the [equg]-based closure we are
looking for, and the proof of validity of the principle. As
always with the companion, we prove that it is valid by proving
that it is below the companion.
|*)
Section bind.

  Context {E: Type -> Type} {X1 X2 Y1 Y2: Type}.

(*|
Specialization of [bind_ctx] to a function acting with [equ] on the bound value,
and with the argument (pointwise) on the continuation.
|*)
  Program Definition bind_ctx_equg SS: mon (rel (ctree E Y1) (ctree E Y2)) :=
    {|body := fun R => @bind_ctx E X1 X2 Y1 Y2 (equg SS) (pointwise SS R) |}.
  Next Obligation.
    eapply leq_bind_ctx; eauto. intros ?? H' ?? H''.
    apply in_bind_ctx. apply H'. intros t t' HS. apply H, H'', HS.
  Qed.

(*|
The resulting enhancing function gives a valid up-to technique
|*)
  Lemma bind_ctx_equg_t (SS : rel X1 X2) (RR : rel Y1 Y2): bind_ctx_equg SS <= gt RR.
  Proof.
    apply Coinduction. intros R. apply (leq_bind_ctx _).
    intros x x' xx' k k' kk'.
    step in xx'.
    cbn; unfold observe; cbn.
    genobs x ox. genobs x' ox'. clear x Heqox x' Heqox'. induction xx'.
    - cbn in *.
      generalize (kk' _ _ REL).
      apply (fequg RR).
      apply id_T.
    - constructor; intros ?. apply (fTf_Tf (fequg _)).
      apply in_bind_ctx. apply REL.
      red; intros. apply (b_T (fequg _)), kk'; auto.
    - econstructor. intros. rewrite Hk. reflexivity. apply IHxx'.
    - econstructor. intros. rewrite Hk. reflexivity. apply IHxx'.
    - constructor. intro a. apply (fTf_Tf (fequg _)).
      apply in_bind_ctx. apply REL.
      red; intros. apply (b_T (fequg _)), kk'; auto.
  Qed.

End bind.

(*|
Expliciting the reasoning rule provided by the up-to principle.
|*)

Lemma gt_clo_bind (E: Type -> Type) (X1 X2 Y1 Y2 : Type) :
	forall (t1 : ctree E X1) (t2 : ctree E X2) (k1 : X1 -> ctree E Y1) (k2 : X2 -> ctree E Y2)
    (S : rel X1 X2) (R : rel Y1 Y2) RR,
		equg S t1 t2 ->
    (forall x1 x2, S x1 x2 -> gt R RR (k1 x1) (k2 x2)) ->
    gt R RR (bind t1 k1) (bind t2 k2)
.
Proof.
  intros.
  apply (ft_t (bind_ctx_equg_t S R)).
  now apply in_bind_ctx.
Qed.

Lemma gt_clo_bind_eq (E: Type -> Type) (X Y1 Y2 : Type) :
	forall (t : ctree E X) (k1 : X -> ctree E Y1) (k2 : X -> ctree E Y2)
    (R : rel Y1 Y2) RR,
    (forall x, gt R RR (k1 x) (k2 x)) ->
    gt R RR (bind t k1) (bind t k2)
.
Proof.
  intros * EQ.
  apply (ft_t (bind_ctx_equg_t (X2 := X) eq R)).
  apply in_bind_ctx. reflexivity.
  intros ? ? <-.
  apply EQ.
Qed.

(*|
And in particular, we get the proper instance justifying rewriting [equg]
to the left of a [bind].
|*)
#[global] Instance bind_equg_cong_gen :
 forall (E : Type -> Type) (X Y : Type) (R : rel Y Y) RR,
   Proper (equg (@eq X) ==> pointwise_relation X (gt R RR) ==> gt R RR) (@bind E X Y).
Proof.
  repeat red. intros.
  eapply gt_clo_bind; eauto.
  intros ? ? <-; auto.
Qed.

(*|
Specializing these congruence lemmas at the [sbisim] level for equational proofs
|*)
Lemma equg_clo_bind (E: Type -> Type) (X1 X2 Y1 Y2 : Type) :
	forall (t1 : ctree E X1) (t2 : ctree E X2) (k1 : X1 -> ctree E Y1) (k2 : X2 -> ctree E Y2)
    (S : rel X1 X2) (R : rel Y1 Y2),
		equg S t1 t2 ->
    (forall x1 x2, S x1 x2 -> equg R (k1 x1) (k2 x2)) ->
    equg R (bind t1 k1) (bind t2 k2)
.
Proof.
  intros.
  apply (ft_t (bind_ctx_equg_t S R)).
  now apply in_bind_ctx.
Qed.

Lemma equg_clo_bind_eq (E: Type -> Type) (X Y1 Y2 : Type) :
	forall (t : ctree E X) (k1 : X -> ctree E Y1) (k2 : X -> ctree E Y2)
    (R : rel Y1 Y2),
    (forall x, equg R (k1 x) (k2 x)) ->
    equg R (bind t k1) (bind t k2)
.
Proof.
  intros * EQ.
  apply (ft_t (bind_ctx_equg_t (X2 := X) eq R)).
  apply in_bind_ctx. reflexivity.
  intros ? ? <-.
  apply EQ.
Qed.

Ltac __upto_bind_equg' SS :=
  match goal with
    (* Out of a coinductive proof --- terminology abuse, this is simply using the congruence of the relation, not a upto *)
    |- @equg ?E ?R1 ?R2 ?RR (CTree.bind (T := ?T1) _ _) (CTree.bind (T := ?T2) _ _) =>
      apply (@equg_clo_bind E T1 T2 R1 R2 _ _ _ _ SS RR)

    (* Upto when unguarded *)
  | |- body (t (@fequg ?E ?R1 ?R2 ?RR)) ?R (CTree.bind (T := ?T1) _ _) (CTree.bind (T := ?T2) _ _) =>
        apply (ft_t (@bind_ctx_equg_t E T1 T2 R1 R2 SS RR)), in_bind_ctx

    (* Upto when guarded *)
  | |- body (bt (@fequg ?E ?R1 ?R2 ?RR)) ?R (CTree.bind (T := ?T1) _ _) (CTree.bind (T := ?T2) _ _) =>
      apply (fbt_bt (@bind_ctx_equg_t E T1 T2 R1 R2 SS RR)), in_bind_ctx
  end.
Tactic Notation "__upto_bind_equg" uconstr(eq) := __upto_bind_equg' eq.

Ltac __eupto_bind_equg :=
  match goal with
    (* Out of a coinductive proof --- terminology abuse, this is simply using the congruence of the relation, not a upto *)
    |- @equg ?E ?R1 ?R2 ?RR (CTree.bind (T := ?T1) _ _) (CTree.bind (T := ?T2) _ _) =>
      eapply (@equg_clo_bind E T1 T2 R1 R2 _ _ _ _ _ RR)

    (* Upto when unguarded *)
  | |- body (t (@fequg ?E ?R1 ?R2 ?RR)) ?R (CTree.bind (T := ?T1) _ _) (CTree.bind (T := ?T2) _ _) =>
        eapply (ft_t (@bind_ctx_equg_t E T1 T2 R1 R2 _ RR)), in_bind_ctx

    (* Upto when guarded *)
  | |- body (bt (@fequg ?E ?R1 ?R2 ?RR)) ?R (CTree.bind (T := ?T1) _ _) (CTree.bind (T := ?T2) _ _) =>
      eapply (fbt_bt (@bind_ctx_equg_t E T1 T2 R1 R2 _ RR)), in_bind_ctx
  end.

Ltac __upto_bind_eq_equg :=
  __upto_bind_equg eq; [reflexivity | intros ? ? <-].

(*|
[utg] is an up-to-guard principle. This is not as powerful as euttge,
but it's just enough to asymmetrically remove a guard in an equg proof.
|*)

Section UpToGuard.

  Program Definition utg {E X} : mon (relation (ctree E X)) := {| body :=
    fun R x y =>
      R x y \/
      match observe x with
      | BrDF 1 k => R (k Fin.F1) y
      | _ => False
      end
    |}.

  Next Obligation.
    repeat intro. cbn. unfold impl in H.
    destruct (observe a) eqn:?; intuition.
    destruct vis; intuition.
    destruct n; intuition.
    destruct n; intuition.
  Qed.

  Theorem utg_t {E X} : @utg E X <= gt eq.
  Proof.
    eapply leq_t. cbn. repeat red. repeat intro.
    destruct (observe a0) eqn:?.
    - eapply equgb_sub. 2: { destruct H; eauto. destruct f. } auto.
    - eapply equgb_sub. 2: { destruct H; eauto. destruct f. } auto.
    - destruct vis.
      + eapply equgb_sub. 2: { destruct H; eauto. destruct f. } auto.
      + destruct n; auto.
        { eapply equgb_sub. 2: { destruct H; eauto. destruct f. } auto. }
        destruct n.
        2: { eapply equgb_sub. 2: { destruct H; eauto. destruct f. } auto. }
        destruct H.
        * eapply equgb_sub. 2: { apply H. }
          auto.
        * eapply Eqg_GuardL. intros. dependent induction x. reflexivity. now apply Fin.case0.
          eapply equgb_sub. 2: { apply H. } auto.
  Qed.

End UpToGuard.

(*|
[equg] is a subrelation of [sbisim].
|*)
Section equg_sbisim.

  Import EquNotations.

  (* dirty copy from Interp.v *)
  Inductive t0_det {E X} : relation (ctree E X) :=
  | t0_det_id : forall t t', t ≅ t' -> t0_det t t'
  | t0_det_tau : forall k t' t'',
      t0_det (k Fin.F1) t' -> t'' ≅  BrD 1 k -> t0_det t'' t'.

  #[global] Instance t0_det_equ : forall {E X}, Proper (equ eq ==> equ eq ==> flip impl) (@t0_det E X).
  Proof.
    repeat intro.
    revert x H. induction H1; intros.
    - econstructor. now rewrite H0, H1.
    - eapply t0_det_tau. apply IHt0_det. apply H0. reflexivity. rewrite H2. apply H.
  Qed.

  #[global] Instance t0_det_equ' : forall {E X}, Proper (equ eq ==> equ eq ==> impl) (@t0_det E X).
  Proof.
    cbn. repeat intro. rewrite <- H, <- H0. apply H1.
  Qed.

  Lemma t0_det_trans {E X} : forall (t0 t u : ctree E X) l,
    t0_det t0 t ->
    trans l t u ->
    trans l t0 u.
  Proof.
    intros.
    induction H.
    - rewrite H. apply H0.
    - rewrite H1.
      apply IHt0_det in H0.
      eapply trans_brD in H0. 2: reflexivity. apply H0.
  Qed.

  Theorem equg_t0 {E X} : forall (t u : ctree E X),
    t (G≅) u ->
    exists t' u', t0_det t t' /\ t0_det u u' /\ fequ eq (equg eq) t' u'.
  Proof.
    intros.
    step in H. cbn in H.
    setoid_rewrite (ctree_eta t). setoid_rewrite (ctree_eta u).
    genobs t ot. genobs u ou. clear t Heqot u Heqou.
    induction H; intros; subst.
    - eexists _, _. split. now left. split. now left. constructor. reflexivity.
    - eexists _, _. split. now left. split. now left. constructor. apply REL.
    - destruct IHequgb as (? & ? & ? & ? & ?).
      exists x, x0.
      split. { eright. 2: reflexivity. rewrite Hk, ctree_eta. apply H0. }
      split. { apply H1. }
      apply H2.
    - destruct IHequgb as (? & ? & ? & ? & ?).
      exists x, x0.
      split. { apply H0. }
      split. { eright. 2: reflexivity. rewrite Hk, ctree_eta. apply H1. }
      apply H2.
    - eexists _, _. split. now left. split. now left. constructor. apply REL.
  Qed.

  Theorem equg_vis {E X Y} : forall (u : ctree E X) (e : E Y) k,
    Vis e k (G≅) u ->
    exists k', t0_det u (Vis e k') /\ forall x, k x (G≅) k' x.
  Proof.
    intros.
    apply equg_t0 in H as (? & ? & ? & ? & ?).
    inversion H; subst. 2: { step in H3. dependent induction H3. }
    rewrite (ctree_eta x) in H2.
    inversion H1; subst.
    - rewrite <- H4 in H2. step in H2. inv H2.
    - rewrite <- H4 in H2.
      apply equ_vis_invT in H2 as ?. subst.
      apply equ_vis_invE in H2 as [<- ?].
      exists k2. split. rewrite H5, <- ctree_eta. apply H0.
      intros. rewrite H2. apply REL.
    - rewrite <- H4 in H2. step in H2. inv H2.
  Qed.

  Theorem equg_br {E X} : forall (u : ctree E X) b n k,
    Br b n k (G≅) u ->
    b = true \/ n <> 1 ->
    exists k', t0_det u (Br b n k') /\ forall x, k x (G≅) k' x.
  Proof.
    intros.
    apply equg_t0 in H as (? & ? & ? & ? & ?).
    inversion H; subst. 2: {
      apply equ_br_invT in H4 as ?. destruct H5 as [-> ->].
      destruct H0. discriminate. exfalso. auto.
    }
    rewrite (ctree_eta x) in H3.
    inversion H2; subst.
    - rewrite <- H5 in H3. step in H3. inv H3.
    - rewrite <- H5 in H3. step in H3. inv H3.
    - rewrite <- H5 in H3.
      apply equ_br_invT in H3 as ?. destruct H4 as [<- <-].
      pose proof (equ_br_invE _ _ H3).
      exists k2. split. rewrite H6, <- ctree_eta. apply H1.
      intros. rewrite H4. apply REL.
  Qed.

  Theorem equg_ret {E X} : forall (u : ctree E X) r,
    Ret r (G≅) u ->
    t0_det u (Ret r).
  Proof.
    intros.
    apply equg_t0 in H as (? & ? & ? & ? & ?).
    inversion H; subst. 2: { step in H3. inv H3. }
    rewrite (ctree_eta x) in H2.
    inversion H1; subst.
    - rewrite <- H4 in H2.
      step in H2. inv H2.
      rewrite H5, <- ctree_eta. apply H0.
    - rewrite <- H4 in H2. step in H2. inv H2.
    - rewrite <- H4 in H2. step in H2. inv H2.
  Qed.

  Theorem equg_trans {E X} : forall (t u t' : ctree E X) l,
    t (G≅) u ->
    trans l t t' ->
    exists u', trans l u u' /\ t' (G≅) u'.
  Proof.
    intros.
    do 3 red in H0.
    genobs t ot. genobs t' ot'.
    revert t Heqot t' Heqot' u H.
    induction H0; intros; subst.
    - rewrite ctree_eta, <- Heqot in H.
      specialize (IHtrans_ _ eq_refl _ eq_refl).
      clear t0 Heqot.
      step in H. cbn in H.
      remember (BrDF n k) as ot.
      setoid_rewrite (ctree_eta u).
      genobs u ou.
      revert u Heqou.
      induction H; intros; subst.
      + discriminate.
      + discriminate.
      + apply Br_eq1 in Heqot as ?. destruct H1 as [_ <-].
        apply Br_eq2 in Heqot. subst.
        apply IHtrans_. rewrite Hk. step. apply H.
      + rewrite <- (Hk Fin.F1) in H.
        specialize (IHequgb eq_refl t2 eq_refl).
        destruct IHequgb as (? & ? & ?).
        exists x0. split. eapply trans_brD with (x := Fin.F1). 2: reflexivity.
        rewrite (Hk Fin.F1), ctree_eta. apply H1. apply H2.
      + apply Br_eq1 in Heqot as ?. destruct H as [-> <-].
        apply Br_eq2 in Heqot. subst.
        specialize (REL x). apply IHtrans_ in REL as (? & ? & ?).
        exists x0. split; auto. etrans.
    - rewrite ctree_eta, <- Heqot in H0.
      apply equg_br in H0 as (? & ? & ?).
      2: { left. reflexivity. }
      exists (x0 x). split. eapply t0_det_trans; etrans.
      rewrite ctree_eta, <- Heqot', <- H, <- ctree_eta. apply H1.
    - rewrite ctree_eta, <- Heqot in H0.
      apply equg_vis in H0 as (? & ? & ?).
      exists (x0 x). split. eapply t0_det_trans; etrans.
      rewrite ctree_eta, <- Heqot', <- H, <- ctree_eta. apply H1.
    - rewrite ctree_eta, <- Heqot in H.
      exists stuckD. apply equg_ret in H. split. eapply t0_det_trans; etrans.
      step. rewrite <- Heqot'. apply Eqg_Br. now apply Fin.case0.
  Qed.

  Theorem equg_sbisim {E X} : subrelation (equg eq) (@sbisim E X).
  Proof.
    red. __coinduction_sbisim R CH.
    symmetric using idtac.
    { intros. apply H. now symmetry. }
    cbn. intros. eapply equg_trans in H0 as ?. 2: apply H. destruct H1 as (? & ? & ?).
    exists x0. apply H1. apply CH. apply H2.
  Qed.

End equg_sbisim.
