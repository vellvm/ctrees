From Coq Require Import
     Arith.PeanoNat
     Lists.List
     Strings.String
     Morphisms
     Setoid
     RelationClasses.

From ExtLib Require Import
     Data.String
     Structures.Monad
     Structures.Traversable
     Data.Monads.StateMonad
     Data.List
     Data.Map.FMapAList.

From ITree Require Import
     ITree
     Basics.CategoryKleisli
     Events.State.

From Coinduction Require Import
	coinduction rel tactics.

From CTree Require Import
     CTree
     Eq
     Interp.Interp
     Interp.State.

Import ListNotations.
Import MonadNotation.
Local Open Scope monad_scope.
Local Open Scope string_scope.

(*|
Imp manipulates a countable set of variables represented as [string]s:
|*)
Definition var : Set := string.

(*|
For simplicity, the language manipulates [nat]s as values.
|*)
Definition value : Type := nat.

Inductive expr : Type :=
| Var (_ : var)
| Lit (_ : value)
| Plus  (_ _ : expr)
| Minus (_ _ : expr)
| Mult  (_ _ : expr).

(*|
Imp with a non-deterministic branching statement
|*)
Inductive stmt : Type :=
| Assign (x : var) (e : expr)    (* x = e *)
| Seq    (a b : stmt)            (* a ; b *)
| If     (i : expr) (t e : stmt) (* if (i) then { t } else { e } *)
| While  (t : expr) (b : stmt)   (* while (t) { b } *)
| Branch (a b : stmt)            (* br { a } or { b } *)
| Skip                           (* ; *)
| Block
.

Variant ImpState : Type -> Type :=
| GetVar (x : var) : ImpState value
| SetVar (x : var) (v : value) : ImpState unit.

Section Semantics.
  Fixpoint denote_expr (e : expr) : ctree (stateE value) value :=
    match e with
    | Var v     => trigger (Get _)
    | Lit n     => ret n
    | Plus a b  => l <- denote_expr a ;; r <- denote_expr b ;; ret (l + r)
    | Minus a b => l <- denote_expr a ;; r <- denote_expr b ;; ret (l - r)
    | Mult a b  => l <- denote_expr a ;; r <- denote_expr b ;; ret (l * r)
    end.

  Definition while (step : ctree (stateE value) (unit + unit)) : ctree (stateE value) unit :=
    CTree.iter (fun _ => step) tt.

  Definition is_true (v : value) : bool := if (v =? 0)%nat then false else true.

  Fixpoint denote_imp (s : stmt) : ctree (stateE value) unit :=
    match s with
    | Assign x e =>  v <- denote_expr e ;; trigger (Put _ v)
    | Seq a b    =>  denote_imp a ;; denote_imp b
    | If i t e   =>
      v <- denote_expr i ;;
      if is_true v then denote_imp t else denote_imp e

    | While t b =>
      while (v <- denote_expr t ;;
	         if is_true v
             then denote_imp b ;; ret (inl tt)
             else ret (inr tt))

    | Branch a b => brD2 (denote_imp a) (denote_imp b)

    | Skip => ret tt

    | Block => CTree.stuckD

    end.

  Definition interp_imp : ctree (stateE value) ~> Monads.stateT value (ctree void1) :=
    interp_state (@h_state _ void1).

End Semantics.
Notation "⟦ c ⟧" := (denote_imp c).
Notation "'ℑ' c" := (@interp_imp _ (denote_imp c)) (at level 10).

Section Theory.

(*|
  Given the direct translation of the [Branch] construction, the
  primitive equational theory that we have at the [ctree] level is
  straightforwardly lifted to the language level, more specifically
  at the level of uninterpreted ctrees.
|*)
  Lemma branch_commut : forall (a b : stmt),
      ⟦Branch a b⟧ ~ ⟦Branch b a⟧.
  Proof.
    intros; apply brD2_commut.
  Qed.

  Lemma branch_assoc : forall (a b c : stmt),
      ⟦Branch a (Branch b c)⟧ ~ ⟦Branch (Branch a b) c⟧.
  Proof.
    intros; cbn.
    now rewrite brD2_assoc.
  Qed.

  Lemma branch_idem : forall a : stmt,
      ⟦Branch a a⟧ ~ ⟦a⟧.
  Proof.
    intros; apply brD2_idem.
  Qed.

  Lemma branch_congr : forall a a' b b',
      ⟦a⟧ ~ ⟦a'⟧ ->
      ⟦b⟧ ~ ⟦b'⟧ ->
      ⟦Branch a b⟧ ~ ⟦Branch a' b'⟧.
  Proof.
    intros. cbn. apply sb_brD_id.
    intro; destruct x; rewrite ?H, ?H0; reflexivity.
  Qed.

  Lemma branch_block_l : forall a : stmt,
      ⟦Branch Block a⟧ ~ ⟦a⟧.
  Proof.
    intros; apply brD2_stuckD_l.
  Qed.

  Lemma branch_block_r : forall a : stmt,
      ⟦Branch a Block⟧ ~ ⟦a⟧.
  Proof.
    intros; apply brD2_stuckD_r.
  Qed.

(*|
  Strong bisimilarity at the uninterpreted level can be transported
  freely after interpretation via [interp_state_sbisim].
  For instance here transporting [branch_block_r].
|*)

  Lemma h_state_is_simple :
    forall (X : Type) (e : stateE value X) (s : value), vsimple (E := void1) (h_state e s).
  Proof.
    unfold h_state, vsimple. intros. destruct e; eauto.
  Qed.

  Lemma branch_block_r_interp : forall (a : stmt) s,
    ℑ (Branch a Block) s ~
    ℑ a s.
  Proof.
    epose proof interp_state_sbisim (h_state (S := value)) h_state_is_simple.
    intros. rewrite branch_block_r. reflexivity.
  Qed.

(*|
Finally, we can put bits together to prove that the programs [p3] and [br p2 or p3]
from Section 2 are indeed equivalent.
|*)
  Example branch_ex : forall s : value,
      ℑ (Branch
           (Seq
              (Assign "x" (Lit 0))
              (Assign "x" (Lit 1)))
           Block) s ~
        ℑ (Assign "x" (Lit 1)) s.
  Proof with (unfold interp_imp).
    intros...
    rewrite branch_block_r_interp...
    rewrite 2 unfold_interp_state.
    cbn. setoid_rewrite sb_guard.
    setoid_rewrite bind_ret_l. rewrite interp_state_ret.
    play. inv_trans.
    - rewrite unfold_interp_state in TR. cbn in TR. rewrite bind_ret_l in TR.
      inv_trans. cbn in TR.
      rewrite unfold_interp_state in TR. cbn in TR.
      inv_trans. subst.
      apply equ_sbisim_subrelation in EQ. etrans.
    - inv_trans. subst. eexists.
      rewrite unfold_interp_state. cbn. rewrite bind_ret_l.
      apply trans_guard. rewrite unfold_interp_state. cbn. etrans.
      now rewrite EQ.
  Qed.

End Theory.
