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

(* Universe issue, TO FIX *)
Unset Universe Checking.
Unset Auto Template Polymorphism.

From ITree Require Import
     ITree
     Basics.CategoryKleisli
     Events.State
     Events.StateFacts.

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

(** Imp manipulates a countable set of variables represented as [string]s: *)
Definition var : Set := string.

(** For simplicity, the language manipulates [nat]s as values. *)
Definition value : Type := nat.

Inductive expr : Type :=
| Var (_ : var)
| Lit (_ : value)
| Plus  (_ _ : expr)
| Minus (_ _ : expr)
| Mult  (_ _ : expr).

(** Classic Imp plus a non-deterministic branching statement *)
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

Section Denote1.
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

    | Branch a b => choiceI2 (denote_imp a) (denote_imp b)

    | Skip => ret tt

    | Block => CTree.stuckI

    end.

  Lemma branch_commut : forall (a b : stmt), denote_imp (Branch a b) ~ denote_imp (Branch b a).
  Proof.
    intros. cbn. apply choiceI2_commut.
  Qed.

  Lemma branch_assoc : forall (a b c : stmt), denote_imp (Branch a (Branch b c)) ~ denote_imp (Branch (Branch a b) c).
  Proof.
    intros. cbn. rewrite choiceI2_assoc. reflexivity.
  Qed.
  
  Lemma branch_idem : forall a : stmt, denote_imp (Branch a a) ~ denote_imp a.
  Proof.
    cbn. intros. apply choiceI2_idem.
  Qed.

  Lemma branch_block_l : forall a : stmt, denote_imp (Branch Block a) ~ denote_imp a.
  Proof.
    cbn. intros. apply choiceI2_stuckI_l.
  Qed.

  Lemma branch_block_r : forall a : stmt, denote_imp (Branch a Block) ~ denote_imp a.
  Proof.
    cbn. intros. apply choiceI2_stuckI_r.
  Qed.

  Lemma branch_block_r_interp : forall (a : stmt) s,
    interp_state (@h_state _ void1) (denote_imp (Branch a Block)) s ~
    interp_state (@h_state _ void1) (denote_imp a) s.
  Proof.
    assert (forall X (e : stateE value X) s, vsimple (h_state (E := void1) e s)).
    { unfold h_state, vsimple. intros. destruct e; eauto. }
    epose proof interp_state_sbisim (h_state (S := value)) H.
    intros. rewrite branch_block_r. reflexivity.
  Qed.

  Lemma branch_congr : forall a a' b b',
    denote_imp a ~ denote_imp a' ->
    denote_imp b ~ denote_imp b' ->
    denote_imp (Branch a b) ~ denote_imp (Branch a' b').
  Proof.
    intros. cbn. apply sb_choiceI_id.
    intro; destruct x; rewrite ?H, ?H0; reflexivity.
  Qed.

  Example branch_ex : forall s : value,
    interp_state (@h_state _ void1) (denote_imp (
      Branch
        (Seq
          (Assign "x" (Lit 0))
          (Assign "x" (Lit 1)))
        Block
    )) s ~
    interp_state (@h_state _ _) (denote_imp (Assign "x" (Lit 1))) s.
  Proof.
    intros. rewrite branch_block_r_interp.
    rewrite 2 unfold_interp_state.
    cbn. setoid_rewrite sb_tauI.
    setoid_rewrite bind_ret_l. rewrite interp_state_ret.
    play. inv_trans.
    - rewrite unfold_interp_state in TR. cbn in TR. rewrite bind_ret_l in TR.
      inv_trans. cbn in TR.
      rewrite unfold_interp_state in TR. cbn in TR.
      inv_trans. subst.
      apply equ_sbisim_subrelation in EQ. etrans.
    - inv_trans. subst. eexists.
      rewrite unfold_interp_state. cbn. rewrite bind_ret_l.
      apply trans_tauI. rewrite unfold_interp_state. cbn. etrans.
      now rewrite EQ.
  Qed.

End Denote1.
