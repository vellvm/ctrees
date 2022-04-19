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
     Eq.

From CTreeYield Require Import
     Par.

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

Inductive stmt : Type :=
| Assign (x : var) (e : expr)    (* x = e *)
| Seq    (a b : stmt)            (* a ; b *)
| If     (i : expr) (t e : stmt) (* if (i) then { t } else { e } *)
| While  (t : expr) (b : stmt)   (* while (t) { b } *)
| Spawn  (t : stmt)              (* spawn t *)
| Skip                           (* ; *)
.

Variant ImpState : Type -> Type :=
| GetVar (x : var) : ImpState value
| SetVar (x : var) (v : value) : ImpState unit.

Section Denote1.
  Fixpoint denote_expr (e : expr) : ctree (stateE value +' spawnE) value :=
    match e with
    | Var v     => trigger (Get _)
    | Lit n     => ret n
    | Plus a b  => l <- denote_expr a ;; r <- denote_expr b ;; ret (l + r)
    | Minus a b => l <- denote_expr a ;; r <- denote_expr b ;; ret (l - r)
    | Mult a b  => l <- denote_expr a ;; r <- denote_expr b ;; ret (l * r)
    end.

  Definition while (step : ctree (stateE value +' spawnE) (unit + unit)) : ctree (stateE value +' spawnE) unit :=
    CTree.iter (fun _ => step) tt.

  Definition is_true (v : value) : bool := if (v =? 0)%nat then false else true.

  Fixpoint denote_imp (s : stmt) : ctree (stateE value +' spawnE) unit :=
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

    | Spawn t =>
        b <- trigger Par.Spawn;;
        match b with
        | true => denote_imp t;; ChoiceI 0 (fun _ => ret tt) (* force the thread to halt here *)
        | false => ret tt
        end
    | Skip => ret tt

    (* | Atomic t => translate ... (denote_imp t) *)
    end.

  Definition h_state {E} `{yieldE value -< E} : forall X, stateE value X -> Monads.stateT value (ctree E) X :=
    fun _ e s =>
      match e with
      | Get _ => Ret (s, s)
      | Put _ s' => Ret (s', tt)
      end.

  (* The effects take place, then yields *)
  Definition h_state_yield {E} `{yieldE value -< E} : forall X, stateE value X -> Monads.stateT value (ctree E) X :=
    fun _ e s =>
      match e with
      | Get _ => s' <- trigger (Yield _ s);; Ret (s', s)
      | Put _ s' => s'' <- trigger (Yield _ s');; Ret (s'', tt)
      end.

  #[global] Instance MonadChoice_stateT {M S} {MM : Monad M} {AM : Utils.MonadChoice M}
    : Utils.MonadChoice (Monads.stateT S M) :=
    fun b n s =>
      f <- choice b n;;
      ret (s, f).

  Definition handler : forall X, (stateE value +' spawnE) X -> Monads.stateT value (ctree (parE value)) X :=
    (fun X (e : (stateE value +' spawnE) X) =>
       match e with
       | inl1 e' => h_state_yield _ e'
       | inr1 e' =>
         match e' in spawnE R return Monads.stateT value (ctree (parE value)) R with
         | Par.Spawn => fun s => b <- trigger Par.Spawn;; Ret(s, b) (* TODO: use MonadTrigger *)
         end
       end).

  Definition interp_state (t : ctree (stateE value +' spawnE) unit) : thread :=
    Interp.interp handler t.

  Definition schedule_denot (t : stmt) : thread :=
    schedule' 1 (fun _ => (interp_state (denote_imp t))) Fin.F1.

  Lemma denote_expr_bounded e :
    choiceI_bound 1 (denote_expr e).
  Proof.
    induction e; cbn; unfold trigger; auto.
    - step. constructor. intros. step. constructor.
    - step. constructor.
    - apply bind_choiceI_bound; auto.
      intros. apply bind_choiceI_bound; auto.
      intros. step. constructor.
    - apply bind_choiceI_bound; auto.
      intros. apply bind_choiceI_bound; auto.
      intros. step. constructor.
    - apply bind_choiceI_bound; auto.
      intros. apply bind_choiceI_bound; auto.
      intros. step. constructor.
  Qed.

  Lemma denote_stmt_bounded t :
    choiceI_bound 1 (denote_imp t).
  Proof.
    induction t; cbn.
    - apply bind_choiceI_bound. apply denote_expr_bounded.
      intros. step. constructor. intros. step. constructor.
    - apply bind_choiceI_bound; auto.
    - apply bind_choiceI_bound. apply denote_expr_bounded.
      intros. step. step in IHt1. step in IHt2. destruct (is_true x); auto.
    - unfold while. apply iter_choiceI_bound; auto.
      intros. apply bind_choiceI_bound. apply denote_expr_bounded.
      intros. destruct (is_true x).
      + apply bind_choiceI_bound; auto.
        intros. step. constructor.
      + step. constructor.
    - apply bind_choiceI_bound.
      + intros. step. constructor. intros. step. constructor.
      + intros. destruct x.
        * apply bind_choiceI_bound; auto.
          intros. step. constructor; auto. intros. step. constructor.
        * step. constructor.
    - step. constructor.
  Qed.

End Denote1.
