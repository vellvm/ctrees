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
     Data.List
     Data.Map.FMapAList.

From ITree Require Import
     ITree
     Basics.CategoryKleisli
     Events.State
     Events.StateFacts.

From CTree Require Import
     CTrees
     Utils.

From CTreeYield Require Import
     Par.

(* From ITree Require Import *)
(*      ITree *)
(*      ITreeFacts *)
(*      Events.MapDefault *)
(*      Events.StateFacts. *)

(* Import Monads. *)
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
| Spawn  (t : stmt)
| Skip                           (* ; *)
.

Variant ImpState : Type -> Type :=
| GetVar (x : var) : ImpState value
| SetVar (x : var) (v : value) : ImpState unit.

Section Denote1.
  (* Definition E : Type -> Type := stateE value +' spawnE. *)

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

    | Spawn t => vis Par.Spawn (fun b : bool =>
                                 if b
                                 then (denote_imp t;; ChoiceI 0 (fun _ => ret tt)) (* force the thread to halt here *)
                                 else ret tt)
    | Skip => ret tt

    (* | Atomic t => translate ... (denote_imp t) *)
    end.

  Definition h_state {E} `{yieldE value -< E} : forall X, stateE value X -> Monads.stateT value (ctree E) X :=
    fun _ e s =>
      match e with
      | Get _ => Ret (s, s)
      | Put _ s' => Ret (s', tt)
      end.

  Definition h_state_yield {E} `{yieldE value -< E} : forall X, stateE value X -> Monads.stateT value (ctree E) X :=
    fun _ e s =>
      match e with
      | Get _ => s' <- trigger (Yield _ s);; Ret (s', s')
      | Put _ s' => s'' <- trigger (Yield _ s');; Ret (s'', tt)
      end.

  #[global] Instance MonadChoice_stateT {M S} {MM : Monad M} {AM : Utils.MonadChoice M}
    : Utils.MonadChoice (Monads.stateT S M).
  Admitted.

  Definition handler : forall X, (stateE value +' spawnE) X -> Monads.stateT value (ctree (parE value)) X :=
    (fun X (e : (stateE value +' spawnE) X) =>
       match e with
       | inl1 e' => h_state _ e'
       | inr1 e' =>
         match e' in spawnE R return Monads.stateT value (ctree (parE value)) R with
         | Par.Spawn => fun s => b <- trigger Par.Spawn;; Ret(s, b) (* TODO: use MonadTrigger *)
         end
       end).

  Definition interp_state (t : ctree (stateE value +' spawnE) unit) : thread :=
    Interp.interp handler t.

  Definition schedule_denot (t : stmt) : completed :=
    schedule (interp_state (denote_imp t)) [].

End Denote1.
