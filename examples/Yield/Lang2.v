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
     Par2.

From Equations Require Import Equations.

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
  Fixpoint denote_expr (e : expr) : ctree (spawnE +' stateE value) value :=
    match e with
    | Var v     => trigger (Get _)
    | Lit n     => ret n
    | Plus a b  => l <- denote_expr a ;; r <- denote_expr b ;; ret (l + r)
    | Minus a b => l <- denote_expr a ;; r <- denote_expr b ;; ret (l - r)
    | Mult a b  => l <- denote_expr a ;; r <- denote_expr b ;; ret (l * r)
    end.

  Definition while (step : ctree (spawnE +' stateE value) (unit + unit)) : ctree (spawnE +' stateE value) unit :=
    CTree.iter (fun _ => step) tt.

  Definition is_true (v : value) : bool := if (v =? 0)%nat then false else true.

  Fixpoint denote_imp (s : stmt) : ctree (spawnE +' stateE value) unit :=
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
        b <- trigger Par2.Spawn;;
        match b with
        | true => denote_imp t;; ChoiceI 0 (fun _ => ret tt) (* force the thread to halt here *)
        | false => ret tt
        end
    | Skip => ret tt

    (* | Atomic t => translate ... (denote_imp t) *)
    end.


  Definition while' (step : ctree (parE value) (unit + unit)) : ctree (parE value) unit :=
    CTree.iter (fun _ => step) tt.
  Fixpoint denote_expr' (e : expr) : ctree (parE value) value :=
    match e with
    | Var v     => x <- trigger (Get _) ;; trigger Yield;; ret x
    | Lit n     => ret n
    | Plus a b  => l <- denote_expr' a ;; r <- denote_expr' b ;; ret (l + r)
    | Minus a b => l <- denote_expr' a ;; r <- denote_expr' b ;; ret (l - r)
    | Mult a b  => l <- denote_expr' a ;; r <- denote_expr' b ;; ret (l * r)
    end.
  Fixpoint denote_imp' (s : stmt) : ctree (parE value) unit :=
    match s with
    | Assign x e =>  v <- denote_expr' e ;; x <- trigger (Put _ v) ;; trigger Yield ;; ret x
    | Seq a b    =>  denote_imp' a ;; denote_imp' b
    | If i t e   =>
      v <- denote_expr' i ;;
      if is_true v then denote_imp' t else denote_imp' e

    | While t b =>
      while' (v <- denote_expr' t ;;
	         if is_true v
             then denote_imp' b ;; ret (inl tt)
             else ret (inr tt))

    | Spawn t =>
        b <- trigger Par2.Spawn;;
        match b with
        | true => denote_imp' t;; ChoiceI 0 (fun _ => ret tt) (* force the thread to halt here *)
        | false => ret tt
        end
    | Skip => ret tt

    (* | Atomic t => translate ... (denote_imp t) *)
    end.

  Definition schedule_denot' (t : stmt) : thread :=
    schedule 1 (fun _ => denote_imp' t) (Some Fin.F1).

  Definition h_state : forall X, stateE value X -> ctree (parE value) X :=
    fun _ e =>
      match e with
      | Get _ => x <- trigger (Get _) ;; trigger Yield ;; Ret x
      | Put _ s' => x <- trigger (Put _ s') ;; trigger Yield ;; Ret x
      end.

  #[global] Instance MonadChoice_stateT {M S} {MM : Monad M} {AM : Utils.MonadChoice M}
    : Utils.MonadChoice (Monads.stateT S M) :=
    fun b n s =>
      f <- choice b n;;
      ret (s, f).

  Definition handler : forall X, (spawnE +' stateE value) X -> ctree (parE value) X :=
    (fun X (e : (spawnE +' stateE value) X) =>
       match e with
       | inl1 e' => trigger e'
       | inr1 e' => h_state _ e'
       end).

  Definition interp_state (t : ctree (spawnE +' stateE value) unit) : thread :=
    Interp.interp handler t.

  Definition schedule_denot (t : stmt) : thread :=
    schedule 1 (fun _ => interp_state (denote_imp t)) (Some Fin.F1).

  Lemma denote_expr_bounded e :
    choiceI_bound 1 (denote_expr' e).
  Proof.
    induction e; cbn; unfold trigger; auto.
    - step. rewrite bind_vis. constructor. intros.
      step. rewrite bind_ret_l. rewrite bind_vis. constructor. intros.
      step. rewrite bind_ret_l. constructor.
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
    choiceI_bound 1 (denote_imp' t).
  Proof.
    induction t; cbn.
    - apply bind_choiceI_bound. apply denote_expr_bounded. intros.
      step. rewrite bind_trigger. constructor. intros.
      step. rewrite bind_trigger. constructor. intros.
      step. constructor.
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

  (* TODO: clean up proof *)
  Lemma interp_state_bounded t :
    choiceI_bound 1 t ->
    choiceI_bound 1 (interp_state t).
  Proof.
    unfold interp_state. unfold Interp.interp. unfold iter. unfold MonadIter_ctree.
    intros. unfold choiceI_bound. revert t H. coinduction r CIH.
    intros. cbn. rewrite unfold_iter.
    cbn. destruct (observe t) eqn:?; cbn. 3: destruct vis.
    - rewrite bind_ret_l. constructor.
    - unfold CTree.map. destruct e; destruct s; cbn.
      + rewrite bind_trigger. rewrite bind_vis. constructor. intros.
        rewrite bind_ret_l. step. constructor; auto.
        intros. apply CIH. step in H. cbn in H. unfold choiceI_bound_ in H. rewrite Heqc in H.
        inversion H. invert. apply H1.
      + rewrite bind_trigger. do 2 rewrite bind_vis. constructor. intros.
        rewrite bind_trigger. do 2 rewrite bind_vis. step. econstructor. intros.
        do 2 rewrite bind_ret_l. step. constructor; auto.
        intros. apply CIH. step in H. cbn in H. unfold choiceI_bound_ in H. rewrite Heqc in H.
        inversion H. invert. apply H1.
      + rewrite bind_trigger. do 2 rewrite bind_vis. constructor. intros.
        rewrite bind_trigger. do 2 rewrite bind_vis. step. econstructor. intros.
        do 2 rewrite bind_ret_l. step. constructor; auto.
        intros. apply CIH. step in H. cbn in H. unfold choiceI_bound_ in H. rewrite Heqc in H.
        inversion H. invert. apply H1.
    - unfold choice. unfold MonadChoice_ctree. unfold CTree.choice.
      do 2 rewrite bind_choice. constructor. intros.
      do 2 rewrite bind_ret_l. step. constructor; auto. intros. apply CIH.
      step in H. cbn in H. unfold choiceI_bound_ in H. rewrite Heqc in H.
      inversion H. invert. apply H1.
    - unfold choice. unfold MonadChoice_ctree. unfold CTree.choice.
      do 2 rewrite bind_choice. constructor.
      2: {
        step in H. cbn in H. unfold choiceI_bound_ in H. rewrite Heqc in H.
        inversion H. invert. apply H3.
      }
      intros.
      do 2 rewrite bind_ret_l. step. constructor; auto. intros. apply CIH.
      step in H. cbn in H. unfold choiceI_bound_ in H. rewrite Heqc in H.
      inversion H. invert. apply H2.
  Qed.

  Lemma schedule_spawns t1 t2 :
    (schedule 1 (fun _ : fin 1 => denote_imp' (Seq (Spawn t1) (Spawn t2))) (Some Fin.F1)) ≅
    TauV (TauV (TauI (schedule 2
                               (cons_vec
                                  (CTree.bind (denote_imp' t2) (fun _ => ChoiceI 0 (fun _ => ret tt)))
                                  (fun _ => CTree.bind (denote_imp' t1) (fun _ => ChoiceI 0 (fun _ => ret tt))))
                               None))).
  Proof.
    rewrite rewrite_schedule. simp schedule_match.
    cbn. CTree.fold_subst.
    step. constructor. intros _.

    rewrite rewrite_schedule. simp schedule_match. simp cons_vec.
    unfold replace_vec. cbn.
    step. constructor. intros _.

    rewrite rewrite_schedule. simp schedule_match. simp cons_vec. cbn.
    step. constructor. intros _.

    apply equ_schedule. intro.
    dependent destruction i.
    - simp remove_vec. simp cons_vec. CTree.fold_subst.
      rewrite bind_ret_l. reflexivity.
    - dependent destruction i; [| inv i].
      simp remove_vec. simp cons_vec.
      unfold remove_front_vec. simp cons_vec. cbn. simp cons_vec.
      rewrite bind_ret_l. rewrite bind_bind.
      eapply equ_clo_bind; auto. intros; subst.
      rewrite bind_choice. step. constructor. intros. inv i.
  Qed.

  (*
  Lemma schedule_order (t1 t2 : ctree (parE value) unit) :
    ChoiceV 2 (fun i' : fin 2 =>
                 schedule 2
                          (cons_vec t1 (fun _ => t2))
                          (Some i')) ~
    ChoiceV 2 (fun i' : fin 2 =>
                 schedule 2
                          (cons_vec t2 (fun _ => t1))
                          (Some i')).
  Proof.
    apply sb_choiceV; intros i.
    - dependent destruction i.
      + exists (Fin.FS Fin.F1). rewrite schedule_perm_2; auto.
        intros. exfalso. dependent destruction i; auto.
        dependent destruction i; auto. inv i.
      + exists (Fin.F1). rewrite schedule_perm_2; auto.
        intros. exfalso. dependent destruction i0; auto.
        dependent destruction i; try inv i.
        dependent destruction i0; try inv i0. auto.
    - dependent destruction i.
      + exists (Fin.FS Fin.F1). rewrite schedule_perm_2; auto.
        intros. exfalso. dependent destruction i; auto.
        dependent destruction i; auto. inv i.
      + exists (Fin.F1). rewrite schedule_perm_2; auto.
        intros. exfalso. dependent destruction i0; auto.
        dependent destruction i; try inv i.
        dependent destruction i0; try inv i0. auto.
  Qed.

  (*   (* permutation lemma would solve immediately *) *)
  (*   revert t1 t2. *)
  (*   coinduction r CIH. intros. *)
  (*   apply step_sb_choiceV; intros i. *)
  (*   - dependent destruction i. *)
  (*     + exists (Fin.FS Fin.F1). *)
  (*       do 2 rewrite rewrite_schedule. simp schedule_match. simp cons_vec. *)
  (*       destruct (observe t1); cbn. *)
  (*       * step. apply step_sb_tauI. rewrite remove_vec_1, remove_vec_2. reflexivity. *)
  (*       * destruct e; [destruct y | destruct s; [destruct s |]]. *)
  (*         -- setoid_rewrite <- (bind_ret_l tt (fun _ => schedule _ _ _)). *)
  (*            do 2 rewrite <- bind_tauI. *)
  (*            apply st_clo_bind; auto. (* TODO: put into separate lemma *) *)
  (*            intros. *)
  (*            do 2 rewrite rewrite_schedule. simp schedule_match. *)
  (*            rewrite replace_vec_1, replace_vec_2. *)
  (*            apply CIH. *)
  (*         -- rewrite replace_vec_1, replace_vec_2. *)
  (*            setoid_rewrite <- (bind_ret_l tt (fun _ => schedule _ _ _)). *)
  (*            do 2 rewrite <- bind_tauV. *)
  (*            apply st_clo_bind; auto. *)
  (*            intros. admit. (* permutation lemma? *) *)
  (*         -- do 2 rewrite <- bind_trigger. *)
  (*            apply st_clo_bind; auto. *)
  (*            intros. *)
  (*            rewrite replace_vec_1, replace_vec_2. *)
  (*            admit. (* also permutation lemma *) *)
  (* Admitted. *)

  Lemma commut_spawns t1 t2 :
    schedule_denot' (Seq (Spawn t1) (Spawn t2)) ~
    schedule_denot' (Seq (Spawn t2) (Spawn t1)).
  Proof.
    unfold schedule_denot'.
    do 2 rewrite schedule_spawns.
    apply sb_tauV. apply sb_tauV. apply sb_tauI_lr.
    do 2 rewrite rewrite_schedule. simp schedule_match.
    apply schedule_order.
  Qed.
*)
End Denote1.
