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
     Events.StateFacts
     Events.MapDefault.

From Coinduction Require Import
	coinduction rel tactics.

From CTree Require Import
     CTree
     Eq
     Eq.WBisim
     Interp.

From CTreeYield Require Import
     Par.

From Equations Require Import Equations.

Import ListNotations.
(* Import MonadNotation. *)
Import CTreeNotations.
Import WBisimNotations.
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
| Fork  (t1 t2 : stmt)           (* fork the current thread, first doing t1 in the inactive thread and t2 in the active thread *)
| Skip                           (* ; *)
| YieldS                         (* yield *)
.

Variant MemE : Type -> Type :=
| rd (x : var) : MemE value
| wr (x : var) (v : value) : MemE unit.

Section Denote1.
  Definition is_true (v : value) : bool := if (v =? 0)%nat then false else true.

  Definition while (step : ctree (@parE MemE) (unit + unit)) : ctree (@parE MemE) unit :=
    CTree.iter (fun _ => step) tt.

  Fixpoint denote_expr (e : expr) : ctree (@parE MemE) value :=
    match e with
    | Var v     => x <- trigger (rd v) ;; trigger Yield;; ret x
    | Lit n     => ret n
    | Plus a b  => l <- denote_expr a ;; r <- denote_expr b ;; ret (l + r)%nat
    | Minus a b => l <- denote_expr a ;; r <- denote_expr b ;; ret (l - r)
    | Mult a b  => l <- denote_expr a ;; r <- denote_expr b ;; ret (l * r)
    end.

  Fixpoint denote_imp (s : stmt) : ctree parE unit :=
    match s with
    | Assign x e =>  v <- denote_expr e ;; u <- trigger (wr x v) ;; ret u
    | Seq a b    =>  denote_imp a ;; denote_imp b
    | If i t e   =>
        v <- denote_expr i ;;
        if is_true v then denote_imp t else denote_imp e

    | While t b =>
        while (v <- denote_expr t ;;
	           if is_true v
               then denote_imp b ;; ret (inl tt)
               else ret (inr tt))

    | Fork t1 t2 =>
        b <- trigger Spawn;;
        match b with
        | true => denote_imp t1
        | false => denote_imp t2
        end
    | Skip => ret tt
    | YieldS => trigger Yield
    end.

  Definition interp_concurrency (t : stmt) : completed :=
    schedule 1 (fun _ => denote_imp t) (Some Fin.F1).

  (* specific case for ctree rather than generic monad M *)
  #[global] Instance MonadBr_stateT {S E} : Utils.MonadBr (Monads.stateT S (ctree E)) :=
    fun b n s =>
      f <- mbr b n;;
      ret (s, f).

  Definition handle_MemE : MemE ~> ctree (mapE var 0%nat) :=
    fun _ e =>
      match e with
      | rd x => trigger (LookupDef x)
      | wr x v => trigger (Insert x v)
      end.

  (* list of key value pairs *)
  Definition env := alist var value.

  Definition handle_map {d : value} : mapE var d ~> Monads.stateT env (ctree void1) :=
    fun _ e s =>
      match e with
      | Insert k v => Ret (Maps.add k v s, tt)
      | LookupDef k => Ret (s, lookup_default k d s)
      | Remove k => Ret (Maps.remove k s, tt)
      end.

  Definition interp_map {d : value} : ctree (mapE var d) ~> Monads.stateT env (ctree void1) :=
    interp handle_map.

  Definition interp_MemE (t : stmt) : Monads.stateT env (ctree void1) unit :=
    let t' := interp handle_MemE (interp_concurrency t) in
    interp_map _ t'.

  Lemma denote_expr_bounded e :
    brD_bound 1 (denote_expr e).
  Proof.
    induction e; cbn; unfold trigger; auto.
    - step. rewrite bind_vis. constructor. intros.
      step. rewrite bind_ret_l. rewrite bind_vis. constructor. intros.
      step. rewrite bind_ret_l. constructor.
    - step. constructor.
    - apply bind_brD_bound; auto.
      intros. apply bind_brD_bound; auto.
      intros. step. constructor.
    - apply bind_brD_bound; auto.
      intros. apply bind_brD_bound; auto.
      intros. step. constructor.
    - apply bind_brD_bound; auto.
      intros. apply bind_brD_bound; auto.
      intros. step. constructor.
  Qed.

  Lemma denote_imp_bounded t :
    brD_bound 1 (denote_imp t).
  Proof.
    induction t; cbn.
    - apply bind_brD_bound. apply denote_expr_bounded. intros.
      step. rewrite bind_trigger. constructor. intros.
      (* step. rewrite bind_trigger. constructor. intros. *)
      step. constructor.
    - apply bind_brD_bound; auto.
    - apply bind_brD_bound. apply denote_expr_bounded.
      intros. step. step in IHt1. step in IHt2. destruct (is_true x); auto.
    - unfold while. apply iter_brD_bound; auto.
      intros. apply bind_brD_bound. apply denote_expr_bounded.
      intros. destruct (is_true x).
      + apply bind_brD_bound; auto.
        intros. step. constructor.
      + step. constructor.
    - apply bind_brD_bound.
      + intros. step. constructor. intros. step. constructor.
      + intros. destruct x; auto.
    - step. constructor.
    - step. constructor. intros. step. constructor.
  Qed.

  (*
  (* TODO: clean up proof *)
  Lemma interp_state_bounded t :
    brD_bound 1 t ->
    brD_bound 1 (interp_state t).
  Proof.
    unfold interp_state. unfold Interp.interp. unfold iter. unfold MonadIter_ctree.
    intros. unfold brD_bound. revert t H. coinduction r CIH.
    intros. cbn. rewrite unfold_iter.
    cbn. destruct (observe t) eqn:?; cbn. 3: destruct vis.
    - rewrite bind_ret_l. constructor.
    - unfold CTree.map. destruct e; destruct s; cbn.
      + rewrite bind_trigger. rewrite bind_vis. constructor. intros.
        rewrite bind_ret_l. step. constructor; auto.
        intros. apply CIH. step in H. cbn in H. unfold brD_bound_ in H. rewrite Heqc in H.
        inversion H. invert. apply H1.
      + rewrite bind_trigger. do 2 rewrite bind_vis. constructor. intros.
        rewrite bind_trigger. do 2 rewrite bind_vis. step. econstructor. intros.
        do 2 rewrite bind_ret_l. step. constructor; auto.
        intros. apply CIH. step in H. cbn in H. unfold brD_bound_ in H. rewrite Heqc in H.
        inversion H. invert. apply H1.
      + rewrite bind_trigger. do 2 rewrite bind_vis. constructor. intros.
        rewrite bind_trigger. do 2 rewrite bind_vis. step. econstructor. intros.
        do 2 rewrite bind_ret_l. step. constructor; auto.
        intros. apply CIH. step in H. cbn in H. unfold brD_bound_ in H. rewrite Heqc in H.
        inversion H. invert. apply H1.
    - unfold br. unfold MonadBr_ctree. unfold CTree.br.
      do 2 rewrite bind_br. constructor. intros.
      do 2 rewrite bind_ret_l. step. constructor; auto. intros. apply CIH.
      step in H. cbn in H. unfold brD_bound_ in H. rewrite Heqc in H.
      inversion H. invert. apply H1.
    - unfold br. unfold MonadBr_ctree. unfold CTree.br.
      do 2 rewrite bind_br. constructor.
      2: {
        step in H. cbn in H. unfold brD_bound_ in H. rewrite Heqc in H.
        inversion H. invert. apply H3.
      }
      intros.
      do 2 rewrite bind_ret_l. step. constructor; auto. intros. apply CIH.
      step in H. cbn in H. unfold brD_bound_ in H. rewrite Heqc in H.
      inversion H. invert. apply H2.
  Qed.
   *)
  Lemma schedule_forks t1 t2 :
    (schedule 1 (fun _ : fin 1 => denote_imp (Fork t1 (Fork t2 Skip))) (Some Fin.F1))
      ≅
     Step (Step (Guard
     (schedule 2
               (cons_vec
                  (denote_imp t2)
                  (fun _ => denote_imp t1))
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

    apply equ_schedule. intro i.
    dependent destruction i.
    - simp remove_vec. simp cons_vec. CTree.fold_subst.
      rewrite bind_ret_l. reflexivity.
    - dependent destruction i; [| inv i].
      simp remove_vec. simp cons_vec.
      unfold remove_front_vec. simp cons_vec. cbn. simp cons_vec.
      rewrite bind_ret_l. reflexivity.
      (* rewrite bind_bind. *)
      (* eapply equ_clo_bind; auto. intros; subst. *)
      (* rewrite bind_br. step. constructor. intros. inv i. *)
  Qed.

  Equations p : fin 2 -> fin 2 :=
    p Fin.F1 := Fin.FS Fin.F1;
    p (Fin.FS Fin.F1) := Fin.F1.

  Lemma p_inverse : forall i, p (p i) = i.
  Proof.
    intros. dependent destruction i.
    - simp p; auto.
    - dependent destruction i. simp p; auto. inv i.
  Qed.

  Lemma schedule_order (t1 t1' t2 t2' : ctree (@parE MemE) unit)
    (Hbound1 : brD_bound 1 t1)
    (Hbound2 : brD_bound 1 t2)
    (Hbound1' : brD_bound 1 t1')
    (Hbound2' : brD_bound 1 t2')
    (Ht1 : t1 ~ t1')
    (Ht2 : t2 ~ t2') :
    BrS 2 (fun i' : fin 2 =>
                 schedule 2
                          (cons_vec t1 (fun _ => t2))
                          (Some i')) ~
    BrS 2 (fun i' : fin 2 =>
                 schedule 2
                          (cons_vec t2' (fun _ => t1'))
                          (Some i')).
  Proof.
    apply sb_brS; intros i; exists (p i); [| symmetry];
      apply schedule_permutation with (q:=p);
      try solve [intros i0; dependent destruction i0; simp cons_vec];
      try solve [apply p_inverse];
      try solve [ intros i0; dependent destruction i0;
                  [| dependent destruction i0; [| inv i0]]; simp p; simp cons_vec; auto];
      try solve [ intros i0; dependent destruction i0;
                  [| dependent destruction i0; [| inv i0]]; simp p; simp cons_vec; symmetry; auto].
  Qed.

  Lemma commut_forks s1 s2 :
    interp_concurrency (Fork s1 (Fork s2 Skip)) ~
    interp_concurrency (Fork s2 (Fork s1 Skip)).
  Proof.
    unfold interp_concurrency.
    do 2 rewrite schedule_forks.
    apply sb_step. apply sb_step. apply sb_guard_lr.

    do 2 rewrite rewrite_schedule. simp schedule_match.
    apply schedule_order; try solve [apply denote_imp_bounded]; reflexivity.
  Qed.

  (* we need 2 yields here since spawning also emits a tau *)
  (* [| fork s skip |] = tau tau s
     (tau at spawn, tau when main thread ends, continue with s) *)
  (* [| yield; yield; s |] = tau tau s *)
  Lemma yield_fork s :
    interp_concurrency (Seq YieldS (Seq YieldS s)) ~
    interp_concurrency (Fork s Skip).
  Proof.
    unfold interp_concurrency.

    cbn.
    do 2 rewrite rewrite_schedule. simp schedule_match.
    cbn. CTree.fold_subst. do 2 rewrite replace_vec_unary.

    symmetry. apply sb_guard_r. symmetry.

    rewrite rewrite_schedule. simp schedule_match.
    apply sb_brS_id. intros. dependent destruction x. 2: inv x.

    symmetry.
    rewrite rewrite_schedule. simp schedule_match.
    simp cons_vec. cbn.
    symmetry. apply sb_guard_r. symmetry.
    rewrite remove_vec_cons_2.

    do 2 rewrite rewrite_schedule. simp schedule_match.
    cbn. CTree.fold_subst. apply sb_guard_r.

    rewrite rewrite_schedule. simp schedule_match.
    apply sb_brS_id. intros. dependent destruction x. 2: inv x.
    rewrite replace_vec_unary.

    eapply sbisim_schedule.
    - intro. rewrite bind_ret_l. apply denote_imp_bounded.
    - intro. rewrite bind_ret_l. apply denote_imp_bounded.
    - intros. do 2 rewrite bind_ret_l. reflexivity.
  Qed.

  Lemma fork_skip_equ s :
    interp_concurrency (Fork s Skip) ≅ Step (Guard (Step (interp_concurrency s))).
  Proof.
    unfold interp_concurrency. cbn.

    rewrite rewrite_schedule. simp schedule_match.
    cbn. CTree.fold_subst.
    rewrite replace_vec_unary.
    step. constructor. intros _.

    rewrite rewrite_schedule. simp schedule_match.
    simp cons_vec. cbn. rewrite remove_vec_cons_2.
    step. constructor. intros _.

    rewrite rewrite_schedule. simp schedule_match.
    step. constructor. intros.

    dependent destruction i. 2: inv i.
    apply equ_schedule. repeat intro. rewrite bind_ret_l. reflexivity.
  Qed.

  Lemma yield_equ s :
    interp_concurrency (Seq YieldS s) ≅ Guard (Step (interp_concurrency s)).
  Proof.
    unfold interp_concurrency. cbn.

    rewrite rewrite_schedule. simp schedule_match.
    cbn. CTree.fold_subst.
    rewrite replace_vec_unary.
    step. constructor. intros _.

    rewrite rewrite_schedule. simp schedule_match.
    step. constructor. intros.

    dependent destruction i. 2: inv i.
    apply equ_schedule. repeat intro. rewrite bind_ret_l. reflexivity.
  Qed.

  Lemma fork_skip_yield s :
    interp_concurrency (Fork s Skip) ≈
    interp_concurrency (Seq YieldS s).
  Proof.
    rewrite fork_skip_equ, yield_equ.
    rewrite guard_wb. rewrite step_wb.
    rewrite guard_wb. rewrite step_wb.
    reflexivity.
  Qed.

  Lemma spawn_skip s :
    interp_concurrency (Fork s Skip) ≈ interp_concurrency s.
  Proof.
    rewrite fork_skip_equ.
    rewrite step_wb.
    rewrite guard_wb.
    rewrite step_wb.
    reflexivity.
  Qed.

  Lemma while_true_unfold_sbisim s1 :
    denote_imp (While (Lit 1%nat) s1) ~ denote_imp s1;; denote_imp (While (Lit 1%nat) s1).
  Proof.
    cbn. unfold while. rewrite unfold_iter at 1.
    rewrite bind_ret_l. unfold is_true.
    assert ((1 =? 0)%nat = false) by reflexivity.
    rewrite H. rewrite bind_bind.
    apply sbisim_clo_bind. reflexivity.
    intros _. rewrite bind_ret_l. apply sb_guard.
  Qed.


  Lemma commut_forks_unfold s :
    interp_concurrency (Fork (While (Lit 1%nat) YieldS) (Fork s Skip)) ~
    interp_concurrency (Fork s (Fork (Seq YieldS (While (Lit 1%nat) YieldS)) Skip)).
  Proof.
    unfold interp_concurrency.
    do 2 rewrite schedule_forks.
    apply sb_step. apply sb_step. apply sb_guard_lr.

    do 2 rewrite rewrite_schedule. simp schedule_match.

    apply schedule_order; try solve [apply denote_imp_bounded]; try reflexivity.
    apply while_true_unfold_sbisim.
  Qed.

End Denote1.
