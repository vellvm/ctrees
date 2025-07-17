From Stdlib Require Import
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

From Coinduction Require Import all.

From CTree Require Import
     CTree
     Eq
     Eq.WBisim
     Interp.FoldCTree
     Interp.FoldStateT
.

From CTreeYield Require Import
     Par
     Util.

From Equations Require Import Equations.

Import ListNotations.
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

  Context (E := yieldE +' forkE +' MemE).

  Definition while (step : ctree E void1 (unit + unit)) : ctree E void1 unit :=
    CTree.iter (fun _ => step) tt.

  Fixpoint denote_expr (e : expr) : ctree E void1 value :=
    match e with
    | Var v     => x <- trigger (rd v) ;; trigger Yield;; ret x
    | Lit n     => ret n
    | Plus a b  => l <- denote_expr a ;; r <- denote_expr b ;; ret (l + r)%nat
    | Minus a b => l <- denote_expr a ;; r <- denote_expr b ;; ret (l - r)
    | Mult a b  => l <- denote_expr a ;; r <- denote_expr b ;; ret (l * r)
    end.

  Fixpoint denote_imp (s : stmt) : ctree E void1 unit :=
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
        b <- trigger Par.Fork;;
        match b with
        | true => denote_imp t1
        | false => denote_imp t2
        end
    | Skip => ret tt
    | YieldS => trigger Yield
    end.

  Definition interp_concurrency (t : stmt) : completed :=
    schedule 1 (fun _ => denote_imp t) (Some Fin.F1).

  Definition handle_spawn : (yieldE +' spawnE +' MemE) ~> ctree (yieldE +' MemE) Bn :=
    fun _ e =>
      match e with
      | inl1 y => trigger y
      | inr1 (inl1 s) => match s with Spawn => ret tt end (* erase spawn events *)
      | inr1 (inr1 m) => trigger m
      end.

  Definition interp_spawn : @completed MemE -> ctree (yieldE +' MemE) Bn unit :=
    Fold.interp handle_spawn (T := unit).

  Definition handle_yield : (yieldE +' MemE) ~> ctree MemE Bn :=
    fun _ e =>
      match e with
      | inl1 s => match s with Yield => ret tt end (* erase yield events *)
      | inr1 m => trigger m
      end.

  Definition interp_yield : ctree (yieldE +' MemE) Bn unit -> ctree MemE Bn unit :=
    Fold.interp handle_yield (T:=unit).

  (* list of key value pairs *)
  Definition env := alist var value.

  Definition handle_state : MemE ~> Monads.stateT env (ctree void1 Bn) :=
    fun _ e s =>
      match e with
      | rd x => Ret (s, lookup_default x 0%nat s)
      | wr x v => Ret (Maps.add x v s, tt)
      end.

  Definition interp_imp (t : stmt) : Monads.stateT env (ctree void1 Bn) unit :=
    interp_state handle_state (interp_yield (interp_spawn (interp_concurrency t))).

  Lemma schedule_forks_equ t1 t2 :
    (schedule 1 (fun _ : fin 1 => denote_imp (Fork t1 (Fork t2 Skip))) (Some Fin.F1))
      ≅
    trigger Spawn;;
    trigger Spawn;;
    (Guard (schedule 2
                     (cons_vec
                        (denote_imp t2)
                        (fun _ => denote_imp t1))
                     None)).
  Proof.
    rewrite rewrite_schedule. simp schedule_match.
    cbn. CTree.fold_subst.
    unfold trigger.
    step. cbn. constructor. intros [].

    rewrite rewrite_schedule. simp schedule_match. simp cons_vec.
    unfold replace_vec. cbn.
    step. cbn. constructor. intros [].

    rewrite rewrite_schedule. simp schedule_match. simp cons_vec. cbn.
    step. cbn. constructor.

    apply equ_schedule. intro i.
    dependent destruction i.
    - simp remove_vec. simp cons_vec. CTree.fold_subst.
      rewrite bind_ret_l. reflexivity.
    - dependent destruction i; [| inv i].
      simp remove_vec. simp cons_vec.
      unfold remove_front_vec. simp cons_vec. cbn. simp cons_vec.
      rewrite bind_ret_l. reflexivity.
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

  Lemma schedule_order (t1 t1' t2 t2' : ctree E void1 unit)
    (Ht1 : t1 ~ t1')
    (Ht2 : t2 ~ t2') :
    BrS (branchn 2) (fun i' : fin 2 =>
                 schedule 2
                          (cons_vec t1 (fun _ => t2))
                          (Some i')) ~
    BrS (branchn 2) (fun i' : fin 2 =>
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

  Lemma schedule_order' (t1 t1' t2 t2' : ctree E void1 unit)
    (Ht1 : t1 ~ t1')
    (Ht2 : t2 ~ t2') :
    Br (branchn 2) (fun i' : fin 2 =>
                 schedule 2
                          (cons_vec t1 (fun _ => t2))
                          (Some i')) ~
    Br (branchn 2) (fun i' : fin 2 =>
                 schedule 2
                          (cons_vec t2' (fun _ => t1'))
                          (Some i')).
  Proof.
    apply sb_br; intros i; exists (p i); [| symmetry];
      apply schedule_permutation with (q:=p);
      try solve [intros i0; dependent destruction i0; simp cons_vec];
      try solve [apply p_inverse];
      try solve [ intros i0; dependent destruction i0;
                  [| dependent destruction i0; [| inv i0]]; simp p; simp cons_vec; auto];
      try solve [ intros i0; dependent destruction i0;
                  [| dependent destruction i0; [| inv i0]]; simp p; simp cons_vec; symmetry; auto].
  Qed.

  Lemma schedule_order'' (t1 t1' t2 t2' : ctree E void1 unit)
    (Ht1 : t1 ~ t1')
        (Ht2 : t2 ~ t2') :
    schedule 2 (cons_vec t1 (fun _ => t2)) None ~
    schedule 2 (cons_vec t2' (fun _ => t1')) None.
  Proof.
    do 2 rewrite rewrite_schedule. simp schedule_match.
    apply sb_vis. intros. apply schedule_order'; auto.
  Qed.

  Lemma commut_forks s1 s2 :
    interp_concurrency (Fork s1 (Fork s2 Skip)) ~
    interp_concurrency (Fork s2 (Fork s1 Skip)).
  Proof.
    unfold interp_concurrency.
    do 2 rewrite schedule_forks_equ.
    unfold trigger.
    (* not sure why we can't just rewrite twice, but we can below *)
    rewrite bind_vis. symmetry. rewrite bind_vis.
    apply sb_vis. intros []. do 2 rewrite bind_ret_l.
    do 2 rewrite bind_vis.
    apply sb_vis. intros []. do 2 rewrite bind_ret_l.
    apply sb_guard_lr.

    do 2 rewrite rewrite_schedule. simp schedule_match.
    apply sb_vis. intros [].
    apply schedule_order'; try solve [apply denote_imp_bounded]; reflexivity.
  Qed.

  Notation br1 t := (br (branchn 1) (fun _ => t)).

  Lemma fork_skip_equ s :
    interp_concurrency (Fork s Skip)
      ≅
    trigger Spawn;;
    Guard
    (trigger Yield;;
     br1 (interp_concurrency s)).
  Proof.
    unfold interp_concurrency. cbn.

    rewrite rewrite_schedule. simp schedule_match.
    cbn. unfold trigger.
    rewrite replace_vec_unary.
    step. cbn. constructor. intros [].

    rewrite rewrite_schedule. simp schedule_match.
    CTree.fold_subst. rewrite (bind_ret_l tt).
    simp cons_vec. cbn. rewrite remove_vec_cons_2.
    step. cbn. constructor.

    rewrite rewrite_schedule. simp schedule_match.
    step. cbn. constructor. intros [].

    CTree.fold_subst. rewrite (bind_ret_l tt).
    step. constructor; intros i.
    dependent destruction i. 2: inv i.
    apply equ_schedule. repeat intro. rewrite bind_ret_l. reflexivity.
  Qed.

  Lemma yield_equ s :
    interp_concurrency (Seq YieldS s) ≅
    Guard
    (trigger Yield;;
     br1 (interp_concurrency s)).
  Proof.
    unfold interp_concurrency. cbn.

    rewrite rewrite_schedule. simp schedule_match.
    cbn. CTree.fold_subst.
    rewrite replace_vec_unary.
    step. cbn. constructor.
    CTree.fold_subst.

    rewrite rewrite_schedule. simp schedule_match.
    step. cbn. constructor.
    intros [].

    CTree.fold_subst.
    step. cbn. constructor; intros i.
    dependent destruction i. 2: inv i.
    apply equ_schedule. repeat intro. rewrite bind_ret_l. reflexivity.
  Qed.

  Lemma br1_guard {F X} (t : ctree F Bn X) :
    br1 t ~ Guard t.
  Proof.
    step; split; intros ?? TR; inv_trans.
    - exists l, t'; split; [| split]; etrans.
    - exists l, t'; split; [| split]; auto.
      eapply trans_br; eauto.
      exact Fin.F1.
  Qed.

  (* first one has one more yield *)
  Lemma yield_yield_fork s :
    interp_yield (interp_spawn (interp_concurrency (Seq YieldS (Seq YieldS s)))) ~
    interp_yield (interp_spawn (interp_concurrency (Fork s Skip))).
  Proof.
    rewrite yield_equ, fork_skip_equ.
    unfold interp_yield, interp_spawn.

    repeat (unfold trigger; rewrite ?interp_bind, ?interp_vis, ?interp_ret, ?bind_ret_l, ?interp_guard, ?sb_guard; cbn).
    rewrite ?interp_br', ?subevent_subevent, ?br1_guard.
    repeat (unfold trigger; rewrite ?interp_bind, ?interp_vis, ?interp_ret, ?bind_ret_l, ?interp_guard, ?sb_guard; cbn).
    rewrite yield_equ.
    rewrite ?interp_guard, sb_guard.
    repeat (unfold trigger; rewrite ?interp_bind, ?interp_vis, ?interp_ret, ?bind_ret_l, ?interp_guard, ?sb_guard; cbn).
    rewrite ?interp_br', ?subevent_subevent, ?br1_guard.
    repeat (unfold trigger; rewrite ?interp_bind, ?interp_vis, ?interp_ret, ?bind_ret_l, ?interp_guard, ?sb_guard; cbn).
    unfold trigger.
    reflexivity.
  Qed.

  Lemma fork_skip_yield s :
    interp_spawn (interp_concurrency (Seq YieldS s)) ~
    interp_spawn (interp_concurrency (Fork s Skip)).
  Proof.
    rewrite yield_equ, fork_skip_equ.
    unfold interp_spawn.
    repeat (unfold trigger; rewrite ?interp_bind, ?interp_vis, ?interp_ret, ?bind_ret_l, ?interp_guard, ?sb_guard; cbn).
    upto_bind_eq; intros [].
    reflexivity.
  Qed.

  Lemma spawn_skip s :
    interp_yield (interp_spawn (interp_concurrency (Fork s Skip))) ~
    interp_yield (interp_spawn (interp_concurrency s)).
  Proof.
    rewrite fork_skip_equ.
    unfold interp_yield, interp_spawn.
    repeat (unfold trigger; rewrite ?interp_bind, ?interp_vis, ?interp_ret, ?bind_ret_l, ?interp_guard, ?sb_guard; cbn).
    rewrite ?interp_br', ?subevent_subevent, br1_guard.
    repeat (unfold trigger; rewrite ?interp_bind, ?interp_vis, ?interp_ret, ?bind_ret_l, ?interp_guard, ?sb_guard; cbn).
    reflexivity.
  Qed.

  Lemma while_true_unfold_sbisim s1 :
    denote_imp (While (Lit 1%nat) s1) ~ denote_imp s1;; denote_imp (While (Lit 1%nat) s1).
  Proof.
    cbn. unfold while. rewrite unfold_iter at 1.
    rewrite bind_ret_l. unfold is_true.
    assert ((1 =? 0)%nat = false) by reflexivity.
    rewrite H. unfold E. rewrite bind_bind.
    upto_bind_eq; intros [].
    rewrite bind_ret_l. apply sb_guard.
  Qed.

  Lemma commut_forks_unfold s :
    interp_concurrency (Fork (While (Lit 1%nat) YieldS) (Fork s Skip)) ~
    interp_concurrency (Fork s (Fork (Seq YieldS (While (Lit 1%nat) YieldS)) Skip)).
  Proof.
    unfold interp_concurrency.
    do 2 rewrite schedule_forks_equ.
    upto_bind_eq; intros [].
    upto_bind_eq; intros [].
    apply sb_guard_lr.

    apply schedule_order''.
    reflexivity.
    apply while_true_unfold_sbisim.
  Qed.

  Lemma assign_equ :
    interp_concurrency (Assign "x" (Lit 2)) ≅
                       (vis (wr "x" 2) (fun _ => Guard (ret tt))).
  Proof.
    unfold interp_concurrency. cbn.

    rewrite rewrite_schedule. simp schedule_match.
    cbn. CTree.fold_subst.
    step. constructor. intros [].

    rewrite rewrite_schedule. simp schedule_match.
    cbn. step. constructor.

    rewrite rewrite_schedule. simp schedule_match. reflexivity.
  Qed.

  Lemma fork_assign_assign_equ :
    interp_concurrency (Fork (Assign "x" (Lit 2))
                             (Assign "x" (Lit 1%nat))) ≅
                       trigger Spawn;; (vis (wr "x" 1%nat) (fun _ => (Guard (trigger Yield;; br1 ((vis (wr "x" 2) (fun _ => Guard (ret tt)))))))).
  Proof.
    unfold interp_concurrency. cbn.

    rewrite rewrite_schedule. simp schedule_match.
    cbn. CTree.fold_subst.
    rewrite replace_vec_unary.
    step. cbn. constructor. intros [].

    rewrite rewrite_schedule. simp schedule_match.
    CTree.fold_subst.
    simp cons_vec. cbn.
    step. cbn. constructor. intros [].

    rewrite rewrite_schedule. simp schedule_match.
    rewrite replace_vec_cons_2.
    step. constructor.

    rewrite rewrite_schedule. simp schedule_match.
    step. cbn. constructor. CTree.fold_subst. intros [].
    step. cbn. constructor. intros i.

    dependent destruction i. 2: inv i.
    rewrite remove_vec_cons_2.
    rewrite rewrite_schedule. simp schedule_match. cbn.
    step. constructor. intros [].

    rewrite rewrite_schedule. simp schedule_match. cbn.
    step. constructor.

    rewrite rewrite_schedule. simp schedule_match. reflexivity.
  Qed.

  Lemma filter_filter : forall {A} f (l : list A), filter f (filter f l) = filter f l.
  Proof.
    intros. induction l.
    - reflexivity.
    - cbn. destruct (f a) eqn:?.
      + cbn. rewrite Heqb. f_equal. apply IHl.
      + apply IHl.
  Qed.

  Lemma alist_add_alist_add : forall {K RD_K V}, RelDec.RelDec_Correct (RD_K) ->
                                            forall k v v' l, @alist_add K eq RD_K V k v (alist_add _ k v' l) = alist_add _ k v l.
  Proof.
    intros. unfold alist_add, alist_remove. cbn. rewrite filter_filter.
    rewrite RelDec.rel_dec_eq_true; auto.
  Qed.

  Lemma interp_fork_assign_assign s :
    interp_imp (Fork (Assign "x" (Lit 2))
                             (Assign "x" (Lit 1%nat))) s ~
    interp_imp (Assign "x" (Lit 2)) s.
  Proof.
    unfold interp_imp.
    rewrite fork_assign_assign_equ, assign_equ.
    unfold interp_yield, interp_spawn.

    rewrite interp_bind. unfold trigger. rewrite interp_vis.
    cbn. rewrite bind_ret_l. setoid_rewrite interp_ret.
    rewrite ?interp_bind, ?interp_guard, ?bind_guard, interp_state_guard.
    rewrite sb_guard.
    rewrite interp_ret, bind_ret_l.

    rewrite interp_vis; cbn.
    unfold trigger; rewrite interp_vis; cbn.
    rewrite bind_vis, interp_vis; cbn.
    rewrite interp_state_bind, interp_state_trigger.
    repeat (cbn; rewrite ?bind_bind, ?bind_ret_l, ?bind_guard, ?sb_guard, ?interp_guard, ?interp_state_guard).
    unfold trigger. rewrite interp_bind, interp_vis; cbn.
    rewrite bind_vis, interp_vis; cbn.
    rewrite interp_state_bind, interp_state_trigger.
    repeat (cbn; rewrite ?bind_bind, ?bind_ret_l, ?bind_guard, ?sb_guard, ?interp_guard, ?interp_state_guard).
    unfold trigger. rewrite interp_bind, interp_vis; cbn.
    repeat (cbn; rewrite ?bind_bind, ?bind_ret_l, ?bind_guard, ?sb_guard, ?interp_ret, ?interp_guard, ?interp_state_guard).
    symmetry; rewrite ?sb_guard; symmetry.
    rewrite ?interp_br', interp_state_br.
    unfold branch; cbn. rewrite bind_br.
    apply sb_br_l; [exact Fin.F1 |].
    intros ?.
    repeat (cbn; rewrite ?bind_bind, ?bind_ret_l, ?bind_guard, ?sb_guard, ?interp_ret, ?interp_guard, ?interp_state_guard).
    rewrite interp_vis; cbn.
    unfold trigger; rewrite bind_vis, interp_vis; cbn.
    rewrite interp_state_bind, interp_state_trigger.
    repeat (cbn; rewrite ?bind_bind, ?bind_ret_l, ?bind_guard, ?sb_guard, ?interp_guard, ?interp_state_guard).
    rewrite ?interp_ret, ?interp_state_ret.
    apply sb_ret.
    rewrite alist_add_alist_add. 2: apply RelDec_Correct_string. reflexivity.
  Qed.

End Denote1.
