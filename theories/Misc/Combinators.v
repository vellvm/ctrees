From ITree Require Import
     Indexed.Sum
     Core.Subevent.

From Coq Require Import
     Logic.Eqdep
     Program.Equality
     Vector.

From CTree Require Import
     CTreeDefinitions
     Misc.Vectors
     Fold
     Take
     Eq.

From Equations Require Import Equations.

Set Implicit Arguments.

Import CTreeNotations VectorNotations.
Local Open Scope ctree_scope.

(*| Unique thread identifiers |*)
Notation id n := (fin (S n)) (only parsing).

Notation i1 := Fin.F1.
Notation i2 := (Fin.FS Fin.F1).

(*| Thread IDs are a product of an effect [E] with a [uid] |*)
Variant parE (n: nat): Type -> Type :=
  | Switch (i: id n): parE n unit.

Arguments Switch {n}.

Definition switch {n E C} `{parE n -< E} (i: id n): ctree E C unit :=
  trigger (Switch i).

Definition preempt{n E C X}`{B1 -< C} (i: id n)(cycles: nat)(a: ctree E C X): ctree (E +' parE n) C (ctree E C X) :=
  trigger (inr1 (Switch i)) ;; translate inl1 (take cycles a).

Lemma unfold_Sn_preempt{N E C X}`{B1 -< C}: forall (i: id N) (n: nat) (t: ctree E C X),
    preempt i (S n) t ≅ trigger (inr1 (Switch i)) ;;
    match observe t with
    | RetF x => Ret (Ret x)
    | VisF e k => Vis (inl1 e) (fun i => translate inl1 (take n (k i))) 
    | BrSF c k => Br true c (fun i => translate inl1 (take n (k i))) 
    | BrDF c k => Br false c (fun i => translate inl1 (take (S n) (k i)))
    end.
Proof.
  intros; unfold preempt.
  upto_bind_eq.
  rewrite unfold_take, unfold_translate.
  desobs t; auto; destruct vis; reflexivity.
Qed.

Lemma unfold_0_preempt{N E C X}`{B1 -< C}(i: id N) (t: ctree E C X):
  preempt i 0 t ≅ trigger (inr1 (Switch i)) ;; Ret t.
Proof.
  intros; unfold preempt.
  upto_bind_eq.
  rewrite unfold_0_take, translate_ret.
  reflexivity.
Qed.

(*| Fair parallel operator, warning: not associative |*)
(*| A || B -> br (A^* ; B) (B^*; A) *) (* (A || B) || C == A || (B || C) *)
Definition fair{E C X}`{B1 -< C}`{B2 -< C}`{BN -< C} : 
  ctree E C X -> ctree E C X -> ctree (E +' parE 2) C X :=
  cofix R (P : ctree E C X) (Q : ctree E C X) :=
    brD2 
      (n <- branch false (branchN) ;;
       p <- preempt i1 n P ;;
       q <- preempt i2 1 Q ;;
       R p q)
      (n <- branch false (branchN) ;;
       q <- preempt i2 n Q ;;
       p <- preempt i1 1 P ;;
       R p q).

Notation fair_ P Q :=
  (brD2
      (n <- branch false (branchN) ;;
       p <- preempt i1 n P ;;
       q <- preempt i2 1 Q ;;
       fair p q)
      (n <- branch false (branchN) ;;
       q <- preempt i2 n Q ;;
       p <- preempt i1 1 P ;;
       fair p q)
   ).

Lemma unfold_fair {E C X}`{B1 -< C}`{B2 -< C}`{BN -< C}:
  forall (a: ctree E C X) (b: ctree E C X),
    (fair a b) ≅ (fair_ a b).
Proof. intros; step; cbn; auto. Qed.

(*| [m] is the total length of the vector, [n] is the iterative type variable.
  Will call from [rr] with [n n]. The return type is a finite scheduled computation ctree, followed by a continuation. |*)
Equations rr' {E C X}`{B1 -< C} n m `{(n <= m)%nat}: vec (S n) (ctree E C X) -> ctree (E +' parE m) C (vec (S n) (ctree E C X)) by wf n :=
  rr' (h :: []) := (x <- preempt i1 1 h;;
                   Ret [x]
                  );
  rr' (h :: ts) := (x <- preempt (Fin.of_nat_lt _) 1 h ;;
                   xs <- rr' ts ;;
                   Ret (x :: xs)
                  ).
Solve All Obligations with auto using Le.le_Sn_le_stt.

Section RR.
  Context {E C: Type -> Type} {X: Type} {HasTau: B1 -< C}.

  (*| Schedule [m] processes in round-robin.
      [m] is the total length of the vector
      [i] counts in reverse m .. 0 
      [j] counts from 0 .. m,
      in every step [i + j = m] is invariant. |*)
  Equations rr'' (m: nat) (i j: nat) (H: m = i + j) (x: id j) (v: vec (S i) (ctree E C X)):
    ctree (E +' parE m) C (vec (S i) (ctree E C X)) by wf i :=
    @rr'' _ 0 j _ _ (h :: []) :=      (* j = m /\ i = 0 *)
      (p <- preempt (eq_rec_r (fun m => id m) x H) 1 h;;
       Ret [p]
      );
    @rr'' _ (S i') j _ _ (h :: ts) := (* S i' + j = m *)
      (p <- preempt (eq_rec_r (fun m => id m) (Fin.R (S i') x) _) 1 h ;; 
       ps <- @rr'' m i' (S j) _ (FS x) ts ;;
       Ret (p :: ps)
      ).

  Definition rr{n}: vec (S n) (ctree E C X) -> ctree (E +' parE n) C X :=
    cofix F v := v <- @rr'' n n 0 (plus_n_O n) i1 v ;; Guard (F v).

  Lemma unfold_rr {n}: forall (v: vec (S n) (ctree E C X)),
      rr v  ≅ v <- @rr'' n n 0 (plus_n_O n) i1 v ;; Guard (rr v).
  Proof. intros; step; cbn; auto. Qed.
End RR.


Lemma unfold_0_rr {E C X}`{B1 -< C}: forall (h: ctree E C X),
    rr [h] ≅ x <- preempt i1 1 h ;; Guard (rr [x]).
Proof.
  intros.
  rewrite unfold_rr.
  simp rr''.
  rewrite bind_bind.
  simpl_eq.  
  upto_bind_eq.
  now rewrite bind_ret_l.
Qed.

(* Get the max index for this non-empty vector *)
Definition v_id {A}: forall n, vec (S n) A -> id n :=
  @Vector.rectS A (fun n _ => id n) (fun _ => i1) (fun _ _ t i => FS i).

Check @rr''.
Search plus.
Search S.
Lemma unfold_Sn_rr {n E C X}`{B1 -< C}:
  forall (h: ctree E C X) (ts: vec (S n) (ctree E C X)),
    rr (h :: ts) ≅
       (x <- preempt i2 1 h ;;
        xs <- @rr'' E C X _ (S n) n 1 (symmetry (PeanoNat.Nat.add_1_r n)) i2 ts ;;
        Guard (rr (x :: xs))).
Proof.
  intros.
  rewrite unfold_rr.
  revert ts h.
  induction n; intros.
  - repeat dependent destruction ts.    
    simp rr''; simpl.
    simpl_eq.
    rewrite !bind_bind.
    upto_bind_eq.
    rewrite !bind_bind.
    upto_bind_eq.
    rewrite !bind_ret_l.
    reflexivity.
  - dependent destruction ts.
    simp rr''.
    rewrite !bind_bind.
    
    simpl_eq.
    Print rr''_obligations_obligation_1.
    unfold rr''_obligations_obligation_2.
    simpl_eq.
    simp rr' in IHn.
    simp rr'; simpl.

    upto_bind_eq.
    rewrite !bind_bind.
    upto_bind_eq.
    Check (of_nat_lt (rr'_obligations_obligation_2 1)).
    Check (v_id [h; h0]).
    simpl.
    
  cbv in HeqF.
  decide equality.
  unfold rr'_obligations_obligation_2, reflexivity.
  cbn.
  cbv.
  Check reflexivity.
  Print  rr'_obligations_obligation_1.
  unfold rr'_obligations_obligation_2.
  simpl.
  unfold of_nat_lt.
  simpl.
  destruct (S n).
  - repeat 
    
Admitted.

(*Declare Scope ctree_combinator_scope.
Local Open Scope ctree_combinator_scope.
Notation "a ⋄ b" := (fair a b) (at level 40, left associativity): ctree_combinator_scope.
Notation "a ∥ b" := (para a b) (at level 40, left associativity): ctree_combinator_scope.
 *)

