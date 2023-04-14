(*|
======================================================
Methods and lemmas for splitting ctrees
======================================================

.. coq:: none
|*)

From ITree Require Import Core.Subevent.
From Coq Require Import Vector Fin.

From CTree Require Import
     CTree
     Logic.Kripke
     Misc.Vectors
     Interp.Fold
     Eq.

From ExtLib Require Import
     Data.Monads.StateMonad
     Structures.Monad
     Structures.MonadState.

From Equations Require Import Equations.

Import CTreeNotations VectorNotations.

Local Open Scope fin_vector_scope.
Local Open Scope vector_scope.
Local Open Scope ctree_scope.

Set Implicit Arguments.

Section Take.
  Context {E C: Type -> Type} {X: Type}.

  (*| This function extracts "at most" [n] visible steps from the ctree
    and puts the rest as the return value to be continued later. |*)
  Fixpoint take(n: nat): ctree E C X -> ctree E C (ctree E C X) :=
    cofix F (t: ctree E C X): ctree E C (ctree E C X) :=
      match n with
      | 0 => Ret t
      | S m => 
          match observe t with
          | RetF x => Ret (Ret x)
          | VisF e k => Vis e (fun i => take m (k i))        (* inductive step *)
          | BrSF c k => Br true c (fun i => take m (k i))    (* inductive step *)
          | BrDF c k => Br false c (fun i => F (k i))        (* coinductive, could spin in delay loop *)
          end
      end.

  Notation take_ n t :=
    (match n with
    | 0 => Ret t
    | S m => 
        match observe t with
        | RetF x => Ret (Ret x)
        | VisF e k => Vis e (fun i => take m (k i))
        | BrSF c k => Br true c (fun i => take m (k i))
        | BrDF c k => Br false c (fun i => take n (k i))
        end
    end)%function.
  
  Lemma unfold_take : forall (n: nat) (t : ctree E C X),
      take n t ≅ take_ n t.
  Proof.
    intro n; induction n; intro; step; eauto.
  Qed.
  
  (*| Taking 0 visible steps returns the unchanged ctree |*)
  Lemma unfold_0_take : forall (t: ctree E C X),
      take 0 t ≅ Ret t.
  Proof.
    setoid_rewrite unfold_take; reflexivity.
  Qed.

  Lemma unfold_Sn_take : forall (t: ctree E C X) n,
      take (S n) t ≅ match observe t with
                     | RetF x => Ret (Ret x)
                     | VisF e k => Vis e (fun i => take n (k i))
                     | BrSF c k => Br true c (fun i => take n (k i))
                     | BrDF c k => Br false c (fun i => take (S n) (k i))
                     end.
  Proof. setoid_rewrite unfold_take; reflexivity. Qed.  

  (* Nice educational proof *)
  #[global] Instance equ_eq_take_proper {n}:
    Proper (equ eq ==> equ (equ eq)) (take n).
  Proof.
    unfold Proper, respectful.
    revert n.  
    coinduction ? ?.
    intro n; destruct n; intros.
    - rewrite !unfold_0_take; auto; now econstructor.
    - rewrite !unfold_take; step in H0; inv H0.
      + now constructor.
      + constructor; intros; auto.
      + destruct b; econstructor; auto. 
  Qed.

End Take.

(*| Emit an event when a thread gets scheduled |*)
Variant parE: Type -> Type :=
  | Switch (i: nat): parE unit.

#[global] Instance handler_parE: parE ~~> state nat :=
  fun _ e => match e with Switch i => put i end.

(*| Run a single [trans] step of tree [a] as processes [i] |*)
Definition preempt{E C X}`{B1 -< C}
           (a: ctree E C X)(uid: nat): ctree (E +' parE) C X :=
  trigger (inr1 (Switch uid)) ;; translate inl1 a. 

Lemma unfold_0_preempt{E C X}`{B1 -< C}(i: nat) (t: ctree E C X):
  preempt (take 0 t) i ≅ trigger (inr1 (Switch i)) ;; Ret t.
Proof.
  intros; unfold preempt.
  upto_bind_eq.
  rewrite unfold_0_take, translate_ret.
  reflexivity.
Qed.

Lemma unfold_Sn_preempt{E C X}`{B1 -< C}: forall (i: nat) (n: nat) (t: ctree E C X),
    preempt (take (S n) t) i ≅ trigger (inr1 (Switch i)) ;;
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

(*| Re-attach split ctrees |*)
Notation flatten u := (u >>= (fun x => x)) (only parsing).

Lemma take_flatten_id {E C X}: forall n (t: ctree E C X),
    flatten (take n t) ≅ t.
Proof.
  Opaque take.
  coinduction ? CIH; intros; destruct n.
  - rewrite unfold_0_take, bind_ret_l; auto.
  - rewrite unfold_take.
    assert(Ht: t ≅ {| _observe := observe t |}) by (apply ctree_eta).
    desobs t.
    + rewrite bind_ret_l; now rewrite Ht.
    + rewrite bind_vis, Ht.
      now econstructor.
    + destruct vis; rewrite bind_br; rewrite Ht; econstructor; intros; eauto.
Qed.

(*| A round robbin scheduler |*)
Section RR.

  Context {E C: Type -> Type} {X: Type} {HasTau: B1 -< C}.
  
  Equations rr'{n} (v: vec n (ctree E C X)) :ctree (E +' parE) C (vec n (ctree E C X)) :=
    rr' (n:=0) [] := Ret [];
    rr' (n:=S n') (h :: ts) := 
        x <- preempt (take 1 h) n' ;;
        xs <- rr' ts ;;
        Ret (x :: xs).
   
  (*| Round robbin scheduler |*)
  Definition rr{n}: vec n (ctree E C X) ->
                    ctree (E +' parE) C (vec n (ctree E C X)) :=   
    CTree.forever rr'.

  Lemma unfold_rr {n}: forall (v: vec n (ctree E C X)),
      rr v ≅ r <- rr' v;; Guard (rr r).
  Proof. intros; step; cbn; auto. Qed.
  
End RR.

Section RRR.

  Context {E C: Type -> Type} {X: Type} {HasTau: B1 -< C} {Hasn: Bn -< C}.

  (* Randomly pick the next process to schedule, with no replacement *)
  Equations rrr' {n} (v: vec n (ctree E C X)) :
    ctree (E +' parE) C (vec n (ctree E C X)) :=
    rrr' (n:=0) []%vector := Ret [];
    rrr' (n:=S n') (h :: ts) := let v := h :: ts in
        i <- branch false (branchn (S n')) ;;        
        x <- preempt (take 1 (v $ i)) (proj1_sig (to_nat i))  ;;
        xs <- rrr' (v -- i) ;;
        Ret (x :: xs).

  (*| Guarded coinduction of [rrr'] |*)
  Definition rrr {n} : vec n (ctree E C X) -> ctree (E +' parE) C (vec n (ctree E C X)) :=
    CTree.forever rrr'.

  Lemma unfold_rrr {n}: forall (v: vec n (ctree E C X)),
      rrr v  ≅  v' <- rrr' v ;; Guard (rrr v'). 
  Proof. intros; step; cbn; auto. Qed.

  Lemma unfold_1_rrr: forall (h: ctree E C X),
      rrr [h] ≅ brD (branchn 1) (fun _ => x <- preempt (take 1 h) 0;; Guard (rrr [x])).
  Proof.
    intros.
    rewrite unfold_rrr.
    simp rrr'; cbn.
    rewrite !bind_bind, bind_branch.
    apply br_equ.
    intros i.
    repeat dependent destruction i.
    rewrite !bind_bind.
    cbn.
    upto_bind_eq.
    rewrite !bind_bind.
    simp vector_remove rrr'.
    now rewrite !bind_ret_l.
  Qed.

End RRR.

