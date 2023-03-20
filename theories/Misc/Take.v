(*|
======================================================
Methods and lemmas for splitting ctrees
======================================================

.. coq:: none
|*)

From ITree Require Import Core.Subevent.
From CTree Require Import
     CTree
     Eq.

Set Implicit Arguments.
Set Contextual Implicit.

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
    match n with
    | 0 => Ret t
    | S m => 
        match observe t with
        | RetF x => Ret (Ret x)
        | VisF e k => Vis e (fun i => take m (k i))
        | BrSF c k => Br true c (fun i => take m (k i))
        | BrDF c k => Br false c (fun i => take n (k i))
        end
    end.
  
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

(*| Traverse the ctree until you encounted a blocking Vis node, then split right before it. |*)
Section ToBlocked.
  Context {E C: Type -> Type} {X: Type}.
  Context (is_blocking: forall T, E T -> bool).
  
  Definition to_blocked: ctree E C X -> ctree E C (ctree E C X) :=
    cofix F (t: ctree E C X): ctree E C (ctree E C X) :=
      match observe t with
      | RetF x => Ret (Ret x)
      | VisF e k =>
          if is_blocking e then (Ret (Vis e k))
          else (Vis e (fun i => F (k i)))
      | BrSF c k => BrS c (fun i => F (k i))
      | BrDF c k => BrD c (fun i => F (k i))
      end.

  Notation to_blocked_ t := 
    match observe t with
    | RetF x => Ret (Ret x)
    | VisF e k =>
        if is_blocking e then (Ret (Vis e k))
        else (Vis e (fun i => to_blocked (k i)))
    | BrSF c k => BrS c (fun i => to_blocked (k i))
    | BrDF c k => BrD c (fun i => to_blocked (k i))
    end.

  Lemma unfold_to_blocked : forall (t : ctree E C X),
      to_blocked t ≅ to_blocked_ t.
  Proof. intro; step; eauto. Qed.
End ToBlocked.

(*| Re-attach split ctrees |*)
Notation flatten u := (CTree.bind u (fun x => x)) (only parsing).

#[global] Instance bind_equ_equ_cong :
  forall (E B : Type -> Type) (X Y : Type) (R : rel Y Y) RR,
    Proper (equ (equ (@eq X)) ==> pointwise (equ eq) (et R RR) ==> et R RR)
           (@CTree.bind E B (ctree E B X) Y).
Proof.
  repeat red; intros.
  eapply et_clo_bind; eauto.
Qed. 

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

(* This is the [Ret (Ret x)] on RHS *)
Lemma trans_take_Sn_val_inv {E C X} `{B0 -< C}: forall (t: ctree E C X) (u: ctree E C (ctree E C X)) (v: ctree E C X) n,
  trans (val v) (take (S n) t) u ->
  exists x, v ≅ Ret x /\ trans (val x) t stuckD /\ u ≅ stuckD.
Proof.
  intros t u v n TR.
  (* The TR induction magic trick *)
  unfold trans, transR in TR;
    cbn in TR.
  match goal with
  | [ H: trans_ _ ?a ?b |- _ ] =>
      remember a as oa;
      remember b as ob
  end.
  revert n u t Heqoa Heqob.
  induction TR; intros; eauto; subst.
  - subst; eapply IHTR with (n:=n); eauto; desobs t0; cbn in *; eauto. 
Admitted.

Lemma trans_take_Sn {E C X} `{B0 -< C}: forall
    (t: ctree E C X) (u: ctree E C (ctree E C X)) l n,
    trans l t (flatten u) ->
    trans l (take (S n) t) u.
Proof.
  Opaque take.  
  intros * TR.
  induction TR; try now inv Heqob.
  - eapply IHTR.
Admitted.

