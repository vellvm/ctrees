(*|
======================================================
Take N visible steps from a ctree and return the rest.
======================================================
A generalization of [head]

.. coq:: none
|*)

From ITree Require Import Core.Subevent.
From CTree Require Import
     CTree Eq.

Import CTree CTreeNotations.
Open Scope ctree_scope.

Set Implicit Arguments.
Set Contextual Implicit.

(*| This function extracts "at most" [n] visible steps from the ctree
   and puts the rest as the return value to be continued later. |*)
Fixpoint take{E C X}(n: nat): ctree E C X -> ctree E C (ctree E C X) :=
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

Lemma unfold_take {E C X} : forall (n: nat) (t : ctree E C X),
    take n t ≅ take_ n t.
Proof.
  intro n; induction n; intros; now step.
Qed.

(*| Taking 0 visible steps returns the unchanged ctree |*)
Lemma equ_take_0 {E C X} : forall (t u: ctree E C X),
    (take 0 t) ≅ Ret t.
Proof.
  setoid_rewrite unfold_take; reflexivity.
Qed.  

(* LEF: This proof is educational -- even though
   [take] in inductive on [n] the coinductive hypothesis
   CIH is enough and we do not need to explicitly induct on [n].
   We do need to generalize [n] prior to coinduction *)
#[global] Instance equ_eq_take_proper {E C X} n:
  Proper (equ eq ==> equ (equ eq)) (@take E C X n).
Proof.
  unfold Proper, respectful.
  revert n.  
  coinduction ? ?.
  intro n; destruct n; intros.
  - rewrite !equ_take_0; auto; now econstructor.
  - rewrite !unfold_take; step in H0; inv H0.
    + now constructor.
    + constructor; intros; auto.
    + destruct b; econstructor; auto. 
Qed.
        
Lemma trans_take_cong{E C X} `{B0 -< C}: forall n (t u: ctree E C X) l,
    trans l t u -> 
    trans l (take (S n) t) (take (S n) u).
Proof.
  intros.
  induction H0; eauto.
  setoid_rewrite unfold_take.
  
Admitted.
