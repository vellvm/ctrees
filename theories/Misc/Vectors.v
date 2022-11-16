From Coq Require Export
     Vector Fin.
From Coq Require Import
     Program.Equality.

From Coq Require
     List.

From CTree Require Import Core.Utils.

From Equations Require Import Equations.

Import VectorNotations.
Declare Scope fin_vector_scope.

Notation vec n T := (Vector.t T n).
Notation fin := Fin.t.

Equations vector_remove{A n}(v: vec (S n) A)(i: fin (S n)) : vec n A by wf n lt :=
  vector_remove (h :: h' :: ts) (FS (FS j)) := h :: (vector_remove (h' :: ts) (FS j));
  vector_remove (h :: h' :: ts) (FS F1) := h :: ts;
  vector_remove (h :: h' :: ts) F1 := h' :: ts;
  vector_remove (h::nil) F1 := @nil A.
Transparent vector_remove.

Equations vector_replace{A n}(v: vec n A)(i: fin n)(a: A): vec n A by wf n lt :=
  vector_replace [] _ _ := [];
  vector_replace (h :: h' :: ts) (FS (FS j)) a := h :: (vector_replace (h' :: ts) (FS j) a);
  vector_replace (h :: h' :: ts) (FS F1) a := h :: a :: ts;
  vector_replace (h :: h' :: ts) F1 a := a :: h' :: ts;
  vector_replace [h] F1 a := [a].
Transparent vector_replace.

Notation "v '@' i ':=' a" := (vector_replace v i a) (at level 80): fin_vector_scope.
Notation "v '$' i" := (nth v i) (at level 80): fin_vector_scope.
Notation "v '--' i" := (vector_remove v i) (at level 80): fin_vector_scope.

(** Vector utils *)
Equations forallb {A}{m: nat}(f: A -> bool)(a: vec m A): bool :=
  forallb _ [] := true;
  forallb f (h :: ts) := andb (f h) (forallb f ts).
Transparent forallb.

Lemma forall_reflect: forall A (m: nat)(f: A -> bool) (l: vec m A),
    forallb f l = true <-> Forall (fun x => f x = true) l.
Proof.
  intros A m f l. 
  split; intros.
  - dependent induction l.
    + econstructor.
    + econstructor; cbn in H; apply andb_prop in H;
        destruct H.
      * exact H.
      * apply IHl; assumption.
  - dependent induction H.
    + reflexivity.
    + cbn;
        apply andb_true_intro; split; assumption.
Defined.


Fixpoint fin_all (n : nat) : list (fin n) :=
  match n as n return list (fin n) with
  | 0 => List.nil
  | S n => List.cons (@F1 n) (List.map (@FS _) (fin_all n))
  end%list.

Theorem fin_all_In : forall {n} (f : fin n),
    List.In f (fin_all n).
Proof.
  induction n; intros.
  inversion f.
  remember (S n). destruct f.
  simpl; firstorder.
  inversion Heqn0. subst.
  simpl. right. apply List.in_map. auto.
Qed.

Theorem fin_case : forall n (f : fin (S n)),
    f = F1 \/ exists f', f = FS f'.
Proof.
  intros. generalize (fin_all_In f). intros.
  destruct H; auto.
  eapply List.in_map_iff in H. right. destruct H.
  exists x. intuition.
Qed.

Lemma vec0 {T}: forall (v:Vector.t T 0), v = [].
  apply (Vector.case0 (fun x => x=[])).
  reflexivity.
Qed.

Fixpoint zip {A B : Type} {n : nat} (a : Vector.t A n) (b : Vector.t B n) : Vector.t (A * B) n :=
  match a in Vector.t _ n return Vector.t B n -> Vector.t (A * B) n  with
  | ha :: ta => fun b => (ha, Vector.hd b) :: zip ta (Vector.tl b)
  | [] => fun _ => []
  end b.

Definition pairwise{A B n}(R: rel A B): rel (vec n A) (vec n B) :=
  fun a b => @Forall (A * B) (fun '(a, b) => R a b) n (zip a b).

Section VInversion.
  Context {A: Type}.
  Lemma inversion_aux : forall n (v: Vector.t A n),
      match n return Vector.t A n -> Prop with
      | 0 => fun v => v = []
      | _ => fun v => exists x y, v = x :: y
      end v.
  Proof.
    intros. destruct v; repeat eexists; trivial.
  Qed.

  Lemma inversion_0 : forall (v:Vector.t A 0), v = [].
  Proof.
    intros. apply (inversion_aux 0).
  Qed.
  Lemma inversion_Sn : forall {n} (v : Vector.t A (S n)),
      exists a b, v = a :: b.
  Proof.
    intros. apply (inversion_aux (S n)).
  Qed.
End VInversion.

(** List utils *)
Fixpoint last{A}(l: list A): option A :=
  match l with
  | List.nil => None
  | List.cons h List.nil => Some h
  | List.cons h ts => last ts
  end.

Fixpoint init{A}(l: list A): list A :=
  match l with
  | List.nil => List.nil
  | List.cons h List.nil => List.nil
  | List.cons h ts => List.cons h (init ts)
  end.
