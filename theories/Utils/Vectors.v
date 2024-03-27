From Coq Require Import
  Vector
  Fin
  Classes.SetoidClass.

From Coq Require Import
     Program.Equality.

From Coq Require
     List.

From Equations Require Import Equations.

Import VectorNotations.
Declare Scope fin_vector_scope.

Notation vec n T := (Vector.t T n).
Notation vec' n T := (vec (S n) T). 
Notation fin := Fin.t.
Notation fin' n := (fin (S n)).

Fixpoint fin_max(n: nat): fin' n :=
  match n with
  | 0 => Fin.F1
  | S n => Fin.FS (fin_max n)
  end.

Lemma fin_max_sanity{n}:
  proj1_sig (to_nat (fin_max n)) = n.
Proof.
  induction n; cbn; auto.
  destruct (to_nat (fin_max n)) eqn:Hm; cbn in *.
  subst.
  reflexivity.
Qed.

Program Definition cycle{n}(i: fin' n): fin' n :=
  if Fin.eq_dec i (fin_max n) then
    Fin.F1
  else
    (_ (Fin.FS i)).
Next Obligation. exact i. Qed.

Lemma next_sanity_max{n}: cycle (fin_max n) = Fin.F1.
Proof.
  unfold cycle.
  destruct (Fin.eq_dec (fin_max n) (fin_max n)); auto.
  exfalso; apply n0; reflexivity.
Qed.

Program Definition of_nat_lt' {n p: nat} (H: p < n): fin' n :=
  (_ (Fin.of_nat_lt H)).
Next Obligation.
  destruct n.
  - dependent destruction x.
  - exact (Fin.FS x).
Defined.

Lemma next_sanity_lt (m n: nat) (Hm: m < n):
    proj1_sig (to_nat (cycle (of_nat_lt' Hm))) <= n.
Proof.
  induction m; cbn; unfold of_nat_lt', of_nat_lt'_obligation_1; cbn.
  - destruct n.
    + inversion Hm.
    + cbn.
      admit.
Admitted.

Definition init T :=
  @Vector.caseS _ (fun n v => vec n T) (fun h n t => t).

Global Arguments init {T} {n} v.

Equations vector_remove{A n}(v: vec (S n) A)(i: fin (S n)) : vec n A by wf n lt :=
  vector_remove (h :: h' :: ts) (FS (FS j)) := h :: (vector_remove (h' :: ts) (FS j));
  vector_remove (h :: h' :: ts) (FS F1) := h :: ts;
  vector_remove (h :: h' :: ts) F1 := h' :: ts;
  vector_remove (h::nil) F1 := @nil A.

Equations nth_map{A n}(v: vec n A)(i: fin n)(f: A -> A): vec n A by wf n lt :=
  nth_map [] _ _ := [];
  nth_map (h :: h' :: ts) (FS (FS j)) _ := h :: (nth_map (h' :: ts) (FS j) f);
  nth_map (h :: h' :: ts) (FS F1) _ := h :: f h' :: ts;
  nth_map (h :: h' :: ts) F1 _ := f h :: h' :: ts;
  nth_map [h] F1 _ := [f h].

(*Equations vector_mapi_{A B n}(v: vec n A)(f: fin n -> A -> B)(i: fin n): vec n B by wf n lt :=
  vector_mapi_ [] _ F1 := [];
  vector_mapi_ (h::ts) f (FS i) := f i h :: vector_mapi_ ts f i.
 *)

Notation "v '$' i" := (nth v i) (at level 80): fin_vector_scope.
Notation "v '--' i" := (vector_remove v i) (at level 80): fin_vector_scope.
Notation "v '@' i 'do' f" := (nth_map v i f) (at level 80): fin_vector_scope.

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

Fixpoint fin_all_v (n : nat) : vec' n (fin' n) :=
  match n as n return vec' n (fin' n) with
  | 0 => Vector.cons _ (F1) _ (@Vector.nil (fin' 0))
  | S n => Vector.cons _ (@FS (S n) (@F1 n)) _ (Vector.map (@FS _) (fin_all_v n))
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

Definition pairwise{A B n}(R: A -> B -> Prop): vec n A -> vec n B -> Prop :=
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
Fixpoint list_last{A}(l: list A): option A :=
  match l with
  | List.nil => None
  | List.cons h List.nil => Some h
  | List.cons h ts => list_last ts
  end.

Fixpoint list_unsnoc{A}(l: list A): option (A * list A) :=
  match l with
  | List.nil => None
  | List.cons h ts =>
      match list_unsnoc ts with
      | Some (h', ts') => Some (h', List.cons h ts')
      | None => Some (h, List.nil)
      end
  end.

(*| For a [vec n T] of size [n] return a list of 
  indices [fin n] for which [f: T -> bool] is satisfied |*)
(*| Coerce p{^ th} element of [fin m] to the p{^ th} element of [fin (S m)] |*)
Fixpoint SL {m} (p : fin m) : fin (S m) :=
  match p with |Fin.F1 => Fin.F1 |Fin.FS p' => Fin.FS (SL p') end.

Lemma SL_sanity {m} (p : fin m) : proj1_sig (Fin.to_nat (SL p)) = proj1_sig (Fin.to_nat p).
Proof.
induction p as [|? p IHp].
- reflexivity.
- simpl; destruct (Fin.to_nat (SL p)); simpl in *; rewrite IHp. now destruct (Fin.to_nat p).
Qed.

Equations filter_to_indices'{N M T}(p: T -> bool)(v: vec (S N) T)(f: fin (S M)): list (fin (S M))  by wf N lt :=
  filter_to_indices' _ (h :: _) Fin.F1 := if p h then List.cons Fin.F1 List.nil else List.nil;
  filter_to_indices' _ [h] (Fin.FS j) := if p h then List.cons (Fin.FS j) List.nil else List.nil;
  filter_to_indices' _ (h :: ts) (Fin.FS j) := if p h then
                                                (Fin.FS j)::filter_to_indices' p ts (SL j)
                                              else
                                                filter_to_indices' p ts (SL j).

Fixpoint length_vec{n T}(v: vec n T): fin (S n) :=
  match v with
  | [] => Fin.F1
  | h :: ts => Fin.FS (length_vec ts)
  end.

Definition filter_to_indices{N T}(v: vec N T) (p: T -> bool): list (fin N) :=
  match v with
  | [] => List.nil
  | h :: ts => filter_to_indices' p (Vector.rev (h :: ts)) (length_vec ts)
  end.

Lemma filter_to_indices_spec: forall n T (v: vec n T) p (l: list (fin n)),
    filter_to_indices v p = l <->
      (forall x, List.In x l <-> p (Vector.nth v x) = true).
Proof.
  induction n; intros; split; intros; dependent destruction v.  
  - dependent destruction x.
  - destruct l; cbn.
    + reflexivity.
    + dependent destruction t.
Admitted.

Equations safe_nth{T}(h: T) (ts: list T)(i: fin (S (length ts))): T :=
  safe_nth h ts Fin.F1 := h;
  safe_nth h (x::ts') (Fin.FS k) := safe_nth x ts' k.
