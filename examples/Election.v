From CTree Require Import
  CTree.Core
  Logic.Ctl
  Utils.Vectors
  CTree.Events.Net.

From Coq Require Import
  Fin
  Classes.SetoidClass.

Set Implicit Arguments.

Import CTreeNotations CtlNotations.
Local Open Scope ctree_scope.
Local Open Scope fin_vector_scope.
Local Open Scope ctl_scope.

Section Election.
  Context (n: nat).
  Variant message :=
    | Candidate (u: fin' n)
    | Elected (u: fin' n).

  Notation netE := (netE n message).

  Definition msg_id(m: message): fin' n :=
    match m with
    | Candidate u => u
    | Elected u => u
    end.

  Definition eqb_message(a b: message): bool :=
    match a, b with
    | Candidate a, Candidate b => Fin.eqb a b
    | Elected a, Elected b => Fin.eqb a b
    | _, _ => false
    end.

  Definition proc(id right: fin' n): ctree netE unit :=
    send right (Candidate id) ;;
    Ctree.iter
      (fun _ =>
         m <- recv ;;
         match m with
         | Some (Candidate candidate) =>
             match Fin_compare candidate id with (* candidate < id *)
             (* [left] neighbor proposed candidate, support her. *)
             | Gt => send right (Candidate candidate) ;; Ret (inl tt)
             (* [left] neighbor proposed a candidate, do not support her. *)
             | Lt => Ret (inl tt)
             (* I am the leader, but only I know. Tell everyone. *)
             | Eq => send right (Elected id) ;; Ret (inr tt)
             end
         | Some (Elected x) =>
             (* I know [x] is the leader *)
             send right (Elected x) ;; Ret (inr tt)
         | None => Ret (inl tt) (* Didn't receive anything *)
         end) tt.
  
  
  Definition get_right(m: nat)(Hlt: m <= n)(i: fin' m) -> fin' n :=
    match 
  Lemma candidate_left_gt: forall id right left out,
      Fin_compare left id = Gt ->
      <( {(proc id right, ([Candidate left], out))} |= AF (now {fun '(inp', out') => inp' = [] /\ out' = out ++ [(id, Candidate left)]}) )>.
  Proof.
    intros.
    apply ctl_af_star_det.
    apply trans_det.
    eexists.
    setoid_rewrite transF_trans_star_iff.
    split.
    exists 2.
    Opaque Eq.
    unfold proc.
    simpl.
    reflexivity.
    cbn.
    unfold Ktree.subst'.

    reflexivity.
    reflexivity.
    cbn.
    next.
    right.
    next.
    intros [p' σ'] TRp.
    cbn in TRp.

(** Equivalence of queues.
    Qs are pairwise either
    1. equal (no diff)
    2. their diff is messages from i -> j, where i < j
 *)
Inductive qequiv(i: uid): list message -> list message -> Prop :=
| QRefl: forall l,
    qequiv i l l
| QNoProgressL: forall h ts l,
  msg_id h < i ->
  qequiv i ts l ->
  qequiv i (h::ts) l
| QNoProgressR: forall h ts l,
  msg_id h < i ->
  qequiv i l ts ->
  qequiv i l (h::ts).
Hint Constructors qequiv: core.

(** Lift an index relation [nat -> rel T] to a [nat -> rel (list T)] *)
Inductive pairwisei T (p: nat -> T -> T -> Prop): nat -> list T -> list T -> Prop :=
| QDone: pairwisei p 0 [] []
| QStep: forall h h' ts ts' n,
  p n h h' ->
  pairwisei p n ts ts' ->
  pairwisei p (S n) (h::ts) (h'::ts').
Hint Constructors pairwisei: core.

(** Lists must be equal size *)
Lemma pairwisei_length: forall T p n (l l': list T),
    pairwisei p n l l' -> length l = length l'.
Proof. induction 1; cbn; auto. Qed.

(** Now define equivalence of queues *)
Definition qsequiv a b := pairwisei qequiv (length a) a b.
Notation "a ⩸ b" := (qsequiv a b) (at level 52, left associativity).
Hint Unfold qsequiv: core.
Arguments qsequiv _ _ /.
Ltac inv H := inversion H; subst; clear H.

#[global] Instance Equivalence_qequiv n: Equivalence (qequiv n).
Proof.
  constructor; red.
  - apply QRefl.
  - induction 1; auto.
  - intros.
    generalize dependent x.
    induction H0; intros; auto.
    apply IHqequiv.
    admit.
Admitted.

#[global] Instance Equivalence_qsequiv: Equivalence qsequiv.
Proof.
  constructor.
  - red; induction x; auto.
    unfold qsequiv; cbn.
    apply QStep; auto.
  - red; intros x y H. cbn in *.
    assert(EqLen:length x = length y) by (now apply pairwisei_length in H).
    rewrite <- EqLen; clear EqLen.
    remember (length x).
    induction H; cbn in *; auto.
    apply QStep; auto.
    inv Heqn.
    now symmetry.
  - red; intros.
Admitted.

(** This the "no constraint" relation # of Event structures.
    It means those messages have no causal order and could be scheduled in any way *)
Reserved Notation "a # b" (at level 52, left associativity).
Inductive netE_noconflict: forall {X Y}, netE message X -> netE message Y -> Prop :=
| RecvAnyOrder: forall from to,
    Recv from # Recv to
| SendAnyOrder: forall from from' to to' m m',
    Send from to m # Send from' to' m'
where "a # b" := (netE_noconflict a b).

#[global] Instance Equivalence_netE {X}: Equivalence (@netE_noconflict X X).
Proof.
  constructor; red.
  - intros.
    constructor.
Reserved Notation "a ⪯ b" (at level 52, left associativity).
Inductive netE_order: netE message -> netE message -> Prop :=
| SendRecvLt: forall from to m,
    Send from to m ⪯ Recv to
where "a ⪯ b" := (netE_order a b).


    length qs = length qs' ->
    Forall (fun '(l, l') =>
              let d = diff l l' in
              d = [] \/ Forall (fun msg => diff l l'combine qs qs'
    Forall (fun l => forall i, In l i -> diff l l'
    msg_id msg < i ->
    qequiv l l'
| NoMsg:
| BadMsg:
  msg_id
  qequiv h :: ts h' :: ts'
