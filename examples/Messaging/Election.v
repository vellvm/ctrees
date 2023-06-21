From ITree Require Import
     Subevent
     CategoryOps
     Indexed.Sum.

From Coq Require Import
     Nat
     Lia
     Vector
     List
     Arith.PeanoNat.

From ITree Require Import
     CategoryOps.

From ExtLib Require Import
     Structures.Monad
     Structures.MonadState
     Data.Monads.StateMonad.

From CTree Require Import
     CTree
     Eq
     Interp.Preempt
     Interp.Network
     Logic.Kripke
     Logic.Ctl
     Misc.Vectors.

From Equations Require Import Equations.

Import CTreeNotations ListNotations VectorNotations CtlNotations.
Local Open Scope vector_scope.
Local Open Scope ctree_scope.
Local Open Scope ctl_scope.

Set Implicit Arguments.

Variant message :=
  | Candidate (u: nat)
  | Elected (u: nat).

(*| Client process |*)
Definition proc (id: uid)(n: nat): ctree (netE message) B01 unit :=
  let right := modulo (S id) n in
  (* 1. Send my [id] to the process on the right *)
  send id right (Candidate id);;
  (* 2. Loop until we know the leader *)
  CTree.iter
    (fun _ =>
       m <- recv id;;
       match m with
       | Some (Candidate candidate) =>
           match Nat.compare candidate id with (* candidate < id *)
           (* My [left] neighbor proposed a candidate, I support that candidate *)
           | Gt => send id right (Candidate candidate) ;; Ret (inl tt)
           (* My left neighbor proposed a candidate, I do not support him *)
           | Lt => Ret (inl tt)
           (* I am the leader, but only I know *)
           | Datatypes.Eq => send id right (Elected id) ;; Ret (inr tt)
           end
       | Some (Elected x) =>
           (* I know [x] is the leader *)
           send id right (Elected x) ;; Ret (inr tt)
       | None => Ret (inl tt) (* Didn't receive anything *)
       end) tt.

(*
  For the system "sched {proc(id,n) | 0 <= id < n}"
  Soundness    :
 - If I exit the loop, it's because I have elected somebody
 - If two processes exit, they have elected the same person
  Termination :
 - Eventually, every process exit/elects
 - (?) AF now {(fun '(qs,id) => nth_error qs id = Some [Elected id]%list)}

Consequence of:
  Invariant (proc (id,n))
  Variant   (proc (id,n))
  Property about sched

On dynamic and logical state:
 Dynamic : one FIFO per process
 Logical (l) : uid -> (has_elected (id) | best_so_far (id))
 (* Could be sufficent to just remember elected or has_seen(n)?*)

The (global system) correctness is:
AF now (fun l => exists id, forall x, l x = has_elected id
                 /\ terminated x)

Let's look at one process: proc(i,n)  (i < n)

P (entry loop iteration) ===> Q (end loop iteration)
 - exists j, l i = best_so_far(j)
 - rcv (Elected k) -> k >= (>?) j
 - rcv (Elected k) -> k >= (>?) j

On the side of termination, let's define the variant:
 - global:
 V(l) =
  Lexicographic on
  + worth 2 if has_elected, worth 1 if has_seen(n)
  + Progresses if a [candidate(n)] or [elected] message gets closer to the head of a fifo (i.e. if I pop from a fifo containing such a message)

V(l) strictly increases if I received n (as candidate or elected)
V(l) remains equal otherwise

Assumption: could the fairness have the granularity of a loop iteration?

Question: how to lift this local obligation to global termination?
- At all time, (candidate(n) or elected(n)) is in a mailbox


We must exploit here the FIFO politics to express that if I rcv and send something having nothing to do with n, I don't push back the message in the queue

forall i, V /\ I ==> AX (proc i) |- V décroit strict ou I
exists j, V /\ I ==> AX (proc j) |- V décroit strict
----------------------------------------------------
V ==> AF (sched n proc) |- V décroit strict


 *)

Section Fair.
  Context {E C : Type -> Type} {X : Type} `{HasB0: B0 -< C} (n : nat).
  Variable sched : vec n (ctree E C X) -> ctree E C X.

  (* Transitions of the scheduled ctree are necessarily taken from
     the individual processes *)
  Definition sched_correct := forall v l T',
    trans l (sched v) T' ->
    exists (i : fin n) t',
    trans l (Vector.nth v i) t' /\ T' ≅ sched (replace v i t').

  (* Process i will make some progress in finite time *)
  Inductive sched_fair1_ i : vec n (ctree E C X) -> Prop :=
  | sched_fair1_now : forall v,
    ((exists l T', trans l (sched v) T') /\
      forall l T', trans l (sched v) T' -> exists t', T' ≅ (sched (replace v i t'))) ->
    sched_fair1_ i v
  | sched_fair1_later : forall v,
    (exists l T', trans l (sched v) T') /\
    (forall l v',
      trans l (sched v) (sched v') ->
      sched_fair1_ i v') ->
    sched_fair1_ i v.

  (* Any process that can progress will do so in finite time *)
  Definition sched_fair1 v :=
    forall l t' i, trans l (Vector.nth v i) t' -> sched_fair1_ i v.

  Program Definition sched_fairF : mon (vec n (ctree E C X) -> Prop) :=
    {| body R v := sched_fair1 v /\ forall l v', trans l (sched v) (sched v') -> R v' |}.
  Next Obligation.
    split; auto. intros. apply H. now apply H1 in H2.
  Qed.

  (* Whenever a process can progress, it will do so in finite time *)
  Definition sched_fair := forall v, (gfp sched_fairF) v.
End Fair.

Definition from_to_ (i j : nat) : nat -> Prop :=
  fun k => Nat.le i k /\ Nat.lt k j.

Definition from_to {n} (i j : fin n) : fin n -> Prop :=
  fun k =>
    let i := proj1_sig (Fin.to_nat i) in
    let j := proj1_sig (Fin.to_nat j) in
    let k := proj1_sig (Fin.to_nat k) in
    (Nat.le i j -> from_to_ i j k) /\
    (Nat.lt j i -> from_to_ j n k /\ from_to_ 0 i k).

Variant candidate_state : Type :=
| CandBegin
| CandTraveling (d: nat)
| CandLost.

Variant election_state : Type :=
| VCandidates (l: list candidate_state)
| VElected (i: nat) (* i => i hops *)
.
Arguments election_state : clear implicits.

Definition ids_wf {n} (ids : vec n nat) :=
  forall j k, j <> k -> Vector.nth ids j <> Vector.nth ids k.

Definition max_id {n} (ids : vec n nat) (wf : ids_wf ids) : fin n.
Admitted.

Lemma max_id_correct : forall {n} (ids : vec n nat) (wf : ids_wf ids),
  forall k, k <> max_id wf -> Vector.nth ids k < Vector.nth ids (max_id wf).
Admitted.

(* Invariant during phase 1 (Candidate messages) *)
Program Definition election_invariant_candidates n (ids : vec (S n) nat) (wf : ids_wf ids)
  (cand_progress : list candidate_state) qs :=
  List.length cand_progress = S n /\
  List.nth (proj1_sig (Fin.to_nat (max_id wf))) cand_progress CandLost <> CandLost /\
  forall i (Hi : (i < S n)%nat),
    (List.nth_error cand_progress i = Some CandBegin \/ List.nth_error cand_progress i = Some CandLost) ->
      ~ In (Candidate i) (concat qs) /\
    forall p, List.nth_error cand_progress i = Some (CandTraveling p) ->
      let i' := Fin.of_nat_lt Hi in
      let j := (i + p + 1) mod (S n) in
      (In (Candidate n) (List.nth j qs []%list)) /\
      (forall k, from_to i' (Fin.of_nat_lt (p := j) _) k ->
        Vector.nth ids k < Vector.nth ids i' /\
        (i' = max_id wf -> k <> i' -> List.nth_error cand_progress (proj1_sig (Fin.to_nat k)) = Some CandLost)).
Next Obligation.
  lia.
Qed.

(* Invariant during phase 2 (Elected message) *)
Definition election_invariant_elected n (ids : vec (S n) nat) (wf : ids_wf ids)
  (elected_progress : nat) (qs: list (list message)) :=
  forall (He : elected_progress < n),
  let m := proj1_sig (Fin.to_nat (max_id wf)) in
  let e' := Fin.of_nat_lt He in
  let j := (m + elected_progress + 1) mod (S n) in
  List.nth j qs []%list = [Elected m]%list /\
  forall k, k <> j -> List.nth k qs []%list = []%list.

Definition election_invariant n (ids : vec (S n) nat) (wf : ids_wf ids) st qs :=
  match st with
  | VCandidates l => election_invariant_candidates wf l qs
  | VElected n => election_invariant_elected wf n qs
  end.

Definition handle_election_state n (qs: list (list message)) (st: election_state) :
  forall X, netE message X -> election_state :=
  fun X e =>
  match e with
  | Send i to msg =>
    match st, msg with
    | VCandidates l, Candidate c =>
      VCandidates (nth_map (fun i =>
        match i with
        | CandBegin => CandTraveling 0
        | CandTraveling d => CandTraveling (S d)
        | _ => CandLost
        end)
        l c)
    | VCandidates l, Elected e => VElected 0
    | VElected i, Elected e => VElected (S i)
    | _, _ => VCandidates (List.repeat CandLost n)
    end
  | _ => st
  end.

Lemma ktrans_trans : forall {E C X St h} `{B0 -< C} (s s' : St) (t t' : ctree E C X),
  ktrans (h := h) (t, s) (t', s') ->
  exists l, trans l t t'.
Proof.
  intros. inversion H0; subst; eauto. (* wrong in the Ret case *)
Admitted.

Theorem distr_system_dec_variant : forall {n C X St Msg} `{HasB0: B0 -< C}
  (h : list (list Msg) -> St -> forall X, netE Msg X -> St)
  (Inv : vec n (ctree (netE Msg) C X) -> list (list Msg) -> St -> Prop) (var : St -> nat)
  (sched : vec n (ctree (netE Msg) C X) -> ctree (netE Msg) C X)
  (Hc : sched_correct sched) (Hf : sched_fair (HasB0 := HasB0) sched)
  (Hprog : forall v qs st, Inv v qs st -> var st > 0 -> ~is_stuck (sched v))
  (Hdec : forall v qs st, Inv v qs st -> var st > 0 ->
    forall v' qs' st', ktrans (h := handler_netE h) (sched v, (qs, st)) (sched v', (qs', st')) ->
    Inv v' qs' st' /\ var st' < var st),
  forall v qs st, Inv v qs st -> entailsF (h := handler_netE h) <(AF (now {(fun '(qs, st) => var st = 0)}))> (sched v) (qs, st).
Proof.
  intros. cbn.
  remember (var st) as i. assert (var st <= i)%nat by lia. clear Heqi.
  revert v qs st H H0. induction i; intros.
  - left. lia.
  - inversion H0. 2: { apply IHi; auto. }
    right. apply I. intros. apply ktrans_trans in H1 as ?. destruct H3.
    apply Hc in H3 as (? & ? & ? & ?).
    rewrite H4 in H1.
    cbn in Hdec. destruct s'.
    unshelve epose proof (Hdec _ _ _ _ _ _ _ _ H1) as []; auto.
    lia.
    assert (var s <= i)%nat by lia.
    replace t' with (sched (replace v x0 x1)) by admit.
    apply IHi; auto.
Admitted.
