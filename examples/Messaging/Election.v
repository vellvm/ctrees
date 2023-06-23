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

Definition proc_handle_msg (id: uid)(right: uid) (m: option message): ctree (netE message) B01 (unit + unit) :=
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
       end.

Definition proc_loop (id: uid)(right: uid): ctree (netE message) B01 unit :=
  CTree.iter
    (fun _ =>
       m <- recv id;;
       proc_handle_msg id right m) tt.

(*| Client process |*)
Definition proc (id: uid)(n: nat): ctree (netE message) B01 unit :=
  let right := modulo (S id) n in
  (* 1. Send my [id] to the process on the right *)
  send id right (Candidate id);;
  (* 2. Loop until we know the leader *)
  proc_loop id right.

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
    (forall l t', trans l v[@i] t' -> trans l (sched v) (sched (replace v i t'))) ->
    (forall l T', trans l (sched v) T' -> exists t', trans l v[@i] t' /\ T' ≅ (sched (replace v i t'))) ->
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

  Lemma sched_fair_not_stuck : sched_correct -> sched_fair -> forall v i, ~ is_stuck v[@i] -> ~ is_stuck (sched v).
  Proof.
    intros.
    red in H0. specialize (H0 v). step in H0. destruct H0.
    intro. apply H1. red. intros. intro.
    apply H0 in H4 as ?. destruct H5.
    - apply H5 in H4. now apply H3 in H4.
    - destruct (H5) as [(? & ? & ?) _]. now apply H3 in H6.
  Qed.

End Fair.

Lemma ktrans_trans : forall {E C X St h} `{B0 -< C} (s s' : St) (t t' : ctree E C X),
  ktrans (h := h) (t, s) (t', s') ->
   (exists l, trans l t t') \/ exists r, trans (val r) t stuckD /\ t' ≅ Ret r /\ s = s'.
Proof.
  intros. inversion H0; subst; etrans.
Qed.

Theorem distr_system_dec_variant : forall {n C X St Msg} `{HasB0: B0 -< C}
  (h : list (list Msg) -> St -> forall X, netE Msg X -> St)
  (Inv : vec n (ctree (netE Msg) C X) -> list (list Msg) -> St -> Prop) (var : St -> nat)
  (Hprog :
    forall (sched : vec n (ctree (netE Msg) C X) -> ctree (netE Msg) C X)
    (Hc : sched_correct sched) (*(Hf : sched_fair (HasB0 := HasB0) sched)*)
    v qs st, Inv v qs st -> var st > 0 -> ~is_stuck (sched v))
  (Hdec :
    forall (sched : vec n (ctree (netE Msg) C X) -> ctree (netE Msg) C X)
    (Hc : sched_correct sched) (*(Hf : sched_fair (HasB0 := HasB0) sched)*)
    v qs st, Inv v qs st -> var st > 0 ->
    forall v' qs' st', ktrans (h := handler_netE h) (sched v, (qs, st)) (sched v', (qs', st')) ->
    Inv v' qs' st' /\ var st' < var st),
  forall (sched : vec n (ctree (netE Msg) C X) -> ctree (netE Msg) C X)
  (Hc : sched_correct sched) (*(Hf : sched_fair (HasB0 := HasB0) sched)*) v qs st,
  Inv v qs st ->
  entailsF (h := handler_netE h) <(AF (now {(fun '(qs, st) => var st = 0)}))> (sched v) (qs, st).
Proof.
  intros.
  remember (var st) as i. assert (var st <= i)%nat by lia. clear Heqi.
  revert v qs st H H0. induction i; intros.
  - left. cbn. lia.
  - inversion H0. 2: { apply IHi; auto. }
    next. right. apply ctl_ax. intros. apply ktrans_trans in H1 as ?.
    destruct (H3) as [ [] | (? & ? & ? & ?) ]; clear H3.
    + apply Hc in H4 as (? & ? & ? & ?).
      rewrite H4 in H1.
      cbn in Hdec. destruct s'.
      unshelve epose proof (Hdec _ _ _ _ _ _ _ _ _ _ H1) as []; auto.
      lia.
      assert (var s <= i)%nat by lia.
      replace t' with (sched (replace v x0 x1)) by admit.
      apply IHi; auto.
    + subst. exfalso. subs.
Admitted.

Variant candidate_state : Type :=
| CandBegin
| CandTraveling (d: nat)
| CandLost.

Variant election_state : Type :=
| VCandidates (l: list candidate_state)
| VElected (i: nat) (* i => i hops *)
.

Definition ids_wf {n} (ids : vec n nat) :=
  forall j k, j <> k -> Vector.nth ids j <> Vector.nth ids k.

Definition max_id {n} (ids : vec n nat) (wf : ids_wf ids) : fin n.
Admitted.

Lemma max_id_correct : forall {n} (ids : vec n nat) (wf : ids_wf ids),
  forall k, k <> max_id wf -> Vector.nth ids k < Vector.nth ids (max_id wf).
Admitted.

Section Election.

Context {n : nat} (Hn : n <> 0) (ids : vec n nat) (wf : ids_wf ids).

Open Scope nat_scope.

Definition from_to_ (i j : nat) : nat -> Prop :=
  fun k => i <= k /\ k < j.

Definition from_to (i j : nat) : nat -> Prop :=
  fun k =>
    (i <= j -> from_to_ i j k) /\
    (j < i -> from_to_ j n k /\ from_to_ 0 i k).

Lemma from_to_bound : forall (i j k : nat) (Hi: i < n) (Hj: j < n), from_to i j k ->
  k < n.
Proof.
  intros. destruct H. unfold from_to_ in *. lia.
Qed.

Definition fin_of_nat_mod i : fin n :=
  Fin.of_nat_lt (p := i mod n) (Nat.mod_upper_bound i n Hn).

(* Invariant during phase 1 (Candidate messages) *)
Definition election_invariant_candidates
  (cand_progress : list candidate_state) qs :=
  List.length cand_progress = n /\
  List.nth (proj1_sig (Fin.to_nat (max_id wf))) cand_progress CandLost <> CandLost /\
  forall i (Hi : (i < n)%nat),
    (List.nth_error cand_progress i = Some CandBegin \/ List.nth_error cand_progress i = Some CandLost) ->
      ~ In (Candidate i) (concat qs) /\
    forall p, List.nth_error cand_progress i = Some (CandTraveling p) ->
      let i' := Fin.of_nat_lt Hi in
      let s := (i + 1) mod n in
      let j := (i + p + 1) mod n in
      (In (Candidate n) (List.nth j qs []%list)) /\
      (forall k (Hk: from_to s j k),
        let k' := Fin.of_nat_lt (@from_to_bound s j k (Nat.mod_upper_bound _ _ Hn) (Nat.mod_upper_bound _ _ Hn) Hk) in
        Vector.nth ids k' < Vector.nth ids i' /\
        (i' = max_id wf -> k <> i -> List.nth_error cand_progress k = Some CandLost)).

(* Invariant during phase 2 (Elected message) *)
Definition election_invariant_elected
  (elected_progress : nat) (qs: list (list message)) :=
  forall (He : elected_progress < n),
  let m := proj1_sig (Fin.to_nat (max_id wf)) in
  let e' := Fin.of_nat_lt He in
  let j := (m + elected_progress + 1) mod n in
  List.nth j qs []%list = [Elected m]%list /\
  forall k, k <> j -> List.nth k qs []%list = []%list.

Definition election_state_invariant st qs :=
  match st with
  | VCandidates l => election_invariant_candidates l qs
  | VElected n => election_invariant_elected n qs
  end.

Definition election_src_invariant_candidate st i (t : ctree (netE message) B01 unit) :=
  match st with
  | CandBegin => t ≅ proc i n
  | CandTraveling j =>
    (j < n -> t ≅ proc_loop i ((i + 1) mod n)) /\
    (j = n -> t ≅ Ret tt)
  | CandLost => t ≅ proc_loop i ((i + 1) mod n)
  end.

Definition election_src_invariant st (v : vec n (ctree (netE message) B01 unit)) :=
  match st with
  | VCandidates l => forall i (Hi : i < n),
    election_src_invariant_candidate (nth i l CandLost) i v[@Fin.of_nat_lt Hi]
  | VElected d =>
    let m := proj1_sig (Fin.to_nat (max_id wf)) in
    forall i (Hi: i < n),
    (from_to ((S m) mod n) ((m + d + 1) mod n) i ->
      v[@Fin.of_nat_lt Hi] ≅ Ret tt) /\
    (not (from_to ((S m) mod n) ((m + d + 1) mod n) i) ->
      v[@Fin.of_nat_lt Hi] ≅ proc_loop i ((i + 1) mod n))
  end.

Definition election_invariant v qs st := election_state_invariant st qs /\ election_src_invariant st v.

Definition cand_state_value (st : candidate_state) :=
  match st with
  | CandBegin => n + 1
  | CandTraveling d => n - d
  | CandLost => 0
  end.

Definition election_variant (st : election_state) :=
  match st with
  | VCandidates l => 2 * n + List.fold_left (fun m st => m + cand_state_value st) l 0
  | VElected d => n - d
  end.

Definition handle_election_state (qs: list (list message)) (st: election_state) :
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

Theorem election_progress :
  forall (sched : vec n (ctree (netE message) B01 unit) -> ctree (netE message) B01 unit)
  (Hc : sched_correct sched) (Hf : sched_fair sched)
  v qs st, election_invariant v qs st -> election_variant st > 0 -> ~is_stuck (sched v).
Proof.
  intros.
  destruct H. destruct st.
  - clear H0. cbn in H, H1. destruct H. destruct H0.
    specialize (H1 (proj1_sig (Fin.to_nat (max_id wf))) (proj2_sig (Fin.to_nat (max_id wf)))).
    destruct (nth (proj1_sig (Fin.to_nat (max_id wf))) l CandLost) eqn:?.
    + cbn in H1. eapply sched_fair_not_stuck; auto. rewrite H1.
      intro. eapply H3. etrans.
    + cbn in H1. eapply sched_fair_not_stuck; auto. admit.
    + auto.
Abort.

End Election.
