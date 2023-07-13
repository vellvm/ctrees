From ITree Require Import
     Subevent
     CategoryOps
     Indexed.Sum.

From Coq Require Import
     Nat
     Lia
     Vector
     List
     Arith.PeanoNat
     Wellfounded Relations.Relation_Operators.

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

Import CTreeNotations ListNotations VectorNotations CtlNotations.
Local Open Scope vector_scope.
Local Open Scope ctree_scope.
Local Open Scope ctl_scope.

Set Implicit Arguments.

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

  (* FIXME the scheduler should have some kind of state *)
  Variable sched : vec n (ctree E C X) -> ctree E C X.
  Variable next_id : vec n (ctree E C X) -> fin n.

  (* Transitions of the scheduled ctree are necessarily taken from
     the individual processes *)
  (* FIXME Ret *)
  Definition sched_correct :=
    forall v,
    (* the scheduling can only be stuck if all the processes are stuck *)
    (forall i l t', trans l v[@i] t' -> exists l' t'', trans l' v[@next_id v] t'') /\
    (* all the transitions of the next scheduled process appear in the scheduled ctrees *)
    (forall l t', trans l v[@next_id v] t' -> trans l (sched v) (sched (replace v (next_id v) t'))) /\
    (* and no other transitions are possible *)
    forall l T', trans l (sched v) T' -> exists t', trans l v[@next_id v] t' /\ T' ≅ sched (replace v (next_id v) t').

  Lemma sched_correct_ktrans : sched_correct ->
    forall S h v,
    (forall i t' st st', ktrans (S := S) (h := h) (v[@i], st) (t', st') -> exists t'' st'', ktrans (S := S) (h := h) (v[@next_id v], st) (t'', st'')) /\
    (forall T' st st',
      ktrans (S := S) (h := h) (sched v, st) (T', st') ->
      exists t',
      ktrans (Vector.nth v (next_id v), st) (t', st') /\ T' ≅ sched (replace v (next_id v) t')) /\
    (forall t' st st',
      ktrans (S := S) (h := h) (v[@next_id v], st) (t', st') ->
      ktrans (S := S) (h := h) (sched v, st) (sched (replace v (next_id v) t'), st')).
  Admitted.

  (* Process i will make some progress in finite time
     sched_fair1_ i v ≜ eventually, sched (v1,..,vn) ~>* sched (v1', ..vi, ..,vn') ~> sched (v1', ..vi',..,vn')
   *)
  Inductive sched_fair1_ i : vec n (ctree E C X) -> Prop :=
  | sched_fair1_now : forall v,
    next_id v = i ->
    sched_fair1_ i v
  | sched_fair1_later : forall v,
    next_id v <> i ->
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

  Lemma sched_fair_not_stuck : sched_correct -> forall v i, ~ is_stuck v[@i] -> ~ is_stuck (sched v).
  Proof.
    intros. intro. apply H0. red. intros. intro.
    apply H in H2 as (? & ? & ?).
    apply H in H2. now apply H1 in H2.
  Qed.

  Record FairSched := {
    fsched : vec n (ctree E C X) -> ctree E C X;
    fnext_id : vec n (ctree E C X) -> fin n;
    fsched_correct : sched_correct;
    fsched_fair : sched_fair;
  }.

  (* What happens if
     [vi] : [Ret v -val v> ∅]

   *)

End Fair.

Lemma ktrans_trans : forall {E C X St h} `{B0 -< C} (s s' : St) (t t' : ctree E C X),
  ktrans (h := h) (t, s) (t', s') ->
   (exists l, trans l t t') \/ exists r, trans (val r) t stuckD /\ t' ≅ Ret r /\ s = s'.
Proof.
  intros. inversion H0; subst; etrans.
Qed.

(* Meta-theorem reducing the correctness and termination of a "scheduled" system *)
Theorem distr_system_dec_variant : forall {n C X St Msg V } `{HasB0: B0 -< C}
  (h : list (list Msg) -> St -> forall X, netE Msg X -> St)
  (sched : vec n (ctree (netE Msg) C X) -> ctree (netE Msg) C X) next_id
  (Hc : sched_correct sched next_id)
  (Inv : vec n (ctree (netE Msg) C X) -> list (list Msg) -> St -> Prop)
  (var : St -> V) (v0 : V) i k φ
  (Hprog :
    forall v qs st, Inv v qs st -> var st <> v0 -> exists l T', trans l (sched v) T')
  (Hinv :
    forall v st st' qs qs' k t',
    Inv v qs st ->
    ktrans (h := handler_netE h) (v[@k], (qs, st)) (t', (qs', st')) ->
    Inv (replace v k t') qs' st')
  (Hdec :
    forall v qs st,
    Inv v qs st ->
    var st = i ->
    next_id v = k ->
    entailsF (h := handler_netE h) <(AF φ)> (sched v) (qs, st))
  (Hcst :
    forall v T st st' qs qs',
    Inv v qs st ->
    var st = i ->
    next_id v <> k ->
    ktrans (h := handler_netE h) (sched v, (qs, st)) (T, (qs', st')) -> var st' = i),
  forall (Hf : sched_fair (HasB0 := HasB0) sched next_id) v qs st,
  Inv v qs st ->
  var st = i ->
  i <> v0 ->
  entailsF (h := handler_netE h) <(AF φ)> (sched v) (qs, st).
Proof.
  intros.
  specialize (Hf v). step in Hf. destruct Hf. clear H3. red in H2.
  clear H2. assert (H2 : sched_fair1_ sched next_id k v) by admit.
  revert qs st H H0.
  induction H2; intros.
  - now eapply Hdec.
  - next. right. apply ctl_ax. intros.
    apply ktrans_trans in H5 as ?. destruct H6; [| admit].
    destruct H6. destruct s'.
    destruct (Hc v) as (? & _ & ?). specialize (H8 x t' H6). destruct H8 as (? & ? & ?). subs.
    eapply H2; eauto. eapply Hinv; eauto. admit.
Admitted.

(* TODO clean up, use more section variables *)
Definition ids_wf {n} (ids : vec n nat) :=
  forall j k, j <> k -> Vector.nth ids j <> Vector.nth ids k.

Definition max_id {n} (ids : vec n nat) (wf : ids_wf ids) : fin n.
Admitted.

Lemma max_id_correct : forall {n} (ids : vec n nat) (wf : ids_wf ids),
  forall k, k <> max_id wf -> Vector.nth ids k < Vector.nth ids (max_id wf).
Admitted.

Section Election.

Context {n : nat} (Hn : n <> 0) (ids : vec n nat) (wf : ids_wf ids).

Variant message :=
  | Candidate (u: nat)
  | Elected (u: nat).

(* TODO use ids *)
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

Definition proc_loop_handle_msg (id: uid)(right: uid) (m: option message): ctree (netE message) B01 unit :=
  lr <- proc_handle_msg id right m;;
  match lr with
  | inl l => Guard (proc_loop id right)
  | inr r => Ret r
  end.

(* send from to msg *)
(* Before: Switch_to i ~> event modelling that process i is being scheduled
   This is currently removed
 *)
(*| Client process |*)
Definition proc (id: uid)(right: nat): ctree (netE message) B01 unit :=
  (* 1. Send my [id] to the process on the right *)
  send id right (Candidate id);;
  (* 2. Loop until we know the leader *)
  proc_loop id right.

(* Logical state: the logical information about the dynamics we wish to keep track of. *)
Variant proc_state : Type :=
| ProcBegin
| ProcWaiting
| ProcProcessing (m: message)
| ProcElected.

Variant election_progress :=
| MaxCandidate (n : nat)
| MaxElected (n : nat).

Record election_state : Type := mk_election_state {
  s_procs : list proc_state;
  (* Distance traveled by the max candidate message, or by the elected message *)
  s_progress : election_progress;
  (* Messages before proccesing the next message that will make the system progress,
     and whether the first message in the queue is being processed *)
  s_queue : nat * bool;
}.

(* The extended mailbox of a process is its mailbox
   plus the message it's currently processing, if any *)
Definition ext_mailbox1 '(q, p) :=
  match p with
  | ProcProcessing p => (p::q)%list
  | _ => q
  end.

Definition ext_mailbox qs st :=
  List.map ext_mailbox1 (combine qs st.(s_procs)).

Context (sched : vec n (ctree (netE message) B01 unit) -> ctree (netE message) B01 unit).
Context (next_id : vec n (ctree (netE message) B01 unit) -> fin n).
Context (Hc : sched_correct sched next_id).

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

Lemma from_to__dec : forall (i j k : nat), { from_to_ i j k } + { ~from_to_ i j k }.
Proof.
  intros. unfold from_to_.
  destruct (Compare_dec.le_dec i k).
  2: tauto.
  destruct (Compare_dec.lt_dec k j); tauto.
Qed.

Lemma from_to_dec : forall (i j k : nat), { from_to i j k } + { ~from_to i j k }.
Proof.
  intros. unfold from_to. Locate "<=". Search nat le sumbool.
  destruct (Compare_dec.le_lt_dec i j).
  - destruct (from_to__dec i j k); [| tauto].
    left. split; [tauto | lia].
  - destruct (from_to__dec j n k); [| tauto].
    destruct (from_to__dec 0 i k); [| tauto].
    left. split; [lia | tauto].
Qed.

Definition next_proc_and_msg st :=
  let m := (proj1_sig (Fin.to_nat (max_id wf))) in
  match st.(s_progress) with
  | MaxCandidate d => ((m + d) mod n, Candidate m)
  | MaxElected d => ((m + d + 1) mod n, Elected m)
  end.

Definition next_proc st :=
  fst (next_proc_and_msg st).

Definition handle_recv (q : nat * bool) :=
  (if snd q then fst q - 1 else fst q, true).

Definition handle_next qs st i :=
  let l := List.length (List.nth i (ext_mailbox qs st) []%list) in
  match List.nth i st.(s_procs) ProcBegin with
  | ProcBegin => (l + 1, true)
  | ProcProcessing _ => (l, true)
  | _ => (l, false)
  end.

Definition handle_send qs st i (q : nat * bool) :=
  if fst q then handle_next qs st ((i + 1) mod n) else (fst q - 1, false).

Definition handle_election_state (qs: list (list message)) (st: election_state) :
  forall X, netE message X -> election_state :=
  fun X e =>
  let m := (proj1_sig (Fin.to_nat (max_id wf))) in
  let next := next_proc st in
  match e with
  | Send i to msg =>
    let p := nth_map (fun _ => ProcWaiting) st.(s_procs) i in
    let pe := nth_map (fun _ => ProcElected) st.(s_procs) i in
    let q := if Nat.eqb i next then handle_send qs st i st.(s_queue) else st.(s_queue) in
    match st.(s_progress), msg with
    | MaxCandidate d, Candidate c =>
      let progress := if Nat.eqb c ids[@max_id wf] then MaxCandidate (S d) else st.(s_progress) in
      mk_election_state p progress q
    | MaxElected d, Candidate c =>
      mk_election_state p st.(s_progress) q
    | MaxElected d, Elected e =>
      mk_election_state pe (MaxElected (S d)) q
    | MaxCandidate d, Elected e =>
      mk_election_state pe (MaxElected 0) q
    end
  | Recv i =>
    let s := match hd_error (nth i qs []%list) with
    | Some m => ProcProcessing m
    | None => ProcWaiting
    end in
    mk_election_state (nth_map (fun _ => s) st.(s_procs) i) st.(s_progress)
      (if Nat.eqb i next then handle_recv st.(s_queue) else st.(s_queue))
  end.

#[local] Instance h : netE message ~~> state (list (list message) * election_state) := handler_netE handle_election_state.

Lemma eq_dec_message : forall (m m' : message), {m = m'} + {m <> m'}.
Proof.
  intros. destruct (m), m'.
  2, 3: right; intro; discriminate.
  - destruct (Nat.eq_dec u u0).
    + subst. auto.
    + right. intro. now injection H.
  - destruct (Nat.eq_dec u u0).
    + subst. auto.
    + right. intro. now injection H.
Qed.

(* Three components in the "moral" configuration: the code, the dynamic state, the logical state.
The invariants relate these three components. *)

(* Invariant for the Candidate messages *)
Definition election_invariant_candidates
  st qs :=
  (* Well-formedness *)
  let procs := st.(s_procs) in
  let m := (proj1_sig (Fin.to_nat (max_id wf))) in
  (forall i, count_occ eq_dec_message (concat (ext_mailbox qs st)) (Candidate i) <= 1) /\
  (forall i j, In (Candidate i) (List.nth j (ext_mailbox qs st) []%list) -> exists k, i = ids[@k]) /\
  forall i (Hi : (i < n)%nat),
    match List.nth_error procs i with
    | Some ProcBegin => ~ In (Candidate i) (concat (ext_mailbox qs st))
    | _ =>
      (* A losing candidate cannot travel beyond the process with the max id *)
      (forall k, k <> m -> In (Candidate ids[@Fin.of_nat_lt Hi]) (List.nth k (ext_mailbox qs st) []%list) -> from_to ((i + 1) mod n) ((m + 1) mod n) k)
    end.

(* Invariant regarding the position in the mailbox of the current message of interest *)
Definition election_invariant_msg_location
  (st : election_state) (qs: list (list message)) (i: nat) (m: message) :=
  snd st.(s_queue) = match List.nth i st.(s_procs) ProcBegin with ProcProcessing m => true | _ => false end /\
  forall j k, List.nth_error (List.nth j (ext_mailbox qs st) []%list) k = Some m <-> j = i /\ k = fst st.(s_queue).

(* Invariant regarding the max candidate *)
Definition election_invariant_max
  (st : election_state) (qs: list (list message)) :=
  let m := (proj1_sig (Fin.to_nat (max_id wf))) in
  let elected_progress := st.(s_progress) in
  fst st.(s_queue) < n /\
  match elected_progress with
  | MaxCandidate d =>
    (* The leader has not been elected yet *)
    (forall c, ~In (Elected c) (concat (ext_mailbox qs st))) /\
    {Hd : d <= n |
      (* The message can only be in the mailbox at distance d from the max *)
      (d <> 0 -> election_invariant_msg_location st qs ((m + d) mod n) (Candidate ids[@max_id wf])) /\
      (d = 0 -> ~In (Candidate ids[@max_id wf]) (concat (ext_mailbox qs st)))
    }
  | MaxElected elected_progress =>
    {He : elected_progress < n |
      let e' := Fin.of_nat_lt He in
      let j := (m + elected_progress + 1) mod n in
      (* There are no (Candidate m) messages left *)
      (forall k, ~ In (Candidate ids[@max_id wf]) (List.nth k (ext_mailbox qs st) []%list)) /\
      (* There can only be one elected message *)
      election_invariant_msg_location st qs j (Elected ids[@max_id wf]) /\
      forall c k, c <> ids[@max_id wf] -> ~In (Elected c) (List.nth k (ext_mailbox qs st) []%list)
    }
  end.

Definition election_state_invariant st qs :=
  List.length st.(s_procs) = n /\
  election_invariant_candidates st qs /\
  election_invariant_max st qs.

(* Ties the proc_states to the ctrees *)
Definition election_src_invariant_candidate st i (t : ctree (netE message) B01 unit) :=
  match st with
  | ProcBegin => t ≅ proc i n
  | ProcWaiting =>
    (t ≅ proc_loop i ((i + 1) mod n))
  | ProcProcessing m => t ≅ proc_handle_msg i ((i + 1) mod n) (Some m);; proc_loop i ((i + 1) mod n)
  | ProcElected => t ≅ Ret tt \/ t ≅ stuckD
  end.

(* Links proc_states and election progress *)
Definition election_src_invariant st (v : vec n (ctree (netE message) B01 unit)) :=
  let m := proj1_sig (Fin.to_nat (max_id wf)) in
  (forall i (Hi : i < n),
    election_src_invariant_candidate (nth i st.(s_procs) ProcBegin) i v[@Fin.of_nat_lt Hi]) /\
  match st.(s_progress) with
  | MaxCandidate d =>
    (d = 0 -> nth m st.(s_procs) ProcBegin = ProcBegin) /\
    forall k, nth k st.(s_procs) ProcBegin <> ProcElected
  | MaxElected d =>
    forall i (Hi: i < n),
    nth i st.(s_procs) ProcBegin <> ProcBegin /\
    (from_to ((S m) mod n) ((m + d + 1) mod n) i <->
      nth i st.(s_procs) ProcBegin = ProcElected)
  end.

Definition election_invariant v qs st := election_state_invariant st qs /\ election_src_invariant st v.
Opaque election_invariant.

Lemma election_elected_proc_states :
  forall v qs st d,
  election_invariant v qs st ->
  st.(s_progress) = MaxElected d ->
  forall i (Hi : i < n),
  let m := proj1_sig (Fin.to_nat (max_id wf)) in
  (from_to ((S m) mod n) ((m + d + 1) mod n) i /\
    nth i st.(s_procs) ProcBegin = ProcElected) \/
  ( ~from_to ((S m) mod n) ((m + d + 1) mod n) i /\
    (nth i st.(s_procs) ProcBegin = ProcWaiting \/
      exists m, nth i st.(s_procs) ProcBegin = ProcProcessing m)).
Proof.
  intros. destruct H as [_ ?]. destruct H as [_ ?]. rewrite H0 in H.
  destruct (from_to_dec (S m mod n) ((m + d + 1) mod n) i).
  - left. split; auto.
    now apply H in f.
  - right. split; auto.
    apply H in Hi as [? ?]. apply not_iff_compat in H2. apply H2 in n0.
    destruct (nth i (s_procs st) ProcBegin) eqn:?; eauto with exfalso.
Qed.

Lemma election_map_proc_state :
  forall v qs st i (Hi : i < n), election_invariant v qs st ->
    election_src_invariant_candidate (nth i st.(s_procs) ProcBegin) i v[@Fin.of_nat_lt Hi].
Proof.
  intros. destruct H as [_ ?]. destruct H as [? _]. apply H.
Qed.

(*
  Correctness of system is a direct consequence of [election_variant = 0] is reached
 *)
Definition election_variant (st : election_state) : nat * (nat * nat) :=
  match st.(s_progress) with
  | MaxCandidate d => (n + n + 1 - d, (fst st.(s_queue), if snd st.(s_queue) then 0 else 1))
  | MaxElected d => (n - d - 1, (fst st.(s_queue), if snd st.(s_queue) then 0 else 1))
  end.

Definition lt_election_variant := slexprod nat (nat * nat) Nat.lt (slexprod nat nat Nat.lt Nat.lt).

Lemma election_variant_wf : well_founded lt_election_variant.
Proof.
  repeat apply wf_slexprod; apply lt_wf.
Qed.

Theorem election_does_progress :
  forall (sched : vec n (ctree (netE message) B01 unit) -> ctree (netE message) B01 unit) next_id
  (Hc : sched_correct sched next_id)
  v qs st, election_invariant v qs st -> election_variant st <> (0, (0, 0)) ->
  exists l T', trans l (sched v) T'.
Proof.
Admitted.

Lemma in_not_nil : forall {A} (l : list A) a, List.In a l -> l <> []%list.
Proof.
  intros * ? ->. destruct H.
Qed.

Lemma nth_not_default : forall {A} (l : list A) n d, List.nth n l d <> d -> n < length l.
Proof.
  intros. revert l H. induction n0; intros.
  - destruct l. cbn in H. contradiction. cbn. lia.
  - destruct l. cbn in H. contradiction. cbn in H. apply IHn0 in H. cbn. lia.
Qed.

(* Messages that do not make the system progress are
   non-maximal Candidate messages *)
Lemma election_other_messages :
  let m := proj1_sig (Fin.to_nat (max_id wf)) in
  forall v qs st msg k,
  election_invariant v qs st ->
  k <> next_proc st ->
  In msg (List.nth k (ext_mailbox qs st) []%list) ->
  exists i, i <> max_id wf /\ msg = Candidate ids[@i].
Proof.
  intros.
  destruct H as [? _]. destruct H as (? & ? & ?). destruct H3.
  destruct (s_progress st) eqn:?.
  - (* phase 1 *)
    destruct H4 as (? & ? & ?).
    assert (k < length (ext_mailbox qs st)).
    { eapply nth_not_default. eapply in_not_nil. apply H1. }
    destruct msg.
    2: {
      exfalso. apply (H4 u). apply in_concat. eexists. split; [| apply H1].
      now apply nth_In.
    }
    destruct H2 as (_ & ? & _).
    apply H2 in H1 as ?. destruct H6 as [? ->].
    exists x0. split; auto. intro. subst.
    destruct (nat_eqdec n0 0).
    + apply a in e. apply e.
      apply in_concat. eexists. split; [| apply H1].
      now apply nth_In.
    + apply a in n1. destruct n1 as [_ ?].
      apply In_nth_error in H1 as []. apply H6 in H1 as [-> ->].
      unfold next_proc, next_proc_and_msg in H0. rewrite Heqe in H0. contradiction.
  - (* phase 2 *)
    destruct H4 as (? & ? & ?).
    assert (k < length (ext_mailbox qs st)).
    { eapply nth_not_default. eapply in_not_nil. apply H1. }
    destruct msg.
    + destruct H2 as (_ & ? & _). apply H2 in H1 as ?. destruct H7 as [? ->].
      exists x0. split; auto. intro. subst.
      now apply H4 in H1.
    + exfalso. destruct (nat_eqdec u ids[@max_id wf]). subst.
      * destruct H5 as [ [_ ?] _]. red in H5.
        apply In_nth_error in H1 as []. apply H5 in H1 as [-> ->].
        unfold next_proc, next_proc_and_msg in H0. rewrite Heqe in H0. contradiction.
      * now apply H5 in H1.
Qed.

Lemma election_processing_ext_mailbox :
  forall v qs st i (Hi : i < n) msg,
  election_invariant v qs st ->
  nth i (s_procs st) ProcBegin = ProcProcessing msg ->
  hd_error (nth i (ext_mailbox qs st) []%list) = Some msg.
Proof.
  intros.
  destruct H as [(? & _ & _) [? _] ].
  specialize (H1 i Hi). red in H1. rewrite H0 in H1.
  change []%list with (ext_mailbox1 ([]%list, ProcBegin)).
  unfold ext_mailbox. rewrite map_nth. unfold ext_mailbox1. Search combine nth.
  rewrite combine_nth, H0. reflexivity. admit. (* TODO add qs length to invariant *)
Admitted.

Lemma hd_error_in : forall {A} (l : list A) a, hd_error l = Some a -> In a l.
Proof.
  intros. destruct l; [discriminate |].
  inversion H. subst. now left.
Qed.

(* ktrans inversion lemmas for leader election processes *)

Lemma ktrans_proc_loop_some_inv : forall i j t' qs qs' st st' m,
  ktrans ((proc_loop i j), (qs, st)) (t', (qs', st')) ->
  List.hd_error (List.nth i qs []%list) = Some m ->
  t' ≅ proc_loop_handle_msg i j (Some m) /\
  qs' = nth_map (fun _ => tl (List.nth i qs []%list)) qs i /\
  st' = mk_election_state
    (nth_map (fun _ => ProcProcessing m) st.(s_procs) i)
    st.(s_progress)
    (if i =? next_proc st then handle_recv (s_queue st) else s_queue st).
Proof.
  intros.
  unfold proc_loop in H. rewrite unfold_iter in H.
  rewrite bind_bind in H. setoid_rewrite bind_trigger in H.
  apply ktrans_vis_inv in H as (? & ? & ? & ?).
  cbn in H2. unfold execState in H2. cbn in H1, H2.
  destruct (nth i qs []%list) eqn:?. { discriminate. }
  inv H0.
  inversion H2. cbn. intuition.
  cbn in H. unfold proc_loop_handle_msg, proc_handle_msg.
  rewrite H. upto_bind_eq. destruct x1 as [ [] | [] ]; reflexivity.
Qed.

Lemma ktrans_proc_loop_none_inv : forall i j t' qs qs' st st',
  ktrans ((proc_loop i j), (qs, st)) (t', (qs', st')) ->
  List.hd_error (List.nth i qs []%list) = None ->
  t' ≅ Guard (proc_loop i j) /\
  qs' = qs /\
  st' = st.
Proof.
  intros.
  unfold proc_loop in H. rewrite unfold_iter in H.
  rewrite bind_bind in H. setoid_rewrite bind_trigger in H.
  apply ktrans_vis_inv in H as (? & ? & ? & ?).
  cbn in H2. unfold execState in H2. cbn in H1, H2.
  destruct (nth i qs []%list) eqn:?. 2: discriminate.
  cbn in H1, H2. inv H2. intuition.
  rewrite H. cbn. rewrite bind_ret_l. now apply br_equ.
Qed.

(*
Lemma ktrans_proc_handle_other_candidate_gt_inv : forall i j c t' v qs qs' st st'
  (INV: election_invariant v qs st),
  ktrans (proc_loop_handle_msg i j (Some (Candidate c)), (qs, st)) (t', (qs', st')) ->
  c > i ->
  i <> next_proc st ->
  t' ≅ Guard (proc_loop i j) /\
  qs' = nth_map (fun q => (q ++ [Candidate c])%list) qs j /\
  st' = mk_election_state
    (nth_map (fun _ => ProcWaiting) st.(s_procs) i)
    st.(s_progress)
    st.(s_queue).
Proof.
  intros.
  unfold proc_loop_handle_msg, proc_handle_msg in H.
  apply Nat.compare_gt_iff in H0. rewrite H0 in H.
  rewrite bind_bind in H. setoid_rewrite bind_trigger in H.
  apply ktrans_vis_inv in H as ([] & ? & _ & ?). rewrite bind_ret_l in H.
  cbn in H2. unfold execState in H2. cbn in H2.
  inversion H2.
  apply Nat.eqb_neq in H1. rewrite !H1.
  destruct (s_progress st) eqn:?.
  - assert (In (Candidate c) (List.nth i (ext_mailbox qs st) []%list)).
    {
      apply hd_error_in. eapply election_processing_ext_mailbox; eauto.
*)

(* Stability of variant when an uninteresting process is scheduled *)
Theorem election_cst_elected :
  let m := proj1_sig (Fin.to_nat (max_id wf)) in
  forall i (Hi : i <> 0 /\ i < n) v T st st' qs qs',
  election_invariant v qs st ->
  fst (election_variant st) = i ->
  proj1_sig (Fin.to_nat (next_id v)) <> (m + (n - i)) mod n ->
  ktrans (sched v, (qs, st)) (T, (qs', st')) -> election_variant st' = election_variant st.
Proof.
  intros.
  destruct st as [? [] ].
  { cbn in H0. destruct H as [(? & ? & ?) _]. cbn in H4. destruct H4 as (? & _ & []). lia. }
  unshelve eapply election_does_progress in H as ?; eauto.
  2: { cbn. cbn in H0. intro. inversion H3. lia. }
  destruct H3 as (? & ? & ?).
  eapply sched_correct_ktrans in H2 as ?; eauto. destruct H4 as (? & ? & ?). subs.
  pose proof (election_elected_proc_states H eq_refl (proj2_sig (Fin.to_nat (next_id v)))).
  apply election_map_proc_state with (Hi := proj2_sig (Fin.to_nat (next_id v))) in H as ?.
  rewrite Fin.of_nat_to_nat_inv in H6.
  destruct H5 as [ [_ ?] | [_ ?] ].
  - (* ProcElected *)
    rewrite H5 in H6. red in H6. destruct H6.
    + rewrite H6 in H4. apply ktrans_ret in H4 as []. inversion H7. now subst.
    + rewrite H6 in H4. apply ktrans_trans in H4 as [(? & ?) | (? & ? & ? & ?)]; inv_trans.
  - destruct H5 as [? | [] ].
    + (* ProcWaiting *)
      rewrite H5 in H6. red in H6. rewrite H6 in H4.
      destruct (List.hd_error (List.nth (proj1_sig (Fin.to_nat (next_id v))) qs []%list)) eqn:?.
      * (* non-empty mailbox *)
        apply ktrans_proc_loop_some_inv with (m := m0) in H4 as (? & -> & ->); auto.
        cbn. f_equal. destruct (_ =? _) eqn:?; auto.
        apply Nat.eqb_eq in Heqb. cbn in Heqb. cbn in H0. subst. rewrite Heqb in H1.
        clear -H1 Hi. exfalso. apply H1. apply Nat.mod_wd; auto. lia.
      * (* empty mailbox *)
        now apply ktrans_proc_loop_none_inv in H4 as (? & -> & ->).
    + (* ProcProcessing *)
      rewrite H5 in H6. red in H6. rewrite H6 in H4.
      eapply election_processing_ext_mailbox in H5; eauto. 2: apply (proj2_sig (Fin.to_nat (next_id v))).
      apply hd_error_in in H5. eapply election_other_messages in H5; eauto.
      2: { cbn in H0 |- *. intro. apply H1. rewrite H7. apply Nat.mod_wd; auto. lia. }
      destruct H5 as (? & ? & ->).
Abort.

End Election.
