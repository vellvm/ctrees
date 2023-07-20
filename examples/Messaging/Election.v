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

Definition ids_wf n (ids : list nat) :=
  length ids = n /\
  forall j k, j <> k -> List.nth j ids 0 <> List.nth k ids 0.

Definition max_id n ids (wf : ids_wf n ids) : nat.
Admitted.

Lemma max_id_correct : forall n ids (wf : ids_wf n ids),
  max_id wf < n /\ forall k, k <> max_id wf -> List.nth k ids 0 < List.nth (max_id wf) ids 0.
Admitted.

Section Election.

Context {n : nat} (Hn : n <> 0) (ids : list nat) (ids_wf : ids_wf n ids).

Let im := max_id ids_wf.
Let pid i := List.nth i ids 0.
Let max := pid im.

Lemma pid_inj : forall i j (Hi : i < n) (Hj : j < n), pid i = pid j -> i = j.
Proof.
Admitted.

Variant message :=
  | Candidate (u: nat)
  | Elected (u: nat).

(* TODO use ids *)
Definition proc_handle_msg (i: uid)(right: uid) (m: option message): ctree (netE message) B01 (unit + unit) :=
       match m with
       | Some (Candidate candidate) =>
           match Nat.compare candidate (pid i) with (* candidate < id *)
           (* My [left] neighbor proposed a candidate, I support that candidate *)
           | Gt => send i right (Candidate candidate) ;; Ret (inl tt)
           (* My left neighbor proposed a candidate, I do not support him *)
           | Lt => Ret (inl tt)
           (* I am the leader, but only I know *)
           | Datatypes.Eq => send i right (Elected (pid i)) ;; Ret (inr tt)
           end
       | Some (Elected x) =>
           (* I know [x] is the leader *)
           send i right (Elected x) ;; Ret (inr tt)
       | None => Ret (inl tt) (* Didn't receive anything *)
       end.

Definition proc_loop (i: uid)(right: uid): ctree (netE message) B01 unit :=
  CTree.iter
    (fun _ =>
       m <- recv i;;
       proc_handle_msg i right m) tt.

Definition proc_loop_handle_msg (i: uid)(right: uid) (m: option message): ctree (netE message) B01 unit :=
  lr <- proc_handle_msg i right m;;
  match lr with
  | inl l => Guard (proc_loop i right)
  | inr r => Ret r
  end.

(* send from to msg *)
(* Before: Switch_to i ~> event modelling that process i is being scheduled
   This is currently removed
 *)
(*| Client process |*)
Definition proc (i: uid)(right: nat): ctree (netE message) B01 unit :=
  (* 1. Send my [id] to the process on the right *)
  send i right (Candidate (pid i));;
  (* 2. Loop until we know the leader *)
  proc_loop i right.

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

Definition from_to (i j : nat) : nat -> Prop :=
  fun k =>
    (i <= j -> i <= k < j) /\
    (j < i -> i <= k < n \/ 0 <= k < j).

Lemma from_to_bound : forall (i j k : nat) (Hi: i < n) (Hj: j < n), from_to i j k ->
  k < n.
Proof.
  intros. destruct H. lia.
Qed.

Lemma from_to_dec_ : forall (i j k : nat), { i <= j < k } + { ~i <= j < k }.
Proof.
  intros.
  destruct (Compare_dec.le_dec i j).
  2: tauto.
  destruct (Compare_dec.lt_dec j k); tauto.
Qed.

Lemma from_to_dec : forall (i j k : nat), { from_to i j k } + { ~from_to i j k }.
Proof.
  intros. unfold from_to.
  destruct (Compare_dec.le_lt_dec i j).
  - destruct (from_to_dec_ i k j); [| tauto].
    left. split; [tauto | lia].
  - destruct (from_to_dec_ i k n); [left; lia |].
    destruct (from_to_dec_ 0 k j); [left; lia |].
    right. lia.
Qed.

Definition next_proc_and_msg st :=
  match st.(s_progress) with
  | MaxCandidate d => ((im + d) mod n, Candidate max)
  | MaxElected d => ((im + d + 1) mod n, Elected max)
  end.

Definition noop_msg i msg :=
  match msg with
  | Candidate c => Nat.ltb c (pid i)
  | Elected e => false
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
  let next := next_proc st in
  match e with
  | Send i to msg =>
    let p := nth_map (fun _ => ProcWaiting) st.(s_procs) i in
    let pe := nth_map (fun _ => ProcElected) st.(s_procs) i in
    let q := if Nat.eqb i next then handle_send qs st i st.(s_queue) else st.(s_queue) in
    match st.(s_progress), msg with
    | MaxCandidate d, Candidate c =>
      let progress := if Nat.eqb c max then MaxCandidate (S d) else st.(s_progress) in
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
    | Some m => if noop_msg i m then ProcWaiting else ProcProcessing m
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
  (forall msg, count_occ eq_dec_message (concat (ext_mailbox qs st)) msg <= 1) /\
  (forall i j, In (Candidate i) (List.nth j (ext_mailbox qs st) []%list) -> exists k, k < n /\ i = List.nth k ids 0) /\
  forall i (Hi : (i < n)%nat),
    match List.nth i procs ProcBegin with
    | ProcBegin => ~ In (Candidate i) (concat (ext_mailbox qs st))
    | _ =>
      (* A losing candidate cannot travel beyond the process with the max id *)
      (forall k, k <> im -> In (Candidate (pid i)) (List.nth k (ext_mailbox qs st) []%list) -> from_to ((i + 1) mod n) ((im + 1) mod n) k)
    end.

(* Invariant regarding the position in the mailbox of the current message of interest *)
Definition election_invariant_msg_location
  (st : election_state) (qs: list (list message)) (i: nat) (m: message) :=
  snd st.(s_queue) = match List.nth i st.(s_procs) ProcBegin with ProcProcessing m => true | _ => false end /\
  (forall j k, List.nth_error (List.nth j (ext_mailbox qs st) []%list) k = Some m <->
    j = i /\ k = fst st.(s_queue) - match List.nth i st.(s_procs) ProcBegin with ProcBegin => 1 | _ => 0 end) /\
  match List.nth i st.(s_procs) ProcBegin with ProcBegin => fst st.(s_queue) > 0 | _ => True end.

(* Invariant regarding the max candidate *)
Definition election_invariant_max
  (st : election_state) (qs: list (list message)) :=
  let elected_progress := st.(s_progress) in
  fst st.(s_queue) < n /\
  match elected_progress with
  | MaxCandidate d =>
    (* The leader has not been elected yet *)
    (forall c k, ~In (Elected c) (List.nth k (ext_mailbox qs st) []%list)) /\
    {Hd : d <= n |
      (* The message can only be in the mailbox at distance d from the max *)
      (d <> 0 -> election_invariant_msg_location st qs ((im + d) mod n) (Candidate max)) /\
      (d = 0 -> ~In (Candidate max) (concat (ext_mailbox qs st)))
    }
  | MaxElected elected_progress =>
    {He : elected_progress < n |
      let e' := Fin.of_nat_lt He in
      let j := (im + elected_progress + 1) mod n in
      (* There are no (Candidate max) messages left *)
      (forall k, ~ In (Candidate max) (List.nth k (ext_mailbox qs st) []%list)) /\
      (* There can only be one elected message *)
      election_invariant_msg_location st qs j (Elected max) /\
      forall c k, c <> max -> ~In (Elected c) (List.nth k (ext_mailbox qs st) []%list)
    }
  end.

Definition election_state_invariant st qs :=
  List.length st.(s_procs) = n /\
  election_invariant_candidates st qs /\
  election_invariant_max st qs.

(* Ties the proc_states to the ctrees *)
Definition election_src_invariant_candidate st i (t : ctree (netE message) B01 unit) :=
  match st with
  | ProcBegin => t ≅ proc i ((i + 1) mod n)
  | ProcWaiting =>
    (t ≅ proc_loop i ((i + 1) mod n))
  | ProcProcessing m => t ≅ proc_loop_handle_msg i ((i + 1) mod n) (Some m) /\ noop_msg i m = false
  | ProcElected => t ≅ Ret tt \/ t ≅ stuckD
  end.

(* Links proc_states and election progress *)
Definition election_src_invariant st (v : vec n (ctree (netE message) B01 unit)) :=
  match st.(s_progress) with
  | MaxCandidate d =>
    (d = 0 <-> nth im st.(s_procs) ProcBegin = ProcBegin) /\
    (forall k, nth k st.(s_procs) ProcBegin <> ProcElected) /\
    (forall k, (from_to im ((im + d) mod n) k \/ d = n) -> nth k st.(s_procs) ProcBegin <> ProcBegin)
  | MaxElected d =>
    forall i (Hi: i < n),
    nth i st.(s_procs) ProcBegin <> ProcBegin /\
    (from_to ((S im) mod n) ((im + d + 1) mod n) i <->
      nth i st.(s_procs) ProcBegin = ProcElected)
  end.

Record election_invariant v qs st :=
{
  wf_queue_len : List.length qs = n;
  wf_procs_len : List.length st.(s_procs) = n;
  wf_candidates : election_invariant_candidates st qs;
  wf_progress : election_invariant_max st qs;
  wf_src_candidates : forall i (Hi : i < n),
    election_src_invariant_candidate (nth i st.(s_procs) ProcBegin) i v[@Fin.of_nat_lt Hi];
  wf_src_progress : election_src_invariant st v
}.

(*Lemma election_candidates_proc_states :
  forall v qs st d,
  election_invariant v qs st ->
  st.(s_progress) = MaxCandidate d ->
  forall i (Hi : i < n),
  (nth i st.(s_procs) ProcBegin = ProcWaiting) \/
  (exists m, nth i st.(s_procs) ProcBegin = ProcProcessing m) \/
  (d <> n /\ ~from_to (im mod n) ((im + d) mod n) i /\
    (nth i st.(s_procs) ProcBegin = ProcBegin)).
Proof.
  intros.
  apply wf_src_progress in H. red in H. rewrite H0 in H.
  destruct (nth i st.(s_procs) ProcBegin) eqn:?.
  - right. right.
  destruct (from_to_dec (S im mod n) ((im + d + 1) mod n) i).
  - left. split; auto.
    now apply H in f.
  - right. split; auto.
    apply H in Hi as [? ?]. apply not_iff_compat in H2. apply H2 in n0.
    destruct (nth i (s_procs st) ProcBegin) eqn:?; eauto with exfalso.
Qed.*)

Lemma election_elected_proc_states :
  forall v qs st d,
  election_invariant v qs st ->
  st.(s_progress) = MaxElected d ->
  forall i (Hi : i < n),
  (from_to ((S im) mod n) ((im + d + 1) mod n) i /\
    nth i st.(s_procs) ProcBegin = ProcElected) \/
  ( ~from_to ((S im) mod n) ((im + d + 1) mod n) i /\
    (nth i st.(s_procs) ProcBegin = ProcWaiting \/
      exists m, nth i st.(s_procs) ProcBegin = ProcProcessing m)).
Proof.
  intros.
  apply wf_src_progress in H. red in H. rewrite H0 in H.
  destruct (from_to_dec (S im mod n) ((im + d + 1) mod n) i).
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
  intros. eapply wf_src_candidates in H. apply H.
Qed.

(*
  Correctness of system is a direct consequence of [election_variant = 0] is reached
 *)
Definition election_variant (st : election_state) : nat * (nat * nat) :=
  match st.(s_progress) with
  | MaxCandidate d => (n + n - d, (fst st.(s_queue), if snd st.(s_queue) then 0 else 1))
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
  forall v qs st msg k,
  election_invariant v qs st ->
  k <> next_proc st ->
  In msg (List.nth k (ext_mailbox qs st) []%list) ->
  exists i, i < n /\ i <> im /\ msg = Candidate (List.nth i ids 0).
Proof.
  intros. destruct H. destruct wf_progress0.
  destruct (s_progress st) eqn:?.
  - (* phase 1 *)
    destruct H2 as (? & ? & ?).
    assert (k < length (ext_mailbox qs st)).
    { eapply nth_not_default. eapply in_not_nil. apply H1. }
    destruct msg.
    2: { exfalso. now apply (H2 u k). }
    destruct wf_candidates0 as (_ & ? & _).
    apply H4 in H1 as ?. destruct H5 as (? & ? & ->).
    exists x0. split; auto. split; auto. intro. subst.
    destruct (nat_eqdec n0 0).
    + apply a in e. apply e.
      apply in_concat. eexists. split; [| apply H1].
      now apply nth_In.
    + apply a in n1. destruct n1 as [_ ?].
      apply In_nth_error in H1 as []. apply H6 in H1 as [-> _].
      unfold next_proc, next_proc_and_msg in H0. rewrite Heqe in H0. contradiction.
  - (* phase 2 *)
    destruct H2 as (? & ? & ?).
    assert (k < length (ext_mailbox qs st)).
    { eapply nth_not_default. eapply in_not_nil. apply H1. }
    destruct msg.
    + destruct wf_candidates0 as (_ & ? & _). apply H5 in H1 as ?. destruct H6 as (? & ? & ->).
      exists x0. split; auto. split; auto. intro. subst.
      now apply H2 in H1.
    + exfalso. destruct (nat_eqdec u max). subst.
      * destruct H3 as [ [_ ?] _].
        apply In_nth_error in H1 as []. apply H3 in H1 as [-> _].
        unfold next_proc, next_proc_and_msg in H0. rewrite Heqe in H0. contradiction.
      * now apply H3 in H1.
Qed.

Lemma election_processing_ext_mailbox :
  forall v qs st i (Hi : i < n) msg,
  election_invariant v qs st ->
  nth i (s_procs st) ProcBegin = ProcProcessing msg ->
  hd_error (nth i (ext_mailbox qs st) []%list) = Some msg.
Proof.
  intros. destruct H.
  specialize (wf_src_candidates0 i Hi). red in wf_src_candidates0. rewrite H0 in wf_src_candidates0.
  change []%list with (ext_mailbox1 ([]%list, ProcBegin)).
  unfold ext_mailbox. rewrite map_nth. unfold ext_mailbox1.
  rewrite combine_nth, H0. reflexivity. now rewrite wf_queue_len0.
Qed.

Lemma hd_error_in : forall {A} (l : list A) a, hd_error l = Some a -> In a l.
Proof.
  intros. destruct l; [discriminate |].
  inversion H. subst. now left.
Qed.

(* ktrans inversion lemmas for leader election processes *)

Lemma ktrans_proc_begin_inv : forall i (Hi : i < n) t' v qs qs' st st' (INV: election_invariant v qs st),
  i <> next_proc st ->
  nth i st.(s_procs) ProcBegin = ProcBegin ->
  ktrans (v[@Fin.of_nat_lt Hi], (qs, st)) (t', (qs', st')) ->
  t' ≅ proc_loop i ((i + 1) mod n) /\
  qs' = nth_map (fun q => (q ++ [Candidate (pid i)])%list) qs ((i + 1) mod n) /\
  st' = mk_election_state
    (nth_map (fun _ => ProcWaiting) st.(s_procs) i)
    st.(s_progress)
    st.(s_queue).
Proof.
  intros. apply election_map_proc_state with (Hi := Hi) in INV as ?.
  red in H2. rewrite H0 in H2.
  unfold proc in H2. setoid_rewrite bind_trigger in H2.
  rewrite H2 in H1. apply ktrans_vis_inv in H1 as (? & ? & -> & ?).
  injection H3 as -> ->.
  split; auto. split; auto.
  destruct st.(s_progress) eqn:?.
  - destruct (Nat.eq_dec i im).
    + subst. rewrite Nat.eqb_refl.
      apply wf_src_progress in INV. red in INV. rewrite Heqe in INV.
      apply (proj1 INV) in H0. subst.
      unfold next_proc, next_proc_and_msg in H. rewrite Heqe in H.
      exfalso. apply H.
      rewrite Nat.mod_small; [| lia]. cbn. lia.
    + apply ids_wf in n1. apply Nat.eqb_neq in H, n1. rewrite H.
      unfold max, pid. rewrite n1. reflexivity. 
  - apply wf_src_progress in INV as ?. red in H3. rewrite Heqe in H3.
    now apply H3 in H0.
Qed.

Lemma ktrans_proc_begin_next_inv : forall i (Hi : i < n) t' v qs qs' st st' (INV: election_invariant v qs st),
  i = next_proc st ->
  nth i st.(s_procs) ProcBegin = ProcBegin ->
  ktrans (v[@Fin.of_nat_lt Hi], (qs, st)) (t', (qs', st')) ->
  t' ≅ proc_loop i ((i + 1) mod n) /\
  qs' = nth_map (fun q => (q ++ [Candidate (pid i)])%list) qs ((i + 1) mod n) /\
  st' = mk_election_state
    (nth_map (fun _ => ProcWaiting) st.(s_procs) i)
    (if pid i =? max then MaxCandidate 1 else st.(s_progress))
    (handle_send qs st i st.(s_queue)).
Proof.
  intros. apply election_map_proc_state with (Hi := Hi) in INV as ?.
  red in H2. rewrite H0 in H2.
  unfold proc in H2. setoid_rewrite bind_trigger in H2.
  rewrite H2 in H1. apply ktrans_vis_inv in H1 as (? & ? & -> & ?).
  injection H3 as -> ->.
  split; auto. split; auto.
  destruct st.(s_progress) eqn:?.
  - destruct (Nat.eq_dec i im).
    + subst. rewrite Nat.eqb_refl.
      apply wf_src_progress in INV. red in INV. rewrite Heqe in INV.
      rewrite e in H0. apply (proj1 INV) in H0. subst. reflexivity.
    + apply ids_wf in n1. apply Nat.eqb_neq in n1.
      unfold max, pid. rewrite n1. subst. rewrite Nat.eqb_refl.
      reflexivity.
  - apply wf_src_progress in INV as ?. red in H3. rewrite Heqe in H3.
    now apply H3 in H0.
Qed.

Lemma ktrans_proc_loop_some_inv : forall i j t' qs qs' st st' m,
  ktrans ((proc_loop i j), (qs, st)) (t', (qs', st')) ->
  List.hd_error (List.nth i qs []%list) = Some m ->
  noop_msg i m = false ->
  t' ≅ proc_loop_handle_msg i j (Some m) /\
  qs' = nth_map (fun _ => tl (List.nth i qs []%list)) qs i /\
  st' = mk_election_state
    (nth_map (fun _ => ProcProcessing m) st.(s_procs) i)
    st.(s_progress)
    (if i =? next_proc st then handle_recv st.(s_queue) else st.(s_queue)).
Proof.
  intros.
  unfold proc_loop in H. rewrite unfold_iter in H.
  rewrite bind_bind in H. setoid_rewrite bind_trigger in H.
  apply ktrans_vis_inv in H as (? & ? & ? & ?).
  cbn in H3. unfold execState in H3. cbn in H2, H3.
  destruct (nth i qs []%list) eqn:?. { discriminate. }
  inv H0.
  inversion H3. cbn. split; [| split; [auto |] ].
  2: now destruct (noop_msg i m).
  cbn in H. unfold proc_loop_handle_msg, proc_handle_msg.
  rewrite H. upto_bind_eq. destruct x1 as [ [] | [] ]; reflexivity.
Qed.

Lemma ktrans_proc_loop_some_noop_inv : forall i j t' qs qs' st st' m,
  ktrans ((proc_loop i j), (qs, st)) (t', (qs', st')) ->
  List.hd_error (List.nth i qs []%list) = Some m ->
  noop_msg i m = true ->
  t' ≅ Guard (proc_loop i j) /\
  qs' = nth_map (fun _ => tl (List.nth i qs []%list)) qs i /\
  st' = mk_election_state
    (nth_map (fun _ => ProcWaiting) st.(s_procs) i)
    st.(s_progress)
    (if i =? next_proc st then handle_recv (s_queue st) else s_queue st).
Proof.
  intros.
  unfold proc_loop in H. rewrite unfold_iter in H.
  rewrite bind_bind in H. setoid_rewrite bind_trigger in H.
  apply ktrans_vis_inv in H as (? & ? & ? & ?).
  cbn in H3. unfold execState in H3. cbn in H2, H3.
  destruct (nth i qs []%list) eqn:?. { discriminate. }
  inv H0.
  inversion H3. cbn. split; [| split; [auto |] ].
  2: now destruct (noop_msg i m).
  unfold noop_msg in H1. destruct m; [| discriminate].
  apply Nat.ltb_lt, Nat.compare_lt_iff in H1.
  cbn in H. unfold proc_loop_handle_msg, proc_handle_msg.
  rewrite H. rewrite H1. rewrite bind_ret_l. reflexivity.
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
  cbn in H1, H2. inv H2. split; auto.
  rewrite H. cbn. rewrite bind_ret_l. now apply br_equ.
Qed.

Definition incr_progress p :=
  match p with
  | MaxCandidate d => MaxCandidate (S d)
  | MaxElected d => MaxElected (S d)
  end.

Lemma proc_handle_msg_equ_inv : forall i (Hi : i < n) j j' msg msg',
  proc_loop_handle_msg i j (Some msg) ≅ proc_loop_handle_msg i j' (Some msg') ->
    (msg = msg' /\ j' = j) \/
    (exists c c', msg = Candidate c /\ msg' = Candidate c' /\ c < pid i /\ c' < pid i) \/
    (msg = Candidate (pid i) /\ msg' = Elected (pid i)) \/
    (msg = Elected (pid i) /\ msg' = Candidate (pid i)).
Proof.
  intros. unfold proc_loop_handle_msg, proc_loop, proc_handle_msg, send in H.
  destruct msg; [destruct (u ?= pid i) eqn:? |]; (destruct msg'; [destruct (u0 ?= pid i) eqn:? |]); try eauto.
  all: try solve [inv_equ].
  - inv_equ. inv EQe. apply Nat.compare_eq_iff in Heqc, Heqc0. subst; eauto.
  - inv_equ. inv EQe. apply Nat.compare_eq_iff in Heqc. subst. eauto.
  - apply Nat.compare_lt_iff in Heqc, Heqc0. eauto 8.
  - inv_equ. inv EQe. eauto.
  - inv_equ. inv EQe. apply Nat.compare_eq_iff in Heqc. subst. eauto.
  - inv_equ. inv EQe. eauto.
Qed.

Lemma proc_handle_msg_inv : forall i (Hi : i < n) j msg v qs st
  (INV: election_invariant v qs st),
  v[@Fin.of_nat_lt Hi] ≅ proc_loop_handle_msg i j (Some msg) ->
  exists msg', List.nth i st.(s_procs) ProcBegin = ProcProcessing msg' /\ (
    (noop_msg i msg' = false /\ msg' = msg) \/
    (exists c c', msg = Candidate c /\ msg' = Candidate c' /\ c < pid i /\ c' < pid i) \/
    (msg = Candidate (pid i) /\ msg' = Elected (pid i)) \/
    (msg = Elected (pid i) /\ msg' = Candidate (pid i))).
Proof.
  intros.
  pose proof INV.(wf_src_candidates). red in H0. specialize (H0 i Hi).
  unfold proc, proc_loop_handle_msg, proc_loop, proc_handle_msg, send, recv in *.
  destruct (nth i (s_procs st) ProcBegin) eqn:?; [| | destruct H0 as [H0 _] | destruct H0]; rewrite H0 in H; clear H0.
  - destruct msg; try solve [inv_equ].
    destruct (u ?= pid i) eqn:?; inv_equ.
    inv EQe. apply Nat.compare_gt_iff in Heqc. lia.
  - rewrite unfold_iter, bind_bind in H. destruct msg; try solve [inv_equ].
    destruct (u ?= pid i) eqn:?; inv_equ.
  - apply proc_handle_msg_equ_inv in H; auto. intuition; eauto 7.
    + eapply wf_src_candidates with (Hi := Hi) in INV. red in INV. rewrite Heqp in INV.
      destruct INV. eauto.
    + destruct H as (? & ? & ? & ? & ? & ?). eauto 10.
  - destruct msg; try solve [inv_equ].
    destruct (u ?= pid i) eqn:?; inv_equ.
  - destruct msg; try solve [inv_equ].
    destruct (u ?= pid i) eqn:?; inv_equ.
Qed.

Lemma election_no_other_elected : forall v qs st (INV: election_invariant v qs st),
  forall i j, j <> max -> ~ In (Elected j) (nth i (ext_mailbox qs st) []%list).
Proof.
  intros. apply wf_progress in INV. red in INV. destruct st.(s_progress).
  - destruct INV as (_ & ? & _). auto.
  - destruct INV as (_ & _ & _ & _ & ?). auto.
Qed.

Lemma proc_handle_msg_candidate_nonmax_inv : forall i (Hi : i < n) j c v qs st
  (INV: election_invariant v qs st),
  i <> im ->
  v[@Fin.of_nat_lt Hi] ≅ proc_loop_handle_msg i j (Some (Candidate c)) ->
  exists msg', List.nth i st.(s_procs) ProcBegin = ProcProcessing msg' /\ (
    (noop_msg i msg' = false /\ msg' = Candidate c) \/
    (exists c', msg' = Candidate c' /\ c < pid i /\ c' < pid i)).
Proof.
  intros. eapply proc_handle_msg_inv in H0; eauto.
  destruct H0 as (? & ? & [ [] | [] ]).
  - eauto.
  - destruct H1 as (? & ? & ? & -> & ? & ?). injection H1 as <-. eauto 7.
  - destruct H1 as [ [? ->] | [] ]; [| discriminate].
    injection H1 as ->.
    eapply election_processing_ext_mailbox in H0; eauto. apply hd_error_in in H0.
    eapply election_no_other_elected in H0; eauto. destruct H0. now apply ids_wf.
Qed.

Lemma ktrans_proc_handle_other_candidate_gt_inv : forall i (Hi : i < n) j c t' v qs qs' st st'
  (INV: election_invariant v qs st)
  (Hvi: v[@Fin.of_nat_lt Hi] ≅ proc_loop_handle_msg i j (Some (Candidate c))),
  ktrans (proc_loop_handle_msg i j (Some (Candidate c)), (qs, st)) (t', (qs', st')) ->
  c > pid i ->
  i <> next_proc st ->
  t' ≅ Guard (proc_loop i j) /\
  qs' = nth_map (fun q => (q ++ [Candidate c])%list) qs j /\
  st' = mk_election_state
    (nth_map (fun _ => ProcWaiting) st.(s_procs) i)
    (if c =? max then incr_progress st.(s_progress) else st.(s_progress))
    st.(s_queue).
Proof.
  intros.
  unfold proc_loop_handle_msg, proc_handle_msg in H.
  apply Nat.compare_gt_iff in H0. rewrite H0 in H.
  rewrite bind_bind in H. setoid_rewrite bind_trigger in H.
  apply ktrans_vis_inv in H as ([] & ? & _ & ?). rewrite bind_ret_l in H. split; auto.
  cbn in H2. unfold execState in H2. cbn in H2.
  injection H2 as ?. subst. split; auto.
  apply Nat.eqb_neq in H1. rewrite !H1.
  eapply proc_handle_msg_inv in Hvi as ?; eauto. destruct H2 as (? & ? & [? | [? | [? | ?] ] ]).
  2: { destruct H3 as (? & ? & ? & ? & ?). apply Nat.compare_gt_iff in H0. inversion H3. lia. }
  2, 3: destruct H3; inversion H3; apply Nat.compare_gt_iff in H0; lia.
  destruct H3 as (? & ->).
  eapply election_processing_ext_mailbox in H2; eauto. apply hd_error_in in H2.
  apply wf_progress in INV. destruct INV. destruct st.(s_progress) eqn:?; auto.
  destruct (c =? max) eqn:?; auto. apply Nat.eqb_eq in Heqb as ->.
  destruct H5. now apply a in H2.
Qed.

Lemma from_succ_absurd : forall i k, i < n -> k < n -> ~from_to ((k + 1) mod n) i k.
Proof.
  intros * Hi Hk ?. unfold from_to in H. destruct H.
  destruct (Nat.eq_dec k (n - 1)).
  ++rewrite e in *. assert ((n - 1 + 1) = n) by lia. rewrite H1 in *.
    rewrite Nat.Div0.mod_same in *.
    pose proof (Nat.mod_upper_bound (im + 1) n). lia.
  ++assert (k + 1 < n) by lia. apply Nat.mod_small in H1. rewrite H1 in *. lia.
Qed.

Lemma nth_neq : forall {A} (l : list A) i j d,
  nth i l d <> nth j l d -> i <> j.
Proof.
  intros * ? ?. now subst.
Qed.

Lemma next_proc_bound : forall st, next_proc st < n.
Proof.
  intros. unfold next_proc, next_proc_and_msg.
  destruct st.(s_progress); now apply Nat.mod_upper_bound.
Qed.

Lemma proc_begin_empty_queue : forall v qs st (INV : election_invariant v qs st),
  nth (next_proc st) st.(s_procs) ProcBegin = ProcBegin ->
  fst st.(s_queue) = 0 ->
  next_proc st = im.
Proof.
  intros.
  pose proof INV.(wf_progress) as [_ ?].
  pose proof INV.(wf_src_progress). red in H2.
  unfold next_proc, next_proc_and_msg.
  destruct st.(s_progress) eqn:?.
  2: { apply H2 in H; [easy |]. apply next_proc_bound. }
  destruct H1 as (_ & ? & ? & ?).
  destruct (Nat.eq_dec n0 0).
  - subst. cbn. rewrite Nat.add_0_r. rewrite Nat.mod_small; [reflexivity |].
    apply max_id_correct.
  - exfalso. clear H3. specialize (H1 n1). destruct H1 as (_ & _ & ?).
    unfold next_proc, next_proc_and_msg in H. rewrite Heqe in H.
    cbn in H. rewrite H in H1. lia.
Qed.

Lemma nth_error_hd_error : forall {A} (l : list A), nth_error l 0 = hd_error l.
Proof.
  intros. now destruct l.
Qed.

Lemma next_msg_begin : forall v qs st (INV : election_invariant v qs st),
  fst st.(s_queue) = 0 ->
  st.(s_progress) = MaxCandidate 0 ->
  List.nth (next_proc st) st.(s_procs) ProcBegin = ProcBegin.
Proof.
  intros.
  pose proof INV.(wf_src_progress). red in H1.
  unfold next_proc, next_proc_and_msg. rewrite H0 in H1 |- *.
  assert ((im + 0) mod n = im). { rewrite Nat.add_0_r. apply Nat.mod_small. apply max_id_correct. }
  rewrite H2. now apply H1.
Qed.

Lemma next_msg_head : forall v qs st (INV : election_invariant v qs st),
  fst st.(s_queue) = 0 ->
  st.(s_progress) <> MaxCandidate 0 ->
  hd_error (List.nth (next_proc st) (ext_mailbox qs st) []%list) = Some (snd (next_proc_and_msg st)).
Proof.
  intros.
  pose proof INV.(wf_progress). red in H1.
  unfold next_proc, next_proc_and_msg in H.
  destruct st.(s_progress) eqn:?.
  - destruct H1 as (_ & _ & _ & ? & _).
    assert (n0 <> 0). { intro. subst. now apply H0. }
    specialize (H1 H2). destruct H1 as (? & ? & ?).
    specialize (H3 ((im + n0) mod n) (fst st.(s_queue))).
    lapply (proj2 H3).
    2: {
      split; auto.
      destruct (nth ((im + n0) mod n) (s_procs st) ProcBegin) eqn:?; lia.
    }
    clear H3. intro. rewrite H in H3. rewrite nth_error_hd_error in H3.
    unfold next_proc, next_proc_and_msg. now rewrite Heqe.
  - destruct H1 as (_ & _ & _ & ? & _).
    destruct H1 as (? & ? & ?).
    specialize (H2 ((im + n0 + 1) mod n) (fst (s_queue st))).
    lapply (proj2 H2).
    2: {
      split; auto.
      destruct (nth ((im + n0 + 1) mod n) (s_procs st) ProcBegin) eqn:?; lia.
    }
    clear H2. intro. rewrite H in H2. rewrite nth_error_hd_error in H2.
    unfold next_proc, next_proc_and_msg. now rewrite Heqe.
Qed.

Theorem election_dec_candidates :
  forall i (Hi : i <> 0 /\ i <= n) v T st st' qs qs',
  election_invariant v qs st ->
  fst (election_variant st) = n + i ->
  proj1_sig (Fin.to_nat (next_id v)) = (im + (n - i)) mod n ->
  ktrans (sched v, (qs, st)) (T, (qs', st')) -> lt_election_variant (election_variant st') (election_variant st).
Proof.
  intros.
  destruct st as [? [] ]; cbn in H0.
  2: { destruct H. destruct wf_progress0 as (_ & _ & [? _]). lia. }
  assert (n0 = n - i) by lia. subst. clear H0.
  unshelve eapply election_does_progress in H as ?; eauto.
  2: { cbn. intro. injection H0 as ?. lia. }
  destruct H0 as (? & ? & ?).
  eapply sched_correct_ktrans in H2 as ?; eauto. destruct H3 as (? & ? & ?). subs.
  apply election_map_proc_state with (Hi := proj2_sig (Fin.to_nat (next_id v))) in H as ?. red in H4. cbn in H4.
  destruct (nth (proj1_sig (Fin.to_nat (next_id v))) s_procs0 ProcBegin) eqn:?.
  - (* ProcBegin *)
    eapply ktrans_proc_begin_next_inv with (Hi := proj2_sig (Fin.to_nat (next_id v))) in H as ?.
    3: eauto.
    3: rewrite Fin.of_nat_to_nat_inv; apply H3.
    2: { cbn. rewrite H1. apply Nat.mod_wd; auto. }
    destruct H5 as (? & -> & ->). cbn.
    destruct (pid (proj1_sig (Fin.to_nat (next_id v))) =? max) eqn:?.
    + cbn. apply Nat.eqb_eq in Heqb. apply pid_inj in Heqb; [| apply (proj2_sig (Fin.to_nat _)) | apply max_id_correct].
      rewrite Heqb in Heqp.
      apply wf_src_progress in H. cbn in H. apply (proj1 H) in Heqp. subst. left. lia.
    + apply Nat.eqb_neq in Heqb. apply nth_neq in Heqb.
      right. left. cbn. unfold handle_send.
      destruct (Nat.eq_dec (fst s_queue0) 0).
      * rewrite e in *. exfalso.
        eapply proc_begin_empty_queue in H as ?; auto.
        2: { cbn. now rewrite H1 in Heqp. }
        cbn in H6. rewrite H1 in Heqb. apply Heqb. rewrite <- H6. apply Nat.mod_wd; auto.
      * destruct (fst s_queue0) eqn:?; [easy |].
        cbn. lia.
  - (* ProcWaiting *)
    rewrite Fin.of_nat_to_nat_inv in H4. rewrite H4 in H3.
    destruct (List.hd_error (List.nth (proj1_sig (Fin.to_nat (next_id v))) qs []%list)) eqn:?.
    (* empty mailbox *)
    2: {
      apply ktrans_proc_loop_none_inv in H3 as (? & -> & ->); auto.
      exfalso.
    }
    (* non-empty mailbox *)
    destruct (noop_msg (proj1_sig (Fin.to_nat (next_id v))) m) eqn:?.
    + apply ktrans_proc_loop_some_noop_inv with (m := m) in H3 as (? & -> & ->); auto.
      cbn. right.
      rewrite ((proj2 (Nat.eqb_eq _ _)) H1).
      unfold handle_recv. cbn.
      destruct (snd s_queue0). 2: right; left.
      left.
      apply wf_progress in H as ?. destruct H5 as [_ ?]. cbn in H5. destruct H5 as (_ & _ & ? & ?).
      destruct (Nat.eq_dec (n - i) 0).
      * assert (n = i) by lia. subst. clear e.
        destruct (Nat.eq_dec (fst s_queue0) 0); [| lia].
        exfalso. apply next_msg_begin in H as ?; auto. 2: cbn; f_equal; lia.
        cbn in H7. assert ((im + (n - n)) = im) by lia.
        rewrite <- H1 in H7. rewrite H7 in Heqp. discriminate.
      * specialize (H5 n0).
        destruct (Nat.eq_dec (fst s_queue0) 0); [| lia].
        apply next_msg_head in H as ?; auto.
        2: { intro. now injection H7. }
        cbn in H7. unfold ext_mailbox in H7. cbn in H7.
        change []%list with (ext_mailbox1 ([]%list, ProcBegin)) in H7. rewrite map_nth in H7.
        unfold ext_mailbox1 in H7. rewrite combine_nth in H7.
        2: { rewrite H.(wf_queue_len). now setoid_rewrite H.(wf_procs_len). }
        rewrite <- H1, Heqp, Heqo in H7. injection H7 as ->.
        unfold noop_msg in Heqb. apply Nat.ltb_lt in Heqb.
        pose proof max_id_correct as [_ ?].
        destruct (Nat.eq_dec (proj1_sig (Fin.to_nat (next_id v))) im).
        --rewrite e0 in Heqb. unfold max in Heqb. lia.
        --apply H7 in n1. unfold max, pid, im in Heqb. lia.
    + apply ktrans_proc_loop_some_inv with (m := m) in H3 as (? & -> & ->); auto.
      cbn. right. rewrite H1, Nat.eqb_refl.
      unfold handle_recv. cbn.
      destruct (snd s_queue0). 2: right; left.
      left. destruct (Nat.eq_dec (fst s_queue0) 0).
      2: destruct (fst s_queue0); lia.
      destruct (Nat.eq_dec i n).
      * subst. rewrite Nat.sub_diag in *.
        apply wf_src_progress in H as ?. cbn in H5.
        rewrite H1, Nat.add_0_r, Nat.mod_small in Heqp; [| apply max_id_correct].
        now rewrite (proj1 (proj1 H5)) in Heqp.
      * apply next_msg_head in H as ?; auto.
        2: { cbn. intro. injection H5. lia. }
        cbn in H5.
Abort.

(* Stability of variant when an uninteresting process is scheduled *)
(* FIXME the ProcWaiting and ProcProcessing cases are duplicated. *)
Theorem election_cst_candidates :
  forall i (Hi : i <> 0 /\ i <= n) v T st st' qs qs',
  election_invariant v qs st ->
  fst (election_variant st) = n + i ->
  proj1_sig (Fin.to_nat (next_id v)) <> (im + (n - i)) mod n ->
  ktrans (sched v, (qs, st)) (T, (qs', st')) -> election_variant st' = election_variant st.
Proof.
  intros.
  destruct st as [? [] ]; cbn in H0.
  2: { destruct H. destruct wf_progress0 as (_ & _ & [? _]). lia. }
  unshelve eapply election_does_progress in H as ?; eauto.
  2: { cbn. intro. inversion H3. lia. }
  destruct H3 as (? & ? & ?).
  eapply sched_correct_ktrans in H2 as ?; eauto. destruct H4 as (? & ? & ?). subs.
  apply election_map_proc_state with (Hi := proj2_sig (Fin.to_nat (next_id v))) in H as ?. red in H5. cbn in H5.
  destruct (nth (proj1_sig (Fin.to_nat (next_id v))) s_procs0 ProcBegin) eqn:?.
  - (* ProcBegin *)
    eapply ktrans_proc_begin_inv with (Hi := proj2_sig (Fin.to_nat (next_id v))) in H as ?.
    3: eauto.
    3: rewrite Fin.of_nat_to_nat_inv; apply H4.
    2: { cbn. intro. apply H1. rewrite H6. apply Nat.mod_wd; auto. lia. }
    destruct H6 as (? & -> & ->). cbn. reflexivity.
  - (* ProcWaiting *)
    rewrite Fin.of_nat_to_nat_inv in H5. rewrite H5 in H4.
    destruct (List.hd_error (List.nth (proj1_sig (Fin.to_nat (next_id v))) qs []%list)) eqn:?.
    (* empty mailbox *)
    2: now apply ktrans_proc_loop_none_inv in H4 as (? & -> & ->).
    (* non-empty mailbox *)
    destruct (noop_msg (proj1_sig (Fin.to_nat (next_id v))) m) eqn:?.
    + apply ktrans_proc_loop_some_noop_inv with (m := m) in H4 as (? & -> & ->); auto.
      cbn. f_equal. destruct (_ =? _) eqn:?; auto.
      apply Nat.eqb_eq in Heqb0. cbn in Heqb0. subst. rewrite Heqb0 in H1.
      clear -H0 H1 Hi. exfalso. apply H1. apply Nat.mod_wd; auto. lia.
    + apply ktrans_proc_loop_some_inv with (m := m) in H4 as (? & -> & ->); auto.
      cbn. f_equal. destruct (_ =? _) eqn:?; auto.
      apply Nat.eqb_eq in Heqb0. cbn in Heqb0. cbn in H0. subst. rewrite Heqb0 in H1.
      clear -H0 H1 Hi. exfalso. apply H1. apply Nat.mod_wd; auto. lia.
  - (* ProcProcessing *)
    rewrite Fin.of_nat_to_nat_inv in H5. destruct H5. rewrite H5 in H4.
    eapply election_processing_ext_mailbox in H as ?; eauto. 2: apply (proj2_sig (Fin.to_nat (next_id v))).
    apply hd_error_in in H7. eapply election_other_messages in H7; eauto.
    2: { cbn in H0 |- *. intro. apply H1. rewrite H8. apply Nat.mod_wd; auto. lia. }
    destruct H7 as (? & ? & ? & ->).
    epose proof (H.(wf_src_candidates) (proj2_sig (Fin.to_nat (next_id v)))).
    cbn in H9. rewrite Heqp in H9. red in H9. unfold noop_msg in H9. rewrite Nat.ltb_ge in H9.
    destruct H9. apply Nat.le_lteq in H10 as [].
    + eapply ktrans_proc_handle_other_candidate_gt_inv with (Hi := proj2_sig (Fin.to_nat (next_id v))) in H4 as (? & ? & ->); eauto.
      2: { cbn in H0 |- *. intro. apply H1. rewrite H11. apply Nat.mod_wd; auto. lia. }
      cbn. unfold election_variant.
      cbn. apply ids_wf in H8. apply Nat.eqb_neq in H8.
      unfold max, pid. rewrite H8. reflexivity.
    + apply pid_inj in H10; auto.
      2: apply (proj2_sig (Fin.to_nat (next_id v))).
      exfalso. subst.
      eapply election_processing_ext_mailbox in H as ?; eauto. apply hd_error_in in H10.
      pose proof H.(wf_candidates). destruct H11 as (_ & _ & ?).
      specialize (H11 _ (proj2_sig (Fin.to_nat (next_id v)))).
      eapply proc_handle_msg_candidate_nonmax_inv in H9; eauto.
      destruct H9 as (? & ? & _).
      rewrite H9 in H11. apply H11 in H8 as ?; auto.
      apply from_succ_absurd in H12; auto. now apply Nat.mod_upper_bound.
  - (* ProcElected *)
    apply wf_src_progress in H. cbn in H. now apply H in Heqp.
Qed.

Theorem election_cst_elected :
  forall i (Hi : i <> 0 /\ i < n) v T st st' qs qs',
  election_invariant v qs st ->
  fst (election_variant st) = i ->
  proj1_sig (Fin.to_nat (next_id v)) <> (im + (n - i)) mod n ->
  ktrans (sched v, (qs, st)) (T, (qs', st')) -> election_variant st' = election_variant st.
Proof.
  intros.
  destruct st as [? [] ].
  { cbn in H0. destruct H. destruct wf_progress0 as (_ & _ & [? _]). lia. }
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
      (* empty mailbox *)
      2: now apply ktrans_proc_loop_none_inv in H4 as (? & -> & ->).
      (* non-empty mailbox *)
      destruct (noop_msg (proj1_sig (Fin.to_nat (next_id v))) m) eqn:?.
      * apply ktrans_proc_loop_some_noop_inv with (m := m) in H4 as (? & -> & ->); auto.
        cbn. f_equal. destruct (_ =? _) eqn:?; auto.
        apply Nat.eqb_eq in Heqb0. cbn in Heqb0. cbn in H0. subst. rewrite Heqb0 in H1.
        clear -H1 Hi. exfalso. apply H1. apply Nat.mod_wd; auto. lia.
      * apply ktrans_proc_loop_some_inv with (m := m) in H4 as (? & -> & ->); auto.
        cbn. f_equal. destruct (_ =? _) eqn:?; auto.
        apply Nat.eqb_eq in Heqb0. cbn in Heqb0. cbn in H0. subst. rewrite Heqb0 in H1.
        clear -H1 Hi. exfalso. apply H1. apply Nat.mod_wd; auto. lia.
    + (* ProcProcessing *)
      rewrite H5 in H6. red in H6. destruct H6 as [? _]. rewrite H6 in H4.
      eapply election_processing_ext_mailbox in H5 as ?; eauto. 2: apply (proj2_sig (Fin.to_nat (next_id v))).
      apply hd_error_in in H7. eapply election_other_messages in H7; eauto.
      2: { cbn in H0 |- *. intro. apply H1. rewrite H8. apply Nat.mod_wd; auto. lia. }
      destruct H7 as (? & ? & ? & ->).
      epose proof (H.(wf_src_candidates) (proj2_sig (Fin.to_nat (next_id v)))).
      rewrite H5 in H9. red in H9. unfold noop_msg in H9. rewrite Nat.ltb_ge in H9.
      destruct H9. apply Nat.le_lteq in H10 as [].
      * eapply ktrans_proc_handle_other_candidate_gt_inv with (Hi := proj2_sig (Fin.to_nat (next_id v))) in H4 as (? & ? & ->); eauto.
        2: { cbn in H0 |- *. intro. apply H1. rewrite H11. apply Nat.mod_wd; auto. lia. }
        cbn. unfold election_variant.
        cbn. apply ids_wf in H8. apply Nat.eqb_neq in H8.
        unfold max, pid. rewrite H8. reflexivity.
      * apply pid_inj in H10; auto.
        2: apply (proj2_sig (Fin.to_nat (next_id v))).
        exfalso. subst.
        eapply election_processing_ext_mailbox in H5; eauto. apply hd_error_in in H5.
        pose proof H.(wf_candidates). destruct H0 as (_ & _ & ?).
        specialize (H0 _ (proj2_sig (Fin.to_nat (next_id v)))).
        eapply proc_handle_msg_candidate_nonmax_inv in H9; eauto.
        destruct H9 as (? & ? & _).
        rewrite H9 in H0. apply H0 in H8 as ?; auto.
        apply from_succ_absurd in H10; auto. now apply Nat.mod_upper_bound.
Qed.

End Election.
