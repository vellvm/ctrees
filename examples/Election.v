From CTree Require Import
  CTree.Core
  Logic.Ctl
  Utils.Vectors
  CTree.Events.Net.

From Coq Require Import
  Fin
  Vector
  Classes.SetoidClass.

Set Implicit Arguments.

Import VectorNotations CTreeNotations CtlNotations MessageOrderScheduler.
Local Close Scope list_scope.
Local Open Scope ctree_scope.
Local Open Scope fin_vector_scope.
Local Open Scope ctl_scope.
Local Open Scope vector_scope.

Section Election.
  Context {n: nat}.
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

  Notation continue := (Ret (inl tt)).
  Notation stop := (Ret (inr tt)).

  (* Always terminates, conditional on receiving either:
     1. (Candidate candidate), where candidate = id -- I received my own [id] back 
     2. (Elected leader) -- Someone else was elected [leader]

    If scheduled fairly, either 1, 2 should always eventually happen.
    Should be WG provable.
  *)
  Definition proc(id: fin' n): ctree netE unit :=
    let right := cycle id in
    send right (Candidate id) ;;
    Ctree.iter
      (fun _ =>
         m <- recv ;;
         match m with
         | Some (Candidate candidate) =>
             match Fin_compare candidate id with (* candidate < id *)
             (* [left] neighbor proposed candidate, support her to [right]. *)
             | Gt => send right (Candidate candidate) ;; continue
             (* [left] neighbor proposed a candidate, do not support her. *)
             | Lt => continue
             (* I am the leader, but only I know. Tell my [right]. *)
             | Eq => send right (Elected id) ;; stop
             end
         | Some (Elected leader) =>
             (* I am a follower and know the [leader] *)
             send right (Elected leader) ;; stop
         | None => continue (* Recv loop *)
         end) tt.

  (* Should be AG provable because each process will spin after completion. *)
  Definition proc_stuck(id: fin' n): ctree netE void :=
    proc id ;; Ctree.stuck.

  (* Should be AG provable because each process will spin after completion. *)
  Definition proc_spin(id: fin' n): ctree netE void :=
    proc id ;; Ctree.spin.

  (* Should be AG provable because every process restarts infinitely often *)
  Definition proc_forever(id: fin' n): ctree netE void :=    
    Ctree.forever void (fun _ => proc id) tt.

  (* TODO: Schedule using [cycle] from [Utils.Vector] *)
  (* Prove AG lemmas *)

  (* Dummy observation; record [is_send] *)
  Definition election_obs(is_send: bool)(i: fin' n)(mail: option message) : option unit :=
    if is_send then Some tt else None.
End Election.

Definition election_s (n: nat) : (sys n message) :=
  Vector.map (fun i => task_new (proc i)) (fin_all_v n).

sschedule election_obs (election_sys n).

  match n with
  | 0 => {| prog := proc_spin (Fin.R n Fin.F1); mail := None |} :: Vector.nil
  | S n' => {| prog := proc_spin i; mail := None |} :: mk_ring (SL i')
    mk_ring Fin.F1 :=
      
    mk_ring (Fin.FS i') :=

  }.
                                              
    match i with
    | Fin.F1 => 
    | Fin.FS i' => 
    end.
End Election.
