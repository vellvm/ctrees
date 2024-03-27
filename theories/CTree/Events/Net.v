From CTree Require Import
  Utils.Vectors
  CTree.Core.

From CTree Require Export
  CTree.Core
  Events.Core
  Events.WriterE
  Events.NetE.

From Equations Require Import Equations.

Import CTreeNotations.
Local Open Scope ctree_scope.
Local Open Scope fin_vector_scope.

Definition send {n T}: fin' n -> T -> ctree (netE n T) unit :=
  fun i p => Ctree.trigger (Send i p).

Definition recv {n T}: ctree (netE n T) (option T) :=
  Ctree.trigger (@Recv n T).

Module MessageOrderScheduler.
  (* Round-robbin Scheduler for infinite ctrees, based on message passing.
   1. Pick non-deterministically an [i: fin n], schedule process [i].
   2. When [i] sends a message to [j], deliver message and schedule [j] next.
   3. Repeat (2).
   *)
  Record Task (n: nat) (T: Type) :=
    {
      prog: ctree (netE n T) void;
      mail: option T
    }.
  Arguments prog {n} {T}.
  Arguments mail {n} {T}.

  Definition task_new {n T}(p: ctree (netE n T) void) :=
    {| prog := p; mail := None |}.
  
  Definition uprog{n T}(p: ctree (netE n T) void)(t: Task n T) :=
    {| prog := p; mail := t.(mail) |}.

  Definition umail{n T}(mail: option T) (t: Task n T) :=
    {| prog := t.(prog); mail := mail |}.

  Notation sys n T := (vec' n (Task n T)).

  (* n: Number of processes
   T: Message payload type
   W: Observation domain *)
  Section ScheduleMsg.
    Context {n: nat} {T W: Type} (fobs: bool -> fin' n -> option T -> option W).
    Notation logE := (writerE W).

    Equations schedule_one' (R: fin' n -> sys n T -> ctree logE void)
      (r: fin' n) (system: sys n T) : ctree logE void :=
      
      schedule_one' R r system with observe (prog (system $ r)) => {
          (** A non-deterministic choice, traverse it *)
          schedule_one' _ _ _ (BrF n' k) :=
            Br n' (fun i => R r (system @ r do uprog (k i)));

          (** A guard, traverse it *)
          schedule_one' _ _ _ (GuardF t') :=
            Guard (R r (system @ r do uprog t'));
          
          (** A network `send` effect, interpet it and context switch *)
          schedule_one' _ _ _ (VisF (Send to m) k) :=
            match fobs true to (Some m) with
            | Some obs =>      
                Vis (Log obs) (fun _: unit =>
                                 R to (system
                                         @ r do (uprog (k tt))
                                                  @ to do (umail (Some m))))
            | None => R to (system
                             @ r do (uprog (k tt))
                                      @ to do (umail (Some m)))
            end;
          
          (** Receive a message *)
          schedule_one' _ _ _ (VisF Recv k) :=
            let m := mail (system $ r) in
            match fobs false r m with
            | Some obs =>          
                Vis (Log obs) (fun _: unit =>
                                 R r (system @ r do (fun t => umail None (uprog (k m) t))))
            | None => R r
                       (system @ r do (fun t => umail None (uprog (k m) t)))
            end;
          schedule_one' _ _ _ (RetF x) :=
            i <- Ctree.unless (Fin.eq_dec r) ;; (* Pick any other [i] *)
            R i system
        }.    

    CoFixpoint schedule_one(r: fin' n)(system: sys n T) :=
      Guard (schedule_one' schedule_one r system).

    (* Nondeterministic pick which process to start first *)
    Definition schedule(system: sys n T) :=
      r <- Ctree.branch n ;;
      schedule_one r system.

  End ScheduleMsg.
End MessageOrderScheduler.
