From Coq Require Import
     Fin
     Nat
     List
     Relations.

From Equations Require Import Equations.

From ITree Require Import
     Indexed.Sum
     Subevent
     CategoryOps.

From CTree Require Import
     CTree
     Equ
     SBisim
     Misc.Vectors
     Core.Utils.

From ExtLib Require Import
     Monad.

From Coinduction Require Import
     coinduction rel tactics.

Import MonadNotation.
Import ListNotations.
Import EquNotations.
Local Open Scope monad_scope.
Local Open Scope fin_vector_scope.

Set Implicit Arguments.

Module Network.

  (*| IP addresses |*)
  Notation uid := fin.
  
  Section Messaging.
    (*| [n] number of processes
        [msg] type of messages |*)
    Context (n: nat) (msg: Set) {E C: Type -> Type} {HasStuck: B0 -< C}.
    
    (*| Messages exchagend |*)
    Record req := {
        principal: uid n;
        payload: msg;
      }.

    (*| A queue of messages |*)
    Definition queue := list req.

    (*| Network effects |*)
    Inductive Net: Type -> Type :=
    | Recv: Net (option req)
    | Send : req -> Net unit
    | Broadcast: msg -> Net unit.
    
    (*| A task is either running or returned |*)
    Inductive Task :=
    | Running (c: ctree E C void)(q: queue)
    (** this is "soft" blocked -- the scheduler can pass it "None"
        which corresponds to a timeout, and it will unblock *)
    | Blocked (k: option req -> ctree E C void).
    
  End Messaging.

  (*| API for messaging processes |*)
  Arguments Running {n} {msg} {E C}.
  Arguments Blocked {n} {msg} {E C}.
  Arguments Send {n} {msg}.
  Arguments Recv {n} {msg}.
  Arguments Broadcast {n} {msg}.
  
  Definition recv {n msg E C} `{Net n msg -< E}: ctree E C (option (req n msg)) := trigger Recv.
  Definition send {n msg E C} `{Net n msg -< E}: uid n -> msg -> ctree E C unit :=
    fun u p => trigger (Send {| principal := u; payload := p |}).
  Definition broadcast {n msg E C} `{Net n msg -< E}: msg -> ctree E C unit :=
    fun bs => trigger (Broadcast bs).

  (*| A process running forever |*)
  Notation daemon t := (@CTree.forever _ _ _ _ void t).

  (*| Contexts -- when a process enters and exits thelet's see how far we go before universe inconsistency |*)
  Inductive frameE(n: nat): Type -> Type :=
  | Enter: uid n -> frameE n unit.

  Arguments Enter {n}.

  Definition enter {n E C} `{frameE n -< E} : uid n -> ctree E C unit :=
    fun u => trigger (Enter u).

  Section Scheduler.
    Context (n: nat) (msg: Set) {E C: Type -> Type} `{B1 -< C} `{B2 -< C} `{Bn -< C}.
    Notation Sys := (vec n (@Task n msg (Net n msg +' E) C)) (only parsing).

    (*| General coinductive scheduler |*)
    Equations schedule_one
              (schedule: Sys -> ctree (frameE n +' E) C void)
              (sys: Sys) (r: uid n): ctree (frameE n +' E) C void :=
      schedule_one schedule sys r with sys $ r => {
          schedule_one _ _ _ (Running a q) with observe a => {
            (** A previous choice, traverse it *)
            schedule_one _ _ _ _ (BrF b c k) :=
            Br b c (fun i' => schedule (sys @ r := Running (k i') q));
            
            (** A network `send` effect, interpet it! *)
            schedule_one _ _ _ _ (VisF (inl1 (Send m)) k) :=
            let msg' := {| principal := r; payload := payload m |} in
            let sys' := sys @ r := Running (k tt) q in
            match sys $ principal m with
            | Running a' q' =>  
                (** Deliver to running *)
                Guard (schedule (sys' @ (principal m) := Running a' (List.cons msg' q')))
            | Blocked kk => 
                (** Deliver to blocked processes and unblock them *)
                Guard (schedule (sys' @ (principal m) := Running (kk (Some msg')) List.nil))
            end;

            (** Receive a message *)
            schedule_one _ _ _ _ (VisF (inl1 Recv) k) :=
            (** Check my inbox q *)
            match last q with
            | Some msg =>
                (** Pop the msg from the end *)
                Guard (schedule (sys @ r := Running (k (Some msg)) (init q)))
            | None =>
                (** Becomes blocked if no messages in q *)
                Guard (schedule (sys @ r := Blocked k))
            end;

            (** Broadcast a message to everyone *)
            schedule_one _ _ _ _ (VisF (inl1 (Broadcast b)) k) :=
            let msg := {| principal := r; payload := b |} in
            let sys' := Vector.map (fun a => match a with
                                          | Running a q => Running a (List.cons msg q)
                                          | Blocked kk => Running (kk (Some msg)) List.nil
                                          end) sys in 
            Guard (schedule (sys' @ r := Running (k tt) q));
            
            (** Some other downstream effect, trigger *)
            schedule_one _ _ _ _ (VisF (inr1 e) k) :=
            Guard (schedule (sys @ r := Running (trigger e >>= k) q))
          };
          (** If the agent is blocked, it could timeout or stay blocked *)
          schedule_one _ _ _ (Blocked k) :=
            brD2
              (schedule (sys @ r := Running (k None) List.nil))  (** Timeout *)
              (schedule (sys @ r := Blocked k));                 (** Keep blocking *)
        }.

    CoFixpoint schedule(sys: Sys): ctree (frameE n +' E) C void :=
      (* Nondterministic pick of a client to run *)
      r <- branch true (branchn n) ;;
      (* Mark context switch *)
      enter r;;
      (* Schedule it *)
      schedule_one schedule sys r.

    (*| Fair scheduler, uses a list of scheduled processes to avoid
      infinitely rescheduling the same process. |*)
    CoFixpoint schedule_fair'(picked: list (fin n))(sys: Sys):
      ctree (frameE n +' E) C void :=
      if (length picked =? n) then
        r <- branch true (branchn n);;
        enter r;;
        schedule_one (schedule_fair' [r]%list) sys r
      else
        r <- CTree.iter (fun _: unit =>                  
                          r <- branch true (branchn n) ;;
                          if (in_dec Fin.eq_dec r picked) then  
                            ret (inl tt)
                          else
                            ret (inr r)) tt;;
        enter r;;
        schedule_one (schedule_fair' (r :: picked)) sys r.

    Notation schedule_fair := (schedule_fair' []%list) (only parsing).
    
    Transparent schedule.
    Transparent schedule_fair'.
    Transparent schedule_one.
    Transparent vector_replace.

    Lemma unfold_schedule(sys: Sys) :
      schedule sys ≅ (r <- branch true (branchn n) ;; enter r;; schedule_one schedule sys r).
    Proof.
      __step_equ; cbn; econstructor; reflexivity.
    Qed.    

    (** Evaluates Net *)
    Program Definition run_network(s: vec n (ctree (Net n msg +' E) C void)):
      ctree (frameE n +' E) C void :=
      schedule (Vector.map (fun it => Running it List.nil) s).
    
    #[global] Instance sbisim_network_goal `{B0 -< C}:
      Proper (pairwise (sbisim eq) ==> sbisim eq) run_network.
    Proof.
      unfold Proper, pairwise, respectful.
      unfold sbisim.
      coinduction ? CIH.
      intros x y FORALL.
      unfold run_network.
      (* TODO: complete *)
    Admitted.

  End Scheduler.
End Network.
