From Coq Require Import
     Fin
     Nat
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
     Core.Utils.

From ExtLib Require Import
     Monad.

From Coinduction Require Import
     coinduction rel tactics.

From DSL Require Import
     Vectors
     Lists
     Utils
     Storage
     Log
     System.

Import MonadNotation ListNotations EquNotations SBisimNotations Log.
Local Open Scope monad_scope.
Local Open Scope fin_vector_scope.


Set Implicit Arguments.

Module Network(S: Systems).
  Module StorageM := Storage(S).
  Import StorageM S.

  Section ParametricN.
    Variable (n: nat).

    (** Messages exchagend *)
    Record req := {
        principal: uid n;
        payload: msg;
      }.

    (** A queue of messages *)
    Definition queue := list req.

    (** Network effects *)
    Inductive Net: Type -> Type :=
    | Recv: Net (option req)
    | Send : req -> Net unit
    | Broadcast: msg -> Net unit.
    
    (** A task is either running or returned *)
    Inductive Task (E: Type -> Type) :=
    | Running (c: ctree E void)(q: queue)
    | Blocked (k: option req -> ctree E void).
    (** this is a "soft" blocked -- the scheduler can pass it "None"
        which corresponds to a timeout, and it will unblock *)

  End ParametricN.

  Arguments Running {n} {E}.
  Arguments Blocked {n} {E}.
  Arguments Send {n}.
  Arguments Recv {n}.
  Arguments Broadcast {n}.

  Definition recv {n E} `{Net n -< E}: ctree E (option (req n)) := trigger Recv.
  Definition send {n E} `{Net n -< E}: uid n -> msg -> ctree E unit :=
    fun u p => trigger (Send {| principal := u; payload := p |}).
  Definition broadcast {n E} `{Net n -< E}: msg -> ctree E unit :=
    fun bs => trigger (Broadcast bs).

  (** A process running forever *)
  Notation daemon t := (@CTree.forever _ _ void t).
  
  Notation Sys n E := (vec n (Task n E)) (only parsing).

  (** Unfair but general scheduler *)
  Equations schedule_one{E: Type -> Type}{n: nat}
            (schedule: Sys n (Net n +' E) -> ctree E void)
            (sys: Sys n (Net n +' E)) (r: fin n): ctree E void :=
    schedule_one schedule sys r with sys $ r => {
        schedule_one _ _ _ (Running a q) with observe a => {
          (** A previous choice, traverse it *)
          schedule_one _ _ _ _ (BrF b n' k) :=
          Br b n' (fun i' => schedule (sys @ r := Running (k i') q));
          
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

  Import CTree.
  CoFixpoint schedule{E}{n: nat}(sys: Sys n (Net n +' E)): ctree E void :=
    r <- br true n ;;
    schedule_one schedule sys r.

  (** Fair scheduler *)
  CoFixpoint schedule_fair'{E}{n: nat}(picked: list (fin n))(sys: Sys n (Net n +' E)): ctree E void :=
    if (length picked =? n) then
      r <- br true n;;
      schedule_one (schedule_fair' [r]) sys r
    else
      r <- CTree.iter (fun _: unit =>                  
                        r <- br true n ;;
                        if (in_dec Fin.eq_dec r picked) then  
                          ret (inl tt)
                        else
                          ret (inr r)) tt;;
      schedule_one (schedule_fair' (r :: picked)) sys r.

  Notation schedule_fair := (schedule_fair' []%list) (only parsing).
                                                              
  Transparent schedule.
  Transparent schedule_fair'.
  Transparent schedule_one.
  Transparent vector_replace.

  Lemma unfold_schedule{E}{n: nat}(sys: Sys n (Net n +' E)) :
    schedule sys ≅ (r <- br true n ;; schedule_one schedule sys r).
  Proof.
    __step_equ; cbn; econstructor; reflexivity.
  Qed.    

  Import VectorNotations.
  Lemma unfold_schedule_fair{E}{n: nat}(sys: Sys n (Net n +' E)):
    n = 0 \/
      exists (r: fin n) (l: list (fin n)),
        schedule_fair sys ≅ schedule_one (schedule_fair' (r :: l)) sys r.
  Proof.    
    induction n. 
    - left; reflexivity.
    - right.
      unfold schedule_one.

      unfold schedule_fair'; cbn.
      destruct (inversion_Sn sys) as [h  [ts H]]; subst.
      exists F1.

      cbn.
      coinduction ? CIH.
    - rewrite (inversion_0 sys); cbn*.
      simp schedule_one; cbn.
      
      cbn.
      econstructor.
    unfold schedule_fair'; cbn.
    simp schedule_one.
    cbn.
  (** Evaluates Net *)
  Program Definition run_network{E n} (s: vec n (ctree (Net n +' E) void)): ctree E void :=
    schedule (Vector.map (fun it => Running it List.nil) s).

  
  #[global] Instance sbisim_network_goal{n E}:
    Proper (pairwise sbisim ==> sbisim) (@run_network E n).
  Proof.
    unfold Proper, pairwise, respectful.
    unfold sbisim.
    coinduction ? CIH.
    intros x y FORALL.
    unfold run_network.

  Admitted.

  (** ================================================================================ *)
  (** This is the top-level denotation of a distributed system to a ctree of behaviors *)
  Program Definition run_storage_network{n}(v: vec n (ctree (Storage +' Net n) void)): heap -> ctree (logE heap) void :=
    fun st: heap => run_network (Vector.map swap (run_states_log v st)).
End Network.

