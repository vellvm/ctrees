From ITree Require Import
     Basics
     Subevent
     Indexed.Sum.

From Coq Require Import
     Fin.

From ExtLib Require Import
     Monad
     Option.

From Coinduction Require Import
     coinduction rel tactics.

From CTree Require Import
     CTree
     Interp.FoldStateT
     Interp.Log
     Interp.Fold
     Interp.Network
     Logic.Ctl
     Misc.Vectors
     Eq.


From Equations Require Import Equations.

Import CTreeNotations VectorNotations CtlNotations Monads Log Network.

Local Open Scope fin_vector_scope.
Local Open Scope ctree_scope.

Set Implicit Arguments.
Set Maximal Implicit Insertion.
Set Asymmetric Patterns.

(** ================================================================================ *)
(** This is the top-level denotation *)
Program Definition run{n C S} `{B1 -< C} `{B2 -< C} `{Bn -< C}
        (v: vec n (ctree (Net n S +' stateE S) C void)): S -> ctree (frameE n +' logE S) C void :=
  fun st: S => run_network (run_states_log v st).
  
Module Toy.

  Notation Net := (Net 2 nat).
  Notation State := (stateE nat).
  Notation Sys := (vec 2 (ctree (Net +' State))).

  Section ParametricC.
    Context {C: Type -> Type} `{B0 -< C} `{B1 -< C} `{B2 -< C} `{Bn -< C}.

    (*| This is a simple two process  system called [echo/inc].
        - Process [echo] sends its state [n]  and waits to hear back a new
          number [m] from process [inc], stores [m] then repeats forever.
        - Process [inc] waits to hear a number [n], then
          sends back [S n], repeats forever.
    |*)


    Definition echo(them: uid 2): ctree (Net +' State) C void :=
      daemon (
          v <- get ;;
          send them v ;;
          CTree.iter (fun _ =>
                        m <- recv ;;
                        match m with
                        | Some (Build_req id m) =>
                            put m;;
                            ret (inr tt)
                        | None =>
                            ret (inl tt)
                        end) tt
        ).

    Definition inc: ctree (Net +' State) C void :=
      daemon (
          m <- recv ;;
          match m with
          | Some (Build_req id m) =>
              send id (S m);;
              ret tt
          | None =>
              ret tt
          end
        ).
    
    Program Definition a : uid 2 := @of_nat_lt 0 2 _.
    Program Definition b : uid 2 := @of_nat_lt 1 2 _.

    Arguments label: clear implicits.

    (*| A context switch event predicate -- process [m] is scheduled *)
    Variant is_in_frame: uid 2 -> label (frameE 2 +' logE nat) -> Prop :=
      | ProcessEnter: forall m, is_in_frame m (obs (inl1 (Enter m)) tt).

    Variant is_eq: nat -> label (frameE 2 +' logE nat) -> Prop :=
      | IsEqualTo: forall n, is_eq n (obs (inr1 (Log n)) tt).

    (** Pick the nth branch *)
    Ltac take_branch n :=
      match goal with
      | [ |- Logic.ex (fun l => Logic.ex (fun t =>  hrel_of (trans l) (brS (branchn ?m) ?k) t /\ _)) ] => exists tau, (k (n: fin m))
      end;
      split; [econstructor; reflexivity|];
      simp schedule_one;  unfold schedule_one_clause_1_clause_1; cbn;
      simp vector_replace; simpl; fold_subst.

    Ltac take_enter :=
      match goal with
      | [ |- Logic.ex (fun l' => Logic.ex (fun t' => hrel_of (trans l') (enter ?i ;; ?k) _ /\ _)) ] => exists (obs (subevent _ (Enter i)) tt), k
      end.

    Ltac step_ef :=
      rewrite ctl_ef_ex; right; unfold ex.

    Ltac run n :=
      instantiate (1:=n);
      rewrite ctl_ef_ex; right; unfold ex;
      do 2 eexists; split; [eapply trans_trigger|];
      rewrite ctl_ef_ex; right; unfold ex;
      exists tau; eexists;
      simp schedule_one; cbn; simp vector_replace; split; cbn;
      (* For solving the [trans] *)
      [eapply trans_guard; rewrite unfold_schedule; cbn;
       eapply trans_bind_l; [intros Hyp; inv Hyp|];
       eapply trans_brS; rewrite bind_ret_l
      | rewrite bind_ret_l; fold_subst].

     (* Will count to [1] infinitely often *)
    Lemma eventually_counts: forall l,
        let sys := run [echo b; inc]%vector 0 in
        sys, l |= AF (lift (is_eq 1)).
    Proof.
      intros l sys.
      (* AF (is_eq 1) sys l *)
      rewrite ctl_af_ax.
      right.
      unfold ax.
      intros.
      unfold sys in *.
      unfold run in H3.      
      unfold sys, echo, inc, run, run_network, run_state_log, run_state_log in H3.
      rewrite unfold_schedule in H3.
      (* Hm the [trans_bind_inv] lemma is too verbose
         specifically for infinite programs we know it will 
         always be stepping. *)
      apply trans_bind_inv in H3.
      destruct H3 as [(Hv3 & t0 & TR & ?) | (Hv3 & t'0 & ?)]. 
      apply trans_brS_inv in TR.
      destruct TR as (i & t''eq & ltau).
      subst.
      Search trans.
        (* Step in the scheduler *)
        rewrite unfold_schedule; rewrite bind_branch; cbn.
        (* Step the [EF] and schedule [inc] *)
        step_ef; take_branch b.
        
        (* [inc] is now blocked waiting for a message *)        
        rewrite ctl_ef_ex; right; unfold ex;
          do 2 eexists; split; [eapply trans_trigger|].
        (* Step the [EF] *)
        rewrite ctl_ef_ex; right; unfold ex.
        exists tau; eexists; split.
        eapply trans_guard.
        simp vector_replace; simpl.
        (* schedule *)
        rewrite unfold_schedule; cbn.
        apply trans_bind_l; [intro HV; inv HV |].
        eapply trans_brS.
        rewrite bind_ret_l.        

        run a.
        run a.
        run b.
        run b.
        run a.
        run a.
        run b.
        run b.
        (* Better way to instantiate using Ltac ? *)
        instantiate (1 := a).
        (* Step the [EF] *)
        rewrite ctl_ef_ex; right; unfold ex;
          do 2 eexists; split; [eapply trans_trigger|].
        (* Step the [EF] *)
        rewrite ctl_ef_ex; right; unfold ex.
        exists tau; eexists.
        simp schedule_one; cbn.
        simp vector_replace; simpl; split.
        eapply trans_guard.
        (* Schedule  *)
        rewrite unfold_schedule; cbn.
        apply trans_bind_l; [intro HV; inv HV |].
        eapply trans_brS.
        rewrite bind_ret_l.
        fold_subst.
        
        (* Semi Automated!! *)
        (* Step the [EF] and schedule [a] *)
        instantiate (1:=b);
          rewrite ctl_ef_ex; right; unfold ex;
          do 2 eexists; split; [eapply trans_trigger|];
          rewrite ctl_ef_ex; right; unfold ex;
          exists tau; eexists;
          simp schedule_one; cbn; simp vector_replace; split; cbn;
          (* For solving the [trans] *)
          [eapply trans_guard; rewrite unfold_schedule; cbn;
           eapply trans_bind_l; [intro HV; inv HV|];
           eapply trans_brS; rewrite bind_ret_l
          | rewrite bind_ret_l; fold_subst].
        (* Now continuing...  *)
        
        (* Ah I forgot which process to schedule now... let's do the same *)
         instantiate (1:=b);
          rewrite ctl_ef_ex; right; unfold ex;
          do 2 eexists; split; [eapply trans_trigger|];
          rewrite ctl_ef_ex; right; unfold ex;
          exists tau; eexists;
          simp schedule_one; cbn; simp vector_replace; split; cbn;
          (* For solving the [trans] *)
          [eapply trans_guard; rewrite unfold_schedule; cbn;
           eapply trans_bind_l; [intro HV; inv HV|];
           eapply trans_brS; rewrite bind_ret_l
          | rewrite bind_ret_l; fold_subst].

         (* Schedule [b] now *)
         instantiate (1:=b);
          rewrite ctl_ef_ex; right; unfold ex;
          do 2 eexists; split; [eapply trans_trigger|];
          rewrite ctl_ef_ex; right; unfold ex;
          exists tau; eexists;
          simp schedule_one; cbn; simp vector_replace; split; cbn;
          (* For solving the [trans] *)
          [eapply trans_guard; rewrite unfold_schedule; cbn;
           eapply trans_bind_l; [intro HV; inv HV|];
           eapply trans_brS; rewrite bind_ret_l
          | rewrite bind_ret_l; fold_subst].
                
        instantiate (1:= b). (* ? *)
        do 4 (rewrite ctree_eta; cbn; fold_subst).
        
      }.
    Admitted.

  End ParametricC.
End Toy.

