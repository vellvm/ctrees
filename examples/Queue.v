From CTree Require Import
  CTree.Core
  Logic.Ctl
  CTree.Equ
  CTree.Logic.Trans
  Logic.Kripke
  CTree.Interp.Core
  CTree.Logic.AF
  CTree.Logic.AX
  CTree.Logic.CanStep
  CTree.Interp.State
  CTree.Events.State
  CTree.Events.Writer.

From ExtLib Require Export
  Structures.MonadState
  Data.Monads.StateMonad
  Structures.Monad.

From Coq Require Import
  List.

Generalizable All Variables.

Import Ctree CTreeNotations CtlNotations ListNotations.
Local Open Scope ctree_scope.
Local Open Scope ctl_scope.
Local Open Scope list_scope.

Variant queueE (S: Type): Type :=
  | Push (s: S)
  | Pop.

Arguments Push {S} s.
Arguments Pop {S}.

Global Instance encode_queueE{S}: Encode (queueE S) :=
    fun e => match e with
          | Push s => unit
          | Pop => option S
          end.

Definition push {S}: S -> ctree (queueE S) unit :=
  fun (s: S) => @Ctree.trigger (queueE S) (queueE S) _ _ (ReSum_refl) (ReSumRet_refl) (Push s).

Definition pop {S}: ctree (queueE S) (option S) :=
  Ctree.trigger Pop.

Arguments push /.
Arguments pop /.

Section QueueEx.
  Context {S: Type}.
  (* Ex1: Drain a queue *)
  Definition drain: ctree (queueE S) unit :=
    iter (fun _ =>
            x <- pop ;;
            match x with
            | Some v => Ret (inl tt) (* keep popping *)
            | None => Ret (inr tt)   (* done *)
            end) tt.

  (* Ex2: Rotate (pop an element, add an element [a]) a queue (a ≠ b) *)
  Definition rotate(a: S): ctree (queueE S) unit :=
    iter (fun _ =>
            push a ;;
            x <- pop ;;
            match x with
            | Some v => Ret (inl tt)
            | None => Ret (inr tt) (* should never return *)
            end) tt.            
      
  Definition h_queueE_sem: queueE S ~> state (list S) := 
    fun e =>
      mkState (fun q =>
                 match e return encode e * list S with
                 | Push v => (tt, q ++ [v])
                 | Pop => match q with
                         | nil => (None, nil)
                         | h :: ts => (Some h, ts)
                         end
                 end).

  Print writerE.
  Variant qview :=
    | QPop (h: option S)
    | QPush (h: option S).
  Definition unbox(q: qview): option S :=
    match q with
    | QPop h => h
    | QPush h => h
    end.
  
  Definition h_queueE: queueE S ~> stateT (list S) (ctree (writerE qview)) :=
    h_writerA
      (* queue semantics *)
      (h_state h_queueE_sem)
      (* queue instrumentation *)
      (fun (e: queueE S) (v: encode e) (_: list S) =>
         match e return encode e -> qview with
         | Pop => fun x: option S => QPop x
         | Push x => fun _ => QPush (Some x)
         end v).

  (*| Eventually we get [s] |*)
  Typeclasses Transparent equ.
  Theorem drain_af_pop: forall (s: S) q,
      <( {interp_state h_queueE drain (q ++ [s])}, Pure |=
         AF finishW {fun '(Log v) 'tt 'tt => v = VPop nil s } )>.
  Proof.
    intros.
    Check af_iter_list'.
    unfold finish_with.
                       
    pose proof (@af_iter_list' (writerE view) _ S unit unit
                  (fun (x : unit) (w : World (writerE view)) =>
                     exists (e : writerE view) (v : encode e),
                       w = Finish e v x /\
                         (let 'Log v0 as x0 := e return (rel (encode x0) unit) in
                          fun 'tt 'tt => v0 = VPop [] s) v
                           x)). 
    apply H.

    cbn.
    Check (finish_with (fun '(Log v) 'tt 'tt => v = VPop nil s)).
      ).
    Check <( |- finish {fun '(Log v) 'tt 'tt => v = VPop nil s })>.
    apply H.
    Opaque entailsF.
    unfold drain.
    revert s.
    induction q; intros. 
    - setoid_rewrite interp_state_unfold_iter.
      eapply af_bind_r_eq.
      + rewrite interp_state_bind.
        rewrite List.app_nil_l.        
        unfold pop, trigger, resum, ReSum_refl.
        rewrite interp_state_vis.
        cbn.
        repeat rewrite bind_bind.
        resum.
        rewrite bind_ret_l.
        rewrite bind_trigger, bind_vis.
        unfold resum, ReSum_refl.
        next; right.
        next; split; eauto with ctl.
        * apply can_step_vis; auto with ctl.
        * intros t' w' TR.
          apply ktrans_vis in TR as (x & -> & Heqt & Hd).
          rewrite bind_ret_l in Heqt.
          rewrite bind_tau in Heqt.
          rewrite <- Heqt.
          next; left.
          apply ax_tau.          
          rewrite interp_state_ret.
          rewrite bind_ret_l.
          cbn.          
          rewrite interp_state_ret.
          apply ax_finish; split; destruct x; eauto.
      + cbn.
        apply af_tau.
        
  Admitted.

  (*
  forever p x |= AF now φ
  ----------------------
  forever p x |= WG WF now φ
   *)
  
  (*| Even though [rotate] does not terminate, we eventually get [a] |*)
  Theorem rotate_af_pop: forall (a b: S) (Hneq: a <> b) q w,
      <( {interp_state instr_queueE (rotate b) (q ++ [a])}, w |=
         AF vis {fun '(Log v) 'tt => exists l, v = VPop l a})>.
  Proof.
    intros.
  Admitted.
End QueueEx.
  
