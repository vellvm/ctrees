From CTree Require Import
  CTree.Core
  Logic.Ctl
  CTree.Equ
  CTree.Pred
  CTree.Logic.Trans
  Logic.Kripke
  CTree.Interp.Core
  CTree.Logic.Lemmas
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

Section QueueEx.
  (* Drain a queue *)
  Definition drain{S}: ctree (queueE S) unit :=
    iter (fun _ =>
            x <- pop ;;
            match x with
            | Some v => Ret (inl tt) (* keep popping *)
            | None => Ret (inr tt)   (* done *)
            end) tt.

  Global Instance handler_queueE{S}: queueE S ~> state (list S) := {
      handler e :=
        mkState (fun q =>
                   match e return encode e * list S with
                   | Push v => (tt, q ++ [v])
                   | Pop => match q with
                           | [] => (None, [])
                           | h :: ts => (Some h, ts)
                           end
                   end)
    }.

  Definition instr_queueE{S}: queueE S ~> stateT (list S) (ctree (writerE (Bar (queueE S)))) :=
    h_stateT_writerE _.
  
  Definition pops_s{S}(e: Bar (queueE S))(s: S) :=
    match e with
    | Obs e x =>
        match e return encode e -> Prop with
        | Pop => fun x: option S => x = Some s
        | _ => fun _ => False
        end x
    end.

  (*| Eventually we get [s] |*)
  Theorem ctl_queue_eventually{S}: forall (s: S) q x,
      <( {(interp_state instr_queueE drain (q ++ [s]), x)} |=
         AF now {fun '(Obs (Log e) _) => pops_s e s} )>.
  Proof.
    intros.
    Opaque entailsF.
    unfold drain.
    revert s x.
    induction q; intros. 
    - setoid_rewrite interp_state_unfold_iter.
      apply ctl_bind_af_l.
      setoid_rewrite interp_state_bind.
      apply ctl_bind_af_l.
      unfold pop, trigger.
      rewrite interp_state_vis.      
      cbn.
      setoid_rewrite bind_bind.
      eapply ctl_bind_af_r; [cbn; econstructor|].
      cbn.
      setoid_rewrite bind_trigger.
      eapply ctl_bind_af_l.
      next; right.
      next; split.
      + econstructor. setoid_rewrite ktrans_vis; eauto.
      + intros [t' w'] TR.
        apply ktrans_vis in TR as (? & ? & ?).
        rewrite <- H, H0.
        apply ctl_af_ax; left.
        apply ctl_now; cbn.
        eauto.
    - setoid_rewrite interp_state_unfold_iter.
      setoid_rewrite interp_state_bind.
      setoid_rewrite bind_bind.
      unfold pop, trigger.
      setoid_rewrite interp_state_vis.
      cbn.
      rewrite !bind_bind.
      eapply ctl_bind_af_r; [cbn; econstructor|].
      cbn.
      setoid_rewrite bind_trigger.
      setoid_rewrite bind_vis.
      next; right.
      next; split.
      + cbn; econstructor.
        eexists.
        apply ktrans_vis; eauto.
      + intros [t' w'] TR.
        apply ktrans_vis in TR as (? & ? & ?).
        rewrite <- H, H0; clear H H0.
        rewrite bind_ret_l, bind_guard.
        rewrite <- ctl_guard_af.
        setoid_rewrite interp_state_ret.
        unfold resum_ret, ReSumRet_refl; cbn.
        rewrite bind_ret_l.
        setoid_rewrite interp_state_ret.
        rewrite bind_ret_l.
        rewrite <- !ctl_guard_af.
        apply IHq.
        Unshelve.
        exact tt.
        exact tt.
  Qed.

  (* Rotate a queue of bools (pop/push) *)
  Definition rotate: ctree (queueE bool) unit :=
    forever (fun _ =>
               x <- pop ;;
               if x then
                 push true
               else
                 push false
      ) tt.

  (*
  forever p x |= AF now φ
  ----------------------
  forever p x |= WG WF now φ
   *)
  
  (*| Always eventually we get [true] |*)
  Theorem ctl_rotate_always_eventually: forall (s: bool) q x,
      <( {(interp_state instr_queueE rotate (q ++ [true]), x)} |=
         AG AF now {fun '(Obs (Log e) _) => pops_s e true} )>.
  Proof.
    intros.
    revert s x.
    induction q; intros.
    - unfold rotate.
      setoid_rewrite app_nil_l.
  Admitted.
End QueueEx.
  
