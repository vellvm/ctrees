From CTree Require Import
  CTree.Core
  Logic.Ctl
  CTree.SBisim
  CTree.Logic.Trans
  Logic.Kripke
  CTree.Interp.Core
  CTree.Logic.Lemmas
  CTree.Interp.State
  CTree.Events.State
  CTree.Events.Writer.

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
  Context {S: Type}.
  Notation queueE := (queueE S).

  (* Drain a queue *)
  Definition drain(s: S): ctree queueE unit :=
    iter (fun _ =>
            x <- pop ;;
            match x with
            | Some v => Ret (inl tt) (* keep popping *)
            | None => Ret (inr tt)   (* done *)
            end) tt.

  Global Instance handler_queueE: queueE ~> state (list S) := {
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

  Definition handlerT_queueE :
    queueE ~> stateT (list S) (ctree (writerE (list S))).
    typeclasses eauto.
  Defined.

  Definition p s := interp_state handlerT_queueE (drain1 s) [].

  (*| Eventually we get [s] |*)
  Theorem ctl_queue_eventually: forall s q,
      <( {(p s, q)} |==
            AF now {fun q => exists ts, q = s :: ts})>.
  Proof.
    intros.
    Opaque entailsF.
    unfold entailsF_lift; simpl fst; simpl snd.
    induction q; simpl ctl_contramap.
    - unfold p, drain1.
      next; right.
      split.
      + apply ctl_now.
        eexists; cbn; eauto.
      + next; split.
        * simpl fst. admit.
        * intros.
          unfold push, trigger in H.
          (* need interp_state_bind *)
          rewrite interp_state_vis in H.
          Search interp_state.
  Admitted.
                
End QueueEx.
  
