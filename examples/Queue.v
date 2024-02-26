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
  Lia
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

  (* Queue semantics *)
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

  Variant qview :=
    | QPop (h: S)
    | QPush (h: S).

  Definition h_queueE: queueE S ~> stateT (list S) (ctree (writerE qview)) :=
    h_writerA
      (* queue semantics *)
      (h_state h_queueE_sem)
      (* queue instrumentation *)
      (fun (e: queueE S) (v: encode e) (_: list S) =>
         match e return encode e -> option qview with
         | Pop => fun x: option S => option_map QPop x
         | Push x => fun _ => Some (QPush x)
         end v).

  Lemma list_app_contra: forall (s: S),
      ~ (exists ts : list S, nil = ts ++ [s]).
  Proof.
    intros * Hv; destruct Hv, x; cbn in *; inv H.
  Qed.

  Lemma list_app_cons: forall (h s: S) ts hs,
      h :: ts = hs ++ [s] ->
      match hs with
      | nil => h = s /\ ts = nil
      | h' :: ts' => h = h' /\ ts = ts' ++ [s]
      end.  
  Proof. destruct hs; intros; cbn in *; inv H; auto. Qed.
  
  (*| Eventually we get [s] |*)
  Typeclasses Transparent equ.
  Opaque entailsF.
  Theorem drain_af_pop: forall (s: S) q,
      <( {interp_state h_queueE drain (q ++ [s])}, Pure |=
         AF finishW \v l, v = QPop s /\ l = @nil S )>.
  Proof.
    intros.
    apply af_iter_state_list
      with (Ri:=fun '(tt) w l =>
                  not_done w /\
                  match w with
                  | Obs (Log (QPop s')) tt =>
                      match l with
                      | nil => s = s'
                      | h :: ts => exists hs, h:: ts = hs ++ [s]
                      end
                  | _ => exists hs, l = hs ++ [s]
                  end); [|eauto with ctl].
    intros [] w l Hw.    
    rewrite interp_state_bind.
    unfold pop, trigger.
    rewrite interp_state_vis, bind_bind.
    unfold runStateT, h_queueE; cbn.
    rewrite bind_bind.
    resum.
    rewrite bind_ret_l. 
    destruct l as [|h ts], Hw as [Hd Hw].
    - (* l = [] *)
      inv Hd; cbn.
      + now apply list_app_contra in Hw.
      + rewrite bind_ret_l, bind_tau.
        apply af_tau.
        rewrite interp_state_ret, bind_ret_l.
        cbn.
        rewrite interp_state_ret.
        next; left.
        apply ax_finish.
        do 2 eexists; intuition.
        destruct e, v, q0; subst; auto.
        now apply list_app_contra in Hw.
    - (* l = h :: ts *)
      cbn.
      rewrite bind_trigger, bind_vis.      
      next; right; next; split.
      + apply can_step_vis; intuition.
      + intros t' w' TR.
        apply ktrans_vis in TR as (x & -> & <- & _).        
        rewrite bind_ret_l, bind_tau.
        apply af_tau.
        rewrite interp_state_ret, bind_ret_l.
        cbn.
        rewrite interp_state_ret.
        next; left.
        apply ax_finish; cbn; destruct x; intuition. 
        inv Hd.
        * destruct Hw as [[|h' ts'] Hw];
            apply list_app_cons in Hw as (-> & ->); cbn.
          -- auto.
          -- destruct ts'; cbn; intuition.
             ++ now (exists nil).
             ++ now (exists (s0 :: ts')).
        * destruct e, q0, v, Hw; apply list_app_cons in H; destruct x, H; subst; cbn; auto.
          all: destruct x; cbn; intuition; [now (exists nil) | now (exists (s1 :: x))].
  Qed.       


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
  
