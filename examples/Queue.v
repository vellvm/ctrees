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
  Data.Monads.StateMonad.

From Coq Require Import
  Lia
  List.

From ExtLib Require Import RelDec.

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
  Context {S: Type} {HDec: RelDec (@eq S)} {HCor: RelDec_Correct HDec}.
  Infix "=?" := (rel_dec) (at level 75).
  
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

  Definition h_queueE: queueE S ~> stateT (list S) (ctree (writerE S)) :=
    h_writerA
      (* queue semantics *)
      (h_state h_queueE_sem)
      (* queue instrumentation, observe [Pop] results *)
      (fun (e: queueE S) (v: encode e) (_: list S) =>
         match e return encode e -> option S with
         | Pop => fun x: option S => x
         | Push x => fun _ => None
         end v).

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
         AF finishW \v l, v = s /\ l = @nil S )>.
  Proof with eauto with ctl.
    intros.
    apply af_iter_state_list
      with (Ri:=fun '(tt) w l =>
                  not_done w /\
                  match w with
                  | Obs (Log s') tt =>
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
      + destruct Hw, x; cbn in *; inv H.
      + destruct e, v.
        subst.
        rewrite bind_ret_l, bind_guard.
        apply af_guard.
        rewrite interp_state_ret, bind_ret_l.
        cbn.
        rewrite interp_state_ret.
        next; left.
        apply ax_done; split...
        do 2 eexists; intuition.
    - (* l = h :: ts *)
      cbn.
      rewrite bind_trigger, bind_vis.      
      next; right; next; split.
      + apply can_step_vis; intuition.
      + intros t' w' TR.
        apply ktrans_vis in TR as (x & -> & <- & _).        
        rewrite bind_ret_l, bind_guard.
        apply af_guard.
        rewrite interp_state_ret, bind_ret_l.
        cbn.
        rewrite interp_state_ret.
        next; left.
        apply ax_done; cbn; destruct x; intuition. 
        inv Hd.
        * destruct Hw as [[|h' ts'] Hw];
            apply list_app_cons in Hw as (-> & ->); cbn; auto.
          destruct ts'; cbn; intuition.
          -- now (exists nil).
          -- now (exists (s0 :: ts')).
        * destruct e, v, Hw; apply list_app_cons in H; destruct x, H; subst; cbn; auto.
          destruct x; cbn; intuition.
          -- now (exists nil).
          -- now (exists (s2 :: x)).
  Qed.       

  Record ghostS :=
   mkGhost {
      elem : S;
      dist : nat;
   }.

  Fixpoint index(l: list S)(s: S): option nat :=
    match l with
    | h :: ts =>
        if h =? s then
          Some (List.length ts)
        else
          index ts s
    | nil => None
    end.


  (* Needle to look for *)
  Context (t: S) (f: S) (Htf: f <> t).

  Lemma index_last_S: forall l,
      index (l ++ [f]) t = option_map Datatypes.S (index l t).
  Proof.
    induction l; cbn.
    - eapply rel_dec_neq_false in Htf; eauto.
      now rewrite Htf.
    - destruct (a =? t) eqn:Ha.
      + rewrite app_length; cbn.
        rewrite PeanoNat.Nat.add_1_r.
        reflexivity.
      + apply IHl.
  Qed.

  Definition h_ghostE: queueE S ~> stateT (list S) (ctree (writerE ghostS)) :=
    h_writerA
      (* queue semantics *)
      (h_state h_queueE_sem)
      (* queue instrumentation, observe [Pop] + ghost state *)
      (fun (e: queueE S) (v: encode e) (q: list S) =>
         match e return encode e -> option ghostS with
         | Pop => fun x: option S =>
                   match x with
                   | Some x =>
                       match index q t with
                       | Some i => Some (mkGhost x i)
                       | None => None
                       end
                   | None => None
                   end
         | Push x => fun _ => None                      
         end v).


  Theorem rotate_af_pop: forall q,
      <( {interp_state h_ghostE (rotate f) (q ++ [t])}, Pure |=
           AF finishW \g l,
             g.(elem) = t /\ g.(dist) = 0 /\ Forall (eq f) l )>.
  Proof with eauto with ctl.
    intros.
    apply af_iter_state_list
      with (Ri:=fun '(tt) w l =>
                  not_done w /\
                  match w with
                  | Obs (Log g) tt =>
                      length l = length q /\
                        index l t = Some g.(dist)
                  | _ => length l = length q /\
                          index l t = Some (length l)
                  end); [|eauto with ctl].
    intros [] w l [Hw H'].    
    rewrite interp_state_bind.
    unfold pop, push, trigger.
    rewrite interp_state_vis, bind_bind.
    unfold runStateT, h_queueE; cbn.
    rewrite bind_bind.
    resum.
    rewrite ?bind_ret_l, bind_guard.
    apply af_guard.
    rewrite interp_state_ret, bind_ret_l.
    rewrite interp_state_bind, interp_state_vis.
    rewrite bind_bind.
    unfold runStateT; cbn.
    rewrite bind_bind.
    resum.
    rewrite bind_ret_l.
    destruct l as [|h ts]; cbn.
    - (* l = [] *)
      rewrite bind_ret_l, bind_guard.
      apply af_guard.
      rewrite interp_state_ret, bind_ret_l.
      cbn.
      rewrite interp_state_ret.
      next; left.
      apply ax_done.
      intuition.
      inv Hw.
      + destruct H'; cbn in *.
        inv H0.
      + destruct v, e.
        cbn in *.
        destruct H'; inv H0.
    - (* l = h::ts *)
      cbn.
      rewrite index_last_S.
      inv Hw; cbn in H'.
      + destruct H'.
        destruct (h =? t) eqn:Hh.
        * inv H0; lia.
        * rewrite H0; cbn.
          rewrite bind_trigger, bind_vis.
          next; right.
          next; split.
          -- apply can_step_vis...
          -- intros t' w' TR.
             apply ktrans_vis in TR as ([] & -> & <- & _).
             rewrite bind_ret_l, bind_guard, af_guard,
               interp_state_ret, bind_ret_l. 
             cbn.
             rewrite interp_state_ret.
  Admitted.
End QueueEx.
  
