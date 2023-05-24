(** * Examples. *)

Module Termination.

  Section WithVars.

    Variable (E B : Type -> Type) (R : Type).
    Context `{B0 -< B}.
    Variable (obs : Type)
    (upd_e : {x : Type & E x & x} -> obs -> obs)
    (upd_r : {x : Type & x} -> obs -> obs).

    Notation computation := (ctree E B R).

    #[local] Instance K : Kripke :=
      @make_Kripke_of_ctree' _ B R _ obs upd_e upd_r.
    Definition true_fact : factK := fun _ => True.

    Definition is_done : formula := Now (fun s => snd s = Done).
    (* Definition AG_ret_compliant (φ : formula) : formula := *)
    (*   AwG (And φ (Or is_done (alive true_fact))). *)

    Definition never_stuck : formula :=
      AwG (Or is_done (alive true_fact)).

    Definition AG_ret_compliant φ :=
      And never_stuck (AwG φ).

    (* Amusingly, it is not possible to observe directly that we
       are stuck in terms of these observations: we must explain
       how labels update observations, we cannot reason about the
       existence of labels.
       However, we can observe termination, and combine this with
       the meta-level stuck/live formulas.
     *)
    Variant status : Set := | Running | Done.

    Variant upd_status : status -> @label E -> status -> Prop :=
      | upd_val {R} (r : R) s : upd_status s (val r) Done
      | upd_run l s : ~ is_val l -> upd_status s l s.

    #[local] Instance K : Kripke :=
      @make_Kripke_of_ctree _ B R _ _ upd_status.

    (* (* Let's fix a computation so that we have a structure *) *)
    (* Variable c : computation. *)
    (* #[local] Instance K : Kripke := Kripke_status c. *)

    Definition is_done : formula := Now (fun s => s = Done).
    Definition may_terminate : formula := EF is_done.
    Definition always_terminate : formula := AF is_done.

    (* Interestingly, in order to express the absence of crash,
       we need to combine this domain specific observation
       of sound termination to the meta-level (a.k.a. LTL level) notion of
       dead computation *)
    Definition false_fact : factK := fun _ => False.
    Definition no_crash : formula := Impl (dead false_fact) is_done.
    Definition may_crash : formula := EF (And (dead false_fact) (Not is_done)).

    (* LEF: This is not great. Specifically, we can produce [trans l (stuckD) u]
     by taking the [right] path of AF or just having an [AX] -- same thing.
     - We probably don't want this lemma to be true, the simplest form is
     [stuck, s |= AX False].
     *)
    Variable (r: R).
    From Coq Require Import Logic.Eqdep.
    Lemma notgood' s0 : satF (FAF (FNow false_fact)) ((Ret r: ctree E B R), s0).
    Proof.
      red.
      cbn.
      unfold false_fact; cbn.
      right.
      intros.
      simpl.
      unfold transK.
      destruct s'.
      destruct H0 as (? & ? & ?).
      inv H0; inv H1.
      apply inj_pair2 in H4; subst.
      red in s; cbn in s.
      replace  (brDF branch0 k) with (observe (brD branch0 k)) in H5.
      apply observe_equ_eq in H5.
      right; intros.
      destruct s'; unfold transK in H0; cbn in H0.
      destruct H0 as (l & ? & ?).
      rewrite <- H5 in H0.
      unfold trans,transR in H0; cbn in H0; dependent destruction H0; contradiction.
      cbn; reflexivity.
      exfalso.
      apply H0.
      econstructor.
    Qed.
  End WithVars.
End Termination.


Module Scheduling.

  Section WithVars.
    Variable (B : Type -> Type) (R : Type).
    Context `{B0 -< B}.
    (* Let's consider statically two threads identified by a boolean *)
    Variant SchedE : Type -> Type :=
      | Yield         : SchedE unit
      | Sched (b : bool) : SchedE unit.
    Notation computation := (ctree SchedE B R).

    (* Let's keep track of three states *)
    Variant status : Set := | Yielded | Scheduled (b : bool).

    Variant upd_status : status -> @label SchedE -> status -> Prop :=
      | upd_yield b : upd_status (Scheduled b) (obs Yield tt) Yielded
      | upd_sched b : upd_status Yielded (obs (Sched b) tt) (Scheduled b).

    #[local] Instance K : Kripke :=
      @make_Kripke_of_ctree _ B R _ _ upd_status.

    (* Interestingly, the partiality of the upd_status already imposes a form of protocole.
     That is, the generic absence of death of the Kripke structure will prove that the protocole is followed by the computation, that is in this case that yield and schedule events alternate strictly.
     As observed in the previous section, one needs however to be careful that death could happen for computations respecting the protocole: due to internal failure or termination.
     *)
    Definition alternating := never_dead.

    Definition s1 := Now (fun σ => σ = Scheduled true).
    Definition s2 := Now (fun σ => σ = Scheduled false).
    (* Fairness can be expressed in various ways I think. For instance: *)
    Definition fair  : formula := And (AG (Impl s1 (AF s2))) (AG (Impl s2 (AF s1))).
    Definition fair' : formula := And (AG (AF s1)) (AG (AF s2)).

  End WithVars.
End Scheduling.

Module Memory.

  Section WithVars.
    Variable (B : Type -> Type) (R : Type).
    Context `{B0 -< B}.
    (* Let's consider a computation over two memory cells *)
    Variant cellE : Type -> Type :=
      | Wr (b : bool) (n : nat) : cellE unit
      | Rd (b : bool)         : cellE nat.
    Notation computation := (ctree cellE B R).

    (* We could observe the content of the cells *)
    Definition status := (parity * parity)%type.
    Definition status := (nat * nat)%type.
    (* We could "implement" the cells to update the status.
     But crucially, note that we are here describing the effect of labels on
     our observations, we do not govern the computation's control! We hence
     cannot perform the effect of a read in the same sense as the one of the write,
     unless:
     - we extend the domain of observation to keep track of the last (?) value read
     - we first implement the cell as a traditional handler in order to linearize
     the trace, carrying in read events the read values.
     *)
    Variant upd_status : status -> @label cellE -> status -> Prop :=
      | upd_WrL n a b   : upd_status (a,b) (obs (Wr true n) tt) (n,b)
      | upd_WrR n a b   : upd_status (a,b) (obs (Wr false n) tt) (a,n)
      | upd_Rd  f n a b : upd_status (a,b) (obs (Rd f) n) (a,b).
    (* ACTUALLY NOPE!
     We can constrain the Kripke system since the update is a relation
     *)
    Variant upd_status' : status -> @label cellE -> status -> Prop :=
      | upd_WrL' n a b   : upd_status' (a,b) (obs (Wr true n) tt) (n,b)
      | upd_WrR' n a b   : upd_status' (a,b) (obs (Wr false n) tt) (a,n)
      | upd_RdL'  a b    : upd_status' (a,b) (obs (Rd true) a)  (a,b)
      | upd_RdR'  a b    : upd_status' (a,b) (obs (Rd false) b) (a,b).

    #[local] Instance K : Kripke :=
      @make_Kripke_of_ctree _ B R _ _ upd_status.

    (* And we can play silly game, expressing some invariant on the cells... *)
    Definition eventually_empty : formula := AF (Now (fun '(a,b) => a + b = 0)).
    Definition constant_sum n : formula := AG (Now (fun '(a,b) => a + b = n)).

  End WithVars.
End Memory.
