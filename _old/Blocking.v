From Coq Require Import
  List
  Classes.RelationPairs
  Classes.RelationClasses.

From CTree Require Import
  KTree.Core
  KTree.Logic.Trans
  KTree.Equ
  Events.Core.

From ExtLib Require Import
  Data.Monads.StateMonad
  Structures.MonadState.

From RelationAlgebra Require Import
  rel srel monoid.

Set Implicit Arguments.
Generalizable All Variables.

Import KTreeNotations ListNotations EquNotations.
Local Open Scope ktree_scope.
Local Open Scope list_scope.

Infix "≅2" := (Eq TS) (at level 58, left associativity).
Section Fixpoints.
  Context `{X: Type} `{sem: E ~~> state Σ}.

  (*| [ts] is a trans fixpoint |*)
  Definition is_fixp (ts: ktree E X * Σ): Prop :=
    trans ts ts.
  Arguments is_fixp ts /.

  (*|
    [TS] transitions to a fixpoint in [n] steps.
    Then, given a different state [σ'] through interference
    which again finitely transitions to a fixpoint. Until
    it terminates. |*)

  Inductive fin_fixp : nat -> ktree E X * Σ -> Prop :=
  | To_Ret t σ:
    is_ret t ->
    fin_fixp 0 (t, σ)
  | To_Fixpoint n m t t' σ σ0 σ'
      (Fin_step: srel.iter TS trans n (t,σ) (t', σ'))
      (Fixp: is_fixp (t', σ'))
      (Rec: fin_fixp m (t', σ0)):
    fin_fixp n (t,σ).

  Lemma is_fixp_iter: forall n ts ts',
      is_fixp ts -> ts ≅2 ts' -> srel.iter TS trans n ts ts'.
  Proof.
    intros.
    induction n; cbn.
    - auto.
    - now (exists ts).
  Qed.

  Class ToFixpoints (t: ktree E X) := {
      (* A finite number of steps to a fixpoint, given state [σ0] *)
      steps(σ: Σ): nat;

      (* Steps to a fixpoint, with [fin_fixp] *)
      wf_fin_fixp: forall σ, fin_fixp (steps σ) (t, σ)
    }.

  #[global] Instance proper_is_fixp:
    Proper (Eq TS ==> iff) is_fixp.
  Proof.
    repeat red; intros; unfold is_fixp; rewrite H; auto.
  Qed.

  (*| [Ret] is a [trans] fixpoint |*)
  Lemma is_fixp_ret: forall x σ,
      is_fixp (Ret x, σ).
  Proof.
    intros; red.
    apply trans_ret; split; reflexivity.
  Qed.
  Hint Resolve is_fixp_ret: core.

  #[global] Instance proper_fin_to_fixp:
    Proper (eq ==> Eq TS ==> iff) fin_fixp.
  Proof.
    split; intros.
    - generalize dependent y; generalize dependent y0.
      induction H1; subst; intros [ts σf] Heq x <-; destruct2 Heq.
      + eapply To_Ret.
        now rewrite Heq in H.
      + eapply To_Fixpoint; eauto.
        rewrite Heq in Fin_step.
        apply Fin_step.
    - generalize dependent x; generalize dependent x0.
      induction H1; subst; intros [ts σf] Heq x ->.
      + eapply To_Ret; destruct2 Heq.
        now rewrite Heq.
      + eapply To_Fixpoint; eauto.
        rewrite <- Heq in Fin_step.
        apply Fin_step.
  Qed.

End Fixpoints.

(*| A reactive tree [rtree] is a [ktree] with the [fin_lasso] property.
    For an input [σ: Σ] the program [inner] will take a non-zero
    number of transition steps to a fixpoint [(t',σ')], meaning
    that [forall n, trans^n (t', σ') (t', σ')].

    There exists a new input state [σ''] (interference)
    such that [fin_to_fixp (t', σ'')].

    The following definition has some serious restrictions.

    1. Programs always reach a fixpoint in a known number (n > 0) of steps.

    2. Fairness, means simply each client is
    executed any finite number of times, up to the fixpoint.

    3. From 1,2 we get an upper bound [n] on how many steps
    each process takes under fair scheduling.
 |*)
Record rtree E X `{E ~~> state Σ} := {
    inner :> ktree E X;
    (* A finite number of steps to a fixpoint [fixp], given state [σ0] *)
    steps(σ0: Σ): nat;

    (* A finite number of steps to a fixpoint [fixp], given state [σ0] *)
    fixp(σ0: Σ): ktree E X * Σ := transF (steps σ0) (inner, σ0);

    (* Connect everything together with [fin_lasso] *)
    wf_fin_lasso(σ0: Σ): fin_lasso (steps σ0) (inner, σ0) (fixp σ0)
  }.

Arguments rtree E X {Σ} {_}.

Section Try.
  Context (n: nat) `(DecT: EqDecidable T) (msg: T).
  Notation uid := (uid n).
  Notation netE := (netE n T).
  Arguments RelCompFun _ _ /.
  Arguments fst _ /.
  Arguments snd _ /.

  (*| Use the single queue semantics for this small example |*)
  Import Net.SingleQueue.

  (*| A program that sends a message to itself then reads it back |*)
  Program Definition send_recv_loop (i: uid): rtree netE T :=
    {|
      inner := Ktree.iter
                 (fun _ =>
                    send i i msg ;;
                    m <- recv i;;
                    match m with
                    | Some v => Ret (inr v)
                    | None => Ret (inl tt)
                    end) tt;
      steps _ := 2
    |}.
  Next Obligation.
    destruct σ0.
    - (* Empty queue *)
      econstructor.
      + rewrite transF_trans_iter_iff.
        cbn.
        split; reflexivity.
      + intro Hfalse.
        inv Hfalse; step in H; inv H.
      + unfold is_fixp.
        rewrite trans_ret; split; reflexivity.
      + apply To_Done.
        now econstructor.
        reflexivity.
        reflexivity.
    - (* Non-empty queue *)
      econstructor.
      + rewrite transF_trans_iter_iff.
        cbn.
        split; reflexivity.
      + intro Hfalse.
        inv Hfalse; step in H; inv H.
      + unfold is_fixp.
        rewrite trans_ret; split; reflexivity.
      + apply To_Done.
        now econstructor.
        reflexivity.
        reflexivity.
        Unshelve.
        exact [].
        exact [].
  Qed.
End Try.

(* Vector setoid -- lift [Eq TS] over [vec n TS] *)
Program Definition VTS `{Encode E} {n Σ X}: EqType :=
  {| type_of := (vec n (ktree E X * Σ))%type ; Eq := Vector.Forall2 (Eq TS) |}.
Next Obligation.
  constructor; cbn; intros; dependent induction x.
  (* refl *)
  + econstructor.
  + econstructor; eauto.
  (* symm *)
  + dependent destruction y.
    econstructor.
  + dependent destruction y; econstructor; dependent destruction H0.
    * now destruct H0; split; symmetry in H0; symmetry in H2.
    * auto.
  (* trans *)
  + dependent destruction y; dependent destruction z; auto.
  + dependent destruction y; dependent destruction z; dependent destruction H0;
      dependent destruction H2; econstructor.
    * destruct H0, H2; split; now transitivity h0.
    * now apply IHx with (y:=y).
Qed.

Section Par.

  Context {n: nat} `{h: E ~~> state Σ} {X: Type}.

  (*|
    Interference is how a local action affects the global state.
    It is the sharing is shared state concurrency. This will be specific to
    each type of effect and semantics.

    Also this is probaly not a decidable function, but a relation.
    For example, consider output queues
        [0: [send 2 m], 1: [send 2 n], 2: []]
    What should the new state [σ'] of process 2 be?
         [m, n] or [n, m]
   |*)
  Variable (interference: vec n Σ -> ktree E X * Σ -> rtree E X * Σ).

  Variant schedule: relation (vec n (rtree E X * Σ)) :=
    | Local_Par_Steps: forall (v v': vec n (rtree E X * Σ)) (fixps: vec n (ktree E X * Σ)) (global: vec n Σ),
        (* Take a big step for each process to their fixpoint.
           This is a fair schedule, but not complete description of all fair schedules.

           For example if [r: rtree] and [steps r σ = 3] then fair scheduling [r]
           [0, 1, 2] times is not considered. This is restrictive as it focuses only
           on "stable" properties, properties which hold in a local fixpoint.
         *)
        fixps = Vector.map (fun '(t, s) => fixp t s) v ->

        (* TODO: Now need to calculate new states from global state through interference *)
        global = Vector.map snd fixps ->

        schedule v (Vector.map (interference global) fixps).


  (*| An alternative representation of schedulers as higher-order [ktrees].

      Scheduling event is not a free event, it is simply a state event over
      all programs with their local states. |*)
  Definition scheduleE n: Type := stateE (vec n (rtree E X * Σ)).

End Par.
