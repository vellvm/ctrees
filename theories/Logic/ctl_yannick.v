(*|
=========================================
Modal logics over ctrees
=========================================
|*)
From Coinduction Require Import
	coinduction rel tactics.

Set Implicit Arguments.

(** * Kripke structures and CTL *)
Section Kripke.

  (** Kripke structures
      They carry:
      - a domain of states [stateK]
      - a (unlabelled) transition function [transK]
      - a domain of atomic propositions [factK]
      - a judgement [checkK] specifying which facts are valid in each state
   *)
  Class Kripke : Type :=
    {
      stateK : Type ;
      transK : stateK -> stateK -> Prop ;
      factK  : Type ;
      checkK : factK -> stateK -> Prop
    }.

  (** CTL formula
      We give a shallow representation of CTL formulas over a Kripke structure [K]
      as [stateK] predicates.
      Point to double check:
      - is it sound to resolve each combinator locally the way it is done?
      In particular, do nested [global] modalities behave correctly?
      Point to investigate:
      - how does it compare with a deep embedding with a single coinductive
      predicate judging them built atop of it?
   *)
  Context {K : Kripke}.

  (* Shallow encoding of formula Lef's style *)
  Definition formula := stateK -> Prop.

  Definition Now (p : factK) : formula :=
    checkK p.

  Definition And (φ ψ : formula) : formula :=
    fun s => φ s /\ ψ s.

  Definition Not (φ : formula) : formula :=
    fun s => ~ φ s.

  Definition Impl (φ ψ : formula) : formula :=
    fun s => φ s -> ψ s.

  Definition Equiv (φ ψ : formula) : formula :=
    fun s => φ s <-> ψ s.

  Definition AX (φ : formula) : formula :=
    fun s => forall s', transK s s' -> φ s'.

  Definition EX (φ : formula) : formula :=
    fun s => exists s', transK s s' /\ φ s'.

  Inductive AF (φ : formula) : formula :=
  | AFnow   s : φ s -> AF φ s
  | AFlater s : (forall s', transK s s' -> AF φ s') -> AF φ s.

  Inductive EF (φ : formula) : formula :=
  | EFnow   s : φ s -> EF φ s
  | EFlater s : (exists s', transK s s' -> EF φ s') -> EF φ s.

  Definition AG_ (φ : formula) (R : formula) : formula :=
    fun s => φ s /\ (forall s', transK s s' -> R s').
  Program Definition AGb (φ : formula) : mon formula :=
    {| body := AG_ φ |}.
  Next Obligation.
  repeat red; intros * IN * []; firstorder.
  Qed.
  Definition AG φ := gfp (AGb φ).

  Definition EG_ (φ : formula) (R : formula) : formula :=
    fun s => φ s /\ (exists s', transK s s' -> R s').
  Program Definition EGb (φ : formula) : mon formula :=
    {| body := EG_ φ |}.
  Next Obligation.
  repeat red; intros * IN * []; firstorder.
  Qed.
  Definition EG φ := gfp (EGb φ).

  (** * Equivalence of formulas
      Note: beware, not to be mixed up with the Equiv formula
   *)
  Definition eqf : formula -> formula -> Prop :=
    fun φ ψ => forall s, φ s <-> ψ s.
  Infix "==" := eqf (at level 70).

  (** * Reasoning about dead and live status *)
  (* We need a top and a bottom in our logic, we posit them and characterise them in the usual impredicative style *)
  Variable false_fact : factK.
  Variable false_fact_false : forall s, checkK false_fact s -> False.
  Variable true_fact : factK.
  Variable true_fact_true : forall s, checkK true_fact s.

  (* A dead state satisfies bottom after all its transition,
     which is only possible if there are none of them *)
  Definition dead : formula := AX (Now false_fact).
  Lemma dead_sound : forall s, (dead s <-> forall s', ~ transK s s').
  Proof.
    split.
    - intros is_stuck s' tr; apply is_stuck in tr.
      eapply false_fact_false; eauto.
    - intros is_stuck s' tr.
      exfalso; eapply is_stuck; eauto.
  Qed.
  (* A live state can exhibit a step with only top as challenge afterwards *)
  Definition alive : formula := EX (Now true_fact).
  Lemma alive_sound : forall s, (alive s <-> exists s', transK s s').
  Proof.
    split.
    - intros (s' & TR & _); eauto.
    - intros [s' TR]; exists s'; split; eauto.
      apply true_fact_true.
  Qed.
  (* Well, classically *)
  Lemma not_not φ : φ == Not (Not φ).
  Proof.
    cbv. firstorder.
    apply Classical_Prop.NNPP.
    unfold not; apply H.
  Qed.

  (* Intuitionistic direction *)
  Lemma alive_stuck : dead == Not alive.
  Proof.
    cbv; firstorder.
  Qed.

  Definition may_die : formula := EF dead.
  Definition doomed_to_die : formula := AF dead.
  Definition never_dead : formula := AG alive. (* a.k.a. diverging *)
  Definition may_survive : formula := EG alive.  (* a.k.a. may diverge *)

End Kripke.

(** * Kripke structures from Labelled Transition Systems *)
Section From_LTS.

  (** Contrary, to Kripke structures, LTSs carry no information in their states,
      but annotate their transitions with labels instead. They are hence made of:
      - a domain of states [stateL]
      - a domain of labels [labelL]
      - a labelled transition relation [transL]
   *)
  Class LTS : Type :=
    {
      stateL : Type;
      labelL : Type;
      transL : stateL -> labelL -> stateL -> Prop
    }.

  (** Building Kripke structures out of LTSs.
      We think of an LTS as describing a computation processing
      an hidden internal state through operations described by
      labels.
      In order to derive a Kripke structure from an LTS, we hence
      provide:
      - a domain of observations [obs] modelling an abstraction of the
      internal state we wish to observe and reason about
      - a function describing how labels act upon observations
      Given this data, the structure goes as follows:
      - states are LTS states enriched with an observation
      - transitions are fired if the state components are related by
      a labelled transition, such that the label taken describes the
      update to the observation
      - facts are predicate over observations, rendering checks trivial
   *)
  Definition make_Kripke_of_LTS
    (L : LTS)
    (obs : Type)
    (upd : obs -> labelL -> obs -> Prop)
    : Kripke :=
    {|
      stateK := stateL * obs;
      transK '(s1,p1) '(s2,p2) := (exists l, transL s1 l s2 /\ upd p1 l p2) ;
      factK  := obs -> Prop ;
      checkK := fun f '(_,o) => f o
    |}.

  (** Canonical observation: histories
      In particular, a canonical notion of observation is to
      record the traces of labels that have been taken up to
      this point
   *)
  Definition Kripke_of_LTS_canonical (L : LTS) :=
    @make_Kripke_of_LTS L (list labelL) (fun h l l' => l' = cons l h).

End From_LTS.

From CTree Require Import
     CTree Eq.

(** * Kripke structures from ctrees *)
Section From_CTree.

  Variable (E B : Type -> Type) (R : Type).
  Context `{B0 -< B}.
  Notation computation := (ctree E B R).

  (* [ctrees] are already seen as LTS, we simply package it in the structure *)
  Definition LTS_of_ctree (c : computation) : LTS :=
  {|
    stateL := computation ;
    labelL := @label E ;
    transL := fun c l c' => trans l c c'
  |}
  .

  (* And hence spawn Kripke structure *)
  Definition make_Kripke_of_ctree
    (c : computation)
    (obs : Type)
    (upd : obs -> @label E -> obs -> Prop)
    : Kripke :=
    make_Kripke_of_LTS (LTS_of_ctree c) upd.

End From_CTree.

(** * Examples. *)

Module Termination.

  Variable (E B : Type -> Type) (R : Type).
  Context `{B0 -< B}.
  Notation computation := (ctree E B R).

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

  Definition Kripke_status (c : computation) : Kripke :=
    make_Kripke_of_ctree c upd_status.

  (* Let's fix a computation so that we have a structure *)
  Variable c : computation.
  #[local] Instance K : Kripke := Kripke_status c.

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

End Termination.

Module Scheduling.

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

  Definition Kripke_status (c : computation) : Kripke :=
    make_Kripke_of_ctree c upd_status.

  (* Let's fix a computation so that we have a structure *)
  Variable c : computation.
  #[local] Instance K : Kripke := Kripke_status c.

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

End Scheduling.

Module Memory.

  Variable (B : Type -> Type) (R : Type).
  Context `{B0 -< B}.
  (* Let's consider a computation over two memory cells *)
  Variant cellE : Type -> Type :=
    | Wr (b : bool) (n : nat) : cellE unit
    | Rd (b : bool)         : cellE nat.
  Notation computation := (ctree cellE B R).

  (* We could observe the content of the cells *)
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

  Definition Kripke_status (c : computation) : Kripke :=
    make_Kripke_of_ctree c upd_status.

  (* Let's fix a computation so that we have a structure *)
  Variable c : computation.
  #[local] Instance K : Kripke := Kripke_status c.

  (* And we can play silly game, expressing some invariant on the cells... *)
  Definition eventually_empty : formula := AF (Now (fun '(a,b) => a + b = 0)).
  Definition constant_sum n : formula := AG (Now (fun '(a,b) => a + b = n)).

End Memory.

