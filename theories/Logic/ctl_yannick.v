(*|
=========================================
Modal logics over ctrees
=========================================
|*)
From Coinduction Require Import
	coinduction rel tactics.
From CTree Require Import Utils.

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
  Coercion stateK: Kripke >-> Sortclass.

  Section bisim.
    (** we fix an automaton X *)
    Variable X: Kripke.

    Program Definition sb : mon (X -> X -> Prop) :=
      {| body R x y :=
          (forall f, checkK f x -> checkK f y) /\
            forall x', transK x x' -> exists y', transK y y' /\ R x' y'
      |}.
    Next Obligation.
      repeat intro.
      intuition.
      edestruct H2 as (? & ? & ?); eauto.
      eexists; split; eauto.
      apply H; auto.
    Qed.
    Definition b := (cap sb (comp converse (comp sb converse))).

    (** whose greatest fixpoint coincides with language equivalence *)
    Definition bisimK := gfp b.

  End bisim.

  Context {K : Kripke}.
  Arguments b {K} : rename.
  Arguments bisimK {K} : rename.

  Infix "~~" := bisimK (at level 70).
  Notation t := (t b).
  Notation T := (T b).
  Notation bt := (bt b).
  Notation bT := (bT b).
  Notation "x [~~] y" := (t _ x y) (at level 79).
  Notation "x {~~} y" := (bt _ x y) (at level 79).

  Definition seq: relation stateK := eq.
  Arguments seq/.

  (** [eq] is a post-fixpoint, thus [const eq] is below [t] *)
  Lemma eq_t: const seq <= t.
  Proof.
    apply leq_t. intro.
    apply cap_spec. split.
    intros p q <-; split; eauto.
    intros p q <-; split; eauto.
  Qed.

  (** converse is compatible *)
  Lemma converse_t: converse <= t.
  Proof.
    apply invol_t.
  Qed.

  (** so is squaring *)
  Lemma square_t: square <= t.
  Proof.
    apply Coinduction, by_Symmetry.
    intros R x z [y xy yz].
    exists y; auto.
    unfold b.
    rewrite cap_l at 1.
    setoid_rewrite <-f_Tf.
    intros R x z [y xy yz]; split; intros.
    destruct xy, yz; auto.
    destruct xy, yz.
    apply H1 in H.
    destruct H as (? & ? & ?).
    apply H3 in H.
    destruct H as (? & ? & ?).
    eexists; split.
    eauto.
    eexists; eauto.
  Qed.

  #[global] Instance Equivalence_t R: Equivalence (t R).
  Proof.
    apply Equivalence_t. apply eq_t. apply square_t. apply converse_t.
  Qed.
  Corollary Equivalence_bisimK : Equivalence bisimK.
  Proof. apply Equivalence_t. Qed.


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

  (* Shallow encoding of formula Lef's style *)
  Definition formula := stateK -> Prop.

  Definition Now (p : factK) : formula :=
    checkK p.

  Definition Or (φ ψ : formula) : formula :=
    fun s => φ s \/ ψ s.

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
  | EFlater s : (exists s', transK s s' /\ EF φ s') -> EF φ s.

  Definition AG_ (φ : formula) (R : formula) : formula :=
    fun s => φ s /\ (forall s', transK s s' -> R s').
  Program Definition AGb (φ : formula) : mon (K -> Prop) :=
    {| body := AG_ φ |}.
  Next Obligation.
    repeat red; intros * IN * []; firstorder.
  Qed.
  Definition AG φ := gfp (AGb φ).

  Definition EG_ (φ : formula) (R : formula) : formula :=
    fun s => φ s /\ (exists s', transK s s' /\ R s').
  Program Definition EGb (φ : formula) : mon (K -> Prop) :=
    {| body := EG_ φ |}.
  Next Obligation.
    repeat red; intros * IN * []; firstorder.
  Qed.
  Definition EG φ := gfp (EGb φ).

  Inductive Formula: Type :=
  | FNow (p : factK): Formula
  | FAnd    : Formula -> Formula -> Formula
  | FOr     : Formula -> Formula -> Formula
  | FImpl   : Formula -> Formula -> Formula
  | FAX     : Formula -> Formula
  | FEX     : Formula -> Formula
  | FAF     : Formula -> Formula
  | FEF     : Formula -> Formula
  | FAG     : Formula -> Formula
  | FEG     : Formula -> Formula.

  (* Satisfiability inductively on formulas *)
  Fixpoint satF (φ: Formula): stateK -> Prop :=
    match φ with
    | FNow p    => Now p
    | FAnd  φ ψ => And (satF φ) (satF ψ)
    | FOr   φ ψ => Or (satF φ) (satF ψ)
    | FImpl φ ψ => Impl (satF φ) (satF ψ)
    | FAX   φ   => AX (satF φ)
    | FEX   φ   => EX (satF φ)
    | FAF   φ   => AF (satF φ)
    | FEF   φ   => EF (satF φ)
    | FAG   φ   => AG (satF φ)
    | FEG   φ   => EG (satF φ)
    end.

  Notation good := (Proper (bisimK ==> iff)).

  Lemma bisim_transK : forall s t s',
      s ~~ t ->
      transK s s' ->
      exists t', transK t t' /\ s' ~~ t'.
  Proof.
    intros * EQ TR.
    step in EQ; destruct EQ as [[_ EQ] _].
    apply EQ in TR; intuition.
  Qed.

  Ltac trans_step eq tr :=
    first [pose proof bisim_transK _ eq tr as (? & ?tr & ?eq) |
           symmetry in eq; pose proof bisim_transK _ eq tr as (? & ?tr & ?eq)].

  Instance Now_bisim φ : good (Now φ).
  Proof.
    intros s t EQ; split; intros HN.
    - step in EQ; destruct EQ as [HF HR].
      apply HF, HN.
    - step in EQ; destruct EQ as [HF HR].
      apply HR, HN.
  Qed.

  Instance And_bisim φ ψ :
    good φ ->
    good ψ ->
    good (And φ ψ).
  Proof.
    intros H1 H2 s t EQ; split; intros HN.
    - destruct HN.
      split.
      eapply H1, H; now symmetry.
      eapply H2, H0; now symmetry.
    - destruct HN.
      split.
      eapply H1, H; now symmetry.
      eapply H2, H0; now symmetry.
  Qed.

  Instance Or_bisim φ ψ :
    good φ ->
    good ψ ->
    good (Or φ ψ).
  Proof.
    intros H1 H2 s t EQ; split; intros HN.
    - destruct HN.
      left; eapply H1, H; now symmetry.
      right; eapply H2, H; now symmetry.
    - destruct HN.
      left; eapply H1, H; now symmetry.
      right; eapply H2, H; now symmetry.
  Qed.

  Instance Not_bisim φ :
    good φ ->
    good (Not φ).
  Proof.
    intros H s t EQ; split; intros HN.
    - intros abs.
      apply HN.
      eapply H; eauto.
    - intros abs.
      apply HN.
      eapply H; [symmetry |]; eauto.
  Qed.

  Instance Impl_bisim φ ψ :
    good φ ->
    good ψ ->
    good (Impl φ ψ).
  Proof.
    intros H1 H2 s t EQ; split; intros HN.
    - intros H; eapply H2; [symmetry; eassumption | eapply HN, H1; [eassumption |]]; eauto.
    - intros H; eapply H2; [ eassumption | eapply HN, H1; [symmetry; eassumption |]]; eauto.
  Qed.

  Instance Equiv_bisim φ ψ :
    good φ ->
    good ψ ->
    good (Equiv φ ψ).
  Proof.
    intros H1 H2 s t EQ; split; intros HN; split; intros H.
    eapply H2; [symmetry; eassumption |]; eapply HN, H1; eauto.
    eapply H1; [symmetry; eassumption |]; eapply HN, H2; eauto.
    eapply H2; [eassumption |]; eapply HN, H1; [symmetry; eassumption | eauto].
    eapply H1; [eassumption |]; eapply HN, H2; [symmetry; eassumption | eauto].
  Qed.

  Instance AX_bisim φ :
    good φ ->
    good (AX φ).
  Proof.
    intros H s t EQ; split; intros HN u TR.
    - trans_step EQ TR.
      apply HN in TR0.
      eapply H; [| apply TR0]; auto.
    - trans_step EQ TR.
      apply HN in TR0.
      eapply H; [| apply TR0]; auto.
  Qed.

  Instance EX_bisim φ :
    good φ ->
    good (EX φ).
  Proof.
    intros H s t EQ; split; intros (? & TR & ?).
    - trans_step EQ TR.
      eexists; split; eauto.
      eapply H; [| apply H0]; symmetry; auto.
    - trans_step EQ TR.
      eexists; split; eauto.
      eapply H; [| apply H0]; symmetry; auto.
  Qed.

  Lemma EF_ind' :
    forall [φ : formula] (P : K -> Prop),
      (forall s : K, φ s -> P s) ->
      (forall (s : K) (HET : exists s' : K, transK s s' /\ EF φ s')
         (IH : exists s' : K, transK s s' /\ P s'), P s) ->
      forall s : K, EF φ s -> P s.
  Proof.
    intros * Hnow Hnext.
    refine (fix F (s : K) (H : EF φ s) : P s := _).
    refine (match H with
            | EFnow _ _ Hφ => Hnow _ Hφ
            | EFlater _ (ex_intro _ s' (conj TR HEF)) => _
            end).
    apply Hnext; auto.
    eexists; split; [exact TR |].
    apply F, HEF.
  Qed.

  Instance AF_bisim φ :
    good φ ->
    good (AF φ).
  Proof.
    intros H s t EQ; split; intros HN.
    - revert t EQ; induction HN; intros.
      + apply AFnow.
        now rewrite <- EQ.
      + apply AFlater; intros ? tr.
        trans_step EQ tr.
        eapply H1; eauto.
        now symmetry.
    - revert s EQ; induction HN; intros.
      + apply AFnow.
        now rewrite EQ.
      + apply AFlater; intros ? tr.
        trans_step EQ tr.
        eapply H1; eauto.
  Qed.

  Instance EF_bisim φ :
    good φ ->
    good (EF φ).
  Proof.
    intros H s t EQ; split; intros HN.
    - revert t EQ.
      induction HN using EF_ind'.
      + intros; apply EFnow.
        now rewrite <- EQ.
      + intros.
        apply EFlater.
        destruct IH as (s' & TR & IH).
        trans_step EQ TR.
        exists x; split; auto.
    - revert s EQ.
      induction HN using EF_ind'.
      + intros; apply EFnow.
        now rewrite EQ.
      + intros.
        apply EFlater.
        destruct IH as (s' & TR & IH).
        trans_step EQ TR.
        exists x; split; auto.
        apply IH.
        now symmetry.
  Qed.

  Lemma coind_AG (φ : formula) :
    forall (R : stateK -> Prop),
      (forall s, R s -> φ s) ->
      (forall s s', R s -> transK s s' -> R s') ->
      forall s, R s -> AG φ s.
  Proof.
    intros * Aφ stable.
    unfold AG; coinduction r CIH.
    intros * HR.
    split; auto.
    intros.
    eapply CIH, stable; eauto.
  Qed.

  Lemma coind_EG (φ : formula) :
    forall (R : stateK -> Prop),
      (forall s, R s -> φ s) ->
      (forall s, R s -> exists s', transK s s' /\ R s') ->
      forall s, R s -> EG φ s.
  Proof.
    intros * Aφ stable.
    unfold EG; coinduction r CIH.
    intros * HR.
    split; auto.
    edestruct stable as (? & ? & ?); eauto.
  Qed.

  Instance AG_bisim φ :
    good φ ->
    good (AG φ).
  Proof.
    intros HG s t EQ; split; intros HN.
    - revert s t EQ HN.
      unfold AG; coinduction R CIH. intros;
        step in HN; destruct HN as [Hφ HN].
      split.
      + eapply HG; [symmetry |]; eauto.
      + intros s' TR.
        trans_step EQ TR.
        eapply CIH.
        symmetry; eauto.
        now apply HN.
    - revert s t EQ HN.
      unfold AG; coinduction R CIH; intros;
        step in HN; destruct HN as [Hφ HN].
      split.
      + eapply HG; eauto.
      + intros s' TR.
        trans_step EQ TR.
        eapply CIH.
        eauto.
        now apply HN.
  Qed.

  Instance EG_bisim φ :
    good φ ->
    good (EG φ).
  Proof.
    intros HG s t EQ; split; intros HN.
    - revert s t EQ HN.
      unfold EG; coinduction R CIH; intros;
        step in HN; destruct HN as [Hφ (? & TR & HG')].
      split.
      + eapply HG; [symmetry |]; eauto.
      + trans_step EQ TR.
        eexists; split; eauto.
    - revert s t EQ HN.
      unfold EG; coinduction R CIH; intros;
        step in HN; destruct HN as [Hφ (? & TR & HG')].
      split.
      + eapply HG; eauto.
      + trans_step EQ TR.
        eexists; split; eauto.
        eapply CIH.
        symmetry; eauto.
        eauto.
  Qed.

  Lemma sat_bisim (φ : Formula) : good (satF φ).
  Proof.
    induction φ;
      eauto using
        Now_bisim, And_bisim, Or_bisim, Not_bisim, Impl_bisim,
      EX_bisim, AX_bisim, EF_bisim, AF_bisim, EG_bisim, AG_bisim.
  Qed.

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
    intros s; intuition.
    intros (? & tr & _); apply H in tr; eapply false_fact_false,tr.
    intros s' tr.
    exfalso; eapply H.
    exists s'; split; auto.
    apply true_fact_true.
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
Import CTreeNotations.

(** * Kripke structures from ctrees *)
Section From_CTree.

  Variable (E B : Type -> Type) (R : Type).
  Context `{B0 -< B}.
  Notation computation := (ctree E B R).

  (* [ctrees] are already seen as LTS, we simply package it in the structure *)
  Definition LTS_of_ctree : LTS :=
  {|
    stateL := computation ;
    labelL := @label E ;
    transL := fun c l c' => trans l c c'
  |}
  .

  (* And hence spawn Kripke structure *)
  Definition make_Kripke_of_ctree
    (obs : Type)
    (upd : obs -> @label E -> obs -> Prop)
    : Kripke :=
    make_Kripke_of_LTS LTS_of_ctree upd.

  Lemma sbisim_bisimK obs (upd : obs -> @label E -> obs -> Prop) :
    forall (t s : computation),
      t ~ s ->
      forall (o : obs),
        bisimK (@make_Kripke_of_ctree obs upd) (t,o) (s,o).
  Proof.
    unfold bisimK.
    coinduction r CIH.
    intros * EQ *.
    split.
    - cbn; split; auto.
      intros [t' o'] (l & TR & up); cbn.
      step in EQ; apply EQ in TR; destruct TR as (? & s' & TR' & EQ' & <-).
      exists (s',o'); split.
      exists l; split; auto.
      apply CIH, EQ'.
    - cbn; split; auto.
      intros [s' o'] (l & TR & up); cbn.
      step in EQ; apply EQ in TR; destruct TR as (? & t' & TR' & EQ' & <-).
      exists (t',o'); split.
      exists x; split; auto.
      apply CIH, EQ'.
  Qed.

  (* Recurrent case: τ transitions do not impact our observations *)
  Variant lift
    {O}
    (upd_e : O -> {x : Type & E x & x} -> O -> Prop)
    (upd_r : O -> {x : Type & x} -> O -> Prop) :
    O -> @label E -> O -> Prop :=
  | lupd_e {X} (e : E X) (x : X) o o' :
    upd_e o (existT2 _ _ X e x) o' ->
    lift upd_e upd_r o (obs e x) o'
  | lupd_r {X} (x : X) o o' :
    upd_r o (existT _ X x) o' ->
    lift upd_e upd_r o (val x) o'
  | lupd_τ o :
    lift upd_e upd_r o tau o
  .

  Definition make_Kripke_of_ctree'
    (obs : Type)
    (upd_e : obs -> {x : Type & E x & x} -> obs -> Prop)
    (upd_r : obs -> {x : Type & x} -> obs -> Prop)
    : Kripke :=
    make_Kripke_of_ctree (lift upd_e upd_r).

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

End Termination
 
                  
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

End Memory.
