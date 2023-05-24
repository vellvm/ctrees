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

  (** Equality over Kripke structure
      Defined as the bisimilarity observing valid facts
   *)
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
      as [stateK] predicates (i.e. [stateK -> Prop]).
      Path quantifiers [P]:
      - [E] : exists a successor
      - [Aw]: forall successors
      - [A] : forall successors _and_ there exists at least one
      List of supported formulae:
      - now  : currently valid fact
      - or   : logical or
      - and  : logical and
      - not  : logical not
      - impl : logical impl
      - [P]X φ : next φ
      - [P]F φ : eventually φ (finitely reachable)
      - [P]G φ : globally φ (valid at all steps)
      - [P]U φ ψ : φ until ψ (with ψ finitely reachable)
      - [P]W φ ψ : φ weak until ψ (ψ may not be reachable if globally φ)
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

  (* Definition Equiv (φ ψ : formula) : formula := *)
  (*   fun s => φ s <-> ψ s. *)

  Variant live : stateK -> Prop :=
    | live_wit s s' : transK s s' -> live s.
  Notation "↯ s" := (live s) (at level 10).

  (* Should AX impose that a step is possible or not? *)
  Definition AwX (φ : formula) : formula :=
    fun s => forall s', transK s s' -> φ s'.

  Definition AX (φ : formula) : formula :=
    fun s => ↯s /\ forall s', transK s s' -> φ s'.

  Definition EX (φ : formula) : formula :=
    fun s => exists s', transK s s' /\ φ s'.

  Inductive AwF (φ : formula) : formula :=
  | AwFnow   s : φ s -> AwF φ s
  | AwFlater s : (forall s', transK s s' -> AwF φ s') -> AwF φ s.

  Inductive AF (φ : formula) : formula :=
  | AFnow   s : φ s -> AF φ s
  | AFlater s : ↯s -> (forall s', transK s s' -> AF φ s') -> AF φ s.

  Unset Elimination Schemes.
  Inductive EF (φ : formula) : formula :=
  | EFnow   s : φ s -> EF φ s
  | EFlater s : (exists s', transK s s' /\ EF φ s') -> EF φ s.
  Set Elimination Schemes.

  Lemma EF_ind :
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

  Definition AwG_ (φ : formula) (R : formula) : formula :=
    fun s => φ s /\ (forall s', transK s s' -> R s').
  Program Definition AwGb (φ : formula) : mon (K -> Prop) :=
    {| body := AwG_ φ |}.
  Next Obligation.
    repeat red; intros * IN * []; firstorder.
  Qed.
  Definition AwG φ := gfp (AwGb φ).

  Definition AG_ (φ : formula) (R : formula) : formula :=
    fun s => φ s /\ ↯ s /\ (forall s', transK s s' -> R s').
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

  Unset Elimination Schemes.
  Inductive EU (φ ψ : formula) : formula :=
  | EUnow  s : ψ s -> EU φ ψ s
  | EUnext s : φ s -> (exists s', transK s s' /\ EU φ ψ s') -> EU φ ψ s.
  Set Elimination Schemes.

  Lemma EU_ind :
    forall [φ ψ : formula] (P : K -> Prop),
      (forall s : K, ψ s -> P s) ->
      (forall (s : K)
         (Hφ : φ s)
         (HET : exists s' : K, transK s s' /\ EU φ ψ s')
         (IH : exists s' : K, transK s s' /\ P s'), P s) ->
      forall s : K, EU φ ψ s -> P s.
  Proof.
    intros * Hnow Hnext.
    refine (fix F (s : K) (H : EU φ ψ s) : P s := _).
    refine (match H with
            | EUnow  _ _ _ Hψ => Hnow _ Hψ
            | EUnext _ Hφ (ex_intro _ s' (conj TR HEF)) => _
            end).
    apply Hnext; auto.
    eexists; split; [exact TR |].
    apply F, HEF.
  Qed.

  Inductive AwU (φ ψ : formula) : formula :=
  | AwUnow  s : ψ s -> AwU φ ψ s
  | AwUnext s : φ s -> (forall s', transK s s' -> AwU φ ψ s') -> AwU φ ψ s.

  Inductive AU (φ ψ : formula) : formula :=
  | AUnow  s : ψ s -> AU φ ψ s
  | AUnext s : φ s -> ↯s -> (forall s', transK s s' -> AU φ ψ s') -> AU φ ψ s.

  (* TODO RELEASE VERSION? *)
  Variant EW_ (φ ψ : formula) (R : formula) : formula :=
    | EW_now  s : ψ s -> EW_ φ ψ R s
    | EW_next s : φ s -> (exists s', transK s s' /\ R s') -> EW_ φ ψ R s.
  Hint Constructors EW_ : core.
  Program Definition EWb (φ ψ : formula) : mon (K -> Prop) :=
    {| body := EW_ φ ψ |}.
  Next Obligation.
    repeat red; intros * IN * []; firstorder.
    econstructor 2; eauto.
    econstructor; split; eauto.
    now apply IN.
  Qed.
  Definition EW φ ψ := gfp (EWb φ ψ).

  Variant AwW_ (φ ψ : formula) (R : formula) : formula :=
    | AwW_now  s : ψ s -> AwW_ φ ψ R s
    | AwW_next s : φ s -> (forall s', transK s s' -> R s') -> AwW_ φ ψ R s.
  Hint Constructors AwW_ : core.
  Program Definition AwWb (φ ψ : formula) : mon (K -> Prop) :=
    {| body := AwW_ φ ψ |}.
  Next Obligation.
    repeat red; intros * IN * []; firstorder.
    econstructor 2; eauto.
    intros * TR.
    now apply IN, H0.
  Qed.
  Definition AwW φ ψ := gfp (AwWb φ ψ).

  Variant AW_ (φ ψ : formula) (R : formula) : formula :=
    | AW_now  s : ψ s -> AW_ φ ψ R s
    | AW_next s : φ s -> ↯s -> (forall s', transK s s' -> R s') -> AW_ φ ψ R s.
  Hint Constructors AW_ : core.
  Program Definition AWb (φ ψ : formula) : mon (K -> Prop) :=
    {| body := AW_ φ ψ |}.
  Next Obligation.
    repeat red; intros * IN * []; firstorder.
    econstructor 2; eauto.
    intros * TR.
    now apply IN, H1.
  Qed.
  Definition AW φ ψ := gfp (AWb φ ψ).


  (** CTL formula
      We give a shallow representation of CTL formulas over a Kripke structure [K]
      as [stateK] predicates (i.e. [stateK -> Prop]).
      Path quantifiers [P]:
      - [E] : exists a successor
      - [Aw]: forall successors
      - [A] : forall successors _and_ there exists at least one
      List of supported formulae:
      - now  : currently valid fact
      - or   : logical or
      - and  : logical and
      - not  : logical not
      - impl : logical impl
      - [P]X φ : next φ
      - [P]F φ : eventually φ (finitely reachable)
      - [P]G φ : globally φ (valid at all steps)
      - [P]U φ ψ : φ until ψ (with ψ finitely reachable)
      - [P]W φ ψ : φ weak until ψ (ψ may not be reachable if globally φ)
   *)
  Inductive Formula: Type :=
  | FNow (p : factK): Formula
  | FAnd    : Formula -> Formula -> Formula
  | FOr     : Formula -> Formula -> Formula
  | FNot    : Formula -> Formula
  | FImpl   : Formula -> Formula -> Formula
  | FAX     : Formula -> Formula
  | FAwX    : Formula -> Formula
  | FEX     : Formula -> Formula
  | FAF     : Formula -> Formula
  | FAwF    : Formula -> Formula
  | FEF     : Formula -> Formula
  | FAG     : Formula -> Formula
  | FAwG    : Formula -> Formula
  | FEG     : Formula -> Formula
  | FEU     : Formula -> Formula -> Formula
  | FAU     : Formula -> Formula -> Formula
  | FAwU    : Formula -> Formula -> Formula
  | FEW     : Formula -> Formula -> Formula
  | FAW     : Formula -> Formula -> Formula
  | FAwW    : Formula -> Formula -> Formula
  .

  (* Satisfiability inductively on formulas *)
  Fixpoint satF (φ: Formula): stateK -> Prop :=
    match φ with
    | FNow p    => Now p
    | FNot  φ   => Not (satF φ)
    | FAnd  φ ψ => And (satF φ) (satF ψ)
    | FOr   φ ψ => Or (satF φ) (satF ψ)
    | FImpl φ ψ => Impl (satF φ) (satF ψ)
    | FAX   φ   => AX (satF φ)
    | FAwX  φ   => AwX (satF φ)
    | FEX   φ   => EX (satF φ)
    | FAF   φ   => AF (satF φ)
    | FAwF  φ   => AwF (satF φ)
    | FEF   φ   => EF (satF φ)
    | FAG   φ   => AG (satF φ)
    | FAwG  φ   => AwG (satF φ)
    | FEG   φ   => EG (satF φ)
    | FEU   φ ψ => EU (satF φ) (satF ψ)
    | FAU   φ ψ => AU (satF φ) (satF ψ)
    | FAwU  φ ψ => AwU (satF φ) (satF ψ)
    | FEW   φ ψ => EW (satF φ) (satF ψ)
    | FAW   φ ψ => AW (satF φ) (satF ψ)
    | FAwW  φ ψ => AwW (satF φ) (satF ψ)
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

  (* Instance Equiv_bisim φ ψ : *)
  (*   good φ -> *)
  (*   good ψ -> *)
  (*   good (Equiv φ ψ). *)
  (* Proof. *)
  (*   intros H1 H2 s t EQ; split; intros HN; split; intros H. *)
  (*   eapply H2; [symmetry; eassumption |]; eapply HN, H1; eauto. *)
  (*   eapply H1; [symmetry; eassumption |]; eapply HN, H2; eauto. *)
  (*   eapply H2; [eassumption |]; eapply HN, H1; [symmetry; eassumption | eauto]. *)
  (*   eapply H1; [eassumption |]; eapply HN, H2; [symmetry; eassumption | eauto]. *)
  (* Qed. *)

  Instance live_bisim : good live.
  Proof.
    intros s s' eq; split; intros MS; inversion_clear MS.
    all: trans_step eq H; econstructor; eauto.
  Qed.

  Instance AwX_bisim φ :
    good φ ->
    good (AwX φ).
  Proof.
    intros H s t EQ; split; intros HN u TR.
    - trans_step EQ TR.
      apply HN in TR0.
      eapply H; [| apply TR0]; auto.
    - trans_step EQ TR.
      apply HN in TR0.
      eapply H; [| apply TR0]; auto.
  Qed.

  Instance AX_bisim φ :
    good φ ->
    good (AX φ).
  Proof.
    intros H s t EQ; split; intros [HP HN].
    - split; [rewrite <- EQ; assumption | intros s' TR].
      trans_step EQ TR.
      apply HN in TR0.
      eapply H; [| apply TR0]; auto.
    - split; [rewrite EQ; assumption | intros s' TR].
      trans_step EQ TR.
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


  Instance AwF_bisim φ :
    good φ ->
    good (AwF φ).
  Proof.
    intros H s t EQ; split; intros HN.
    - revert t EQ; induction HN; intros.
      + apply AwFnow.
        now rewrite <- EQ.
      + apply AwFlater; intros ? tr.
        trans_step EQ tr.
        eapply H1; eauto.
        now symmetry.
    - revert s EQ; induction HN; intros.
      + apply AwFnow.
        now rewrite EQ.
      + apply AwFlater; intros ? tr.
        trans_step EQ tr.
        eapply H1; eauto.
  Qed.

  Instance AF_bisim φ :
    good φ ->
    good (AF φ).
  Proof.
    intros H s t EQ; split; intros HN.
    - revert t EQ; induction HN; intros.
      + apply AFnow.
        now rewrite <- EQ.
      + apply AFlater.
        now rewrite <- EQ.
        intros ? tr.
        trans_step EQ tr.
        eapply H2; eauto.
        now symmetry.
    - revert s EQ; induction HN; intros.
      + apply AFnow.
        now rewrite EQ.
      + apply AFlater.
        now rewrite EQ.
        intros ? tr.
        trans_step EQ tr.
        eapply H2; eauto.
  Qed.

  Instance EF_bisim φ :
    good φ ->
    good (EF φ).
  Proof.
    intros H s t EQ; split; intros HN.
    - revert t EQ.
      induction HN.
      + intros; apply EFnow.
        now rewrite <- EQ.
      + intros.
        apply EFlater.
        destruct IH as (s' & TR & IH).
        trans_step EQ TR.
        exists x; split; auto.
    - revert s EQ.
      induction HN.
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

  Lemma coind_AwG (φ : formula) :
    forall (R : stateK -> Prop),
      (forall s, R s -> φ s) ->
      (forall s s', R s -> transK s s' -> R s') ->
      forall s, R s -> AwG φ s.
  Proof.
    intros * Aφ stable.
    unfold AwG; coinduction r CIH.
    intros * HR.
    split; auto.
    intros.
    eapply CIH, stable; eauto.
  Qed.

  Lemma coind_AG (φ : formula) :
    forall (R : stateK -> Prop),
      (forall s, R s -> φ s) ->
      (forall s, R s -> ↯s /\ (forall s', transK s s' -> R s')) ->
      forall s, R s -> AG φ s.
  Proof.
    intros * Aφ stable.
    unfold AG; coinduction r CIH.
    intros * HR.
    split; auto.
    split.
    apply stable; auto.
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

  Instance AwG_bisim φ :
    good φ ->
    good (AwG φ).
  Proof.
    intros HG s t EQ; split; intros HN.
    - revert s t EQ HN.
      unfold AwG; coinduction R CIH. intros;
        step in HN; destruct HN as [Hφ HN].
      split.
      + eapply HG; [symmetry |]; eauto.
      + intros s' TR.
        trans_step EQ TR.
        eapply CIH.
        symmetry; eauto.
        now apply HN.
    - revert s t EQ HN.
      unfold AwG; coinduction R CIH; intros;
        step in HN; destruct HN as [Hφ HN].
      split.
      + eapply HG; eauto.
      + intros s' TR.
        trans_step EQ TR.
        eapply CIH.
        eauto.
        now apply HN.
  Qed.

  Instance AG_bisim φ :
    good φ ->
    good (AG φ).
  Proof.
    intros HG s t EQ; split; intros HN.
    - revert s t EQ HN.
      unfold AG; coinduction R CIH. intros;
        step in HN; destruct HN as (Hφ & HS & HN).
      split; [| split].
      + eapply HG; [symmetry |]; eauto.
      + rewrite <- EQ; auto.
      + intros s' TR.
        trans_step EQ TR.
        eapply CIH.
        symmetry; eauto.
        now apply HN.
    - revert s t EQ HN.
      unfold AG; coinduction R CIH; intros;
        step in HN; destruct HN as (Hφ & HS & HN).
      split; [| split].
      + eapply HG; eauto.
      + rewrite EQ; auto.
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

  Instance EU_bisim φ ψ :
    good φ ->
    good ψ ->
    good (EU φ ψ).
  Proof.
    intros HG HG' s t EQ; split; intros HN.
    - revert t EQ.
      induction HN; intros.
      constructor; now rewrite <- EQ.
      econstructor 2.
      now rewrite <- EQ.
      destruct IH as (s' & TR & IH).
      trans_step EQ TR; eauto.
    - revert s EQ.
      induction HN; intros.
      constructor; now rewrite EQ.
      econstructor 2.
      now rewrite EQ.
      destruct IH as (s' & TR & IH).
      trans_step EQ TR.
      exists x; split; eauto.
      apply IH; now symmetry.
  Qed.

  Instance AwU_bisim φ ψ :
    good φ ->
    good ψ ->
    good (AwU φ ψ).
  Proof.
    intros HG HG' s t EQ; split; intros HN.
    - revert t EQ.
      induction HN; intros.
      constructor; now rewrite <- EQ.
      econstructor 2.
      now rewrite <- EQ.
      intros ? TR.
      trans_step EQ TR.
      eapply H1; eauto.
      now symmetry.
    - revert s EQ.
      induction HN; intros.
      constructor; now rewrite EQ.
      econstructor 2.
      now rewrite EQ.
      intros ? TR.
      trans_step EQ TR.
      eauto.
  Qed.

  Instance AU_bisim φ ψ :
    good φ ->
    good ψ ->
    good (AU φ ψ).
  Proof.
    intros HG HG' s t EQ; split; intros HN.
    - revert t EQ.
      induction HN; intros.
      constructor; now rewrite <- EQ.
      econstructor 2.
      now rewrite <- EQ.
      now rewrite <- EQ.
      intros ? TR.
      trans_step EQ TR.
      eapply H2; eauto.
      now symmetry.
    - revert s EQ.
      induction HN; intros.
      constructor; now rewrite EQ.
      econstructor 2.
      now rewrite EQ.
      now rewrite EQ.
      intros ? TR.
      trans_step EQ TR.
      eauto.
  Qed.

  Instance EW_bisim φ ψ :
    good φ ->
    good ψ ->
    good (EW φ ψ).
  Proof.
    intros HG HG' s t EQ; split; intros HN.
    - revert s t EQ HN.
      unfold EW; coinduction r cih; intros;
        step in HN; cbn in HN; destruct HN as [? Hφ | ? Hφ (? & TR & HW')].
      constructor; now rewrite <- EQ.
      econstructor 2.
      now rewrite <- EQ.
      trans_step EQ TR; eauto.
    - revert s t EQ HN.
      unfold EW; coinduction r cih; intros;
        step in HN; cbn in HN; destruct HN as [? Hφ | ? Hφ (? & TR & HW')].
      constructor; now rewrite EQ.
      econstructor 2.
      now rewrite EQ.
      trans_step EQ TR; eexists; split; eauto.
      eapply cih. symmetry; eauto. eauto.
  Qed.

  Instance AW_bisim φ ψ :
    good φ ->
    good ψ ->
    good (AW φ ψ).
  Proof.
    intros HG HG' s t EQ; split; intros HN.
    - revert s t EQ HN.
      unfold AW; coinduction r cih; intros;
        step in HN; cbn in HN; destruct HN as [? Hφ | ? Hφ Hp Hn].
      constructor; now rewrite <- EQ.
      econstructor 2.
      now rewrite <- EQ.
      now rewrite <- EQ.
      intros ? TR.
      trans_step EQ TR; eauto.
      eapply cih.
      symmetry; eauto.
      eauto.
    - revert s t EQ HN.
      unfold AW; coinduction r cih; intros;
        step in HN; cbn in HN; destruct HN as [? Hφ | ? Hφ Hp Hn].
      constructor; now rewrite EQ.
      econstructor 2.
      now rewrite EQ.
      now rewrite EQ.
      intros ? TR.
      trans_step EQ TR; eauto.
 Qed.

  Instance AwW_bisim φ ψ :
    good φ ->
    good ψ ->
    good (AwW φ ψ).
  Proof.
    intros HG HG' s t EQ; split; intros HN.
    - revert s t EQ HN.
      unfold AwW; coinduction r cih; intros;
        step in HN; cbn in HN; destruct HN as [? Hφ | ? Hφ Hn].
      constructor; now rewrite <- EQ.
      econstructor 2.
      now rewrite <- EQ.
      intros ? TR.
      trans_step EQ TR; eauto.
      eapply cih.
      symmetry; eauto.
      eauto.
    - revert s t EQ HN.
      unfold AwW; coinduction r cih; intros;
        step in HN; cbn in HN; destruct HN as [? Hφ | ? Hφ Hn].
      constructor; now rewrite EQ.
      econstructor 2.
      now rewrite EQ.
      intros ? TR.
      trans_step EQ TR; eauto.
  Qed.

  Lemma sat_bisim (φ : Formula) : good (satF φ).
  Proof.
    induction φ;
      eauto using
        Now_bisim, And_bisim, Or_bisim, Not_bisim, Impl_bisim,
      EX_bisim, AwX_bisim, AX_bisim, EF_bisim, AwF_bisim, AF_bisim, EG_bisim, AwG_bisim, AG_bisim, EU_bisim, AwU_bisim, AU_bisim, EW_bisim, AwW_bisim, AW_bisim.
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
  Definition dead : formula := AwX (Now false_fact).
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
