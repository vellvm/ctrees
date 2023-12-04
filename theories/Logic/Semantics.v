(*|
=========================================
Modal logics over kripke semantics
=========================================
|*)
From Coq Require Import
  Basics
  Classes.RelationPairs.

From Coinduction Require Import
  coinduction lattice.

From ExtLib Require Import
  Structures.Monad
  Data.Monads.StateMonad.

From CTree Require Import
  Utils.Utils.

From CTree Require Export
  Logic.Kripke.

Set Implicit Arguments.
Generalizable All Variables.

(*| CTL logic based on kripke semantics |*)
Section Ctl.
  Context `{KMS: @Kripke M W} {X: Type}.

  Notation MP := (M X * W -> Prop).

  Definition cax(p: MP) : MP :=
    fun m => can_step m /\ forall m', ktrans m m' -> p m'.

  Definition cex(p: MP) : MP :=
    fun m => exists m', ktrans m m' /\ p m'.
  Hint Unfold cax cex: core.

  Unset Elimination Schemes.
  (* Forall strong until *)
  Inductive cau(p q: MP): MP :=
  | MatchA: forall m,       
      q m ->  (* Matches [q] now; done *)
      cau p q m
  | StepA:  forall m,
      p m ->    (* Matches [p] now; steps to [m'] *)
      cax (cau p q) m ->
      cau p q m.

  (* Exists strong until *)
  Inductive ceu(p q: MP): MP :=
  | MatchE: forall m,
      q m ->       (* Matches [q] now; done *)
      ceu p q m
  | StepE: forall m,
      p m ->    (* Matches [p] now; steps to [m'] *)
      cex (ceu p q) m ->
      ceu p q m.

  (* Custom induction schemes for [cau, ceu] *)
  Definition cau_ind :
    forall [p q: MP] (P : MP),
      (forall m, q m -> P m) -> (* base *)
      (forall m,
          p m ->          (* [p] now*)
          cax (cau p q) m ->
          cax P m ->
         P m) ->
      forall m, cau p q m -> P m :=
    fun p q P Hbase Hstep =>
      fix F (t : M X * W) (c : cau p q t) {struct c}: P t :=
      match c with
      | MatchA _ _ (t,w) y => Hbase (t,w) y
      | @StepA _ _ (t,w) Hp (conj Hs HtrP) =>
          Hstep (t,w) Hp
            (conj Hs HtrP)
            (conj Hs (fun m' tr => F m' (HtrP m' tr)))
      end.

  Definition ceu_ind :
    forall [p q: MP] (P : MP),
      (forall m, q m -> P m) -> (* base *)
      (forall m,
          p m ->          (* [p] now*)
          cex (ceu p q) m ->
          cex P m ->
         P m) ->
      forall m, ceu p q m -> P m :=
    fun p q P Hbase Hstep =>
      fix F (t : M X * W) (c : ceu p q t) {struct c}: P t :=
      match c with
      | MatchE _ _ m y => Hbase m y
      | @StepE _ _ m y (ex_intro _ m' (conj tr h)) =>
          Hstep m y (ex_intro _ m' (conj tr h)) (ex_intro _  m' (conj tr (F m' h)))
      end.
  Set Elimination Schemes.
  
  (* Forall release *)
  Variant carF (R p q: MP): MP :=
  | RMatchA: forall m,       
      q m ->  (* Matches [q] now; done *)
      p m ->  (* Matches [p] as well *)
      carF R p q m
  | RStepA:  forall m,
      p m ->    (* Matches [p] now; steps to (t', s') *)
      cax R m ->
      carF R p q m.
                          
  (* Exists release *)
  Variant cerF (R p q: MP): MP :=
  | RMatchE: forall m,
      q m ->       (* Matches [q] now; done *)
      p m ->       (* Matches [p] as well *)
      cerF R p q m
  | RStepE: forall m,
      p m ->    (* Matches [p] now; steps to (t', s') *)
      cex R m ->
      cerF R p q m.

  Hint Constructors cau ceu carF cerF: core.

  (*| Global (coinductives) |*)
  Program Definition car_: mon (MP -> MP -> MP) :=
    {| body := fun R p q m => carF (R p q) p q m |}.
  Next Obligation.
    repeat red; unfold impl; intros.
    destruct H0; auto; cbn in H1.
    apply RStepA; unfold cax in *; intuition.
  Qed.
  
  Program Definition cer_: mon (MP -> MP -> MP) :=
    {| body := fun R p q m => cerF (R p q) p q m |}.
  Next Obligation.
    repeat red; unfold impl.
    intros.
    destruct H0.
    - now apply RMatchE.
    - destruct H1 as (m' & TR' & H').
      apply RStepE; eauto.
  Qed.      
  
  Inductive CtlFormula: Type :=
  | CNow (p : W -> Prop): CtlFormula
  | CDone (p: forall {X: Type}, X -> W -> Prop): CtlFormula
  | CAnd    : CtlFormula -> CtlFormula -> CtlFormula
  | COr     : CtlFormula -> CtlFormula -> CtlFormula
  | CImpl   : CtlFormula -> CtlFormula -> CtlFormula
  | CAX     : CtlFormula -> CtlFormula
  | CEX     : CtlFormula -> CtlFormula
  | CAU     : CtlFormula -> CtlFormula -> CtlFormula
  | CEU     : CtlFormula -> CtlFormula -> CtlFormula
  | CAR     : CtlFormula -> CtlFormula -> CtlFormula
  | CER     : CtlFormula -> CtlFormula -> CtlFormula.

  (* Entailment inductively on formulas *)
  Fixpoint entailsF (φ: CtlFormula)(m: M X * W): Prop :=
    match φ with
    | CNow   p  => p (snd m)
    | CDone  p  => exists (x: X), mequ X (fst m) (ret x) /\
                              p X x (snd m)
    | CAnd  φ ψ => (entailsF φ m) /\ (entailsF ψ m)
    | COr   φ ψ => (entailsF φ m) \/ (entailsF ψ m)
    | CImpl φ ψ => (entailsF φ m) -> (entailsF ψ m)
    | CAX   φ   => cax (entailsF φ) m
    | CEX   φ   => cex (entailsF φ) m
    | CAU   φ ψ => cau (entailsF φ) (entailsF ψ) m
    | CEU   φ ψ => ceu (entailsF φ) (entailsF ψ) m
    | CAR   φ ψ => gfp car_ (entailsF φ) (entailsF ψ) m
    | CER   φ ψ => gfp cer_ (entailsF φ) (entailsF ψ) m
    end.
  Arguments entailsF: simpl never.

End Ctl.

Arguments CtlFormula: clear implicits.

Module CtlNotations.

  Local Open Scope ctl_scope. 
  Delimit Scope ctl_scope with ctl.
  
  Notation "<( e )>" := e (at level 0, e custom ctl at level 95) : ctl_scope.
  Notation "( x )" := x (in custom ctl, x at level 99) : ctl_scope.
  Notation "{ x }" := x (in custom ctl at level 0, x constr): ctl_scope.
  Notation "x" := x (in custom ctl at level 0, x constr at level 0) : ctl_scope.
  Notation "m |= φ " := (entailsF φ m) (in custom ctl at level 80,
                              φ custom ctl,
                              right associativity): ctl_scope.

  Notation "|- φ " := (entailsF φ) (in custom ctl at level 80,
                                       φ custom ctl, only parsing): ctl_scope.

  (* Temporal *)
  Notation "'now' p" := (CNow p) (in custom ctl at level 79): ctl_scope.
  Notation "'done' p" := (CDone p) (in custom ctl at level 79): ctl_scope.
  Notation "'EX' p" := (CEX p) (in custom ctl at level 75): ctl_scope.
  Notation "'AX' p" := (CAX p) (in custom ctl at level 75): ctl_scope.

  Notation "p 'EU' q" := (CEU p q) (in custom ctl at level 75): ctl_scope.
  Notation "p 'AU' q" := (CAU p q) (in custom ctl at level 75): ctl_scope.
  Notation "p 'ER' q" := (CER p q) (in custom ctl at level 75): ctl_scope.
  Notation "p 'AR' q" := (CAR p q) (in custom ctl at level 75): ctl_scope.
  Notation "'EF' p" := (CEU (CNow (fun _=> True)) p) (in custom ctl at level 74): ctl_scope.
  Notation "'AF' p" := (CAU (CNow (fun _=> True)) p) (in custom ctl at level 74): ctl_scope.
  Notation "'EG' p" := (CER p (CNow (fun _=>False))) (in custom ctl at level 74): ctl_scope.
  Notation "'AG' p" := (CAR p (CNow (fun _=>False))) (in custom ctl at level 74): ctl_scope.
  
  (* Propositional *)
  Notation "p '/\' q" := (CAnd p q) (in custom ctl at level 77, left associativity): ctl_scope.
  Notation "p '\/' q" := (COr p q) (in custom ctl at level 77, left associativity): ctl_scope.
  Notation "p '->' q" := (CImpl p q) (in custom ctl at level 78, right associativity): ctl_scope.
  Notation " ¬ p" := (CImpl p (CNow (fun _ => False))) (in custom ctl at level 76): ctl_scope.
  Notation "p '<->' q" := (CAnd (CImpl p q) (CImpl q p)) (in custom ctl at level 77): ctl_scope.
  Notation "⊤" := (CNow (fun _ => True)) (in custom ctl at level 76): ctl_scope.
  Notation "⊥" := (CNow (fun _ => False)) (in custom ctl at level 76): ctl_scope.

  (* Companion notations *)
  Notation car := (gfp car_).
  Notation cer := (gfp cer_).
  Notation cart := (t car_).
  Notation cert := (t cer_).
  Notation carbt := (bt car_).
  Notation cerbt := (bt cer_).
  Notation carT := (T car_).
  Notation cerT := (T cer_).
  Notation carbT := (bT car_).
  Notation cerbT := (bT cer_).
  #[global] Hint Constructors ceu cau carF cerF: core.
End CtlNotations.

Import CtlNotations.
Local Open Scope ctl_scope.

Lemma ctl_now `{KMS: Kripke M W} X: forall (m: M X * W) φ,
    <( m |= now φ )> <-> φ (snd m).
Proof. unfold entailsF; now cbn. Qed.

Global Hint Unfold can_step: core.

(*| AX, EX unfold |*)
Lemma ctl_ax `{KMS: Kripke M W} X: forall (m: M X * W) p,
    <( m |= AX p )> <-> can_step m /\ forall m', m ↦ m' -> <( m' |= p )>.
Proof.
  intros; split; intro H; repeat destruct H.
  - split; eauto.
  - destruct m; cbn in H.
    unfold entailsF, cax; split; eauto.
Qed.

Lemma ctl_ax_inv `{KMS: Kripke M W} X: forall (m: M X *W) p,
    <( m |= AX p )> -> forall m', m ↦ m' -> <( m' |= p )>.
Proof.
  intros.
  destruct H.
  now apply H1.
Qed.

Lemma ctl_ex `{KMS: Kripke M W} X: forall (m: M X * W) p,
    <( m |= EX p )> <-> exists m', m ↦ m' /\ <( m' |= p )>.
Proof.
  intros; split; intro H; repeat destruct H.
  - now exists x.
  - unfold entailsF, cex; exists x; split; auto.
Qed.

Lemma ctl_af_match `{KMS: Kripke M W} X: forall (m: M X * W) p,
    <( m |= p )> -> <( m |= AF p )>.
Proof. intros. now apply MatchA. Qed.

Lemma ctl_ef_match `{KMS: Kripke M W} X: forall (m: M X * W) p,
    <( m |= p )> -> <( m |= EF p )>.
Proof. intros. now apply MatchE. Qed.

Global Hint Resolve ctl_ax ctl_ex ctl_af_match ctl_ef_match: core.

(* [AX φ] is stronger than [EX φ] *)
Lemma ctl_ax_ex `{KMS: Kripke M W} X: forall (m: M X *W) p,
    <( m |= AX p )> -> <( m |= EX p )>.
Proof.
  unfold cex, cax; intros * H.
  rewrite ctl_ax in H.
  destruct m, H; cbn in H.
  destruct H as (m' & w' & TR).
  specialize (H0 (m',w') TR).
  exists (m', w'); auto.
Qed.

(* [AF φ] is stronger than [EF φ] *)
Lemma ctl_af_ef `{KMS: Kripke M W} X: forall (m: M X*W) p,
    <( m |= AF p )> -> <( m |= EF p )>.
Proof.
  intros. 
  unfold entailsF in H; induction H.
  - now apply MatchE.
  - destruct m.
    destruct H1 as ((m' & ? & ?) & ?).
    destruct H0 as ((? & ? & ?) & ?).
    apply StepE; auto.
    exists (x0, x1); split; auto.
    now apply H2.
Qed.

(*| Induction lemmas |*)
Lemma ctl_au_ind `{KMS: Kripke M W} X: 
  forall [p q: CtlFormula W] (P : M X * W -> Prop),
    (forall m, <( m |= q )> -> P m) -> (* base *)
    (forall m,
        <( m |= p )> ->          (* [p] now*)
        <( m |= AX (p AU q))> ->
        cax P m ->
        P m) ->
    forall m, <( m |= p AU q )> -> P m.
Proof. intros; induction H1; auto. Qed.

Lemma ctl_eu_ind `{KMS: Kripke M W} X: 
  forall [p q: CtlFormula W] (P : M X * W -> Prop),
    (forall m, <( m |= q )> -> P m) -> (* base *)
    (forall m,
        <( m |= p )> ->          (* [p] now*)
        <( m |= EX (p EU q))> ->
        cex P m ->
        P m) ->
    forall m, <( m |= p EU q )> -> P m.
Proof. intros; induction H1; auto. Qed.
  
(*| Bot is false |*)
Lemma ctl_sound `{KMS: Kripke M W} X: forall (m: M X*W),
    ~ <( m |= ⊥ )>.
Proof. intros _ []. Qed.

(*| Ex-falso |*)
Lemma ctl_ex_falso `{KMS: Kripke M W} X: forall (m: M X*W) p,
    <( m |= ⊥ -> p )>.
Proof.
  intros; unfold entailsF; intro CONTRA; contradiction.
Qed. 

(*| Top is True |*)
Lemma ctl_top `{KMS: Kripke M W} X: forall (m: M X*W),
    <( m |= ⊤ )>.
Proof. reflexivity. Qed. 

(*| Cannot exist path such that eventually Bot |*)
Lemma ctl_sound_ef `{KMS: Kripke M W} X: forall (m: M X*W),
    ~ <( m |= EF ⊥ )>.
Proof.
  intros m.
  intro Contra.  
  unfold entailsF in Contra.
  induction Contra.
  - contradiction.
  - destruct H1 as (? & ? & ?).
    contradiction.
Qed.

(*| Cannot have all paths such that eventually always Bot |*)
Lemma ctl_sound_af `{KMS: Kripke M W} X: forall (m: M X*W),
    ~ <( m |= AF ⊥ )>.
Proof.
  intros m.
  intro Contra.
  apply ctl_af_ef in Contra.
  apply ctl_sound_ef in Contra.
  contradiction.
Qed.

(*| [CtlFormula] is a contravariant functor |*)
Fixpoint ctl_contramap{X Y}(f: X -> Y) (φ: CtlFormula Y): CtlFormula X :=
  match φ with
  | CNow  p  => CNow (fun x => p (f x))
  | CDone p  => CDone (fun X z x => p X z (f x))
  | CAnd  φ ψ => CAnd (ctl_contramap f φ) (ctl_contramap f ψ)
  | COr   φ ψ => COr (ctl_contramap f φ) (ctl_contramap f ψ)
  | CImpl φ ψ => CImpl (ctl_contramap f φ) (ctl_contramap f ψ)
  | CAX   φ   => CAX (ctl_contramap f φ)
  | CEX   φ   => CEX (ctl_contramap f φ)
  | CAU   φ ψ => CAU (ctl_contramap f φ) (ctl_contramap f ψ)
  | CEU   φ ψ => CEU (ctl_contramap f φ) (ctl_contramap f ψ)
  | CAR   φ ψ => CAR (ctl_contramap f φ) (ctl_contramap f ψ)
  | CER   φ ψ => CER (ctl_contramap f φ) (ctl_contramap f ψ)
  end.

(*| [CtlFormula W] can act as a [CtlFormula (option W)] where [W] is always Some |*)
Fixpoint ctl_option{W}(φ: CtlFormula W): CtlFormula (option W) :=
  match φ with
  | CNow  p  => CNow (fun o => exists x, o = Some x /\ p x)
  | CDone p  => CDone (fun X z o => exists x, o = Some x /\ p X z x)
  | CAnd  φ ψ => CAnd (ctl_option φ) (ctl_option ψ)
  | COr   φ ψ => COr (ctl_option φ) (ctl_option ψ)
  | CImpl φ ψ => CImpl (ctl_option φ) (ctl_option ψ)
  | CAX   φ   => CAX (ctl_option φ)
  | CEX   φ   => CEX (ctl_option φ)
  | CAU   φ ψ => CAU (ctl_option φ) (ctl_option ψ)
  | CEU   φ ψ => CEU (ctl_option φ) (ctl_option ψ)
  | CAR   φ ψ => CAR (ctl_option φ) (ctl_option ψ)
  | CER   φ ψ => CER (ctl_option φ) (ctl_option ψ)
  end.

 (*| Semantic equivalence of formulas |*)
Definition equiv_ctl `{K: Kripke M W} {X}: relation (CtlFormula W) :=
  fun p q => forall (m: M X * W), entailsF p m <-> entailsF q m.

Infix "⩸" := equiv_ctl (at level 58, left associativity): ctl_scope.

Global Instance proper_ctl_option{W X} `{K:Kripke M W} `{Kripke M (option W)}:
  Proper (equiv_ctl (X:=X) (K:=K) ==> equiv_ctl (X:=X)) ctl_option.
Proof.
  unfold Proper, respectful.
(* intros x y; split; [generalize dependent y | generalize dependent x]; revert m f;
   [induction x; destruct y | induction y; destruct x]; intros; cbn in *. *)
  
(* Wow 242 goals. Need inversion lemmas like
   [equiv_ctl <( |- now p )> q -> q = <( |- now p )>]  *)
Admitted.

Global Instance Proper_ctl_contramap{X W Y}(f: Y -> W) `{K:Kripke M W} `{Kripke M Y}:
  Proper (equiv_ctl (X:=X) (K:=K) ==> equiv_ctl (X:=X)) (ctl_contramap f).
Proof.
  unfold Proper, respectful.
Admitted.

Notation "m |== φ " :=
  (entailsF (ctl_option φ) m)
    (in custom ctl at level 81,
        φ custom ctl,
        right associativity): ctl_scope.
