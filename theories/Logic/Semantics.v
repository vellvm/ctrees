(*|
=========================================
Modal logics over kripke semantics
=========================================
|*)
From Coq Require Import
         Basics
         FunctionalExtensionality
         Classes.RelationPairs.

From Coinduction Require Import
  coinduction lattice.

From ExtLib Require Import
  Structures.Monad
  Data.Monads.StateMonad.

From CTree Require Import
  Events.Core
  Events.WriterE
  Utils.Utils.

From CTree Require Export
  Logic.Kripke.

Set Implicit Arguments.
Generalizable All Variables.

(*| CTL logic based on kripke semantics |*)
Section Ctl.
  Context `{KMS: Kripke M W} {X: Type} (strong: bool).  
  Notation MP := (M X -> World W -> Prop).
  Local Open Scope ctl_scope.

  (*| Shallow strong/weak forall [next] modality |*)
  Definition cax (p: MP) (t: M X) (w: World W): Prop :=    
    (if strong then
       can_step t w
     else True) /\ forall t' w', [t,w] ↦ [t', w'] -> p t' w'.
  
  Definition cex(p: MP) (t: M X) (w: World W): Prop :=
    exists t' w', [t, w] ↦ [t', w'] /\ p t' w'.
  
  Hint Unfold cax cex: core.

  Unset Elimination Schemes.
  (* Forall strong until *)
  Inductive cau (p q: MP): MP :=
  | MatchA: forall t w,       
      q t w ->    (* Matches [q] now; done *)
      cau p q t w
  | StepA:  forall t w,
      p t w ->    (* Matches [p] now; steps to [m'] *)
      cax (cau p q) t w ->
      cau p q t w.

  (* Exists strong until *)
  Inductive ceu(p q: MP): MP :=
  | MatchE: forall t w,
      q t w ->    (* Matches [q] now; done *)
      ceu p q t w
  | StepE: forall t w,
      p t w ->    (* Matches [p] now; steps to [m'] *)
      cex (ceu p q) t w ->
      ceu p q t w.

  (* Custom induction schemes for [cau, ceu] *)
  Definition cau_ind :
    forall [p q: MP] (P : MP),
      (forall t w, q t w -> P t w) -> (* base *)
      (forall t w,
          p t w ->          (* [p] now*)
          cax (cau p q) t w ->
          cax P t w ->
         P t w) ->
      forall t w, cau p q t w -> P t w :=
    fun p q P Hbase Hstep =>
      fix F (t : M X) (w: World W) (c : cau p q t w) {struct c}: P t w :=
      match c with
      | MatchA _ _ t w y => Hbase t w y
      | @StepA _ _ t w Hp (conj Hs HtrP) =>
          Hstep t w Hp
            (conj Hs HtrP)
            (conj Hs (fun t' w' tr => F t' w' (HtrP t' w' tr)))
      end.

  Definition ceu_ind :
    forall [p q: MP] (P : MP),
      (forall t w, q t w -> P t w) -> (* base *)
      (forall t w,
          p t w ->          (* [p] now*)
          cex (ceu p q) t w ->
          cex P t w ->
         P t w) ->
      forall t w, ceu p q t w -> P t w :=
    fun p q P Hbase Hstep =>
      fix F (t : M X) (w: World W) (c : ceu p q t w) {struct c}: P t w :=
      match c with
      | MatchE _ _ t w y => Hbase t w y
      | @StepE _ _ t w y (ex_intro _ t' (ex_intro _ w' (conj tr h))) =>
          Hstep t w y
            (ex_intro _ t'
               (ex_intro _ w'
                  (conj tr h))) (ex_intro _  t' (ex_intro _ w' (conj tr (F t' w' h))))
      end.
  Set Elimination Schemes.
  
  (* Forall release *)
  Variant carF (R p q: MP): MP :=
  | RMatchA: forall t w,       
      q t w ->  (* Matches [q] now; done *)
      p t w ->  (* Matches [p] as well *)
      carF R p q t w
  | RStepA:  forall t w,
      p t w ->    (* Matches [p] now; steps to (t', s') *)
      cax R t w ->
      carF R p q t w.

  (* Exists release *)
  Variant cerF (R p q: MP): MP :=
  | RMatchE: forall t w,
      q t w ->       (* Matches [q] now; done *)
      p t w ->       (* Matches [p] as well *)
      cerF R p q t w
  | RStepE: forall t w,
      p t w ->    (* Matches [p] now; steps to (t', s') *)
      cex R t w ->
      cerF R p q t w.

  Hint Constructors cau ceu carF cerF: core.

  (*| Global (coinductives) |*)
  Program Definition car_: mon (MP -> MP -> MP) :=
    {| body := fun R p q m => carF (R p q) p q m |}.
  Next Obligation.
    repeat red; unfold impl; intros.
    destruct H0; auto; cbn in H0.
    apply RStepA; unfold cax in *; intuition.
  Qed.
  
  Program Definition cer_: mon (MP -> MP -> MP) :=
    {| body := fun R p q m => cerF (R p q) p q m |}.
  Next Obligation.
    repeat red; unfold impl.
    intros.
    destruct H0.
    - now apply RMatchE.
    - destruct H1 as (t' & w' & TR' & H').
      apply RStepE; auto.
      exists t', w'; auto.
  Qed.      

End Ctl.

Inductive ctlf (W: Type) `{HW: Encode W} : Type :=
  | CBase (p : World W -> Prop): ctlf
  | CAnd    : ctlf -> ctlf -> ctlf
  | COr     : ctlf -> ctlf -> ctlf
  | CImpl   : ctlf -> ctlf -> ctlf
  | CAX     : ctlf -> ctlf
  | CWX     : ctlf -> ctlf     
  | CEX     : ctlf -> ctlf
  | CAU     : ctlf -> ctlf -> ctlf
  | CWU     : ctlf -> ctlf -> ctlf
  | CEU     : ctlf -> ctlf -> ctlf
  | CAR     : ctlf -> ctlf -> ctlf
  | CWR     : ctlf -> ctlf -> ctlf
  | CER     : ctlf -> ctlf -> ctlf.

Arguments ctlf W {HW}.

(* Entailment inductively on formulas *)
Fixpoint entailsF `{KMS: Kripke M W} {X}
  (φ: ctlf W):  M X -> World W -> Prop :=
    match φ with
    | CBase  p  => fun _ => p
    | CAnd  φ ψ => fun t w => (entailsF φ t w) /\ (entailsF ψ t w)
    | COr   φ ψ => fun t w => (entailsF φ t w) \/ (entailsF ψ t w)
    | CImpl φ ψ => fun t w => (entailsF φ t w) -> (entailsF ψ t w)
    | CAX   φ   => cax true (entailsF φ)
    | CWX   φ   => cax false (entailsF φ)
    | CEX   φ   => cex (entailsF φ)
    | CAU   φ ψ => cau true (entailsF φ) (entailsF ψ)
    | CWU   φ ψ => cau false (entailsF φ) (entailsF ψ)
    | CEU   φ ψ => ceu (entailsF φ) (entailsF ψ)
    | CAR   φ ψ => gfp (car_ true) (entailsF φ) (entailsF ψ)
    | CWR   φ ψ => gfp (car_ false) (entailsF φ) (entailsF ψ)
    | CER   φ ψ => gfp cer_ (entailsF φ) (entailsF ψ)
    end.

Module CtlNotations.

  Local Open Scope ctl_scope. 
  Delimit Scope ctl_scope with ctl.
  
  Notation "<( e )>" := e (at level 0, e custom ctl at level 95) : ctl_scope.
  Notation "( x )" := x (in custom ctl, x at level 99) : ctl_scope.
  Notation "{ x }" := x (in custom ctl at level 0, x constr): ctl_scope.
  Notation "x" := x (in custom ctl at level 0, x constr at level 0) : ctl_scope.
  Notation " t , w  |= φ " := (entailsF φ t w) (in custom ctl at level 80,
                              φ custom ctl,
                              right associativity): ctl_scope.

  Notation "|- φ " := (entailsF φ) (in custom ctl at level 80,
                                       φ custom ctl, only parsing): ctl_scope.

  (* Temporal syntax: base *)
  Notation "'now' p" := (CBase p) (in custom ctl at level 74): ctl_scope.
  Notation "'pure'" := (CBase (fun w => w = Pure)) (in custom ctl at level 74): ctl_scope.
  Notation "'vis' R" := (CBase (vis_with R)) (in custom ctl at level 74): ctl_scope.
  Notation "'finish' R" := (CBase (finish_with R)) (in custom ctl at level 74): ctl_scope.
  Notation "'done' R" := (CBase (done_with R)) (in custom ctl at level 74): ctl_scope.
  Notation "'done=' r w" := (CBase (done_with (fun r' w' => r = r' /\ w = w')))
                              (in custom ctl at level 74): ctl_scope.

  Notation "'finishW' \ v s , y " :=
    (CBase (finish_with (fun pat : writerE _ =>
                           let 'Log v as x := pat
                  return (rel (encode x) (unit * _)) in
                  fun 'tt '(tt, s) => y)))
      (in custom ctl at level 75,
          v binder,
          s binder,
          y constr, left associativity): ctl_scope.

  Notation "⊤" := (CBase (fun _ => True)) (in custom ctl at level 76): ctl_scope.
  Notation "⊥" := (CBase (fun _ => False)) (in custom ctl at level 76): ctl_scope.
  
  (* Temporal syntax: inductive *)
  Notation "'EX' p" := (CEX p) (in custom ctl at level 75): ctl_scope.
  Notation "'AX' p" := (CAX p) (in custom ctl at level 75): ctl_scope.
  Notation "'WX' p" := (CWX p) (in custom ctl at level 75): ctl_scope.

  Notation "p 'EU' q" := (CEU p q) (in custom ctl at level 75): ctl_scope.
  Notation "p 'AU' q" := (CAU p q) (in custom ctl at level 75): ctl_scope.
  Notation "p 'WU' q" := (CWU p q) (in custom ctl at level 75): ctl_scope.
  
  Notation "p 'ER' q" := (CER p q) (in custom ctl at level 75): ctl_scope.
  Notation "p 'AR' q" := (CAR p q) (in custom ctl at level 75): ctl_scope.
  Notation "p 'WR' q" := (CWR p q) (in custom ctl at level 75): ctl_scope.
  
  Notation "'EF' p" := (CEU (CBase (fun _=> True)) p) (in custom ctl at level 74): ctl_scope.
  Notation "'AF' p" := (CAU (CBase (fun _=> True)) p) (in custom ctl at level 74): ctl_scope.
  Notation "'WF' p" := (CWU (CBase (fun _=> True)) p) (in custom ctl at level 74): ctl_scope.
  Notation "'EG' p" := (CER p (CBase (fun _=>False))) (in custom ctl at level 74): ctl_scope.
  Notation "'AG' p" := (CAR p (CBase (fun _=>False))) (in custom ctl at level 74): ctl_scope.
  Notation "'WG' p" := (CWR p (CBase (fun _=>False))) (in custom ctl at level 74): ctl_scope.
  
  (* Propositional syntax *)
  Notation "p '/\' q" := (CAnd p q) (in custom ctl at level 77, left associativity): ctl_scope.
  Notation "p '\/' q" := (COr p q) (in custom ctl at level 77, left associativity): ctl_scope.
  Notation "p '->' q" := (CImpl p q)
                           (in custom ctl at level 78, right associativity): ctl_scope.
  Notation " ¬ p" := (CImpl p (CBase (fun _ => False))) (in custom ctl at level 76): ctl_scope.
  Notation "p '<->' q" := (CAnd (CImpl p q) (CImpl q p)) (in custom ctl at level 77): ctl_scope.

  (* Companion notations *)
  Notation car := (gfp (car_ true)).
  Notation cwr := (gfp (car_ false)).
  Notation cer := (gfp cer_).
  Notation cart := (t (car_ true)).
  Notation cwrt := (t (car_ false)).
  Notation cert := (t cer_).
  Notation carbt := (bt (car_ true)).
  Notation cwrbt := (bt (car_ false)).
  Notation cerbt := (bt cer_).
  Notation carT := (T (car_ true)).
  Notation cwrT := (T (car_ false)).
  Notation cerT := (T cer_).
  Notation carbT := (bT (car_ true)).
  Notation cwrbT := (bT (car_ false)).
  Notation cerbT := (bT cer_).
  #[global] Hint Constructors ceu cau carF cerF: ctl.
End CtlNotations.

Import CtlNotations.
Local Open Scope ctl_scope.

(*| Base constructors of logical formulas |*)
Lemma ctl_now `{KMS: Kripke M W} X: forall (t: M X) (w: World W) (φ: World W -> Prop),
    <( t, w |= now φ )> <-> φ w.
Proof. unfold entailsF; now cbn. Qed.
Global Hint Resolve ctl_now: ctl.

Lemma ctl_pure `{KMS: Kripke M W} X: forall (t: M X) (w: World W),
    <( t, w |= pure )> <-> w = Pure.
Proof. unfold entailsF; now cbn. Qed.
Global Hint Resolve ctl_pure: ctl.

Lemma ctl_vis `{KMS: Kripke M W} X: forall (t: M X) (w: World W) φ,
    <( t, w |= vis φ )> <-> vis_with φ w. 
Proof. unfold entailsF; now cbn. Qed.
Global Hint Resolve ctl_vis: ctl.

Lemma ctl_done `{KMS: Kripke M W} X: forall (t: M X) (w: World W) (φ: X -> World W -> Prop),
    <( t, w |= done φ )> <-> done_with φ w.
Proof. unfold entailsF; now cbn. Qed.
Global Hint Resolve ctl_done: ctl.

Lemma ctl_done_eq `{KMS: Kripke M W} X: forall (t: M X) (w: World W) (r:X),
    <( t, w |= done= r w )> <-> done_with (fun r' w' => r=r' /\ w=w') w.
Proof. unfold entailsF; now cbn. Qed.
Global Hint Resolve ctl_done_eq: ctl.

Lemma ctl_finish `{KMS: Kripke M W} X: forall (t: M X) (w: World W) φ,
    <( t, w |= finish φ )> <-> @finish_with W _ X φ w.
Proof. unfold entailsF; now cbn. Qed.
Global Hint Resolve ctl_finish: ctl.

(*| AX, WX, EX unfold |*)
Lemma ctl_ax `{KMS: Kripke M W} X: forall (t: M X) (w: World W) p,
    <( t, w |= AX p )> <-> can_step t w /\ forall t' w', [t, w] ↦ [t',w'] -> <( t',w' |= p )>.
Proof.
  intros; split; intro H'; repeat destruct H'.
  - split; eauto with ctl.
  - unfold entailsF, cax; split; eauto with ctl.
Qed.

Lemma ctl_wx `{KMS: Kripke M W} X: forall (t: M X) (w: World W) p,
    <( t,w |= WX p )> <-> forall t' w', [t,w] ↦ [t',w'] -> <( t',w' |= p )>.
Proof.
  intros; split; intro H'; repeat destruct H'.
  - apply H0. 
  - unfold entailsF, cax; split; auto.
Qed.

Lemma ctl_ex `{KMS: Kripke M W} X: forall (t: M X) (w: World W) p,
    <( t,w |= EX p )> <-> exists t' w', [t,w] ↦ [t',w'] /\ <( t',w' |= p )>.
Proof.
  intros; split; intro H; repeat destruct H.
  - now exists x, x0.
  - unfold entailsF, cex; exists x, x0; split; auto.
Qed.
Global Hint Resolve ctl_ax ctl_ex ctl_wx: ctl.

(* [AX φ] is stronger than [EX φ] *)
Lemma ctl_ax_ex `{KMS: Kripke M W} X: forall (t: M X) (w: World W) p,
    <( t, w |= AX p )> -> <( t, w |= EX p )>.
Proof.
  unfold cex, cax; intros * H.
  rewrite ctl_ax in H.
  destruct H.
  destruct H as (m' & w' & TR).
  exists m', w'; auto.
Qed.

(* [AF φ] is stronger than [EF φ] *)
Lemma ctl_af_ef `{KMS: Kripke M W} X: forall (t: M X) (w: World W) p,
    <( t, w |= AF p )> -> <( t, w |= EF p )>.
Proof.
  intros. 
  unfold entailsF in H; induction H.
  - now apply MatchE. 
  - destruct H0 as ((m' & ? & ?) & ?).
    destruct H1 as ((? & ? & ?) &  ?).
    apply StepE; auto.
    exists x0, x1; split; auto.
    now apply H3.
Qed.

(* [AF φ] is stronger than [WF φ] *)
Lemma ctl_af_wf `{KMS: Kripke M W} X: forall (t: M X) (w: World W) p,
    <( t, w |= AF p )> -> <( t, w |= WF p )>.
Proof.
  intros. 
  unfold entailsF in H; induction H.
  - now apply MatchA.
  - destruct H0 as ((m' & ? & ?) & ?).
    destruct H1 as ((? & ? & ?) & ?).
    apply StepA; trivial.
    unfold cax; split; auto.
Qed.
  
(*| Bot is false |*)
Lemma ctl_sound `{KMS: Kripke M W} X: forall (t: M X) (w: World W),
    ~ <( t, w |= ⊥ )>.
Proof. intros * []. Qed.

(*| Ex-falso |*)
Lemma ctl_ex_falso `{KMS: Kripke M W} X: forall (t: M X) (w: World W) p,
    <( t, w |= ⊥ -> p )>.
Proof. intros; unfold entailsF; intro CONTRA; contradiction. Qed.

(*| Top is True |*)
Lemma ctl_top `{KMS: Kripke M W} X: forall (t: M X) (w: World W),
    <( t, w |= ⊤ )>.
Proof. reflexivity. Qed. 

(*| Cannot exist path such that eventually Bot |*)
Lemma ctl_sound_ef `{KMS: Kripke M W} X: forall (t: M X) (w: World W),
    ~ <( t, w |= EF ⊥ )>.
Proof.
  intros * Contra.
  unfold entailsF in Contra.
  induction Contra.
  - contradiction.
  - destruct H1 as (? & ? & ? & ?).
    contradiction.
Qed.

(*| Cannot have all paths such that eventually always Bot |*)
Lemma ctl_sound_af `{KMS: Kripke M W} X: forall (t: M X) (w: World W),
    ~ <( t, w |= AF ⊥ )>.
Proof.
  intros * Contra.
  apply ctl_af_ef in Contra.
  apply ctl_sound_ef in Contra.
  contradiction.
Qed.

(*| Semantic equivalence of formulas |*)
Definition equiv_ctl {M} `{HE: Encode W} {K: Kripke M W}{X}: relation (ctlf W)
  := fun p q => forall (t: M X) (w: World W), entailsF p t w <-> entailsF q t w.

Infix "⩸" := equiv_ctl (at level 58, left associativity): ctl_scope.

Section EquivCtlEquivalence.
  Context {M: Type -> Type} `{HE: Encode W} {K: Kripke M W}
    {X: Type}.
  Notation equiv_ctl := (@equiv_ctl M W HE K X).

  Global Instance Equivalence_equiv_ctl:
    Equivalence equiv_ctl.
  Proof.
    constructor.
    - intros P x; reflexivity.
    - intros P Q H' x; symmetry; auto.
    - intros P Q R H0' H1' x; etransitivity; auto.
  Qed.

  (*| [equiv_ctl] proper under [equiv_ctl] |*)
  Global Add Parametric Morphism : equiv_ctl with signature
         equiv_ctl ==> equiv_ctl ==> iff as equiv_ctl_equiv.
  Proof.
    intros p q EQpq p' q' EQpq'; split;
      intros EQpp'; split; intro BASE; cbn in *.
    - symmetry in EQpq'; apply EQpq'.
      symmetry in EQpp'; apply EQpp'.
      now apply EQpq.
    - symmetry in EQpq'; apply EQpq.
      apply EQpp'.
      now apply EQpq'.
    - apply EQpq'.
      symmetry in EQpp'; apply EQpp'.
      symmetry in EQpq; now apply EQpq.
    - apply EQpq.
      apply EQpp'.
      symmetry in EQpq'; now apply EQpq'.
  Qed.
End EquivCtlEquivalence.
