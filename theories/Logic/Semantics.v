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
  Utils.Utils.

From CTree Require Export
  Logic.Kripke.

Set Implicit Arguments.
Generalizable All Variables.

(*| CTL logic based on kripke semantics |*)
Section Ctl.
  Context `{KMS: Kripke M mequ W} {X: Type} (strong: bool).  
  Notation MP := (M X * World W -> Prop).

  (*| Shallow strong/weak forall [next] modality |*)
  Definition cax (p: MP) (m: M X * World W): Prop :=    
    (if strong then
       can_step m 
     else True) /\ forall m', ktrans m m' -> p m'.
  
  Definition cex(p: MP) : MP :=
    fun m => exists m', ktrans m m' /\ p m'.
  
  Hint Unfold cax cex: core.

  Unset Elimination Schemes.
  (* Forall strong until *)
  Inductive cau (p q: MP): MP :=
  | MatchA: forall m,       
      q m ->    (* Matches [q] now; done *)
      cau p q m
  | StepA:  forall m,
      p m ->    (* Matches [p] now; steps to [m'] *)
      cax (cau p q) m ->
      cau p q m.

  (* Exists strong until *)
  Inductive ceu(p q: MP): MP :=
  | MatchE: forall m,
      q m ->    (* Matches [q] now; done *)
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
      fix F (t : M X * World W) (c : cau p q t) {struct c}: P t :=
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
      fix F (t : M X * World W) (c : ceu p q t) {struct c}: P t :=
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
    - destruct H1 as (m' & TR' & H').
      apply RStepE; eauto.
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
Fixpoint entailsF `{KMS: Kripke M meq W} {X}
  (φ: ctlf W)(m: M X * World W): Prop :=
    match φ with
    | CBase  p  => p (snd m)
    | CAnd  φ ψ => (entailsF φ m) /\ (entailsF ψ m)
    | COr   φ ψ => (entailsF φ m) \/ (entailsF ψ m)
    | CImpl φ ψ => (entailsF φ m) -> (entailsF ψ m)
    | CAX   φ   => cax true (entailsF φ) m
    | CWX   φ   => cax false (entailsF φ) m
    | CEX   φ   => cex (entailsF φ) m
    | CAU   φ ψ => cau true (entailsF φ) (entailsF ψ) m
    | CWU   φ ψ => cau false (entailsF φ) (entailsF ψ) m                      
    | CEU   φ ψ => ceu (entailsF φ) (entailsF ψ) m
    | CAR   φ ψ => gfp (car_ true) (entailsF φ) (entailsF ψ) m
    | CWR   φ ψ => gfp (car_ false) (entailsF φ) (entailsF ψ) m                      
    | CER   φ ψ => gfp cer_ (entailsF φ) (entailsF ψ) m
    end.

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

  (* Temporal syntax: base *)
  Notation "'now' p" := (CBase p)
                           (in custom ctl at level 74): ctl_scope.
  Notation "'pure'" := (CBase (fun w => w = Pure))
                         (in custom ctl at level 74): ctl_scope.
  Notation "'obs' p" := (CBase (fun o => exists e x, o = Obs e x /\ p e x))
                          (in custom ctl at level 74): ctl_scope.
  Notation "'done' p" := (CBase (fun w => exists x, w = Done x /\ p x))
                             (in custom ctl at level 74): ctl_scope.
  Notation "'finish' p" := (CBase (fun w => exists e v x, w = Finish e v x /\ p e v x))
                             (in custom ctl at level 74): ctl_scope.

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
  Notation "p '->' q" := (CImpl p q) (in custom ctl at level 78, right associativity): ctl_scope.
  Notation " ¬ p" := (CImpl p (CBase (fun _ => False))) (in custom ctl at level 76): ctl_scope.
  Notation "p '<->' q" := (CAnd (CImpl p q) (CImpl q p)) (in custom ctl at level 77): ctl_scope.
  Notation "⊤" := (CBase (fun _ => True)) (in custom ctl at level 76): ctl_scope.
  Notation "⊥" := (CBase (fun _ => False)) (in custom ctl at level 76): ctl_scope.

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
Lemma ctl_now `{KMS: Kripke M meq W} X: forall (m: M X * World W) (φ: World W -> Prop),
    <( m |= now φ )> <-> φ (snd m).
Proof. unfold entailsF; now cbn. Qed.
Global Hint Resolve ctl_now: ctl.

Lemma ctl_pure `{KMS: Kripke M meq W} X: forall (m: M X * World W),
    <( m |= pure )> <-> snd m = Pure.
Proof. unfold entailsF; now cbn. Qed.
Global Hint Resolve ctl_pure: ctl.

Lemma ctl_done `{KMS: Kripke M meq W} X: forall (m: M X * World W) (φ: X -> Prop),
    <( m |= done φ )> <-> exists (x: X), snd m = Done x /\ φ x.
Proof. unfold entailsF; now cbn. Qed.
Global Hint Resolve ctl_done: ctl.

Lemma ctl_obs `{KMS: Kripke M meq W} X: forall (m: M X * World W) (φ: forall (e: W), encode e -> Prop),
    <( m |= obs φ )> <-> exists (e: W) (x: encode e), snd m = Obs e x /\ φ e x.
Proof. unfold entailsF; now cbn. Qed.
Global Hint Resolve ctl_obs: ctl.

Lemma ctl_finish `{KMS: Kripke M meq W} X: forall (m: M X * World W) (φ: forall (e: W), encode e -> X -> Prop),
    <( m |= finish φ )> <-> exists (e: W) (v: encode e) (x: X), snd m = Finish e v x /\ φ e v x.
Proof. unfold entailsF; now cbn. Qed.
Global Hint Resolve ctl_finish: ctl.

(*| AX, WX, EX unfold |*)
Lemma ctl_ax `{KMS: Kripke M meq W} X: forall (m: M X * World W) p,
    <( m |= AX p )> <-> can_step m /\ forall m', m ↦ m' -> <( m' |= p )>.
Proof.
  intros; split; intro H'; repeat destruct H'.
  - split; eauto with ctl.
  - destruct m.
    unfold entailsF, cax; split; eauto with ctl.
Qed.

Lemma ctl_wx `{KMS: Kripke M meq W} X: forall (m: M X * World W) p,
    <( m |= WX p )> <-> forall m', m ↦ m' -> <( m' |= p )>.
Proof.
  intros; split; intro H'; repeat destruct H'.
  - apply H0. 
  - unfold entailsF, cax; split; auto.
Qed.

Lemma ctl_ex `{KMS: Kripke M meq W} X: forall (m: M X * World W) p,
    <( m |= EX p )> <-> exists m', m ↦ m' /\ <( m' |= p )>.
Proof.
  intros; split; intro H; repeat destruct H.
  - now exists x.
  - unfold entailsF, cex; exists x; split; auto.
Qed.
Global Hint Resolve ctl_ax ctl_ex ctl_wx: ctl.

(* [AX φ] is stronger than [EX φ] *)
Lemma ctl_ax_ex `{KMS: Kripke M meq W} X: forall (m: M X * World W) p,
    <( m |= AX p )> -> <( m |= EX p )>.
Proof.
  unfold cex, cax; intros * H.
  rewrite ctl_ax in H.
  destruct m, H.
  destruct H as (m' & w' & TR).
  exists (m', w'); auto.
Qed.

(* [AF φ] is stronger than [EF φ] *)
Lemma ctl_af_ef `{KMS: Kripke M meq W} X: forall (m: M X * World W) p,
    <( m |= AF p )> -> <( m |= EF p )>.
Proof.
  intros. 
  unfold entailsF in H; induction H.
  - now apply MatchE. 
  - destruct m.
    destruct H0 as ((m' & ? & ?) & ?).
    destruct H1 as ((? & ? & ?) &  ?).
    apply StepE; auto.
    exists (x0, x1); split; auto.
    now apply H3.
Qed.

(* [AF φ] is stronger than [WF φ] *)
Lemma ctl_af_wf `{KMS: Kripke M meq W} X: forall (m: M X * World W) p,
    <( m |= AF p )> -> <( m |= WF p )>.
Proof.
  intros. 
  unfold entailsF in H; induction H.
  - now apply MatchA.
  - destruct m.
    destruct H0 as ((m' & ? & ?) & ?).
    destruct H1 as ((? & ? & ?) & ?).
    apply StepA; trivial.
    unfold cax; split; auto.
Qed.

(*| Induction lemmas |*)
Lemma ctl_au_ind `{KMS: Kripke M meq W} X: 
  forall [p q: ctlf W] (P : M X * World W -> Prop),
    (forall m, <( m |= q )> -> P m) -> (* base *)
    (forall m,
        <( m |= p )> ->          (* [p] now*)
        <( m |= AX (p AU q))> ->
        cax true P m ->
        P m) ->
    forall m, <( m |= p AU q )> -> P m.
Proof. intros; induction H1; auto. Qed.

Lemma ctl_wu_ind `{KMS: Kripke M meq W} X: 
  forall [p q: ctlf W] (P : M X * World W -> Prop),
    (forall m, <( m |= q )> -> P m) -> (* base *)
    (forall m,
        <( m |= p )> ->          (* [p] now*)
        <( m |= WX (p WU q))> ->
        cax false P m ->
        P m) ->
    forall m, <( m |= p WU q )> -> P m.
Proof. intros; induction H1; auto. Qed.

Lemma ctl_eu_ind `{KMS: Kripke M meq W} X: 
  forall [p q: ctlf W] (P : M X * World W -> Prop),
    (forall m, <( m |= q )> -> P m) -> (* base *)
    (forall m,
        <( m |= p )> ->          (* [p] now*)
        <( m |= EX (p EU q))> ->
        cex P m ->
        P m) ->
    forall m, <( m |= p EU q )> -> P m.
Proof. intros; induction H1; auto. Qed.
  
(*| Bot is false |*)
Lemma ctl_sound `{KMS: Kripke M meq W} X: forall (m: M X * World W),
    ~ <( m |= ⊥ )>.
Proof. intros _ []. Qed.

(*| Ex-falso |*)
Lemma ctl_ex_falso `{KMS: Kripke M meq W} X: forall (m: M X * World W) p,
    <( m |= ⊥ -> p )>.
Proof. intros; unfold entailsF; intro CONTRA; contradiction. Qed.

(*| Top is True |*)
Lemma ctl_top `{KMS: Kripke M meq W} X: forall (m: M X * World W),
    <( m |= ⊤ )>.
Proof. reflexivity. Qed. 

(*| Cannot exist path such that eventually Bot |*)
Lemma ctl_sound_ef `{KMS: Kripke M meq W} X: forall (m: M X * World W),
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
Lemma ctl_sound_af `{KMS: Kripke M mequ W} X: forall (m: M X * World W),
    ~ <( m |= AF ⊥ )>.
Proof.
  intros m.
  intro Contra.
  apply ctl_af_ef in Contra.
  apply ctl_sound_ef in Contra.
  contradiction.
Qed.

(*| Semantic equivalence of formulas |*)
Definition equiv_ctl `{K: Kripke M meq W}{X}: relation (ctlf W) :=
  fun p q => forall (m: M X * World W), entailsF p m <-> entailsF q m.

Infix "⩸" := equiv_ctl (at level 58, left associativity): ctl_scope.
