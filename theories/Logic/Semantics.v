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
  Context `{KMS: Kripke M mequ W} {X: Type} (strong: bool).

  Notation MP := (M X * option W -> Prop).

  (*| Shallow, strong? forall next |*)
  Definition cax (p: MP) : MP :=    
    fun m => (if strong then
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
      fix F (t : M X * option W) (c : cau p q t) {struct c}: P t :=
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
      fix F (t : M X * option W) (c : ceu p q t) {struct c}: P t :=
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
    destruct H2; auto; cbn in H2.
    apply RStepA; unfold cax in *; intuition.
  Qed.
  
  Program Definition cer_: mon (MP -> MP -> MP) :=
    {| body := fun R p q m => cerF (R p q) p q m |}.
  Next Obligation.
    repeat red; unfold impl.
    intros.
    destruct H2.
    - now apply RMatchE.
    - destruct H3 as (m' & TR' & H').
      apply RStepE; eauto.
  Qed.      

End Ctl.

Section Formulas.
  Context {W: Type} `{KMS: Kripke M meq W} {X: Type}.
  Inductive CtlFormula: Type :=
  | CNow (p : option W -> Prop): CtlFormula
  | CDone (p: forall {X: Type}, X -> option W -> Prop): CtlFormula
  | CAnd    : CtlFormula -> CtlFormula -> CtlFormula
  | COr     : CtlFormula -> CtlFormula -> CtlFormula
  | CImpl   : CtlFormula -> CtlFormula -> CtlFormula
  | CAX     : CtlFormula -> CtlFormula
  | CWX     : CtlFormula -> CtlFormula                             
  | CEX     : CtlFormula -> CtlFormula
  | CAU     : CtlFormula -> CtlFormula -> CtlFormula
  | CWU     : CtlFormula -> CtlFormula -> CtlFormula
  | CEU     : CtlFormula -> CtlFormula -> CtlFormula
  | CAR     : CtlFormula -> CtlFormula -> CtlFormula
  | CWR     : CtlFormula -> CtlFormula -> CtlFormula
  | CER     : CtlFormula -> CtlFormula -> CtlFormula.

  (* Entailment inductively on formulas *)
  Fixpoint entailsF (φ: CtlFormula)(m: M X * option W): Prop :=
    match φ with
    | CNow   p  => p (snd m)
    | CDone  p  => exists (x: X), meq (fst m) (ret x) /\ p X x (snd m)
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
End Formulas.

(*| Formula is parametric on state |*)
Arguments CtlFormula: clear implicits.

(*| Lots of implicit arguments |*)
Arguments entailsF {W} {M} {_} {meq} {_} {_} {X} φ m.

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

  (* Temporal syntax *)
  Notation "'nothing'" := (CNow (fun x => x = None)) (in custom ctl at level 79): ctl_scope.
  Notation "'now' p" := (CNow (fun o => exists w, o = Some w /\ p w))
                          (in custom ctl at level 79): ctl_scope.
  Notation "'done' p" := (CDone (fun X x o => exists w, o = Some w /\ p X x w))
                           (in custom ctl at level 79): ctl_scope.
  Notation "'EX' p" := (CEX p) (in custom ctl at level 75): ctl_scope.
  Notation "'AX' p" := (CAX p) (in custom ctl at level 75): ctl_scope.
  Notation "'WX' p" := (CWX p) (in custom ctl at level 75): ctl_scope.

  Notation "p 'EU' q" := (CEU p q) (in custom ctl at level 75): ctl_scope.
  Notation "p 'AU' q" := (CAU p q) (in custom ctl at level 75): ctl_scope.
  Notation "p 'WU' q" := (CWU p q) (in custom ctl at level 75): ctl_scope.
  
  Notation "p 'ER' q" := (CER p q) (in custom ctl at level 75): ctl_scope.
  Notation "p 'AR' q" := (CAR p q) (in custom ctl at level 75): ctl_scope.
  Notation "p 'WR' q" := (CWR p q) (in custom ctl at level 75): ctl_scope.
  Notation "'EF' p" := (CEU (CNow (fun _=> True)) p) (in custom ctl at level 74): ctl_scope.
  Notation "'AF' p" := (CAU (CNow (fun _=> True)) p) (in custom ctl at level 74): ctl_scope.
  Notation "'WF' p" := (CWU (CNow (fun _=> True)) p) (in custom ctl at level 74): ctl_scope.
  Notation "'EG' p" := (CER p (CNow (fun _=>False))) (in custom ctl at level 74): ctl_scope.
  Notation "'AG' p" := (CAR p (CNow (fun _=>False))) (in custom ctl at level 74): ctl_scope.
  Notation "'WG' p" := (CWR p (CNow (fun _=>False))) (in custom ctl at level 74): ctl_scope.
  
  (* Propositional syntax *)
  Notation "p '/\' q" := (CAnd p q) (in custom ctl at level 77, left associativity): ctl_scope.
  Notation "p '\/' q" := (COr p q) (in custom ctl at level 77, left associativity): ctl_scope.
  Notation "p '->' q" := (CImpl p q) (in custom ctl at level 78, right associativity): ctl_scope.
  Notation " ¬ p" := (CImpl p (CNow (fun _ => False))) (in custom ctl at level 76): ctl_scope.
  Notation "p '<->' q" := (CAnd (CImpl p q) (CImpl q p)) (in custom ctl at level 77): ctl_scope.
  Notation "⊤" := (CNow (fun _ => True)) (in custom ctl at level 76): ctl_scope.
  Notation "⊥" := (CNow (fun _ => False)) (in custom ctl at level 76): ctl_scope.

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
  #[global] Hint Constructors ceu cau carF cerF: ctree.
End CtlNotations.

Import CtlNotations.
Local Open Scope ctl_scope.

Lemma ctl_now `{KMS: Kripke M meq W} X: forall (m: M X * option W) φ,
    <( m |= now φ )> <-> exists x, snd m = Some x /\ φ x.
Proof. unfold entailsF; now cbn. Qed.
Global Hint Resolve ctl_now: ctree.

Lemma ctl_nothing `{KMS: Kripke M meq W} X: forall (m: M X * option W),
    <( m |= nothing )> <-> snd m = None.
Proof. unfold entailsF; now cbn. Qed.
Global Hint Resolve ctl_nothing: ctree.

Lemma ctl_done `{KMS: Kripke M meq W} X: forall (m: M X * option W) φ,
    <( m |= done φ )> <->
      exists w x, meq X (fst m) (ret x) /\ snd m = Some w /\ φ X x w.
Proof. unfold entailsF; firstorder. Qed.
Global Hint Resolve ctl_done: ctree.

(*| AX, WX, EX unfold |*)
Lemma ctl_ax `{KMS: Kripke M meq W} X: forall (m: M X * option W) p,
    <( m |= AX p )> <-> can_step m /\ forall m', m ↦ m' -> <( m' |= p )>.
Proof.
  intros; split; intro H'; repeat destruct H'.
  - split; eauto with ctree.
  - destruct m.
    unfold entailsF, cax; split; eauto with ctree.
Qed.

Lemma ctl_wx `{KMS: Kripke M meq W} X: forall (m: M X * option W) p,
    <( m |= WX p )> <-> forall m', m ↦ m' -> <( m' |= p )>.
Proof.
  intros; split; intro H'; repeat destruct H'.
  - apply H2. 
  - unfold entailsF, cax; split; auto.
Qed.

Lemma ctl_ex `{KMS: Kripke M meq W} X: forall (m: M X * option W) p,
    <( m |= EX p )> <-> exists m', m ↦ m' /\ <( m' |= p )>.
Proof.
  intros; split; intro H1; repeat destruct H1.
  - now exists x.
  - unfold entailsF, cex; exists x; split; auto.
Qed.
Global Hint Resolve ctl_ax ctl_ex ctl_wx: ctree.

(* [AX φ] is stronger than [EX φ] *)
Lemma ctl_ax_ex `{KMS: Kripke M meq W} X: forall (m: M X * option W) p,
    <( m |= AX p )> -> <( m |= EX p )>.
Proof.
  unfold cex, cax; intros * H1.
  rewrite ctl_ax in H1.
  destruct m, H1.
  destruct H1 as (m' & w' & TR).
  exists (m', w'); auto.
Qed.

(* [AF φ] is stronger than [EF φ] *)
Lemma ctl_af_ef `{KMS: Kripke M meq W} X: forall (m: M X * option W) p,
    <( m |= AF p )> -> <( m |= EF p )>.
Proof.
  intros. 
  unfold entailsF in H1; induction H1.
  - now apply MatchE. 
  - destruct m.
    destruct H2 as ((m' & ? & ?) & ?).
    destruct H3 as ((? & ? & ?) & ?).
    apply StepE; auto.
    exists (x0, x1); split; auto.
    now apply H5.
Qed.

(* [AF φ] is stronger than [WF φ] *)
Lemma ctl_af_wf `{KMS: Kripke M meq W} X: forall (m: M X * option W) p,
    <( m |= AF p )> -> <( m |= WF p )>.
Proof.
  intros. 
  unfold entailsF in H1; induction H1.
  - now apply MatchA.
  - destruct m.
    destruct H2 as ((m' & ? & ?) & ?).
    destruct H3 as ((? & ? & ?) & ?).
    apply StepA; trivial.
    unfold cax; split; auto.
Qed.

(*| Induction lemmas |*)
Lemma ctl_au_ind `{KMS: Kripke M meq W} X: 
  forall [p q: CtlFormula W] (P : M X * option W -> Prop),
    (forall m, <( m |= q )> -> P m) -> (* base *)
    (forall m,
        <( m |= p )> ->          (* [p] now*)
        <( m |= AX (p AU q))> ->
        cax true P m ->
        P m) ->
    forall m, <( m |= p AU q )> -> P m.
Proof. intros; induction H3; auto. Qed.

Lemma ctl_wu_ind `{KMS: Kripke M meq W} X: 
  forall [p q: CtlFormula W] (P : M X * option W -> Prop),
    (forall m, <( m |= q )> -> P m) -> (* base *)
    (forall m,
        <( m |= p )> ->          (* [p] now*)
        <( m |= WX (p WU q))> ->
        cax false P m ->
        P m) ->
    forall m, <( m |= p WU q )> -> P m.
Proof. intros; induction H3; auto. Qed.

Lemma ctl_eu_ind `{KMS: Kripke M meq W} X: 
  forall [p q: CtlFormula W] (P : M X * option W -> Prop),
    (forall m, <( m |= q )> -> P m) -> (* base *)
    (forall m,
        <( m |= p )> ->          (* [p] now*)
        <( m |= EX (p EU q))> ->
        cex P m ->
        P m) ->
    forall m, <( m |= p EU q )> -> P m.
Proof. intros; induction H3; auto. Qed.
  
(*| Bot is false |*)
Lemma ctl_sound `{KMS: Kripke M meq W} X: forall (m: M X * option W),
    ~ <( m |= ⊥ )>.
Proof. intros _ []. Qed.

(*| Ex-falso |*)
Lemma ctl_ex_falso `{KMS: Kripke M meq W} X: forall (m: M X * option W) p,
    <( m |= ⊥ -> p )>.
Proof.
  intros; unfold entailsF; intro CONTRA; contradiction.
Qed. 

(*| Top is True |*)
Lemma ctl_top `{KMS: Kripke M meq W} X: forall (m: M X * option W),
    <( m |= ⊤ )>.
Proof. reflexivity. Qed. 

(*| Cannot exist path such that eventually Bot |*)
Lemma ctl_sound_ef `{KMS: Kripke M meq W} X: forall (m: M X * option W),
    ~ <( m |= EF ⊥ )>.
Proof.
  intros m.
  intro Contra.  
  unfold entailsF in Contra.
  induction Contra.
  - contradiction.
  - destruct H3 as (? & ? & ?).
    contradiction.
Qed.

(*| Cannot have all paths such that eventually always Bot |*)
Lemma ctl_sound_af `{KMS: Kripke M mequ W} X: forall (m: M X * option W),
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
  | CNow  p  => CNow (fun x => p (option_map f x))
  | CDone p  => CDone (fun X z x => p X z (option_map f x))
  | CAnd  φ ψ => CAnd (ctl_contramap f φ) (ctl_contramap f ψ)
  | COr   φ ψ => COr (ctl_contramap f φ) (ctl_contramap f ψ)
  | CImpl φ ψ => CImpl (ctl_contramap f φ) (ctl_contramap f ψ)
  | CAX   φ   => CAX (ctl_contramap f φ)
  | CWX   φ   => CWX (ctl_contramap f φ)                    
  | CEX   φ   => CEX (ctl_contramap f φ)
  | CAU   φ ψ => CAU (ctl_contramap f φ) (ctl_contramap f ψ)
  | CWU   φ ψ => CWU (ctl_contramap f φ) (ctl_contramap f ψ)                    
  | CEU   φ ψ => CEU (ctl_contramap f φ) (ctl_contramap f ψ)
  | CAR   φ ψ => CAR (ctl_contramap f φ) (ctl_contramap f ψ)
  | CWR   φ ψ => CWR (ctl_contramap f φ) (ctl_contramap f ψ)                    
  | CER   φ ψ => CER (ctl_contramap f φ) (ctl_contramap f ψ)
  end.

Lemma option_map_id{X}: forall (m: option X),
    option_map (fun x => x) m = m.
Proof. destruct m; reflexivity. Qed.
Global Hint Resolve option_map_id: core.

Lemma option_map_compose{X Y Z}: forall (m: option X) (f: X -> Y) (g: Y -> Z),
    option_map g (option_map f m) = option_map (fun x => g (f x)) m.
Proof. destruct m; cbn; reflexivity. Qed.
Global Hint Resolve option_map_compose: core.

From Coq Require Import FunctionalExtensionality.
(*| Contravariant functor laws: Identity |*)
Lemma ctl_contramap_id{X}: forall (p: CtlFormula X),
    ctl_contramap (fun x => x) p = p.
Proof.
  intros; induction p; cbn;
    rewrite ?IHp1, ?IHp2, ?IHp; auto.
  replace (fun x : option X => p (option_map (fun x0 : X => x0) x)) with p. reflexivity.
  apply functional_extensionality; intros.
  now rewrite option_map_id.
  replace (fun (X0 : Type) (z : X0) (x : option X) => p X0 z (option_map (fun x0 : X => x0) x))
    with p. reflexivity.
  apply functional_extensionality_dep; intros.
  apply functional_extensionality; intros.
  apply functional_extensionality; intros.
  now rewrite option_map_id.
Qed.

(*| Contravariant functor laws: composition |*)
Lemma ctl_contramap_compose{X Y Z}: forall (p: CtlFormula X) (f: Z -> Y) (g: Y -> X),
    ctl_contramap f (ctl_contramap g p) = ctl_contramap (fun x => g (f x)) p.
Proof.
  intros; induction p; cbn in *; try reflexivity;
    rewrite ?IHp1, ?IHp2, ?IHp; auto.
  replace (fun x : option Z => p (option_map g (option_map f x)))
    with (fun x : option Z => p (option_map (fun x0 : Z => g (f x0)) x)). reflexivity.
  apply functional_extensionality; intros.
  now rewrite option_map_compose.
  replace (fun (X0 : Type) (z : X0) (x : option Z) => p X0 z (option_map g (option_map f x)))
    with (fun (X0 : Type) (z : X0) (x : option Z) => p X0 z (option_map (fun x0 : Z => g (f x0)) x)).
  reflexivity.
  apply functional_extensionality_dep; intros.
  apply functional_extensionality; intros.
  apply functional_extensionality; intros.
  now rewrite option_map_compose.
Qed.  

(*| Semantic equivalence of formulas |*)
Definition equiv_ctl `{K: Kripke M meq W}: relation (CtlFormula W) :=
  fun p q => forall (X: Type) (m: M X * option W), entailsF p m <-> entailsF q m.

Infix "⩸" := equiv_ctl (at level 58, left associativity): ctl_scope.

Global Instance Proper_ctl_contramap{W Y}(f: Y -> W) `{K:Kripke M meq W} `{Kripke M meq Y}:
  Proper (equiv_ctl (K:=K) ==> equiv_ctl) (ctl_contramap f).
Proof.
  unfold Proper, respectful.
Admitted.
