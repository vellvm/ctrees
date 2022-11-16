(*|
=========================================
Modal logics over ctrees
=========================================
|*)
From Coq Require Import
     Lia
     Basics
     Fin
     RelationClasses
     Program.Equality
     Logic.Eqdep.

From Coinduction Require Import
     coinduction rel tactics.

From ITree Require Import Core.Subevent.

From CTree Require Import
     CTree
     Utils
     Interp.State
     Eq
     Eq.Trans.

From RelationAlgebra Require Export
     rel srel.

Set Implicit Arguments.

(* TODO: Decide where to set this *)
Arguments trans : simpl never.

Section LogicSyntax.
  Arguments label: clear implicits.
  Context {E C: Type -> Type} {X: Type} {HasStuck: B0 -< C}.
  
  Notation SS := (ctree E C X).
  Notation SP := (label E -> Prop).
  Notation RP := (X -> Prop).

  Inductive LProp :=
  | Spec(p: SP)  (* Predicate on actions *)
  | And(a: LProp) (b: LProp)
  | Or(a: LProp) (b: LProp)
  | Next(p: LProp)
  | Until (p: LProp) (q: LProp) (* tree is finite (ps) (inductive) *)
  | Forever (p: LProp)    (* tree is coinductive *)
  .

  (*| Semantics of LTL over ctree LTS |*)
  Inductive entailsF (R: label E -> SS -> LProp -> Prop): label E -> SS -> LProp -> Prop :=
  | SpecEnt: forall t (p: SP) l,
      p l ->
      entailsF R l t (Spec p)
  | AndEnt: forall t a b l,
      entailsF R l t a ->
      entailsF R l t b ->
      entailsF R l t (And a b)
  | OrEntL: forall t a b l,
      entailsF R l t a ->
      entailsF R l t (Or a b)
  | OrEntR: forall t a b l,
      entailsF R l t b ->
      entailsF R l t (Or a b)
  | NextEnt: forall (t t': SS) l l' p,
      trans l' t t' ->
      entailsF R l' t' p ->
      entailsF R l t (Next p)
  | UntilEntQ: forall t p q l,                              (* base case *)
      entailsF R l t q ->                                  (* 0 |- q *)
      entailsF R l t (Until p q)
  | UntilEntP: forall (t t': SS) p q l l',                  (* Inductive case *)
      trans l' t t' ->
      entailsF R l t p ->                                  (* n |- p *)
      entailsF R l' t' (Until p q) ->                      (* n+1 |- Until P Q *)
      entailsF R l t (Until p q)
  | ForeverEnt: forall (t t': SS) p l l',
      trans l' t t' ->
      entailsF R l t p ->
      R l' t' (Forever p) ->                              (* GFP *)
      entailsF R l t (Forever p).

  Hint Constructors entailsF: core.

  Program Definition entails_ : mon (label E -> SS -> LProp -> Prop) :=
    {|
      body R l t p := entailsF R l t p
    |}.
  Next Obligation. induction H0; eauto. Qed.

End LogicSyntax.

(*| Coinductive definition |*)
Definition entails{E C X} `{HasStuck : B0 -< C}:
  @label E -> ctree E C X -> LProp -> Prop := (gfp (@entails_ E C X _)).

Module LtlNotations.

  Notation Top := (Spec (fun _ => True)).
  Notation Bot := (Spec (fun _ => False)).
  Notation Eventually p := (Until Top p).
  Notation InfinitelyOften p := (Forever (Eventually p)).
  
  Notation entailst := (t entails_).
  Notation entailsbt := (bt entails_).
  Notation entailsT := (T entails_).
  Notation entailsbT := (bT entails_).

  Notation "t ∇ l |= p" := (entails l t p) (at level 40, left associativity).
  Notation "t ∇ l [|=] p" := (entails_ _ l t p) (at level 79).
  Notation "t ∇ l [[|=]] p" := (entailsF _ l t p) (at level 79).
  Notation "t ∇ l {|=} p" := (entailst _ l t p) (at level 79).
  Notation "t ∇ l {{|=}} p" := (entailsbt _ l t p) (at level 79).
  
  Notation "t |= p" := (entails tau t p) (at level 70).
  Notation "t [|=] p" := (entails_ _ tau t p) (at level 79).
  Notation "t [[|=]] p" := (entailsF _ tau t p) (at level 79).
  Notation "t {|=} p" := (entailst _ tau t p) (at level 79).
  Notation "t {{|=}} p" := (entailsbt _ tau t p) (at level 79). 
End LtlNotations.

Import LtlNotations.

Ltac fold_entails :=
  repeat
    match goal with
    | h: context[@entails_ ?R ?E ?C ?X ?HS ] |- _ => fold (@entails R E C X HS) in h
    | |- context[@entails_ ?R ?E ?C ?X ?HS ]      => fold (@entails R E C X HS)
    end.

Ltac __coinduction_entails R H :=
  unfold entails; apply_coinduction; fold_entails; intros R H.

Tactic Notation "__step_entails" :=
  match goal with
  | |- context[@entails ?E ?C ?X ?HasStuck ?l ?t ?p] =>
      unfold entails;
      step;
      fold (@entails E C X HasStuck l t p)
  | |- _ => step
  end.

(* #[local] Tactic Notation "step" := __step_entails. *)
#[local] Tactic Notation "lleft" := (eapply OrEntL || eapply UntilEntP).
#[local] Tactic Notation "lright" := (eapply OrEntR || eapply UntilEntQ).
#[local] Tactic Notation "coinduction" simple_intropattern(R) simple_intropattern(H) :=
  __coinduction_entails R H.

Ltac __step_in_entails H :=
  match type of H with
  | context [@entails ?E ?C ?X ?HasStuck ] =>
      unfold entails in H;
      step in H;
      fold (@entails E C X HasStuck) in H
  end.

#[local] Tactic Notation "step" "in" ident(H) := __step_in_entails H.

Section Lemmas.
  Arguments label: clear implicits.
  Context {E C: Type -> Type} {X: Type} {HasStuck: B0 -< C}
          (t: ctree E C X).

  (*| Top is True |*)
  Lemma top_tautology:
    t |= Top.
  Proof.
    step; now econstructor.
  Qed.    

  (*| Bot is False |*)
  Lemma bot_false:
    ~ t |= Bot.
  Proof.
    intro CONTRA.
    step in CONTRA.
    now inv CONTRA.
  Qed.

  (*| Ex-falso *)
  Lemma bot_ex_falso: forall p,
      t |= Bot -> t |= p.
  Proof.
    intros p CONTRA.
    exfalso; now apply bot_false in CONTRA.
  Qed.
  
  (*| Distributivity of Next and Or |*)
  Lemma distr_next_or : forall p q,
      t |= Next (Or p q) <-> t |= Or (Next p) (Next q).
  Proof with eauto.
    split; intros; step; step in H; inv H; cbn*.
    - inv H4.
      + lleft; auto; econstructor...
      + lright; auto; econstructor...
    - inv H3; econstructor; eauto; lleft...
    - inv H3; econstructor; eauto; lright...
  Qed.

  (*| Eventually p either p or next p *)
  Lemma eventually_next: forall p,
      t |= Eventually p <-> t |= Or p (Next (Eventually p)).
  Proof.
    split; intros; step in H; step; inv H.
    - now lleft.
    - lright; econstructor; eauto.
    - now lright.
    - inv H3; lleft; eauto. 
      now econstructor.
  Qed.

  Lemma next_until: forall p q,
      t |= Next (Until p q) <-> t |= Until (Next p) (Next q).
  Proof with eauto.
    split; intros; step in H; step; inv H. 
    - inv H4.
      + lright; econstructor... 
      + lleft...
        econstructor...
  Admitted.

  Lemma forever_next: forall p,
      t |= Forever p -> t |= And p (Next (Forever p)).
  Proof.
    coinduction ? ?.
    intros.
  Admitted.

End Lemmas.
