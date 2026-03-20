(* begin hide *)

From ExtLib Require Import
     Structures.Functor
     Structures.Monad.

From ITree Require Import
     Basics.Basics
     Core.Subevent.

From CTree Require Import
     CTreeDefinitions
     CTree Eq.

Set Implicit Arguments.

Import CTreeNotations.
Open Scope ctree_scope.

(* end hide *)

(** ** Fold *)

(** The most general shape of fold over the structure takes two parameters:
    - an event handler [E ~> M] describing how to implement events
    - a local scheduler [B ~> M] describing valid branches
    and defines for it a monad morphism [ctree E B ~> M]
    for any monad [M] with a loop operator. *)
Definition fold {E B M : Type -> Type}
           {FM : Functor M} {MM : Monad M} {IM : MonadIter M}
           {Mstuck : MonadStuck M} {Mstep : MonadStep M}
           (h : E ~> M)
           (g : B ~> M) :
  ctree E B ~> M :=
  fun R =>
    iter (fun t =>
	          match observe t with
	          | RetF r => ret (inr r)
            | StuckF => mstuck _
            | GuardF t => ret (inl t)
            | StepF t => fmap (fun _ => inl t) mstep
	          | BrF c k => fmap (fun x => inl (k x)) (g _ c)
	          | VisF e k => fmap (fun x => inl (k x)) (h _ e)
	          end).

Arguments fold {E B M FM MM IM Mstuck Mstep} h g [T].

(** Implementing simultaneously external events while refining
    the internal non-determinism is somewhat uncommon.
    We hence also define two particular case:
    - [interp] only implements external events, and re-emit branches
    without cutting them (internalized in [M] via [MonadBr]
    - [refine] only refines the internal branches,
    and re-emit external events (internalized in [M] via [MonadTrigger]
 *)

Definition interp {E B M : Type -> Type}
  {FM : Functor M} {MM : Monad M}
  {IM : MonadIter M}
  {Mstuck : MonadStuck M}
  {Mstep : MonadStep M}
  {Mbranch : MonadBr B M}
  (h : E ~> M) : ctree E B ~> M :=
  fold h (@mbr B M Mbranch).

Arguments interp {E B M FM MM IM _ _ _} h [T].

Definition refine {E B M : Type -> Type}
  {FM : Functor M} {MM : Monad M} {IM : MonadIter M} {TM : MonadTrigger E M}
  {Mstuck : MonadStuck M}
  {Mstep : MonadStep M}
  (g : B ~> M)
  :=
  fold (fun _ e => mtrigger e) g.

Arguments refine {E B M FM MM IM TM _ _} g [T].

Definition translateF {E F C R}
           (h : E ~> F)
           (rec: ctree E C R -> ctree F C R)
           (t : ctreeF E C R _) : ctree F C R  :=
  match t with
  | RetF x => Ret x
  | StuckF => Stuck
  | StepF t => Step (rec t)
  | GuardF t => Guard (rec t)
  | VisF e k => Vis (h _ e) (fun x => rec (k x))
  | BrF c k => Br c (fun x => rec (k x))
  end.

Definition translate {E F C} (h : E ~> F) : ctree E C ~> ctree F C
  := fun R => cofix translate_ t := translateF h translate_ (observe t).

Arguments translate {E F C} h [T].

(** Useful congruences and lemmas for [interp] and [refine] *)
#[global] Instance interp_equ {E F B C X} `{HasB: B -< C} h:
  Proper (equ eq ==> @equ F C X X eq)
    (@interp E B _ _ _ _ _ _ _ h X).
Proof.
  cbn.
  coinduction R CH.
  intros. setoid_rewrite unfold_iter.
  step in H. inv H; setoid_rewrite <- H1; setoid_rewrite <- H2.
  - now setoid_rewrite bind_ret_l.
  - now setoid_rewrite bind_stuck.
  - setoid_rewrite bind_ret_l.
    constructor; eauto.
  - setoid_rewrite bind_map.
    setoid_rewrite bind_step.
    constructor; rewrite ! bind_ret_l.
    step; constructor.
    eauto.
  - setoid_rewrite bind_bind. setoid_rewrite bind_ret_l.
    upto_bind_eq.
    constructor. intros.
    apply CH. apply REL.
  - setoid_rewrite bind_bind.
    upto_bind_eq.
    setoid_rewrite bind_ret_l.
    constructor.
    apply CH. apply REL.
Qed.

#[global] Instance refine_equ {E C D X} (h : C ~> ctree E D):
  Proper (equ eq ==> @equ E D X X eq) (@refine E C _ _ _ _ _ _ _ h X).
Proof.
  cbn.
  coinduction R CH.
  intros. setoid_rewrite unfold_iter.
  step in H. inv H; setoid_rewrite <- H1; setoid_rewrite <- H2.
  - now setoid_rewrite bind_ret_l.
  - now setoid_rewrite bind_stuck.
  - setoid_rewrite bind_ret_l.
    constructor; eauto.
  - setoid_rewrite bind_map.
    setoid_rewrite bind_step.
    constructor; rewrite ! bind_ret_l.
    step; constructor.
    eauto.
  - setoid_rewrite bind_bind. setoid_rewrite bind_trigger.
    constructor. intros.
    setoid_rewrite bind_ret_l.
    step. constructor.
    apply CH. apply REL.
  - setoid_rewrite bind_bind.
    upto_bind_eq.
    setoid_rewrite bind_ret_l.
    constructor.
    apply CH. apply REL.
Qed.

(** [translate] lemmas *)

(** Unfolding of [translate]. *)
Notation translate_ h t :=
  (match observe t with
   | RetF x => Ret x
   | StuckF => Stuck
   | StepF t => Step (translate h t)
   | GuardF t => Guard (translate h t)
   | VisF e k => Vis (h _ e) (fun x => translate h (k x))
   | BrF c k => Br c (fun x => translate h (k x))
   end).
(** Unfold lemma. *)
Lemma unfold_translate {E F C X} (t: ctree E C X) (h: E ~> F):
  translate h t ≅ translate_ h t.
Proof.
  intros; step; cbn; auto.
Qed.

Lemma translate_ret {E F C X}(x: X)(h: E ~> F):
  @translate E F C h X (Ret x) ≅ Ret x.
Proof. now rewrite unfold_translate. Qed.

Lemma translate_stuck {E F C X}(x: X)(h: E ~> F):
  @translate E F C h X Stuck ≅ Stuck.
Proof. now rewrite unfold_translate. Qed.

Lemma translate_guard {E F C X} (t: ctree E C X) (h: E ~> F):
  @translate E F C h X (Guard t) ≅ Guard (translate h t).
Proof. now rewrite unfold_translate. Qed.

Lemma translate_step {E F C X} (t: ctree E C X) (h: E ~> F):
  @translate E F C h X (Step t) ≅ Step (translate h t).
Proof. now rewrite unfold_translate. Qed.

Lemma translate_vis {E F C X U} (e: E U)(k: U -> ctree E C X)(h: E ~> F):
  @translate E F C h X (Vis e k) ≅ Vis (h _ e) (fun x => translate h (k x)).
Proof. now rewrite unfold_translate. Qed.

Lemma translate_br {E F C X U} (c : C U) (k: _ -> ctree E C X)(h: E ~> F):
  @translate E F C h X (Br c k) ≅ Br c (fun x => translate h (k x)).
Proof. now rewrite unfold_translate. Qed.

#[global] Instance translate_equ {E F C X} (h: E ~> F):
  Proper (equ eq ==> equ eq) (@translate E F C h X).
Proof.
  cbn.
  coinduction r CIH.
  intros * EQ; step in EQ.
  rewrite 2 unfold_translate.
  inv EQ; auto; constructor; intros; auto.
Qed.
