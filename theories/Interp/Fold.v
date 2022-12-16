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
           (h : E ~> M) (g : bool -> B ~> M) :
  ctree E B ~> M :=
  fun R =>
    iter (fun t =>
	    match observe t with
	    | RetF r => ret (inr r)
	    | BrF b c k => fmap (fun x => inl (k x)) (g b _ c)
	    | VisF e k => fmap (fun x => inl (k x)) (h _ e)
	    end).

Arguments fold {E B M FM MM IM} h g [T].

(** Implementing simultaneously external events while refining
    the internal non-determinism is somewhat uncommon.
    We hence also define two particular case:
    - [interp] only implements external events, and re-emit branches
    without cutting them (internalized in [M] via [MonadBr]
    - [refine] only refines the internal branches,
    and re-emit external events (internalized in [M] via [MonadTrigger]
 *)

Definition interp {E B M : Type -> Type}
           {FM : Functor M} {MM : Monad M} {IM : MonadIter M} {BM : MonadBr B M}
           (h : E ~> M) := fold h (fun b _ c => mbr b c).

Arguments interp {E B M FM MM IM BM} h [T].

Definition refine {E B M : Type -> Type}
           {FM : Functor M} {MM : Monad M} {IM : MonadIter M} {TM : MonadTrigger E M}
           (g : bool -> B ~> M) := fold (fun _ e => mtrigger e) g.

Arguments refine {E B M FM MM IM TM} g [T].

Definition translateF {E F C R}
           (h : E ~> F)
           (rec: ctree E C R -> ctree F C R)
           (t : ctreeF E C R _) : ctree F C R  :=
  match t with
  | RetF x => Ret x
  | VisF e k => Vis (h _ e) (fun x => rec (k x))
  | BrF b c k => Br b c (fun x => rec (k x))
  end.

Definition translate {E F C} (h : E ~> F) : ctree E C ~> ctree F C
  := fun R => cofix translate_ t := translateF h translate_ (observe t).

Arguments translate {E F C} h [T].

(** Useful congruences and lemmas for [interp] and [refine] *)
#[global] Instance interp_equ {E C X} `{HasTau: B1 -< C}  h:
  Proper (equ eq ==> @equ E C X X eq) (@interp E C _ _ _ _ _ h X).
Proof.
  cbn.
  coinduction R CH.
  intros. setoid_rewrite unfold_iter.
  step in H. inv H; setoid_rewrite <- H1; setoid_rewrite <- H2.
  - setoid_rewrite bind_ret_l. reflexivity.
  - setoid_rewrite bind_bind. setoid_rewrite bind_ret_l.
    upto_bind_eq.
    constructor. intros.
    apply CH. apply REL.
  - setoid_rewrite bind_bind.
    upto_bind_eq.
    setoid_rewrite bind_ret_l.
    constructor. intros _.
    apply CH. apply REL.
Qed.

#[global] Instance refine_equ {E C X} `{HasTau: B1 -< C} h:
  Proper (equ eq ==> @equ E C X X eq) (@refine E C _ _ _ _ _ h X).
Proof.
  cbn.
  coinduction R CH.
  intros. setoid_rewrite unfold_iter.
  step in H. inv H; setoid_rewrite <- H1; setoid_rewrite <- H2.
  - setoid_rewrite bind_ret_l. reflexivity.
  - setoid_rewrite bind_bind. setoid_rewrite bind_trigger.
    constructor. intros.
    setoid_rewrite bind_ret_l.
    step. constructor. intros _.
    apply CH. apply REL.
  - setoid_rewrite bind_bind.
    upto_bind_eq.
    setoid_rewrite bind_ret_l.
    constructor. intros _.
    apply CH. apply REL.
Qed.
