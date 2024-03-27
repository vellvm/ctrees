#[global] Set Warnings "-intuition-auto-with-star".
From Coq Require Import
     Fin.

From ExtLib Require Import
  Structures.Functor
  Structures.Applicative
  Structures.Monad.

From Coinduction Require Import
     coinduction.

From CTree Require Export
  Classes
  Events.Core.

Generalizable All Variables.

Notation fin' n := (Fin.t (S n)).

Create HintDb ctree.

Section Ctree.
  Context {E: Type} `{Encode E} {X: Type}.
  Variant ctreeF(ctree: Type): Type :=
    | RetF (x: X)
    | BrF {n} (k: fin' n -> ctree)
    | GuardF (t: ctree)
    | VisF (e: E)(k: encode e -> ctree).

  #[projections(primitive)] CoInductive ctree: Type :=
    go { _observe: ctreeF ctree }.
  
End Ctree.

Declare Scope ctree_scope.
Bind Scope ctree_scope with ctree.
Delimit Scope ctree_scope with ctree.
Local Open Scope ctree_scope.

Arguments ctree E {H} X. 
Arguments ctreeF E {H} X.
Arguments BrF {E H X} [ctree] n k.
Arguments GuardF {E H X} [ctree] t.
Arguments RetF {E H X} [ctree] x.
Arguments VisF {E H X} [ctree] e k.

Notation ctree' E X := (ctreeF E X (ctree E X)).

(*| We wrap the primitive projection [_observe] in a function [observe]. |*)
Definition observe `{HE: Encode E} `(t : ctree E X) : ctree' E X := @_observe E HE X t.

Notation Ret x        := (go (RetF x)).
Notation Vis e k      := (go (VisF e k)).
Notation Br n k     := (go (BrF n k)).
Notation Guard t     := (go (GuardF t)).
Notation step t     := (Br 0 (fun _ => t)).

(* Use resum and resum_ret to map the events in an entree to another type *)
CoFixpoint resumCtree' {E1 E2 : Type} `{ReSumRet E1 E2}
           {A} (ot : ctree' E1 A) : ctree E2 A :=
  match ot with
  | RetF r => Ret r
  | BrF n k => Br n (fun i => resumCtree' (observe (k i)))
  | GuardF t =>  Guard (resumCtree' (observe t))
  | VisF e k => Vis (resum e) (fun x => resumCtree' (observe (k (resum_ret e x))))
  end.

Definition resumCtree {E1 E2 : Type} `{ReSumRet E1 E2}
           {A} (t : ctree E1 A) : ctree E2 A :=
  resumCtree' (observe t).

Module Ctree.

  Definition subst' {E : Type@{eff}} {HE: Encode E} {R S : Type@{eff}}
    (k : R -> ctree E S) : ctree' E R -> ctree E S  :=
    cofix _subst (ot : ctree' E R) :=
      match ot with
      | RetF r => k r
      | BrF n h => Br n (fun x => _subst (observe (h x)))
      | GuardF t => Guard (_subst (observe t))
      | VisF e k => Vis e (fun x => _subst (observe (k x)))
    end.

  (*| Monadic composition [bind] |*)
  Definition bind `{HE: Encode E} {X Y} (t : ctree E X) (k : X -> ctree E Y) :=
    subst' k (observe t).

  (*| Monadic composition of continuations (i.e., Kleisli composition). |*)
  Definition cat `{HE: Encode E} `(k : X -> ctree E Y) `(h : Y -> ctree E Z) :
    X -> ctree E Z := fun t => bind (k t) h.

  (*| Functorial map ([fmap] in Haskell) |*)
  Definition map `{HE: Encode E} `(f : X -> Y) (t : ctree E X) : ctree E Y :=
      bind t (fun x => Ret (f x)).

  Definition trigger {E1 E2 : Type@{eff}} `{ReSumRet E1 E2}
    (e : E1) : ctree E2 (encode e) :=
    Vis (resum e) (fun x : encode (resum e) => Ret (resum_ret e x)).
  
  (*| Atomic ctrees with choice. |*)
  Definition branch `{HE: Encode E} n: ctree E (fin' n) :=
    Br n (fun x => Ret x).

  (*| Binary non-deterministic branch |*)
  Definition br2 `{HE: Encode E}{X} (a b: ctree E X): ctree E X :=
    Br 1 (fun x: fin' 1 =>
            match x in Fin.t n return n = 2 -> ctree E X with
            | Fin.F1 => fun _: _ = 2 => a
            | _ => fun _: _ = 2 => b
            end eq_refl).

  (*| Ternary non-deterministic branch |*)
  Definition br3 `{HE: Encode E}{X} (a b c: ctree E X): ctree E X :=
    Br 2 (fun x: fin' 2 =>
            match x in Fin.t n return n = 3 -> ctree E X with
            | Fin.F1 => fun _: _ = 3 => a
            | Fin.FS Fin.F1 => fun _: _ = 3 => b
            | _ => fun _: _ = 3 => c
            end eq_refl).

  (*| Ignore the result of a ctree. |*)
  Definition ignore `{HE: Encode E} {R} : ctree E R -> ctree E unit :=
    map (fun _ => tt).

  (*| Run forever, do nothing |*)
  CoFixpoint stuck `{HE: Encode E} {R} : ctree E R := Guard stuck.
  
  (*| Run forever, do tau steps |*)
  CoFixpoint spin `{HE: Encode E} {R} : ctree E R := step spin.

  (*| [iter] |*)
  Definition iter `{HE: Encode E} {R I: Type}
    (step : I -> ctree E (I + R)) : I -> ctree E R :=
    cofix iter_ i := bind (step i)
                       (fun lr =>
                          match lr with
                          | inl l => (Guard (iter_ l))
                          | inr r => Ret r
                          end).

  Definition forever `{HE: Encode E} {R: Type} (X: Type) (k: R -> ctree E R) (x: R) :=
    iter (R:=X) (fun x => map inl (k x)) x.

  (* Continue sampling until non-deterministic choice satisfies [P] *)
  Definition when `{HE: Encode E} {n P Q} (f: forall (i: fin' n), {P i} + {Q i}): ctree E (fin' n) :=
    iter (fun _  => bind (branch n)
                   (fun i =>
                      if f i then
                        Ret (inr i)
                      else
                        Ret (inl tt))) tt.
  
  (* Continue sampling until non-deterministic choice satisfies [~ P] *)
  Definition unless `{HE: Encode E} {n P Q} (f: forall (i: fin' n), {P i} + {Q i}): ctree E (fin' n) :=
    iter (fun _  => bind (branch n)
                   (fun i =>
                      if f i then
                        Ret (inl tt)
                      else
                        Ret (inr i))) tt.

End Ctree.


Ltac fold_bind :=
  repeat match goal with
    | h: context [Ctree.subst' ?k ?t] |- _ => fold (Ctree.bind (go t) k) in h
    | |- context [Ctree.subst' ?k ?t] => fold (Ctree.bind (go t) k)
    end.

#[global] Hint Extern 0 => fold_bind: core.

(*|
[on_left lr l t]: run a computation [t] if the first argument is an [inl l].
[l] must be a variable (used as a pattern), free in the expression [t]:

   - [on_left (inl x) l t = t{l := x}]
   - [on_left (inr y) l t = Ret y]
|*)

Notation on_left lr l t :=
  (match lr with
   | inl l => t
   | inr r => Ret r
   end) (only parsing).

Ltac desobs t :=
  let H := fresh "Heqt" in destruct (observe t) eqn:H.

Module CTreeNotations.
  Declare Scope ctree_scope.
  Bind Scope ctree_scope with ctree.
  Delimit Scope ctree_scope with ctree.
  Local Open Scope ctree_scope.

  Notation "t1 >>= k2" := (Ctree.bind t1 k2)
                            (at level 58, left associativity) : ctree_scope.
  Notation "x <- t1 ;; t2" := (Ctree.bind t1 (fun x => t2))
                               (at level 62, t1 at next level, right associativity) : ctree_scope.
  Notation "t1 ;; t2" := (Ctree.bind t1 (fun _ => t2))
                           (at level 62, right associativity) : ctree_scope.
  Notation "' p <- t1 ;; t2" :=
    (Ctree.bind t1 (fun x_ => match x_ with p => t2 end))
      (at level 62, t1 at next level, p pattern, right associativity) : ctree_scope.
End CTreeNotations.

(*| Common instances for [ctree] |*)
#[global] Instance Functor_ctree `{Encode E} : Functor (ctree E) :=
  { fmap := @Ctree.map E _ }.

#[global] Instance Applicative_ctree `{Encode E} : Applicative (ctree E) :=
  {
    pure := fun _ x => Ret x;
    ap := fun _ _ f x =>
            Ctree.bind f (fun f => Ctree.bind x (fun x => Ret (f x)) );
  }.

#[global] Instance Monad_ctree `{HE: Encode E} : Monad (ctree E) :=
  {
    ret := fun _ x => Ret x;
    bind := @Ctree.bind E HE;
  }.

#[global] Instance MonadIter_ctree `{HE: Encode E} : MonadIter (ctree E) :=
  fun _ _ => Ctree.iter.

#[global] Instance MonadBr_ctree `{HE: Encode E} : MonadBr (ctree E) :=
  fun n => Ctree.branch n.

(*| Export various useful Utils |*)
From CTree Require Export Utils.Utils.
