From ITree Require Import
     Core.Subevent.

From CTree Require Import
     CTreeDefinitions
     Take
     Eq.

Import CTreeNotations.
Local Open Scope ctree_scope.

Set Implicit Arguments.


(*| Unique thread identifiers |*)
Notation id n := (fin (S n)).

(*| Thread IDs are a product of an effect [E] with a [uid] |*)
Variant switchE (n: nat): Type -> Type :=
  | Process (i: id n): switchE n unit.

Arguments Process {n}.

Definition switch {n E C} `{switchE n -< E} (i: id n): ctree E C unit :=
  trigger (Process i).

Definition cinj{n E C X}`{B1 -< C}`{B1 -< D}(a: ctree E C X)(i: id n): ctree (E +' switchE n) C X :=
  fold Handler.einl_ Handler.binl_ a.

Definition cinr_{E F C D X}`{B1 -< C}`{B1 -< D}(a: ctree F D X): ctree (E +' F) (C +' D) X :=
  fold Handler.einr_ Handler.binr_ a.

(*| Parallel composition, no synchronization |*)    
Definition para{E C D X F}`{B0 -< C}`{B1 -< C}`{B2 -< C}`{B0 -< D}`{B1 -< D}`{B2 -< D}:
  ctree E C X -> ctree F D X -> ctree (E +' F) (C +' D) void :=
  cofix R (P : ctree E C X) (Q : ctree F D X) :=
    brD2
      (rP <- cinl_ (head P);;
       match rP with
       | ARet rP => stuckD
       | ABr c kP => BrS (inl1 c) (fun i => R (kP i) Q)
       | AVis e kP => Vis (inl1 e) (fun i => R (kP i) Q)
       end)
      
      (rQ <- cinr_ (head Q);;
       match rQ with
       | ARet rQ => stuckD
       | ABr c kQ => BrS (inr1 c) (fun i => R P (kQ i))
       | AVis e kQ => Vis (inr1 e) (fun i => R P (kQ i))
       end).

(*| Fair parallel operator, warning: not associative |*)
(*| A || B -> br (A^* ; B) (B^*; A) *) (* (A || B) || C == A || (B || C) *)
Definition fair{E C D X F}`{B1 -< C}`{B1 -< D} `{B2 -< C +' D}`{BN -< C +' D}: 
  ctree E C X -> ctree F D X -> ctree (E +' F) (C +' D) X :=
  cofix R (P : ctree E C X) (Q : ctree F D X) :=
    brD2 
      (n <- branch false (branchN) ;;      
       p <- cinl_ (take n P) ;;
       q <- cinr_ (take 1 Q) ;; (* this is equivalent to [head] *)
       R p q)
      (n <- branch false (branchN) ;;
       q <- cinr_ (take n Q) ;;
       p <- cinl_ (take 1 P) ;;
       R p q).

Notation fair_ P Q :=
  (
    brD2 
      (n <- branch false (branchN) ;;      
       p <- cinl_ (take n P) ;;
       q <- cinr_ (take 1 Q) ;;
       fair p q)
      (n <- branch false (branchN) ;;
       q <- cinr_ (take n Q) ;;
       p <- cinl_ (take 1 P) ;;
       fair p q)
  ).

Lemma unfold_fair {E C X F}`{B1 -< C}`{B2 -< C}`{BN -< C}:
  forall (a: ctree E C X) (b: ctree F C X),
    (fair a b) ≅ (fair_ a b).
Proof. intros; step; cbn; auto. Qed.

(*| Round-robbin fair parallel operator, not associative either |*)
Definition rr{E C D X F}`{B1 -< C}`{B1 -< D}: ctree E C X -> ctree F D X -> ctree (E +' F) (C +' D) X :=
  cofix F P Q :=
    Guard
      (p <- cinl_ (take 1 P) ;;
       q <- cinr_ (take 1 Q) ;; 
       F p q).

Notation rr_ a b :=
  (
    Guard
      (p <- cinl_ (take 1 a) ;;
       q <- cinr_ (take 1 b) ;; 
       rr p q)
  ).

Lemma unfold_rr {E C D X F}`{B1 -< C}`{B1 -< D}:
  forall (a: ctree E C X) (b: ctree F D X),
    (rr a b) ≅ (rr_ a b).
Proof. intros; step; cbn; auto. Qed.

Declare Scope ctree_combinator_scope.
Local Open Scope ctree_combinator_scope.
Notation "p *" := (kleene_star p) (at level 40): ctree_combinator_scope.
Notation "p +" := (kleene_plus p) (at level 40): ctree_combinator_scope.
Notation "a ∥ b" := (para a b) (at level 40, left associativity): ctree_combinator_scope.
Notation "a ⋄ b" := (fair a b) (at level 40, left associativity): ctree_combinator_scope.

Inductive is_r{E F C D}: @label (E +' F) (C +' D) -> Prop :=
| IsRightEffect: forall X (x: X) e,
    is_r (obs (inr1 e) x)
| IsRightBranch: forall X (d: D X),
    is_r (tau (inr1 d)).

Inductive is_l{E F C D}: @label (E +' F) (C +' D) -> Prop :=
| IsLeftEffect: forall X (x: X) e,
    is_l (obs (inl1 e) x)
| IsLeftBranch: forall X (d: C X),
    is_l (tau (inl1 d)).

Hint Constructors is_r is_l: core.

(*| Left injection on labels |*)
Definition linl{E F C D}(l: @label E C): @label (E +' F) (C +' D) :=
  match l with
  | tau c => tau (inl1 c)
  | obs e x => obs (inl1 e) x
    | val x => val x
    end.
  
  (*| Right injection on labels |*)
  Definition linr{E F C D}(l: @label F D): @label (E +' F) (C +' D) :=
    match l with
    | tau c => tau (inr1 c)
    | obs e x => obs (inr1 e) x
    | val x => val x
    end.
  
  Lemma is_l_linl{E F C D: Type -> Type}:forall (l: @label E C),
      ~ is_val l -> @is_l E F C D (linl l).
  Proof.
    intros.
    destruct l; cbn; eauto.
    - exfalso; apply H; econstructor.
  Qed.

  Lemma is_r_linr{E F C D: Type -> Type}:forall (l: @label F D),
      ~ is_val l -> @is_r E F C D (linr l).
  Proof.
    intros.
    destruct l; cbn; eauto.
    - exfalso; apply H; econstructor.
  Qed.

  Lemma is_val_linl_iff{E F C D: Type -> Type}:forall (l: @label E C),
      is_val l <-> is_val (@linl E F C D l).
  Proof.
    intros; split; destruct l; cbn; intro H; inv H; econstructor.
  Qed.

  Lemma is_val_linr_iff{E F C D: Type -> Type}:forall (l: @label F D),
      is_val l <-> is_val (@linr E F C D l).
  Proof.
    intros; split; destruct l; cbn; intro H; inv H; econstructor.
  Qed.
  
  Lemma trans_cinl_inv{E F C D X} `{B0 -< C} `{B0 -< D} `{B1 -< C} `{B1 -< D}:
    forall (t: ctree E C X) (u: ctree (E +' F) (C +' D) X) (l: @label (E +' F) (C +' D)),
      trans l (cinl_ t) u -> exists (l' : @label E C) (u' : ctree E C X), l = linl l' /\ u ≅ cinl_ u' /\ trans l' t u'.
  Proof.
    intros * TR.

    (* induction on trans *)
    rewrite (ctree_eta (cinl_ t)) in TR; rewrite (ctree_eta u) in TR;
      unfold trans, transR in TR; cbn in TR; dependent induction TR.
  Admitted.

  Section FairFacts.
    Context {C D: Type -> Type}
            {HasStuck: B0 -< C} {HasStuck': B0 -< D} {HasTau: B1 -< C} {HasTau': B1 -< D}.

    Arguments label: clear implicits.
    
    Lemma rr_is_fair' {E F: Type -> Type}:
      forall (t: ctree E C void) (u: ctree F D void) l, (rr t u), l |= AF (lift is_l).
    Proof.
      Opaque take.
      intros t u l; apply ctl_af_ax; right; unfold ax; cbn; intros * TR.
      rewrite unfold_rr in TR; unfold rr_ in TR;
        eapply trans_guard_inv in TR.
      eapply trans_bind_inv in TR as [(VL & t1 & TR & EQ) | (x & TRv & TR)].
      - eapply trans_cinl_inv in TR as (l' & t1' & -> & EQt & TR).     (* Step of [bind] *)
        eapply MatchA; unfold lift.
        rewrite <- (@is_val_linl_iff E F C D) in VL. 
        now eapply is_l_linl.
      - eapply trans_cinl_inv in TRv as (l' & t1' & EQl & EQt & TRv). (* Ret of [bind] *)
        destruct l'; dependent destruction EQl.
        apply trans_take_Sn_val_inv in TRv as (CONTRA & ?); contradiction.
    Qed.
  End FairFacts.

  
End CTreeCombinators.
