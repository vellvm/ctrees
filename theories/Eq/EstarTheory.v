From Stdlib Require Import Program.Equality.

From CTree Require Import
     CTree
     Eq.Equ
     Eq.TransAlt.

From RelationAlgebra Require Export
     monoid kat kat_tac rel srel.
From Coinduction Require Import all.

Import CTree.
Import EquNotations.
Set Implicit Arguments.

(* l -> *ε ⋅ l *)
Lemma estar_l_lift {X} {C G : Type -> Type} :
    forall (t t' : @S G C X) l,
    trans_alt l t t' ->
    ((trans_alt ε)^* ⋅ trans_alt l) t t'.
  Proof.
    intros. use_steps O. assumption.
  Qed.

(* ^*ε is transitive. *)
Lemma estar_trans {G B : Type -> Type} {V : Type} (a b c : @S G B V) :
  (trans_alt ε)^* a b -> (trans_alt ε)^* b c -> (trans_alt ε)^* a c.
Proof.
  intros S1 S2.
  assert (H : (@trans_alt G B V ε)^* ⋅ (trans_alt ε)^* ≦ (trans_alt ε)^*) by ka.
  apply H; eexists; eassumption.
Qed.

(* adding an ε preserves ^*ε. *)
Lemma estar_cons_epsilon {G B : Type -> Type} {V : Type} (a b c : @S G B V) :
  trans_alt ε a b -> (trans_alt ε)^* b c -> (trans_alt ε)^* a c.
Proof.
  intros S1 S2.
  assert (H : @trans_alt G B V ε ⋅ (trans_alt ε)^* ≦ (trans_alt ε)^*) by ka.
  apply H; eexists; eassumption.
Qed.

(* lift ε to ^*ε *)
Lemma estar_single {G B : Type -> Type} {V : Type} (a b : @S G B V) :
  trans_alt ε a b -> (trans_alt ε)^* a b.
Proof.
  enough (H: (@trans_alt G B V ε) ≦ (trans_alt ε)^*); 
  [apply H | ka].
Qed.

(* adding an ε preserves ^ε ⋅ l for any l *)
Lemma estar_cons_label {G B : Type -> Type} {V : Type} (a b c : @S G B V) l :
  trans_alt ε a b -> ((trans_alt ε)^* ⋅ trans_alt l) b c ->
  ((trans_alt ε)^* ⋅ trans_alt l) a c.
Proof.
  enough (H: @trans_alt G B V ε ⋅ ((trans_alt ε)^* ⋅ trans_alt l)
              ≦ (trans_alt ε)^* ⋅ trans_alt l); [|ka].
  intros; apply H; eexists; eauto. 
Qed.

(* adding .^*ε preserves ^ε ⋅ l for any l *)
Lemma estar_app {G B : Type -> Type} {V : Type} (a b c : @S G B V) l :
  (trans_alt ε)^* a b -> ((trans_alt ε)^* ⋅ trans_alt l) b c ->
  ((trans_alt ε)^* ⋅ trans_alt l) a c.
Proof.
  enough (H : (@trans_alt G B V ε)^* ⋅ ((trans_alt ε)^* ⋅ trans_alt l)
              ≦ (trans_alt ε)^* ⋅ trans_alt l); [|ka].
  intros; apply H; eexists; eassumption.
Qed.

(* lift ^*ε through ⩸ *)
Lemma estar_seq {E B X} (a b : @SS E B X) :
  a ⩸ b -> (trans_alt ε)^* a b.
Proof.
  intros H; exists O; exact H.
Qed.

Lemma estar_passive {E B X Z} (e : E Z) (g : Z -> ctree E B X) (m : @SS E B X) :
  (trans_alt ε)^* (Passive e g) m ->
  (Passive e g : @SS E B X) ⩸ m.
Proof.
  intros [n STAR]; destruct n.
  - cbn in STAR. exact STAR.
  - destruct STAR as [mid STEP _].
  (* STEP is absurd; [β] only steps with [rcv] *)
    apply trans_passive_inv' in STEP as (z & _ & Habs); easy.
Qed.

Lemma estar_active {E B X} (t : ctree E B X) (u : @S E B X) :
  (trans_alt ε)^* (Active t) u -> exists u0 : ctree E B X, u ⩸ (Active u0).
Proof.
  intros [n STAR]; revert t STAR; induction n; intros t STAR.
  - cbn in STAR; dependent destruction STAR. eexists; reflexivity.
  - destruct STAR as [mid STEP REST].
    unfold trans_alt in STEP; cbn in STEP; dependent destruction STEP.
    + eapply IHn; exact REST.
    + eapply IHn; exact REST.
Qed.

Import CTreeNotations. 
Lemma estar_bind {E B X Y} (t u : ctree E B X) (k : X -> ctree E B Y) :
  (trans_alt ε)^* (Active t) (Active u) ->
  (trans_alt ε)^* (Active (x <- t;; k x)) (Active (x <- u;; k x)).
Proof.
  intros [n STAR]; revert t STAR; induction n; intros t STAR.
  - cbn in STAR; dependent destruction STAR.
    apply estar_seq; constructor.
    now rewrite EQ.
  - destruct STAR as [mid STEP REST].
    unfold trans_alt in STEP; cbn in STEP; dependent destruction STEP.
    + eapply estar_cons_epsilon.
      * apply trans_bind_l_ε; eapply Transbr; eauto.
      * apply IHn; exact REST.
    + eapply estar_cons_epsilon.
      * apply trans_bind_l_ε; eapply Transguard; eauto.
      * apply IHn; exact REST.
Qed.