From Stdlib Require Import Program.Equality.

From CTree Require Import
     CTree
     Eq.Equ
     Eq.TransAlt.

From RelationAlgebra Require Import
     monoid kat kat_tac rel srel.
From Coinduction Require Import all.

Import CTree.
Import EquNotations.
Set Implicit Arguments.

Ltac use_steps n := 
lazymatch goal with 
|- context [(str _)] => 
  repeat red; 
  
  repeat match goal with 
  
  (* ^* case *)
  | |- exists2 _, _ & _ => eexists; repeat red 
  (* base case: just ^* *)
  | |- exists n : nat, _ =>
  exists (n : nat); 
  cbn; try solve [reflexivity] end
  end. 

Lemma trans_star_self {E B R} (x : SS) l: (@trans_alt E B R l)^* x x.
Proof. use_steps O. Qed.   

Lemma trans_star_l {E B R} (x y : SS) l1 l2 : 
trans_alt l2 x y -> 
((@trans_alt E B R l1)^* ⋅ trans_alt l2) x y.
Proof. intros. use_steps O. assumption. Qed. 

Tactic Notation "use" ident(n) "steps" := use_steps n.

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

Lemma estar_vis_inv {G K : Type -> Type} {W Z} (e : G Z) (k : Z -> ctree G K W) (m : @S G K W) :
  (trans_alt ε)^* (Active (Vis e k)) m ->
  (Active (Vis e k) : @S G K W) ⩸ m.
Proof.
  intros [n STAR]; destruct n.
  - exact STAR.
  - destruct STAR as [mid STEP _].
    apply trans_vis_inv' in STEP as (_ & Habs); easy.
Qed.

Definition Sbind {E B X Y} (s : @S E B X) (k : X -> ctree E B Y) : @S E B Y :=
  match s with
  | Active t => Active (x <- t;; k x)
  | Passive e g => Passive e (fun z => x <- g z;; k x)
  end.

Lemma Sbind_Seq {E B X Y} (s u : @S E B X) (k : X -> ctree E B Y) :
  s ⩸ u -> (Sbind s k) ⩸ (Sbind u k).
Proof.
  intros EQ; destruct EQ; cbn; constructor.
  - now rewrite EQ.
  - intros; now rewrite EQ.
Qed.

Lemma estar_Sbind {E B X Y} (s u : @S E B X) (k : X -> ctree E B Y) :
  (trans_alt ε)^* s u -> (trans_alt ε)^* (Sbind s k) (Sbind u k).
Proof.
  destruct s as [t | Z e g]; intros STAR.
  - destruct (estar_active STAR) as [u0 EQ].
    assert (STAR2 : (trans_alt ε)^* (Active t) (Active u0))
      by (eapply estar_trans; [ exact STAR | apply estar_seq, EQ ]).
    eapply (estar_trans (b := Sbind (Active u0 : @S E B X) k)).
    + cbn. apply estar_bind; exact STAR2.
    + apply estar_seq. apply Sbind_Seq. now symmetry.
  - apply estar_passive in STAR. now apply estar_seq, Sbind_Seq.
Qed.

Variant guardR {E B X} : hrel (@S E B X) (@S E B X) :=
  | Guardstep t t' u : t ≅ Guard t' -> u ≅ t' -> guardR (Active t) (Active u).

#[global] Instance guardR_Seq {E B X} :
  Proper (Seq ==> Seq ==> iff) (@guardR E B X).
Proof.
  intros a a' Ea b b' Eb; split; intros H; destruct H;
    dependent destruction Ea; dependent destruction Eb; econstructor.
  - rewrite <- EQ; eassumption.
  - rewrite <- EQ0; eassumption.
  - rewrite EQ; eassumption.
  - rewrite EQ0; eassumption.
Qed.

Definition guard_alt {E B X} : srel (@SS E B X) (@SS E B X) :=
  {| hrel_of := @guardR E B X : hrel (@SS E B X) (@SS E B X) |}.

Definition epsilon_det' {E B X} : srel (@SS E B X) (@SS E B X) := (@guard_alt E B X)^*.

Lemma guard_alt_eps {E B X} : @guard_alt E B X ≦ trans_alt ε.
Proof.
  intros a b H; destruct H; eapply Transguard; eassumption.
Qed.

Lemma epsilon_det'_estar {E B X} (a b : @SS E B X) :
  epsilon_det' a b -> (trans_alt ε)^* a b.
Proof.
  enough (H : (@guard_alt E B X)^* ≦ (trans_alt ε)^*) by apply H.
  now rewrite guard_alt_eps.
Qed.

Lemma epsilon_det'_guard {E B X} (t t' : ctree E B X) :
  t ≅ Guard t' -> epsilon_det' (Active t) (Active t').
Proof.
  intros EQ; exists 1%nat, (Active t'); [econstructor; [exact EQ | reflexivity] | reflexivity].
Qed.

Lemma epsilon_det'_trans {E B X} (a b c : @SS E B X) :
  epsilon_det' a b -> epsilon_det' b c -> epsilon_det' a c.
Proof.
  intros S1 S2.
  assert (H : (@guard_alt E B X)^* ⋅ (guard_alt)^* ≦ (guard_alt)^*) by ka.
  apply H; eexists; eassumption.
Qed.

Lemma epsilon_det'_seq {E B X} (a b : @SS E B X) :
  a ⩸ b -> epsilon_det' a b.
Proof.
  intros H; exists O; exact H.
Qed.
