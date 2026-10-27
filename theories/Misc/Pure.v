From CTree Require Import
     Eq Eq.Epsilon.

Variant pureb {E C X} (rec : ctree E C X -> Prop) (t : ctree E C X) : Prop :=
  | pureb_ret   (v : X) (EQ : t ≅ Ret v) : pureb rec t
  | pureb_stuck (EQ : t ≅ Stuck) : pureb rec t
  | pureb_br {Y} (c: C Y) k (EQ : t ≅ Br c k) (REC: forall v, rec (k v)) : pureb rec t
  | pureb_guard  u (EQ : t ≅ Guard u) (REC: rec u) : pureb rec t.
Hint Constructors pureb: core.

Program Definition fpure {E C R} : mon (ctree E C R -> Prop) := {|body := pureb|}.
Next Obligation.
  inversion_clear H0; eauto.
Qed.

Section pure.

  Context {E C : Type -> Type} {X : Type}.

  Class pure (t : ctree E C X) := pure_ : gfp (@fpure E C X) t.

  #[global] Instance pure_equ : Proper (@equ E C X X eq ==> flip impl) pure.
  Proof.
    cbn. intros. step in H0. inversion H0; step;
      [econstructor 1 | econstructor 2 | econstructor 3 | econstructor 4]; eauto.
    all: rewrite H, EQ; eauto.
  Qed.

  #[global] Instance pure_ret r : pure (Ret r).
  Proof.
    step; cbn; eauto.
  Qed.

  #[global] Instance pure_br {T} (c : C T) k :
    (forall x, pure (k x)) ->
    pure (Br c k).
  Proof.
    intros; step; cbn; eauto.
  Qed.

  #[global] Instance pure_guard t :
    pure t ->
    pure (Guard t).
  Proof.
    intros; step; cbn; eauto.
  Qed.

  #[global] Instance pure_stuck :
    pure Stuck.
  Proof.
    intros; step; cbn; eauto.
  Qed.

  Lemma pure_br_inv : forall {X} (c : C X) k x,
    pure (Br c k) ->
    pure (k x).
  Proof.
    intros. step in H. inv H; inv_equ.
    rewrite EQ0. apply REC.
  Qed.

  Lemma pure_guard_inv : forall t,
    pure (Guard t) ->
    pure t.
  Proof.
    intros. step in H. inv H; inv_equ.
    rewrite EQ. apply REC.
  Qed.

  Lemma pure_productive : forall (t : ctree E C X),
    pure t -> productive t -> exists r, t ≅ Ret r.
  Proof.
    intros. step in H. inv H; eauto.
    all: rewrite EQ in H0; inv H0; inv_equ.
  Qed.

  Lemma pure_epsilon :
    forall t t', pure t -> epsilon t t' -> pure t'.
  Proof.
    intros. rewrite ctree_eta in H. rewrite ctree_eta. red in H0. genobs t ot. genobs t' ot'.
    clear t t' Heqot Heqot'. induction H0.
    - now subs.
    - apply IHepsilon_. rewrite <- ctree_eta. eapply pure_br_inv. apply H.
    - apply IHepsilon_. rewrite <- ctree_eta. eapply pure_guard_inv. apply H.
  Qed.

  (* issue: active/passive makes this annoying, though it is a logical non-issue  *)
 Lemma trans_pure_is_val (t : ctree E C X) (st : @Trans.S E C X) l :
    pure t ->
    trans l t st ->
    is_val l.
  Proof. 
    intros Hp TR. repeat red in TR.
    remember (Active t).
    generalize dependent t. 
    induction TR; intros t0 Hp Heqs; inv Heqs.
    (* just these 2 cases need to 'thread the purity argument' *)
    - eapply IHTR. 
      all: try reflexivity.
      rewrite H in Hp. step in Hp. inversion Hp; inv_equ. rewrite H0, EQ0. 
      apply REC. 
    - eapply IHTR. 
      all: try reflexivity.
      rewrite H in Hp. step in Hp. inversion Hp; inv_equ. rewrite EQ.
      apply REC. 
    - rewrite H in Hp. step in Hp; inv Hp; inv_equ.
    - rewrite H in Hp. step in Hp; inv Hp; inv_equ. 
    - constructor. 
  Qed.

  Lemma trans_bind_pure {Y} (t : ctree E C X) k (u : ctree E C Y) l :
    pure t ->
    trans l (CTree.bind t k) u ->
    exists v, trans (val v) t Stuck /\ trans l (k v) u.
  Proof.
    intros. apply trans_bind_inv in H0 as [(? & ? & ? & ?) |].
    - now apply trans_pure_is_val in H1.
    - destruct H0 as [[Z [e (Hl & g & Htrans & Hsym)]] | H0].
      + inv Hsym. 
      + apply H0.
  Qed.

End pure.

(* TO MOVE *)
Lemma map_stuck {E B X Y} (f : X -> Y) :
    @CTree.map E B _ _ f Stuck ≅ Stuck.
Proof.
  intros. unfold CTree.map.
  apply bind_stuck.
Qed.

Lemma map_br {E B X Y Z} (e : B Z) k (f : X -> Y) :
    @CTree.map E B _ _ f (Br e k) ≅ Br e (fun x => CTree.map f (k x)).
Proof.
  intros. unfold CTree.map.
  apply bind_br.
Qed.

#[global] Instance pure_map {E B X Y} : forall (t : ctree E B X) (f : X -> Y),
  pure t ->
  pure (CTree.map f t).
Proof.
  red. coinduction R CH. intros.
  step in H. destruct H.
  - econstructor 1; rewrite EQ, map_ret; reflexivity.
  - econstructor 2. rewrite EQ, map_stuck; reflexivity.
  - econstructor 3. rewrite EQ, map_br; reflexivity. intros; apply CH, REC.
  - econstructor 4. rewrite EQ, map_guard; reflexivity. intros; apply CH, REC.
Qed.

Section pure_finite.

  Context {E C : Type -> Type} {X : Type}.

  Inductive pure_finite_ : ctree E C X -> Prop :=
  | puref_ret (v : X) t (EQ: t ≅ Ret v) : pure_finite_ t
  | puref_stuck t (EQ : t ≅ Stuck) : pure_finite_ t
  | puref_br {Y} (c: C Y) k t (EQ : t ≅ Br c k) (REC: forall v, pure_finite_ (k v)) : pure_finite_ t
  | puref_guard t u (EQ : t ≅ Guard u) (REC: pure_finite_ u) : pure_finite_ t.

  Class pure_finite (t : ctree E C X) : Prop :=
    pure_finite__ : pure_finite_ t.

  #[global] Instance pure_finite_equ :
    Proper (equ eq ==> flip impl) pure_finite.
  Proof.
    cbn. intros. revert x H. induction H0; intros.
    - econstructor 1; now subs.
    - econstructor 2; now subs.
    - econstructor 3; now subs.
    - econstructor 4; now subs.
  Qed.

  #[global] Instance pure_finite_ret r : pure_finite (Ret r).
  Proof.
    now econstructor 1.
  Qed.

  #[global] Instance pure_finite_stuck : pure_finite Stuck.
  Proof.
    now econstructor 2.
  Qed.

  #[global] Instance pure_finite_br {T} (c : C T) k :
    (forall x, pure_finite (k x)) ->
    pure_finite (Br c k).
  Proof.
    now econstructor 3.
  Qed.

  #[global] Instance pure_finite_guard t :
    pure_finite t ->
    pure_finite (Guard t).
  Proof.
    now econstructor 4.
  Qed.

End pure_finite.

Lemma pure_finite_bind_R {E C X Y} :
  forall R t (k : X -> ctree E C Y),
  t (≅R) t ->
  pure_finite t ->
  (forall x, R x x -> pure_finite (k x)) ->
  pure_finite (CTree.bind t k).
Proof.
  intros. induction H0.
  - subs. inv_equ. rewrite bind_ret_l; auto.
  - subs. rewrite bind_stuck. apply pure_finite_stuck.
  - subs. inv_equ. rewrite bind_br. apply pure_finite_br. auto.
  - subs. inv_equ. rewrite bind_guard. apply pure_finite_guard. auto.
Qed.

#[global] Instance pure_finite_bind {E C X Y} :
  forall t (k : X -> ctree E C Y),
  pure_finite t ->
  (forall x, pure_finite (k x)) ->
  pure_finite (CTree.bind t k).
Proof.
  intros. apply (pure_finite_bind_R eq); auto.
Qed.

#[global] Instance pure_pure_finite {E C X} :
  forall (t : ctree E C X),
  pure_finite t ->
  pure t.
Proof.
  intros. induction H; subs; step.
    - econstructor 1; now subs.
    - econstructor 2; now subs.
    - econstructor 3; now subs.
    - econstructor 4; now subs.
  Qed.

Lemma is_stuck_pure : forall {E B X Y} t (k : X -> ctree E B Y),
  pure t ->
  (forall x, is_stuck (k x)) ->
  is_stuck (CTree.bind t k).
Proof.
  red. intros. intro.
  apply trans_bind_inv in H1 as
    [ (-> & t' & TR & _)
    | [ (Z & e & -> & g & TR & _)
    | (v & TRv & TRk) ]].
  (* discriminate labels; they should be val since t is pure *)
  - apply trans_pure_is_val in TR; [inv TR | exact H].
  - apply trans_pure_is_val in TR; [inv TR | exact H].
  - eapply H0; exact TRk.
Qed.