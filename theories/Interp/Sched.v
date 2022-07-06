From ExtLib Require Import
     Structures.Functor
     Structures.Monad.

From CTree Require Import
     CTree
     Eq
     Interp.Interp
     Interp.State.

Import ITree.Basics.Basics.Monads.
Import MonadNotation.
Open Scope monad_scope.

#[global] Instance ctree_trigger {E C} : MonadTrigger E (ctree E C) :=
  @CTree.trigger _ _.

#[global] Instance stateT_trigger {E S M} {MM : Monad M} {MT: MonadTrigger E M} :
  MonadTrigger E (stateT S M) :=
  fun _ e s => v <- mtrigger _ e;; ret (s, v).

Definition schedule_gen {E C M : Type -> Type}
           {FM : Functor M} {MM : Monad M}
           {IM : MonadIter M} {FoM : MonadTrigger E M}
           (h : bool -> C ~> M) :
	ctree E C ~> M :=
  interp mtrigger h.

Definition schedule {E C M : Type -> Type}
           {FM : Functor M} {MM : Monad M}
           {IM : MonadIter M} {FoM : MonadTrigger E M}
           {CM : MonadChoice M (C01 +' C)}
           (h : bool -> C ~> M) :
    ctree E (C01 +' C) ~> M :=
 schedule_gen (fun b X (c: (C01 +' C) X) =>
    match c, X return M X with
    | inr1 c, X => h b X c
    | c, X => Utils.choice b X c
    end).

Set Typeclasses Depth 5.
Definition schedule_cst {E} (h : forall n, fin (S n)) :
  ctree E (C01 +' Cn) ~> ctree E (C01 +' Cn) :=
  schedule (fun b X (c: Cn X) =>
    match c, X return (ctree E (C01 +' Cn) X) with
    | choicen (S n), X =>
        (choice b choice1 (fun _ => Ret (h n)))
    | c, X => CTree.choose b (inr1 c)
    end).
Unset Typeclasses Depth.

Lemma schedule_cst_choiceI_inv : forall {E X Y} (t : ctree E _ X) h c (k : Y -> ctree E _ X),
  schedule_cst h _ t ≅ ChoiceI c k ->
    (is_stuck t /\ is_stuck (ChoiceI c k)) \/
    (exists X (c : (C01 +' Cn) X) k x,
      t ≅ ChoiceI c k /\
      schedule_cst h _ t ≅ tauI (tauI (schedule_cst h _ (k x)))).
Proof.
  intros. setoid_rewrite unfold_interp in H.
  setoid_rewrite (ctree_eta t) at 2. setoid_rewrite (ctree_eta t) at 3.
  genobs t ot.
  destruct ot.
  - step in H. inv H.
  - setoid_rewrite bind_trigger in H. { step in H. inv H. }
  - destruct c0. setoid_rewrite bind_choice in H.
    apply equ_choice_invT in H as H'. destruct H' as [-> ->].
    destruct s; destruct c0.
    + left.
      rewrite ctree_eta. rewrite <- Heqot.
      split. apply choice0_is_stuck. setoid_rewrite <- H.
      apply choice0_is_stuck.
    + right.
      do 3 eexists. exists tt. split. eauto.
      setoid_rewrite unfold_interp at 1. cbn.
      setoid_rewrite bind_choice. apply choice_equ. intros [].
      rewrite bind_ret_l. reflexivity.
    + destruct c0. destruct n.
      * destruct vis. { step in H. inv H. }
        rewrite ctree_eta. rewrite <- Heqot.
        left. split.
        -- repeat intro. apply trans_choiceI_inv in H0.
           destruct H0. now eapply Fin.case0.
        -- rewrite <- H. apply is_stuck_bind. apply choice_fin0_is_stuck.
      * right. setoid_rewrite bind_choice in H.
        destruct vis. { step in H. inv H. }
        do 3 eexists. exists (h n). split; eauto.
        setoid_rewrite unfold_interp at 1. cbn.
        rewrite bind_choice. apply choice_equ. intros _.
        rewrite bind_ret_l. reflexivity.
Qed.

Theorem schedule_cst_refinement :
  forall {E X} (h : forall n, fin (S n)) (t : ctree E (C01 +' Cn) X),
  schedule_cst h _ t ≲ t.
Proof.
  intros until h. coinduction R CH. repeat intro.
  do 3 red in H. remember (observe _) as os. genobs t' ot'.
  assert (EQ : go os ≅ schedule_cst h X t \/ go os ≅ tauI (schedule_cst h X t)).
  { left. rewrite Heqos. now rewrite <- ctree_eta. } clear Heqos.
  apply (f_equal go) in Heqot'. eq2equ Heqot'.
  rewrite <- ctree_eta in EQ0. setoid_rewrite <- EQ0. clear t' EQ0.
  revert t EQ.
  induction H; intros; subst.
  - destruct EQ as [EQ|EQ]; symmetry in EQ.
    apply schedule_cst_choiceI_inv in EQ as ?.
    destruct H0.
    + destruct H0. replace t with (observe (go t)) in H by reflexivity.
      rewrite trans__trans in H. eapply trans_choiceI in H; eauto. now apply H1 in H.
    + destruct H0 as (? & ? & ? & ? & ? & ?).
      setoid_rewrite H0. rewrite EQ in H1.
      apply equ_choice_invT in H1 as ?. destruct H2 as [-> _].
      apply equ_choice_invE with (x := x) in H1. rewrite H1 in H. cbn in H.
      replace t with (observe (go t)) in H by reflexivity. apply trans_tauI_inv in H.
      specialize (IHtrans_ (x2 x3)). setoid_rewrite <- (ctree_eta (k x)) in IHtrans_.
      lapply IHtrans_; eauto. intros (? & ? & ? & ? & ?). subst.
      exists x4, x5. etrans.
    + apply IHtrans_. left. apply equ_choice_invT in EQ as ?. destruct H0 as [<- _].
      apply equ_choice_invE with (x := x) in EQ. rewrite <- ctree_eta. now rewrite EQ.
  - destruct EQ. 2: { step in H0. inv H0. }
    setoid_rewrite unfold_interp in H0. cbn in H0.
    repeat break_match_in H0;
      (try setoid_rewrite bind_choice in H0);
      (try setoid_rewrite bind_trigger in H0);
      subst; try now step in H0; inv H0.
    + apply equ_choice_invT in H0 as ?. destruct H1 as [-> <-].
      apply equ_choice_invE with (x := x) in H0. rewrite bind_ret_l in H0.
      destruct s; destruct c0, x.
      exists (k0 tt). exists tau. rewrite ctree_eta, Heqc0. split; etrans.
      rewrite <- H, H0, <- ctree_eta, sb_tauI.
      split; eauto.
    + apply equ_choice_invT in H0 as ?. destruct H1 as [-> <-].
      apply equ_choice_invE with (x := x) in H0. rewrite bind_ret_l in H0.
      exists (k0 (h n0)). exists tau. rewrite ctree_eta, Heqc0. split; etrans.
      rewrite <- H, H0, <- ctree_eta, sb_tauI.
      split; eauto.
  - destruct EQ. 2: { step in H0. inv H0. }
    setoid_rewrite unfold_interp in H0. cbn in H0.
    destruct (observe t0) eqn:?; try (now step in H0; inv H0).
    + setoid_rewrite bind_trigger in H0.
      apply equ_vis_invT in H0 as ?. destruct H1.
      apply equ_vis_invE in H0 as [-> ?].
      exists (k0 x). eexists. split.
      { rewrite ctree_eta, Heqc. etrans. }
      split; auto.
      rewrite <- H, H0, <- ctree_eta, sb_tauI. apply CH.
    + repeat break_match_in H0; step in H0; inv H0.
  - destruct EQ. 2: { step in H. inv H. }
    exists stuckI. exists (val r).
    setoid_rewrite unfold_interp in H.
    destruct (observe t) eqn:?; try (now step in H; inv H).
    + step in H. inv H. rewrite ctree_eta, Heqc.
      split; etrans. split; auto.
      step. apply is_stuck_ss. apply choice0_is_stuck.
    + repeat break_match_in H; step in H; inv H.
Qed.

Program Definition schedule_state {E St} (f : St -> forall n, St * fin (S n)) :
    ctree E (C01 +' Cn) ~> stateT St (ctree E (C01 +' Cn)) :=
  schedule (
    fun (b : bool) T (c : Cn T) s =>
    match c, T return (ctree E (C01 +' Cn) (St * T)) with
      | choicen (S n), T =>
          choice b choice1 (fun _ => Ret (f s n))
      | c, T => choice b c (fun x => Ret (s, x))
      end).

Program Definition round_robin {E} :
    ctree E (C01 +' Cn) ~> stateT nat (ctree E (C01 +' Cn)) :=
  schedule_state (fun s n =>
    (S s, @Fin.of_nat_lt (Nat.modulo s (S n)) (S n) (le_n_S _ _ (PeanoNat.Nat.le_sub_l _ _)))).

Lemma round_robin_choiceI_inv :
  forall {E St X Y} f (t : ctree E _ X) s c (k : Y -> ctree E _ (St * X)),
  schedule_state f _ t s ≅ ChoiceI c k ->
    (is_stuck t /\ is_stuck (ChoiceI c k)) \/
    (exists X (c : (C01 +' Cn) X) k x s',
      t ≅ ChoiceI c k /\
      schedule_state f _ t s ≅ tauI (tauI (schedule_state f _ (k x) s'))).
Proof.
  intros. unfold schedule_state, schedule, schedule_gen in H.
  setoid_rewrite interp_interp_state in H. rewrite unfold_interp_state in H.
  setoid_rewrite (ctree_eta t) at 2. setoid_rewrite (ctree_eta t) at 3.
  genobs t ot.
  destruct ot; cbn in H.
  - step in H. inv H.
  - rewrite bind_bind in H. setoid_rewrite bind_trigger in H.
    { step in H. inv H. }
  - destruct c0. do 2 setoid_rewrite bind_choice in H.
    apply equ_choice_invT in H as H'. destruct H' as [-> ->].
    destruct s0; destruct c0.
    + left.
      rewrite ctree_eta. rewrite <- Heqot.
      split. apply choice0_is_stuck. setoid_rewrite <- H.
      apply choice0_is_stuck.
    + right.
      do 3 eexists. exists tt. exists s. split. eauto.
      unfold schedule_state, schedule, schedule_gen.
      setoid_rewrite interp_interp_state at 1. rewrite unfold_interp_state. cbn.
      rewrite bind_bind. setoid_rewrite bind_choice.
      apply choice_equ. intros [].
      rewrite 2 bind_ret_l. reflexivity.
    + destruct c0. destruct n.
      * destruct vis. { step in H. inv H. }
        rewrite ctree_eta. rewrite <- Heqot.
        left. split.
        -- repeat intro. apply trans_choiceI_inv in H0.
           destruct H0. now eapply Fin.case0.
        -- rewrite <- H. apply is_stuck_bind. apply choice_fin0_is_stuck.
      * right. setoid_rewrite bind_choice in H.
        destruct vis. { step in H. inv H. }
        do 4 eexists. exists (fst (f s n)). split; eauto.
        unfold schedule_state, schedule, schedule_gen.
        setoid_rewrite interp_interp_state at 1. rewrite unfold_interp_state. cbn.
        rewrite bind_choice. apply choice_equ. intros _.
        rewrite bind_ret_l. cbn. unfold interp_state. reflexivity.
Qed.

Variant lift_val_rel {E X Y} (R : rel X Y): @label E -> @label E -> Prop :=
| Rel_Val (v1 : X) (v2 : Y) : R v1 v2 -> lift_val_rel R (val v1) (val v2)
| Rel_Tau : lift_val_rel R tau tau
| Rel_Obs : forall {X X'} e e' (x : X) (x' : X'), obs e x = obs e' x' -> lift_val_rel R (obs e x) (obs e' x')
.

Definition Rrr {St X} (p : St * X) (x : X) := snd p = x.
Definition Lrr {St E X} := @lift_val_rel E _ X (@Rrr St X).

Theorem schedule_state_refinement :
  forall {E X St} f (t : ctree E (C01 +' Cn) X) (s : St),
  schedule_state f _ t s (≲@Lrr St E X) t.
Proof.
  intros ? ? ? ?. coinduction R CH. repeat intro.
  do 3 red in H. remember (observe _) as os. genobs t' ot'.
  assert (EQ : go os ≅ schedule_state f X t s \/ go os ≅ tauI (schedule_state f X t s)).
  { left. rewrite Heqos. now rewrite <- ctree_eta. } clear Heqos.
  apply (f_equal go) in Heqot'. eq2equ Heqot'.
  rewrite <- ctree_eta in EQ0. setoid_rewrite <- EQ0. clear t' EQ0.
  revert t s EQ.
  induction H; intros; subst.
  - destruct EQ as [EQ|EQ]; symmetry in EQ.
    apply round_robin_choiceI_inv in EQ as ?.
    destruct H0.
    + destruct H0. replace t with (observe (go t)) in H by reflexivity.
      rewrite trans__trans in H. eapply trans_choiceI in H; eauto. now apply H1 in H.
    + destruct H0 as (? & ? & ? & ? & ? & ? & ?).
      setoid_rewrite H0. rewrite EQ in H1.
      apply equ_choice_invT in H1 as ?. destruct H2 as [-> _].
      apply equ_choice_invE with (x := x) in H1. rewrite H1 in H. cbn in H.
      replace t with (observe (go t)) in H by reflexivity. apply trans_tauI_inv in H.
      specialize (IHtrans_ (x2 x3) x4). setoid_rewrite <- (ctree_eta (k x)) in IHtrans_.
      lapply IHtrans_; eauto. intros (? & ? & ? & ? & ?). subst.
      exists x5. etrans.
    + eapply IHtrans_. left. apply equ_choice_invT in EQ as ?. destruct H0 as [<- _].
      apply equ_choice_invE with (x := x) in EQ. rewrite <- ctree_eta. now rewrite EQ.
  - destruct EQ. 2: { step in H0. inv H0. }
    unfold round_robin, schedule, schedule_gen in H0.
    setoid_rewrite interp_interp_state at 1 in H0. rewrite unfold_interp_state in H0. cbn in H0.
    destruct (observe t0) eqn:?; cbn in H0;
    repeat break_match_in H0;
      (try setoid_rewrite bind_choice in H0);
      (try setoid_rewrite bind_trigger in H0);
      subst; try now step in H0; inv H0.
    + rewrite bind_choice in H0.
      apply equ_choice_invT in H0 as ?. destruct H1 as [-> <-].
      apply equ_choice_invE with (x := x) in H0.
      rewrite bind_bind in H0. rewrite bind_ret_l in H0.
      cbn in H0. rewrite bind_ret_l in H0.
      destruct s0; destruct c0, x.
      exists (k0 tt). exists tau. rewrite ctree_eta, Heqc0. split; etrans.
      split; [| constructor ].
      rewrite <- ctree_eta, <- H, H0, sb_tauI.
      cbn. apply CH.
    + apply equ_choice_invT in H0 as ?. destruct H1 as [-> <-].
      apply equ_choice_invE with (x := x) in H0. rewrite bind_ret_l in H0.
      cbn in H0. eexists (k0 _).
      exists tau. rewrite ctree_eta, Heqc0. split; etrans. split; [| constructor ].
      rewrite <- H, H0, <- ctree_eta, sb_tauI. apply CH.
  - destruct EQ. 2: { step in H0. inv H0. }
    setoid_rewrite interp_interp_state at 1 in H0.
    rewrite unfold_interp_state in H0.
    destruct (observe t0) eqn:?; try (now step in H0; inv H0).
    + cbn in H0. setoid_rewrite bind_trigger in H0.
      rewrite bind_vis in H0.
      apply equ_vis_invT in H0 as ?. destruct H1.
      apply equ_vis_invE in H0 as [-> ?].
      exists (k0 x). eexists. split.
      { rewrite ctree_eta, Heqc. etrans. }
      split; [| apply Rel_Obs; econstructor ].
      rewrite <- H, H0, <- ctree_eta, bind_ret_l, sb_tauI. apply CH.
    + cbn in H0. repeat break_match_in H0; step in H0; inv H0.
  - destruct EQ. 2: { step in H. inv H. }
    unfold round_robin, schedule, schedule_gen in H.
    setoid_rewrite interp_interp_state at 1 in H.
    rewrite unfold_interp_state in H.
    exists stuckI. destruct r. exists (val x).
    destruct (observe t) eqn:?; try (now step in H; inv H).
    + step in H. inv H. rewrite ctree_eta, Heqc.
      inv REL.
      split; etrans. split; auto.
      step. apply is_stuck_ss. apply choice0_is_stuck.
      constructor. reflexivity.
    + cbn in H. repeat break_match_in H; step in H; inv H.
Qed.

Theorem round_robin_refinement :
  forall {E X} (t : ctree E (C01 +' Cn) X) n,
  round_robin _ t n (≲@Lrr nat E X) t.
Proof.
  intros. apply schedule_state_refinement.
Qed.

(* TODO:
Can we do something with a stream?
One round robin per arity?
Random scheduler on the OCaml side?
Fairness? Too low level here I think? Maybe at the level of Imp.
Prove that the original computation simulates the scheduled one?
*)


Definition guarded_form {E C X} `{C1 -< C} (t : ctree E C X) : ctree E C X :=
	CTree.iter (fun t =>
				        match observe t with
				        | RetF r => ret (inr r)
				        | ChoiceIF c k =>
                    ChoiceI c (fun x => Ret (inl (k x)))
				        | ChoiceVF c k =>
                    ChoiceI c (fun x => tauV (Ret (inl (k x))))
				        | VisF e k => bind (mtrigger _ e) (fun x => Ret (inl (k x)))
				        end) t.

Lemma unfold_guarded_form {E C X} `{C1 -< C} (t : ctree E C X) :
  guarded_form t ≅
  match observe t with
	| RetF r => ret r
	| ChoiceIF c k =>
      ChoiceI c (fun x => tauI (guarded_form (k x)))
	| ChoiceVF c k =>
      ChoiceI c (fun x => tauV (tauI (guarded_form (k x))))
	| VisF e k => bind (mtrigger _ e) (fun x => tauI (guarded_form (k x)))
	end.
Proof.
  unfold guarded_form at 1.
  rewrite unfold_iter.
  desobs t; cbn.
  - now rewrite bind_ret_l.
  - unfold mtrigger; rewrite bind_bind, !bind_trigger.
    step; constructor; intros ?.
    rewrite bind_ret_l.
    reflexivity.
  - destruct vis.
    + rewrite bind_choice.
      step; constructor; intros ?.
      rewrite bind_tauV; step; constructor; intros ?.
      rewrite bind_ret_l.
      step; constructor; auto.
    + rewrite bind_choice.
      step; constructor; intros ?.
      rewrite bind_ret_l.
      step; constructor; auto.
Qed.

Lemma trans_guarded_inv_strong :
  forall {E C X} `{HasStuck : C0 -< C} `{HasTau : C1 -< C} (t u v : ctree E C X) l,
    (v ≅ guarded_form t \/ v ≅ tauI (guarded_form t)) ->
    trans l v u ->
    exists t', trans l t t'
          /\ (u ≅ guarded_form t' \/ u ≅ tauI (guarded_form t')).
Proof.
  intros * EQ TR.
  revert t EQ.
  unfold trans in TR; repeat red in TR.
  dependent induction TR.
  - intros ? [EQ | EQ].
    + rewrite ctree_eta, <- x, unfold_guarded_form in EQ.
      setoid_rewrite (ctree_eta t).
      desobs t; try now step in EQ; inv EQ.
      destruct vis.
      * pose proof equ_choice_invT _ _ _ _ EQ as [<- _].
        apply equ_choice_invE with (x := x0) in EQ .
        rewrite EQ in TR.
        apply trans_tauV_inv in TR as [EQ' ->].
        eexists; split; eauto.
        etrans.

      * pose proof equ_choice_invT _ _ _ _ EQ as [<- _].
        apply equ_choice_invE with (x := x0) in EQ .
        specialize (IHTR _ _ eq_refl eq_refl).
        edestruct IHTR as (t' & ? & ?); eauto.
        exists t'.
        split.
        eapply trans_choiceI with (x := x0); eauto.
        eauto.

    + rewrite ctree_eta, <- x in EQ.
      pose proof equ_choice_invT _ _ _ _ EQ as [-> _].
      apply equ_choice_invE with (x := x0) in EQ .
      specialize (IHTR _ _ eq_refl eq_refl).
      edestruct IHTR as (t' & ? & ?); eauto.

  - (* G(t) ≅ ChoiceV k : absurd *)
    intros ? [EQ | EQ].
    + rewrite ctree_eta, <- x1, unfold_guarded_form in EQ.
      desobs t0; try now step in EQ; inv EQ.
      destruct vis; try now step in EQ; inv EQ.
    + rewrite ctree_eta, <- x1 in EQ.
      now step in EQ; inv EQ.

  - (* G(t) ≅ Vis e k : t ≅ Vis e k', k x ≅ TauI (G (k' x)) *)
    intros ? [EQ | EQ].
    + setoid_rewrite (ctree_eta t0).
      rewrite ctree_eta, <- x1, unfold_guarded_form in EQ.
      rewrite (ctree_eta t), x in H.
      clear t x.
      desobs t0; try now step in EQ; inv EQ.
      2:destruct vis; try now step in EQ; inv EQ.
      cbn in *.
      unfold mtrigger in EQ; rewrite bind_trigger in EQ.
      pose proof equ_vis_invT _ _ _ _ EQ; subst.
      pose proof equ_vis_invE _ _ _ _ EQ as [-> EQ'].
      eexists; split.
      etrans.
      rewrite <- ctree_eta in H.
      rewrite <- H.
      rewrite EQ'.
      auto.
    + rewrite ctree_eta, <- x1 in EQ.
      now step in EQ; inv EQ.

  - (* G(t) ≅ Ret x : t ≅ Ret x *)
    intros ? [EQ | EQ].
    + setoid_rewrite (ctree_eta t).
      rewrite ctree_eta, <- x0, unfold_guarded_form in EQ.
      desobs t; try now step in EQ; inv EQ.
      2:destruct vis; try now step in EQ; inv EQ.
      step in EQ; inv EQ.
      eexists; split.
      etrans.
      left.
      rewrite ctree_eta, <- x, unfold_guarded_form.
      cbn.
      rewrite ! choice0_always_stuck.
      reflexivity.
    + rewrite ctree_eta, <- x0 in EQ.
      now step in EQ; inv EQ.
Qed.

Lemma trans_guarded_inv :
  forall E C X `(C0 -< C) `(C1 -< C) (t u : ctree E C X) l,
    trans l (guarded_form t) u ->
    exists t', trans l t t'
          /\ u ~ guarded_form t'.
Proof.
  intros.
  edestruct @trans_guarded_inv_strong as (t' & TR & EQ); [|eassumption|].
  left; eauto.
  exists t'; split; auto.
  destruct EQ as [EQ |EQ]; rewrite EQ; auto.
  rewrite sb_tauI; auto.
Qed.

#[global] Instance guarded_equ E C X `(C1 -< C) : Proper (equ eq ==> equ eq) (@guarded_form E C X _).
Proof.
  do 2 red.
  coinduction ? IH.
  intros * EQ.
  step in EQ.
  rewrite ! unfold_guarded_form.
  cbn*.
  inv EQ; auto.
  - cbn.
    constructor; intros ?.
    fold_subst; rewrite ! bind_ret_l.
    step; constructor; intros _.
    auto.
  - destruct b; cbn.
    all: constructor; intros ?.
    all: repeat (step; constructor; intros ?).
    all: auto.
Qed.

(* TODO: bind simpl never globally? *)
(* TODO: Taus without continuation? *)
(* TODO: tactic for better stepping for equ *)
(* TODO: tactics for better stepping for sbisim (see a couple above) *)
(* Equality on [observe u] rewritten in [equ]? *)
Opaque CTree.bind.
Lemma trans_guarded_strong :
  forall E C X `(HasStuck : C0 -< C) `(HasTau : C1 -< C) (t u : ctree E C X) l,
    trans l t u ->
    exists u',
      trans l (guarded_form t) u'
      /\ (u' ≅ guarded_form u
         \/ u' ≅ tauI (guarded_form u)).
Proof.
  intros * TR.
  (* revert t EQ. *)
  unfold trans in TR; repeat red in TR.
  dependent induction TR; intros.
  - (* destruct EQ as [EQ | EQ]. *)
    edestruct IHTR as (u' & TR' & EQ'); eauto.
    setoid_rewrite unfold_guarded_form at 1; rewrite <- x.
    exists u'; split.
    eapply trans_choiceI with (x := x0); [| reflexivity].
    now apply trans_tauI.
    auto.
  - setoid_rewrite unfold_guarded_form at 1; rewrite <- x1.
    eexists; split.
    eapply trans_choiceI with (x := x0); [| reflexivity].
    etrans.
    right.
    step; constructor; intros ?.
    rewrite H.
    rewrite (ctree_eta t0),x,<- ctree_eta.
    auto.
  - setoid_rewrite unfold_guarded_form at 1; rewrite <- x1.
    eexists; split.
    unfold mtrigger, ctree_trigger; cbn.
    rewrite bind_trigger.
    etrans.
    right.
    step; constructor; intros ?.
    rewrite H.
    rewrite (ctree_eta t0),x,<- ctree_eta.
    auto.
  - setoid_rewrite unfold_guarded_form at 1; rewrite <- x0.
    eexists; split.
    (*
      Why do I need to cbn even if I add:
      Hint Unfold ret Monad_ctree : trans.
     *)
    cbn; etrans.
    left.
    rewrite unfold_guarded_form, <- x; cbn.
    now rewrite ! choice0_always_stuck.
Qed.

Lemma trans_guarded :
  forall E C X `(C0 -< C) `(C1 -< C) (t u : ctree E C X) l,
    trans l t u ->
    exists u',
      trans l (guarded_form t) u'
      /\ u' ~ guarded_form u.
Proof.
  intros * TR.
  edestruct trans_guarded_strong as (u' & TR' & EQ'); eauto.
  exists u'; split; eauto.
  destruct EQ' as [EQ' | EQ']; rewrite EQ'; auto.
  now rewrite sb_tauI.
Qed.

(* TODO: define properly the set of tactics in [sbisim] and kill this.
   TODO: this is not resilient enough, it loops if the goal is not exactly of the right shape
 *)
Ltac sret  := apply step_sb_ret.
Ltac svis  := apply step_sb_vis.
Ltac stauv := apply step_sb_tauV.
Ltac sstep := sret || svis || stauv.

Lemma guarded_is_bisimilar {E C X} `{C0 -< C} `{C1 -< C} : forall (t : ctree E C X),
    guarded_form t ~ t.
Proof.
  coinduction ? IH.
  intros t.
  rewrite (ctree_eta t) at 2.
  rewrite unfold_guarded_form.
  desobs t.
  - now cbn.
  - cbn.
    unfold mtrigger; rewrite bind_trigger.
    svis; intros ?.
    rewrite sb_tauI.
    apply IH.
  - destruct vis.
    + cbn.
      split; intros ? ? TR.
      * inv_trans.
        subst.
        eexists. eexists.
        split; [etrans |].
        split; [| reflexivity].
        rewrite EQ.
        rewrite sb_tauI.
        apply IH.
      * cbn.
        inv_trans; subst.
        eexists. eexists.
        split; [etrans |].
        split; [| reflexivity ].
        rewrite sb_tauI.
        rewrite EQ; apply IH.
    + split.
      * intros ? ? TR.
        cbn.
        inv_trans.
        edestruct trans_guarded_inv as (u' & TR' & EQ'); eauto.
        eexists. eexists.
        split; [etrans |].
        split; [| reflexivity].
        rewrite EQ'; auto.
      * cbn; intros ? ? TR.
        inv_trans.
        edestruct trans_guarded as (u' & TR' & EQ'); eauto.
        eexists. eexists.
        split; [etrans |].
        split; [| reflexivity].
        rewrite EQ'; auto.
Qed.
