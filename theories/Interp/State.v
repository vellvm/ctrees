From ExtLib Require Import
     Structures.Functor
     Structures.Monad.

From ITree Require Import
     Events.State
     CategoryOps.
Import Basics.Monads.

From CTree Require Import
     CTree
     Interp
     Eq
     Equ
     SBisim.

Import SBisimNotations.
Import MonadNotation.
Open Scope monad_scope.

Set Implicit Arguments.

Section State.

  Variable (S : Type).

  #[global] Instance MonadChoice_stateT {M} {MM : Monad M} {AM : MonadBr M}: MonadBr (stateT S M) :=
  fun b n s =>
    f <- mbr b n;;
    ret (s, f).

  Definition interp_state {E M}
           {FM : Functor M} {MM : Monad M}
           {IM : MonadIter M}{MC: MonadBr M} (h : E ~> stateT S M) :
    ctree E ~> stateT S M := interp h.

  Notation stateE := (stateE S).

  Definition h_state {E} : stateE ~> stateT S (ctree E) :=
    fun _ e s =>
      match e with
      | Get _ => Ret (s, s)
      | Put _ s' => Ret (s', tt)
      end.

  Definition pure_state {S E} : E ~> stateT S (ctree E)
    := fun _ e s => Vis e (fun x => Ret (s, x)).

  Definition run_state {E}
    : ctree (stateE +' E) ~> stateT S (ctree E)
    := interp_state (case_ h_state pure_state).

  (** Facts about state (equational theory) *)
  Definition _interp_state {E F R}
           (f : E ~> stateT S (ctree F)) (ot : ctreeF E R _)
  : stateT S (ctree F) R := fun s =>
  match ot with
  | RetF r => Ret (s, r)
  | BrF b n' k =>
      Br b n' (fun i => Guard (interp_state f (k i) s))
  | VisF e k => f _ e s >>= (fun sx => Guard (interp_state f (k (snd sx)) (fst sx)))
  end.

  Lemma unfold_interp_state {E F R}
        (h : E ~> Monads.stateT S (ctree F))
        (t : ctree E R) s :
    interp_state h t s ≅ _interp_state h (observe t) s.
  Proof.
    unfold interp_state, interp, Basics.iter, MonadIter_stateT0, Basics.iter, MonadIter_ctree; cbn.
    rewrite unfold_iter; destruct observe eqn:Hobs; cbn.
    - rewrite 2 bind_ret_l; reflexivity.
    - rewrite bind_map, bind_bind; cbn; setoid_rewrite bind_ret_l.
      reflexivity.
    - do 2 rewrite bind_bind; cbn; do 2 setoid_rewrite bind_ret_l; cbn.
      rewrite bind_bind.
      setoid_rewrite bind_ret_l; cbn.
      setoid_rewrite bind_br.
      setoid_rewrite bind_ret_l.

      apply br_equ; intros t'.
      step; econstructor.
      intros.
      reflexivity.
  Qed.

  #[global] Instance equ_interp_state {E F R} (h : E ~> Monads.stateT S (ctree F)) :
    Proper (equ eq ==> eq ==> equ eq)
      (@interp_state _ _ _ _ _ _ h R).
  Proof.
    unfold Proper, respectful.
    coinduction ? IH; intros * EQ1 * <-.
    rewrite !unfold_interp_state.
    step in EQ1; inv EQ1; cbn [_interp_state]; auto.
    - simpl bind. upto_bind_eq.
      constructor; intros; auto.
    - constructor; intros.
      step; constructor; intros.
      auto.
  Qed.

  Lemma interp_state_ret {E F : Type -> Type} {R: Type}
        (f : forall T, E T -> S -> ctree F (S * T)%type)
        (s : S) (r : R) :
    (interp_state f (Ret r) s) ≅ (Ret (s, r)).
  Proof.
    rewrite ctree_eta. reflexivity.
  Qed.

  Lemma interp_state_vis {E F : Type -> Type} {T U : Type}
        (e : E T) (k : T -> ctree E U) (h : E ~> Monads.stateT S (ctree F)) (s : S)
    : interp_state h (Vis e k) s
                   ≅ h T e s >>= fun sx => Guard (interp_state h (k (snd sx)) (fst sx)).
  Proof.
    rewrite unfold_interp_state; reflexivity.
  Qed.

  Lemma interp_state_br {E F : Type -> Type} {T : Type}
        (b : bool) (n : nat) (k : fin n -> ctree E T) (h : E ~> stateT S (ctree F)) (s : S)
    : interp_state h (Br b n k) s
                   ≅ Br b n (fun sx => Guard (interp_state h (k sx) s)).
  Proof.
    rewrite unfold_interp_state; reflexivity.
  Qed.

  Lemma interp_state_tau {E F : Type -> Type} {T : Type}
        (t : ctree E T) (h : E ~> Monads.stateT S (ctree F)) (s : S)
    : interp_state h (Guard t) s ≅ Guard (Guard (interp_state h t s)).
  Proof.
    rewrite unfold_interp_state; reflexivity.
  Qed.

  Lemma interp_state_trigger_eqit {E F : Type -> Type} {R: Type}
        (e : E R) (f : E ~> Monads.stateT S (ctree F)) (s : S)
    : (interp_state f (CTree.trigger e) s) ≅ (f _ e s >>= fun x => Guard (Ret x)).
  Proof.
    unfold CTree.trigger. rewrite interp_state_vis; cbn.
    upto_bind_eq.
    apply br_equ. intros _.
    rewrite interp_state_ret.
    now destruct x1.
  Qed.

  Lemma interp_state_trigger {E F : Type -> Type} {R: Type}
        (e : E R) (f : E ~> Monads.stateT S (ctree F)) (s : S)
    : interp_state f (CTree.trigger e) s ~ f _ e s.
  Proof.
    unfold CTree.trigger. rewrite interp_state_vis.
    rewrite <- (bind_ret_r (f R e s)).
    match goal with
      |- ?y ~ ?x => remember y; rewrite <- (bind_ret_r x); subst
    end.
    cbn.
    upto_bind_eq.
    rewrite sb_guard, interp_state_ret.
    now destruct x.
  Qed.

  Lemma interp_state_bind {E F : Type -> Type} {A B: Type}
        (f : forall T, E T -> S -> ctree F (S * T)%type)
        (t : ctree E A) (k : A -> ctree E B)
        (s : S) :
    (interp_state f (t >>= k) s)
      ≅
      (interp_state f t s >>= fun st => interp_state f (k (snd st)) (fst st)).
  Proof.
    revert s t.
    coinduction ? IH; intros.
    rewrite (ctree_eta t).
    cbn.
    rewrite unfold_bind.
    rewrite unfold_interp_state.
    destruct (observe t) eqn:Hobs; cbn.
    - rewrite interp_state_ret. rewrite bind_ret_l. cbn.
      rewrite unfold_interp_state. reflexivity.
    - rewrite interp_state_vis.
      cbn.
      rewrite bind_bind. cbn.
      upto_bind_eq.
      rewrite bind_Guard.
      constructor; intros ?; apply IH.
    - rewrite unfold_interp_state.
      cbn.
      rewrite bind_br.
      constructor; intros ?.
      rewrite bind_Guard.
      step; constructor; intros ?.
      apply IH.
  Qed.

Lemma trans0_interp_state : forall {E F X} (h : E ~> stateT S (ctree F)) (t t' : ctree E X) s,
  trans0 t t' -> trans0 (interp_state h t s) (interp_state h t' s).
Proof.
  intros. red in H. setoid_rewrite (ctree_eta t). setoid_rewrite (ctree_eta t').
  genobs t ot. genobs t' ot'. clear t Heqot t' Heqot'.
  induction H.
  - constructor. rewrite H. reflexivity.
  - rewrite unfold_interp_state. cbn.
    apply T0Br with (x := x).
    apply T0Br with (x := Fin.F1). apply IHtrans0_.
Qed.

(* transi *)

Inductive transi_state {E F X} (h : E ~> stateT S (ctree F)) : @label F -> S -> S -> ctree E X -> ctree E X -> Prop :=
| transis_val : forall (x : X) t t' s,
    trans (val x) t t' ->
    transi_state h (val (s, x)) s s t t'
| transis_tau : forall t t' s,
    trans tau t t' ->
    transi_state h tau s s t t'
| transis_obs : forall Y (e : E Y) x l t t' t'' s s',
    trans (obs e x) t t' ->
    t0_det t'' (Ret (s', x)) ->
    trans l (h _ e s) t'' ->
    transi_state h l s s' t t'
| transis_obs0 : forall Y (e : E Y) l x t t' t'' s s' s'',
    trans (obs e x) t t' ->
    transi_state h l s' s'' t' t'' ->
    trans (val (s', x)) (h _ e s) CTree.stuckD ->
    transi_state h l s s'' t t''
.

#[global] Instance transis_equ :
  forall {E F X} (h : E ~> stateT S (ctree F)) l s s',
  Proper (equ eq ==> equ eq ==> flip impl) (@transi_state E F X h l s s').
Proof.
  cbn. intros.
  revert x x0 H H0. induction H1; intros.
  - apply transis_val. rewrite H0, H1. apply H.
  - apply transis_tau. rewrite H0, H1. apply H.
  - rewrite <- H2, <- H3 in *. eapply transis_obs; eauto.
  - rewrite <- H2 in *. eapply transis_obs0; eauto.
Qed.

#[global] Instance transis_equ' :
  forall {E F X} (h : E ~> stateT S (ctree F)) l s s',
  Proper (equ eq ==> equ eq ==> impl) (@transi_state E F X h l s s').
Proof.
  cbn. intros. rewrite <- H, <- H0. apply H1.
Qed.

Lemma transis_brD {E F X} (h : E ~> stateT S (ctree F)) : forall l s s' (t' : ctree E X) n k x,
  transi_state h l s s' (k x) t' ->
  transi_state h l s s' (BrD n k) t'.
Proof.
  intros. inv H.
  - apply transis_val. etrans.
  - apply transis_tau. etrans.
  - eapply transis_obs; etrans.
  - eapply transis_obs0; etrans.
Qed.

Lemma trans0_transi {E F X} (h : E ~> stateT S (ctree F)) :
  forall l s s' (t t' t'' : ctree E X), trans0 t t' -> transi_state h l s s' t' t'' -> transi_state h l s s' t t''.
Proof.
  intros.
  red in H. rewrite (ctree_eta t). rewrite (ctree_eta t') in H0.
  genobs t ot. genobs t' ot'. clear t Heqot. clear t' Heqot'.
  revert l t'' H0. induction H; intros.
  - rewrite H. apply H0.
  - eapply transis_brD. setoid_rewrite <- ctree_eta in IHtrans0_. apply IHtrans0_. apply H0.
Qed.

Lemma transis_sbisim {E F X} (h : E ~> stateT S (ctree F)) :
  forall l s s' (t t' u : ctree E X), transi_state h l s s' t t' ->
  t ~ u ->
  exists u', transi_state h l s s' u u' /\ t' ~ u'.
Proof.
  intros. revert u H0.
  induction H; intros.
  - step in H0. destruct H0 as [? _]. apply H0 in H. destruct H.
    exists x0. split. now apply transis_val. apply H1.
  - step in H0. destruct H0 as [? _]. apply H0 in H. destruct H.
    exists x. split. now apply transis_tau. apply H1.
  - step in H2. destruct H2 as [? _]. apply H2 in H. destruct H.
    exists x0. split. eapply transis_obs; eauto. apply H3.
  - step in H2. destruct H2 as [? _]. apply H2 in H. destruct H.
    apply IHtransi_state in H3 as (? & ? & ?). exists x1.
    split. eapply transis_obs0; eauto. apply H4.
Qed.

Lemma transis_trans {E F X} (h : E ~> stateT S (ctree F)) (Hh : forall X e s, vsimple (h X e s)) :
  forall l s s' (t t' : ctree E X),
  transi_state h l s s' t t' -> exists t0, trans l (interp_state h t s) t0 /\ t0_det t0 (interp_state h t' s').
Proof.
  intros. induction H.
  - exists CTree.stuckD. apply trans_val_inv in H as ?.
    apply trans_val_trans0 in H as [].
    eapply trans0_interp_state in H. rewrite interp_state_ret in H. setoid_rewrite H0.
    setoid_rewrite interp_state_br. setoid_rewrite br0_always_stuck.
    eapply trans0_trans in H; etrans. split; etrans. now left.
  - exists (Guard (interp_state h t' s)). split; [| eright; eauto; now left ].
    apply trans_tau_trans0 in H as (? & ? & ? & ? & ?).
    eapply trans0_interp_state in H. setoid_rewrite H0. eapply trans0_trans; etrans.
    setoid_rewrite interp_state_br.
    econstructor. reflexivity.
  - exists (x <- t'';; Guard (interp_state h t' s')).
    split. 2: { eapply t0_det_bind_ret_l; eauto. eright; eauto. now left. }
    apply trans_obs_trans0 in H as (? & ? & ?).
    eapply trans0_interp_state in H. setoid_rewrite H2. eapply trans0_trans; etrans.
    setoid_rewrite interp_state_vis.
    eapply trans_bind_l with (k := fun sx => Guard (interp_state h (x0 (snd sx)) (fst sx))) in H1.
    setoid_rewrite t0_det_bind_ret_l_equ in H1 at 2; eauto. cbn in *. eapply H1.
    { intro. inv H3. apply trans_val_inv in H1. rewrite H1 in H0. inv H0. step in H3. inv H3. step in H4. inv H4. }
  - destruct IHtransi_state as (? & ? & ?).
    destruct (Hh Y e s). 2: { destruct H4. rewrite H4 in H1. apply trans_vis_inv in H1 as (? & ? & ?). step in H1. inv H1. }
    destruct H4. rewrite H4 in H1. inv_trans. subst.
    exists x0. split. 2: auto.
    apply trans_obs_trans0 in H as (? & ? & ?). eapply trans0_interp_state in H.
    setoid_rewrite interp_state_vis in H. setoid_rewrite H4 in H. setoid_rewrite bind_ret_l in H.
    eapply trans0_trans; etrans. setoid_rewrite <- H1. etrans.
Qed.

(** Various lemmas for the proof that interp_state preserves sbisim in some cases. *)

Lemma interp_state_ret_inv {E F X} (h : E ~> stateT S (ctree F)) : forall s (t : ctree E X) r,
  interp_state h t s ≅ Ret r -> t ≅ Ret (snd r) /\ s = fst r.
Proof.
  intros. setoid_rewrite (ctree_eta t) in H. setoid_rewrite (ctree_eta t).
  destruct (observe t) eqn:?.
  - rewrite interp_state_ret in H. step in H. inv H. split; reflexivity.
  - rewrite interp_state_vis in H. apply ret_equ_bind in H as (? & ? & ?). step in H0. inv H0.
  - rewrite interp_state_br in H. step in H. inv H.
Qed.

Lemma trans_interp_state_inv_gen {E F X Y} (h : E ~> stateT S (ctree F)) (Hh : forall X e s, vsimple (h X e s)) :
  forall l s (k : Y -> ctree E X) t' (pre : ctree F Y),
  is_simple pre ->
  trans l (x <- pre;; interp_state h (k x) s) t' ->
  exists t0 s', t0_det t' (interp_state h t0 s') /\
  ((exists l t1 x, trans l pre t1 /\ t0_det t1 (Ret x : ctree F Y) /\ t0 ≅ k x) \/
    exists (x : Y), trans (val x) pre CTree.stuckD /\ trans l (interp_state h (k x) s) t' /\ transi_state h l s s' (k x) t0).
Proof.
  intros * Hpre H.
  do 3 red in H. remember (observe (x <- pre;; interp_state h (k x) s)) as oi.
  setoid_rewrite (ctree_eta t') at 1.
  setoid_rewrite (ctree_eta t') at 2.
  genobs t' ot'. clear t' Heqot'.
  assert (go oi ≅ x <- pre;; interp_state h (k x) s).
  { rewrite Heqoi, <- ctree_eta. reflexivity. } clear Heqoi.
  revert Y s k pre Hpre H0. induction H; intros.
  - destruct n. now apply Fin.case0.
    symmetry in H0. apply br_equ_bind in H0 as ?.
    destruct H1 as [[] | (? & ? & ?)].
    + rewrite H1 in H0. setoid_rewrite bind_ret_l in H0. setoid_rewrite H1. clear pre Hpre H1.
      rewrite (ctree_eta (k0 x0)) in H0. destruct (observe (k0 x0)) eqn:?.
      * rewrite interp_state_ret in H0. step in H0. inv H0.
      * rewrite interp_state_vis in H0. apply br_equ_bind in H0 as ?. destruct H1 as [[] | (? & ? & ?)].
        --setoid_rewrite H1 in H0. setoid_rewrite bind_ret_l in H0.
          apply equ_br_invT in H0 as ?. destruct H2 as [? _]. apply eq_add_S in H2 as <-.
          simple apply equ_br_invE with (x := x) in H0.
          rewrite <- H0 in H.
          specialize (IHtrans_ _ (fst x1) (fun (_ : unit) => k1 (snd x1)) (Ret tt)).
          edestruct IHtrans_ as (? & ? & ?).
          { apply is_simple_ret. }
          { rewrite <- ctree_eta. setoid_rewrite bind_ret_l. setoid_rewrite H0. reflexivity. }
          destruct H2. exists x2, x3. split; auto. right. destruct H3.
          { destruct H3 as (? & ? & ? & ? & ? & ?). inv_trans. subst.
            inv H4. step in H3. inv H3. step in H6. inv H6. }
          destruct H3 as (_ & _ & ? & ?). exists x0. split. etrans. split.
          ++setoid_rewrite (ctree_eta (k0 x0)). rewrite Heqc.
            setoid_rewrite interp_state_vis. setoid_rewrite H1. setoid_rewrite bind_ret_l. apply trans_guard. apply H3.
          ++setoid_rewrite (ctree_eta (k0 x0)). rewrite Heqc. destruct x1.
             eapply transis_obs0. etrans. 2: { rewrite H1. etrans. } cbn in H4. cbn in *. etrans.
        --destruct (Hh X0 e s).
          destruct H3. rewrite H3 in H1. step in H1. inv H1.
          destruct H3. rewrite H3 in H1. step in H1. inv H1.
      * rewrite interp_state_br in H0.
        apply equ_br_invT in H0 as ?. destruct H1 as [-> ->].
        simple apply equ_br_invE with (x := x) in H0 as ?.
        specialize (IHtrans_ _ s (fun _ : unit => k1 x) (Guard (Ret tt))).
        edestruct IHtrans_ as (? & ? & ? & ?).
        { apply is_simple_guard_ret. }
        { rewrite <- ctree_eta. setoid_rewrite bind_br. setoid_rewrite bind_ret_l. now rewrite H1. }
        destruct H3.
        { destruct H3 as (? & ? & ? & ? & ? & ?). inv_trans. subst.
          inv H4. step in H3. inv H3. step in H5. inv H5. }
        destruct H3 as (? & ? & ? & ?).
        exists x1, x2. split; auto. right. exists x0. split; etrans. split.
        rewrite (ctree_eta (k0 x0)), Heqc, interp_state_br.
        eapply trans_brD. 2: reflexivity. apply trans_guard. apply H4.
        rewrite (ctree_eta (k0 x0)), Heqc. eapply transis_brD; etrans.
    + specialize (IHtrans_ _ s k0 (x0 x)).
      edestruct IHtrans_ as (? & ? & ? & ?).
      { apply is_simple_brD. red. setoid_rewrite <- H1. apply Hpre. }
      rewrite <- ctree_eta. apply H2. destruct H4 as [(? & ? & ? & ? & ? & ?) | (? & ? & ? & ?)].
        exists (k0 x5), x2. split. { now rewrite H6 in H3. }
        left. eapply trans_brD in H4. 2: reflexivity. rewrite <- H1 in H4. eauto 6.
      * exists x1, x2. split; auto. right. exists x3. rewrite H1. etrans.
  - destruct n. now apply Fin.case0.
    symmetry in H0. apply br_equ_bind in H0 as ?. destruct H1 as [[] | (? & ? & ?)].
    + rewrite H1 in H0. setoid_rewrite bind_ret_l in H0.
      rewrite (ctree_eta (k0 x0)) in H0. destruct (observe (k0 x0)) eqn:?.
      * rewrite interp_state_ret in H0. step in H0. inv H0.
      * rewrite interp_state_vis in H0. apply br_equ_bind in H0 as ?.
        destruct H2 as [[] | (? & ? & ?)].
        { rewrite H2 in H0. setoid_rewrite bind_ret_l in H0. step in H0. inv H0. }
        pose proof (trans_brS x1 x). rewrite <- H2 in H4.
        edestruct Hh. { destruct H5. rewrite H5 in H4. inv_trans. }
        destruct H5. rewrite H5 in H4. apply trans_vis_inv in H4 as (? & ? & ?). discriminate.
      * rewrite interp_state_br in H0.
        apply equ_br_invT in H0 as ?. destruct H2 as [-> ->].
        simple eapply equ_br_invE in H0 as ?. rewrite H in H2.
        exists (k1 x), s. symmetry in H2. split.
        { rewrite <- ctree_eta. rewrite H2. eapply t0_det_tau; auto. apply t0_det_id; auto. }
        right. exists x0. rewrite H1. split; etrans.
        split; setoid_rewrite (ctree_eta (k0 x0)); setoid_rewrite Heqc.
        { setoid_rewrite interp_state_br. rewrite H2.
          econstructor. now rewrite <- ctree_eta. }
        econstructor; etrans.
    + pose proof (trans_brS x0 x).
      rewrite <- H1 in H3. edestruct Hpre.
      { apply H4 in H3. inv H3. }
      apply H4 in H3 as [].
      specialize (H2 x).
      exists (k0 x1), s. rewrite H in H2. split.
      { rewrite <- ctree_eta, H2. eapply t0_det_bind_ret_l; eauto. now left. }
      left. exists tau, (x0 x), x1. split; auto. rewrite H1. etrans.
  - symmetry in H0. apply vis_equ_bind in H0 as ?. destruct H1 as [[] | (? & ? & ?)].
    + rewrite H1 in H0. setoid_rewrite bind_ret_l in H0.
     rewrite (ctree_eta (k0 x0)) in H0. destruct (observe (k0 x0)) eqn:?.
      * rewrite interp_state_ret in H0. step in H0. inv H0.
      * rewrite interp_state_vis in H0. apply vis_equ_bind in H0 as ?.
        destruct H2 as [[] | (? & ? & ?)].
        { rewrite H2 in H0. setoid_rewrite bind_ret_l in H0. step in H0. inv H0. }
        pose proof (trans_vis e x x1). rewrite <- H2 in H4.
        edestruct Hh. { destruct H5. rewrite H5 in H4. inv H4. }
        destruct H5. rewrite H5 in H4.
        specialize (H3 x). rewrite H5 in H2.
        apply equ_vis_invT in H2 as ?. subst.
        apply equ_vis_invE in H2 as ?. destruct H6 as [-> ?].
        rewrite <- H6 in *. rewrite bind_ret_l in H3.
        exists (k1 (snd x)), (fst x).
        rewrite H in H3. split. { rewrite <- ctree_eta, H3. eright; eauto. eleft; auto. }
        right.
        exists x0. rewrite H1. split; etrans.
        split; setoid_rewrite (ctree_eta (k0 x0)); setoid_rewrite Heqc.
        { setoid_rewrite interp_state_vis. rewrite H5. setoid_rewrite bind_vis.
          econstructor. rewrite bind_ret_l. rewrite <- H3, <- ctree_eta. reflexivity. }
        eapply transis_obs; etrans. 2: { rewrite H5. etrans. } destruct x. now left.
      * rewrite interp_state_br in H0. step in H0. inv H0.
    + pose proof (trans_vis e x x0).
      rewrite <- H1 in H3. edestruct Hpre.
      { apply H4 in H3. inv H3. }
      apply H4 in H3 as [].
      specialize (H2 x).
      exists (k0 x1), s. rewrite H in H2. split.
      { rewrite <- ctree_eta, H2. eapply t0_det_bind_ret_l; eauto. now left. }
      left. exists (obs e x), (x0 x), x1. split; auto. rewrite H1. etrans.
     - exists (CTree.stuckD), (fst r). split.
       + left. unfold CTree.stuckD. rewrite interp_state_br.
         rewrite !br0_always_stuck. reflexivity.
       + right. symmetry in H0. apply ret_equ_bind in H0 as (? & ? & ?).
         exists x. rewrite H. split; etrans. split.
         rewrite H0. rewrite br0_always_stuck. etrans.
         apply interp_state_ret_inv in H0 as []. subst. rewrite H0. destruct r. cbn. apply transis_val. econstructor; etrans.
Qed.

Lemma trans_interp_state_inv {E F X} (h : E ~> stateT S (ctree F)) (Hh : forall X e s, vsimple (h X e s)) :
  forall l (t : ctree E X) t' s,
  trans l (interp_state h t s) t' ->
  exists l t0 s', t0_det t' (interp_state h t0 s') /\ transi_state h l s s' t t0.
Proof.
  intros.
   assert (trans l (Guard (Ret tt);; interp_state h t s) t').
   { cbn. etrans. }
  eapply trans_interp_state_inv_gen in H0; eauto. destruct H0 as (? & ? & ? & ?).
  destruct H1 as [(? & ? & ? & ? & ? & ?) | (? & ? & ? & ?)].
  - inv_trans. subst. inv H2. step in H1. inv H1. step in H3. inv H3.
  - inv_trans. subst. eauto.
  - left. intros. inv_trans. subst. constructor.
Qed.

(** The main theorem stating that interp_state preserves sbisim. *)

Theorem interp_state_sbisim_gen {E F X Y} (h : E ~> stateT S (ctree F)) (Hh : forall X e s, vsimple (h X e s)) :
  forall s (k k' : X -> ctree E Y) (pre pre' : ctree F X),
  (forall x, sbisim (k x) (k' x)) ->
  pre ≅ pre' ->
  vsimple pre ->
  sbisim (a <- pre;; Guard (interp_state h (k a) s)) (a <- pre';; Guard (interp_state h (k' a) s)).
Proof.
  revert X. coinduction R CH.
  symmetric using idtac.
  { intros. apply H; eauto.  intros. rewrite H0. reflexivity. now rewrite H1. red; now setoid_rewrite <- H1. }
  assert (CH' : forall (t t' : ctree E Y) s, t ~ t' -> st R (interp_state h t s) (interp_state h t' s)).
  {
    intros.
    assert (st R (a <- Ret tt;; Guard (interp_state h ((fun _ => t) a) s))
      (a <- Ret tt;; Guard (interp_state h ((fun _ => t') a) s))).
    { apply CH; eauto. left; eauto. }
    setoid_rewrite bind_ret_l in H0.
    rewrite !sb_guard in H0.
    apply H0.
  }
  intros. setoid_rewrite <- H0. clear pre' H0. cbn. intros.
  copy H0. rewrite bind_tau_r in H0.
  eapply trans_interp_state_inv_gen in H0 as (? & ? & ? & ?); auto.
  2: { destruct H1 as [[] | []]; rewrite H1.
    rewrite bind_ret_l. apply is_simple_guard_ret.
    rewrite bind_trigger. right. intros. inv_trans. subst.
    exists x0. rewrite EQ. eright. left. reflexivity. reflexivity.
  }
  destruct H2.
  - destruct H2 as (? & ? & ? & ? & ? & ?). rewrite H4 in H0. clear x H4.
    destruct H1 as [[] | []].
    + rewrite H1, bind_ret_l in H2. rewrite H1, bind_ret_l in cpy. inv_trans. subst.
      inv H3. step in H2. inv H2. step in H4. inv H4.
    + rewrite H1 in *. rewrite bind_trigger in H2. apply trans_vis_inv in H2 as (? & ? & ?). subst.
      rewrite H2 in H3. inv H3. step in H4. inv H4.
      apply equ_br_invE in H5. 2: apply Fin.F1.
      rewrite <- H5 in H4. inv H4. 2: { step in H6. inv H6. }
      step in H3. inv H3. clear x2 H2 t H5.
      rewrite bind_trigger in cpy. apply trans_vis_inv in cpy. destruct cpy as (? & ? & ?). subst.
      exists (Guard (interp_state h (k' x1) s)). rewrite H1. rewrite bind_trigger. now constructor.
      rewrite H2, !sb_guard. apply CH'. apply H.
  - destruct H2 as (? & ? & ? & ?).
    destruct H1 as [[] | []]. 2: { rewrite H1 in H2. setoid_rewrite bind_trigger in H2. inv_trans. }
    rewrite H1 in *. rewrite bind_ret_l in H2. inv_trans. subst. clear EQ.
    eapply transis_sbisim in H4; eauto. destruct H4 as (? & ? & ?).
    apply transis_trans in H2 as (? & ? & ?); auto.
    exists x3. rewrite H1, bind_ret_l. etrans.
    assert (st R (interp_state h x x0) (interp_state h x1 x0)).
    { apply CH'. apply H4. }
    rewrite sbisim_t0_det. 2: apply H0.
    setoid_rewrite sbisim_t0_det at 3. 2: apply H5.
    apply H6.
Qed.

#[global] Instance interp_state_sbisim {E F R} (h : E ~> stateT S (ctree F)) (Hh : forall X e s, vsimple (h X e s)) :
  Proper (sbisim ==> eq ==> sbisim) (interp_state h (T := R)).
Proof.
  cbn. intros. subst.
  assert (a <- Ret tt;; Guard (interp_state h ((fun _ => x) a) y0) ~
    a <- Ret tt;; Guard (interp_state h ((fun _ => y) a) y0)).
  apply interp_state_sbisim_gen; auto.
  red; eauto.
  setoid_rewrite bind_ret_l in H0. rewrite !sb_guard in H0. apply H0.
Qed.

End State.

Arguments get {S E _}.
Arguments put {S E _}.
Arguments run_state {S E} [_] _ _.
Arguments interp_state {S E M FM MM IM MC} h [T].
