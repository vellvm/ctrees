From ExtLib Require Import
     Structures.Functor
     Structures.Monad.

From ITree Require Import
     Events.State
     CategoryOps.
Import Basics.Monads.

From CTree Require Import
     CTree
     Fold
     Eq
     Eq.Epsilon
     Eq.SSimAlt
     Eq.SBisimAlt.

Import SBisimNotations.
Import MonadNotation.
Open Scope monad_scope.

Set Implicit Arguments.

#[global] Instance MonadBr_stateT {S M C} {MM : Monad M} {AM : MonadBr C M}: MonadBr C (stateT S M) :=
  fun b X c s => f <- mbr b c;; ret (s,f).

#[global] Instance MonadTrigger_stateT {E S M} {MM : Monad M} {MT: MonadTrigger E M} :
  MonadTrigger E (stateT S M) :=
  fun _ e s => v <- mtrigger e;; ret (s, v).

Definition fold_state {E C M} S
  {FM : Functor M} {MM : Monad M} {IM : MonadIter M}
  (h : E ~> stateT S M) (g : bool -> C ~> stateT S M) :
  ctree E C ~> stateT S M := fold h g.

Definition interp_state {E C M} S
  {FM : Functor M} {MM : Monad M} {IM : MonadIter M} {BM : MonadBr C M}
  (h : E ~> stateT S M) :
  ctree E C ~> stateT S M := interp h.

Definition refine_state {E C M} S
  {FM : Functor M} {MM : Monad M} {IM : MonadIter M} {TM : MonadTrigger E M}
  (g : bool -> C ~> stateT S M) :
  ctree E C ~> stateT S M := refine g.

#[global] Typeclasses Opaque fold_state interp_state refine_state.

Section State.
  Variable (S : Type).
  Variant stateE : Type -> Type :=
    | Get : stateE S
    | Put : S -> stateE unit.

  Definition get {E C} `{stateE -< E} : ctree E C S := trigger Get.
  Definition put {E C} `{stateE -< E} : S -> ctree E C unit := fun s => trigger (Put s).

  Definition h_state {E C} : stateE ~> stateT S (ctree E C) :=
    fun _ e s =>
      match e with
      | Get => Ret (s, s)
      | Put s' => Ret (s', tt)
      end.

  Definition pure_state {E C} : E ~> stateT S (ctree E C)
    := fun _ e s => Vis e (fun x => Ret (s, x)).

  Definition pure_state_choice {E C} b : C ~> stateT S (ctree E C)
    := fun _ c s => br b c (fun x => Ret (s, x)).

  Definition run_state {E C} `{B1 -< C}
    : ctree (stateE +' E) C ~> stateT S (ctree E C) :=
    fold_state (case_ h_state pure_state) pure_state_choice.


End State.

Ltac break :=
  match goal with
  | v: _ * _ |- _ => destruct v
  end.

(* Stateful handlers [E ~> stateT S (itree F)] and morphisms
   [E ~> state S] define stateful itree morphisms
   [itree E ~> stateT S (itree F)]. *)
Section State.

  Variable (S : Type).
  Context {E F C D : Type -> Type}
          `{B1 -< D}
          {R : Type}
          (h : E ~> stateT S (ctree F D))
          (g : bool -> C ~> stateT S (ctree F D)).

  (** Unfolding of [fold]. *)
  Notation fold_state_ h g t s :=
    (match observe t with
     | RetF r => Ret (s, r)
     | VisF e k => bind (h _ e s) (fun xs => Guard (fold_state h g (k (snd xs)) (fst xs)))
     | BrF b c k => bind (g b _ c s) (fun xs => Guard (fold_state h g (k (snd xs)) (fst xs)))
     end)%function.

  Lemma unfold_fold_state (t : ctree E C R) (s : S) :
    fold_state h g t s ≅ fold_state_ h g t s.
  Proof.
    unfold fold_state, fold, MonadIter_stateT0, iter, MonadIter_ctree, Basics.iter.
    rewrite unfold_iter at 1.
    cbn.
    rewrite bind_bind.
    destruct (observe t); cbn.
    - now repeat (cbn; rewrite ?bind_ret_l).
    - rewrite bind_map. cbn.
      upto_bind_eq.
      now cbn; rewrite ?bind_ret_l.
    - rewrite bind_map. cbn.
      upto_bind_eq.
      now cbn; rewrite ?bind_ret_l.
  Qed.

  #[global] Instance equ_fold_state:
    Proper (equ eq ==> eq ==> equ eq)
           (fold_state h g (T := R)).
  Proof.
    unfold Proper, respectful.
    coinduction ? IH; intros * EQ1 * <-.
    rewrite !unfold_fold_state.
    step in EQ1; inv EQ1; auto.
    - cbn. upto_bind_eq.
      constructor; intros; auto.
    - simpl bind. upto_bind_eq.
      constructor; auto.
  Qed.

  Lemma fold_state_ret
        (s : S) (r : R) :
    (fold_state h g (Ret r) s) ≅ (Ret (s, r)).
  Proof.
    rewrite ctree_eta. reflexivity.
  Qed.

  Lemma fold_state_vis {T : Type}
    (e : E T) (k : T -> ctree E C R) (s : S) :
    fold_state h g (Vis e k) s ≅ h e s >>= fun sx => Guard (fold_state h g (k (snd sx)) (fst sx)).
  Proof.
    rewrite unfold_fold_state; reflexivity.
  Qed.

  Lemma fold_state_br {T: Type} `{C -< D}
    (b : bool) (c : C T) (k : T -> ctree E C R) (s : S) :
    fold_state h g (br b c k) s ≅ g b c s >>= fun sx => Guard (fold_state h g (k (snd sx)) (fst sx)).
  Proof.
    rewrite !unfold_fold_state; reflexivity.
  Qed.

  (* TODO move *)
  #[global] Instance equ_Guard:
    forall {E B : Type -> Type} {R : Type} `{B1 -< B},
      Proper (equ eq ==> equ eq) (@Guard E B R _).
  Proof.
    repeat intro.
    unfold Guard; now setoid_rewrite H1.
  Qed.

  Lemma fold_state_trigger (e : E R) (s : S) :
    fold_state h g (CTree.trigger e) s ≅
    h e s >>= fun x => Guard (Ret x).
  Proof.
    unfold CTree.trigger.
    rewrite fold_state_vis; cbn.
    upto_bind_eq; cbn.
    rewrite fold_state_ret.
    now break.
  Qed.

  Lemma fold_state_trigger_sb `{B0 -< D} (e : E R) (s : S)
    : fold_state h g (CTree.trigger e) s ~ h e s.
  Proof.
    unfold CTree.trigger. rewrite fold_state_vis.
    rewrite <- (bind_ret_r (h e s)) at 2.
    cbn.
    upto_bind_eq.
    rewrite sb_guard, fold_state_ret.
    now break.
  Qed.

  (** Unfolding of [interp]. *)
  Notation interp_state_ h t s :=
    (match observe t with
     | RetF r => Ret (s, r)
	   | VisF e k => bind (h _ e s) (fun xs => Guard (interp_state h (k (snd xs)) (fst xs)))
	   | BrF b c k => bind (mbr (M := stateT _ _) b c s) (fun xs => Guard (interp_state h (k (snd xs)) (fst xs)))
     end)%function.

  Lemma unfold_interp_state `{C-<D} (t : ctree E C R) (s : S) :
    interp_state h t s ≅ interp_state_ h t s.
  Proof.
    unfold interp_state, interp, MonadIter_stateT0, fold, MonadIter_ctree, Basics.iter.
    rewrite unfold_iter at 1.
    cbn.
    rewrite bind_bind.
    destruct (observe t); cbn.
    - now repeat (cbn; rewrite ?bind_ret_l).
    - rewrite bind_map. cbn.
      upto_bind_eq.
      now cbn; rewrite ?bind_ret_l.
    - rewrite bind_map. cbn.
      upto_bind_eq.
      now cbn; rewrite ?bind_ret_l.
  Qed.

  #[global] Instance equ_interp_state `{C-<D}:
    Proper (equ eq ==> eq ==> equ eq)
           (interp_state (C := C) h (T := R)).
  Proof.
    unfold Proper, respectful.
    coinduction ? IH; intros * EQ1 * <-.
    rewrite !unfold_interp_state.
    step in EQ1; inv EQ1; auto.
    - cbn. upto_bind_eq.
      constructor; intros; auto.
    - simpl bind. upto_bind_eq.
      constructor; auto.
  Qed.

  Lemma interp_state_ret `{C-<D}
        (s : S) (r : R) :
    (interp_state (C := C) h (Ret r) s) ≅ (Ret (s, r)).
  Proof.
    rewrite ctree_eta. reflexivity.
  Qed.

  Lemma interp_state_vis `{C-<D} {T : Type}
    (e : E T) (k : T -> ctree E C R) (s : S) :
    interp_state h (Vis e k) s ≅ h e s >>= fun sx => Guard (interp_state h (k (snd sx)) (fst sx)).
  Proof.
    rewrite unfold_interp_state; reflexivity.
  Qed.

  Lemma interp_state_br {T: Type} `{C -< D}
    (b : bool) (c : C T) (k : T -> ctree E C R) (s : S) :
    interp_state h (Br b c k) s ≅ branch b c >>= fun x => Guard (interp_state h (k x) s).
  Proof.
    rewrite !unfold_interp_state; cbn.
    rewrite bind_bind.
    upto_bind_eq.
    rewrite bind_ret_l.
    reflexivity.
  Qed.

  Lemma interp_state_guard `{B1 -< C} `{C -< D}
    (t : ctree E C R) (s : S) :
    interp_state h (Guard t) s ≅
    Guard (H := fun _ c => H1 _ (H0 _ c))
      (Guard (interp_state h t s)).
  Proof.
    unfold Guard at 1.
    rewrite interp_state_br.
    cbn.
    unfold branch; rewrite bind_br.
    rewrite subevent_subevent.
    apply br_equ. intros.
    rewrite bind_ret_l.
    reflexivity.
  Qed.

  Lemma interp_interp_state `{C -< D} : forall (t : ctree E C R) s,
    interp h t s ≅ interp_state h t s.
  Proof.
    reflexivity.
  Qed.

  (** Unfolding of [refine]. *)
  Notation refine_state_ g t s :=
    (match observe t with
     | RetF r => Ret (s, r)
	   | VisF e k => bind (mtrigger e) (fun x => Guard (refine_state g (k x) s))
	   | BrF b c k => bind (g b _ c s) (fun xs => Guard (refine_state g (k (snd xs)) (fst xs)))
     end)%function.

  Lemma unfold_refine_state `{E-<F} (t : ctree E C R) (s : S) :
    refine_state g t s ≅ refine_state_ g t s.
  Proof.
    unfold refine_state, refine, MonadIter_stateT0, fold, MonadIter_ctree, Basics.iter.
    rewrite unfold_iter at 1.
    cbn.
    rewrite !bind_bind.
    destruct (observe t); cbn.
    - now repeat (cbn; rewrite ?bind_ret_l).
    - rewrite bind_map. cbn.
      rewrite !bind_bind.
      upto_bind_eq.
      now cbn; rewrite ?bind_ret_l.
    - rewrite bind_map. cbn.
      upto_bind_eq.
      now cbn; rewrite ?bind_ret_l.
  Qed.

  #[global] Instance equ_refine_state `{E-<F}:
    Proper (equ eq ==> eq ==> equ eq)
           (refine_state (E := E) g (T := R)).
  Proof.
    unfold Proper, respectful.
    coinduction ? IH; intros * EQ1 * <-.
    rewrite !unfold_refine_state.
    step in EQ1; inv EQ1; auto.
    - cbn. upto_bind_eq.
      constructor; intros; auto.
    - simpl bind. upto_bind_eq.
      constructor; auto.
  Qed.

  Lemma refine_state_ret `{E-<F}
        (s : S) (r : R) :
    (refine_state (E := E) g (Ret r) s) ≅ (Ret (s, r)).
  Proof.
    rewrite ctree_eta. reflexivity.
  Qed.

  Lemma refine_state_vis `{E-<F} {T : Type}
    (e : E T) (k : T -> ctree E C R) (s : S) :
    refine_state g (Vis e k) s ≅
      trigger e >>= fun x => Guard (refine_state g (k x) s).
  Proof.
    rewrite unfold_refine_state; reflexivity.
  Qed.

  Lemma refine_state_br {T: Type} `{E -< F}
    (b : bool) (c : C T) (k : T -> ctree E C R) (s : S) :
    refine_state g (Br b c k) s ≅
    g b c s >>= fun xs => Guard (refine_state g (k (snd xs)) (fst xs)).
  Proof.
    rewrite !unfold_refine_state; cbn.
    now upto_bind_eq.
  Qed.

End State.

Section FoldBind.
  Variable (S : Type).
  Context {E F C D : Type -> Type}
    `{B1 -< D}.

  Lemma fold_state_bind
    (h : E ~> stateT S (ctree F D))
    (g : bool -> C ~> stateT S (ctree F D))
    {A B}
    (t : ctree E C A) (k : A -> ctree E C B)
    (s : S) :
    fold_state h g (t >>= k) s
      ≅ fold_state h g t s >>= fun st => fold_state h g (k (snd st)) (fst st).
  Proof.
    revert s t.
    coinduction ? IH; intros.
    rewrite (ctree_eta t).
    cbn.
    rewrite unfold_bind.
    rewrite unfold_fold_state.
    destruct (observe t) eqn:Hobs; cbn.
    - rewrite fold_state_ret. rewrite bind_ret_l. cbn.
      rewrite unfold_fold_state. reflexivity.
    - rewrite fold_state_vis.
      cbn.
      rewrite bind_bind. cbn.
      upto_bind_eq.
      rewrite bind_guard.
      constructor; intros ?; apply IH.
    - rewrite unfold_fold_state.
      cbn.

      rewrite bind_bind.
      upto_bind_eq.
      rewrite bind_guard.
      constructor; intros ?; apply IH.
  Qed.

  Lemma interp_state_bind `{C -< D}
    (h : E ~> stateT S (ctree F D))
    {A B}
    (t : ctree E C A) (k : A -> ctree E C B)
    (s : S) :
    interp_state h (t >>= k) s ≅ interp_state h t s >>= fun xs => interp_state h (k (snd xs)) (fst xs).
  Proof.
    eapply fold_state_bind.
  Qed.

  Lemma refine_state_bind `{E -< F}
    (g : bool -> C ~> stateT S (ctree F D))
    {A B}
    (t : ctree E C A) (k : A -> ctree E C B)
    (s : S) :
    refine_state g (t >>= k) s ≅ refine_state g t s >>= fun xs => refine_state g (k (snd xs)) (fst xs).
  Proof.
    eapply fold_state_bind.
  Qed.

End FoldBind.

(* Stateful handlers [E ~> stateT S (itree F)] and morphisms
   [E ~> state S] define stateful itree morphisms
   [itree E ~> stateT S (itree F)]. *)
From CTree Require Import FoldCTree.

(* TODO MOVE *)
Lemma trans_branch :
  forall {E B : Type -> Type} {X : Type} {H : B0 -< B} {Y : Type}
    [l : label] [t t' : ctree E B X] (c : B Y) (k : Y -> ctree E B X) (x : Y),
    trans l t t' -> k x ≅ t -> trans l (CTree.branch false c >>= k) t'.
Proof.
  intros.
  setoid_rewrite bind_branch.
  eapply trans_brD; eauto.
Qed.

Section transi_state.

  Variable S : Type.
  Context {E F C D : Type -> Type}
    `{CST1 : B0 -< C} {CST2 : C -< D} `{CST3 : B1 -< D} `{CST4 : E -< F}.
  Context {X : Type}.
  Variable (h : E ~> stateT S (ctree F D)).

  Lemma epsilon_interp_state : forall (t t' : ctree E C X) s,
      epsilon t t' ->
      epsilon (interp_state h t s) (interp_state h t' s).
  Proof.
    intros; red in H.
    rewrite (ctree_eta t), (ctree_eta t').
    genobs t ot. genobs t' ot'. clear t Heqot t' Heqot'.
    induction H.
    - constructor. rewrite H. reflexivity.
    - rewrite unfold_interp_state. cbn.
      rewrite bind_bind.
      unfold mbr, MonadBr_ctree, CTree.branch.
      rewrite bind_br.
      eapply EpsilonBr with (x := x).
      rewrite !bind_ret_l.
      cbn.
      eapply EpsilonBr with (x := tt).
      apply IHepsilon_.
  Qed.

  (* transi *)

  Instance foo : B0 -< D.
  intros ? ?; now apply CST2, CST1.
  Defined.

  Inductive transi_state : @label F -> S -> S -> ctree E C X -> ctree E C X -> Prop :=
  | transis_val : forall (x : X) t t' s,
      trans (val x) t t' ->
      transi_state (val (s, x)) s s t t'
  | transis_tau : forall t t' s,
      trans tau t t' ->
      transi_state tau s s t t'
  | transis_obs : forall Y (e : E Y) x l t t' t'' s s',
      trans (obs e x) t t' ->
      epsilon_det t'' (Ret (s', x)) ->
      trans l (h e s) t'' ->
      transi_state l s s' t t'
  | transis_obs0 : forall Y (e : E Y) l x t t' t'' s s' s'',
      trans (obs e x) t t' ->
      transi_state l s' s'' t' t'' ->
      trans (val (s', x)) (h e s) stuckD ->
      transi_state l s s'' t t''
  .

  #[global] Instance transis_equ :
    forall l s s',
      Proper (equ eq ==> equ eq ==> flip impl) (@transi_state l s s').
  Proof.
    cbn. intros.
    revert x x0 H H0. induction H1; intros.
    - apply transis_val. rewrite H0, H1. apply H.
    - apply transis_tau. rewrite H0, H1. apply H.
    - rewrite <- H2, <- H3 in *. eapply transis_obs; eauto.
    - rewrite <- H2 in *. eapply transis_obs0; eauto.
  Qed.

  #[global] Instance transis_equ' :
    forall l s s',
      Proper (equ eq ==> equ eq ==> impl) (@transi_state l s s').
  Proof.
    cbn. intros. rewrite <- H, <- H0. apply H1.
  Qed.

  Lemma transis_brD : forall Y l s s' (t' : ctree E C X) (c : C Y) k x,
      transi_state l s s' (k x) t' ->
      transi_state l s s' (BrD c k) t'.
  Proof.
    intros. inv H.
    - apply transis_val. etrans.
    - apply transis_tau. etrans.
    - eapply transis_obs; etrans.
    - eapply transis_obs0; etrans.
  Qed.

  Lemma epsilon_transi :
    forall l s s' (t t' t'' : ctree E C X),
      epsilon t t' ->
      transi_state l s s' t' t'' ->
      transi_state l s s' t t''.
  Proof.
    intros.
    red in H. rewrite (ctree_eta t). rewrite (ctree_eta t') in H0.
    genobs t ot. genobs t' ot'. clear t Heqot. clear t' Heqot'.
    revert l t'' H0. induction H; intros.
    - rewrite H. apply H0.
    - eapply transis_brD. setoid_rewrite <- ctree_eta in IHepsilon_. apply IHepsilon_. apply H0.
  Qed.

  Lemma transis_sbisim :
    forall l s s' (t t' u : ctree E C X),
      transi_state l s s' t t' ->
      t ~ u ->
      exists u', transi_state l s s' u u' /\ t' ~ u'.
  Proof.
    intros. revert u H0.
    induction H; intros.
    - step in H0. destruct H0 as [? _]. apply H0 in H.
      destruct H as (? & ? & ? & ? & ?); subst.
      eexists. split. eapply transis_val; eauto. apply H1.
    - step in H0. destruct H0 as [? _]. apply H0 in H.
      destruct H as (? & ? & ? & ? & ?); subst.
      eexists. split. eapply transis_tau; eauto. apply H1.
    - step in H2. destruct H2 as [? _]. apply H2 in H.
      destruct H as (? & ? & ? & ? & ?); subst.
      eexists. split. eapply transis_obs; eauto. apply H3.
    - step in H2. destruct H2 as [? _]. apply H2 in H.
      destruct H as (? & ? & ? & ? & ?); subst.
      apply IHtransi_state in H3 as (? & ? & ?).
      eexists; split. eapply transis_obs0; eauto. apply H4.
  Qed.

  Lemma transis_trans (Hh : forall X (e : _ X) s, vsimple (h e s)) :
    forall l s s' (t t' : ctree E C X),
      transi_state l s s' t t' ->
      exists t0, trans l (interp_state h t s) t0 /\ epsilon_det t0 (interp_state h t' s').
  Proof.
    intros. induction H.
    - exists stuckD. apply trans_val_inv in H as ?.
      apply trans_val_epsilon in H as [].
      eapply epsilon_interp_state in H. rewrite interp_state_ret in H. setoid_rewrite H0.
      setoid_rewrite interp_state_br.
      split.
      eapply epsilon_trans in H; etrans.
      left.
      setoid_rewrite bind_branch.
      step.
      constructor; intros [].

    - exists (Guard (interp_state h t' s)). split; [| eright; eauto; now left ].
      apply trans_tau_epsilon in H as (? & ? & ? & ? & ? & ?).
      eapply epsilon_interp_state in H. setoid_rewrite H0. eapply epsilon_trans; etrans.
      rewrite interp_state_br. setoid_rewrite bind_branch.
      econstructor. reflexivity.
    - exists (x <- t'';; Guard (interp_state h t' s')).
      split.
      2: { eapply epsilon_det_bind_ret_l; eauto. eright; eauto. }
      apply trans_obs_epsilon in H as (? & ? & ?).
      eapply epsilon_interp_state in H. setoid_rewrite H2. eapply epsilon_trans; etrans.
      setoid_rewrite interp_state_vis.
      eapply trans_bind_l with (k := fun sx => Guard (interp_state h (x0 (snd sx)) (fst sx))) in H1.
      setoid_rewrite epsilon_det_bind_ret_l_equ in H1 at 2; eauto. cbn in *. eapply H1.
      { intro. inv H3. apply trans_val_inv in H1. rewrite H1 in H0. inv H0. step in H3. inv H3. step in H4. inv H4. auto using void_unit_elim. }
    - destruct IHtransi_state as (? & ? & ?).
      destruct (Hh Y e s).
      2: { destruct H4. rewrite H4 in H1. apply trans_vis_inv in H1 as (? & ? & ?). step in H1. inv H1. }
      destruct H4. rewrite H4 in H1. inv_trans. subst.
      exists x0. split. 2: auto.
      apply trans_obs_epsilon in H as (? & ? & ?). eapply epsilon_interp_state in H.
      setoid_rewrite interp_state_vis in H. setoid_rewrite H4 in H. setoid_rewrite bind_ret_l in H.
      eapply epsilon_trans; etrans. setoid_rewrite <- H1. etrans.
  Qed.

  Lemma interp_state_ret_inv :
    forall s (t : ctree E C X) r,
      interp_state h t s ≅ Ret r -> t ≅ Ret (snd r) /\ s = fst r.
  Proof.
    intros. setoid_rewrite (ctree_eta t) in H. setoid_rewrite (ctree_eta t).
    destruct (observe t) eqn:?.
    - rewrite interp_state_ret in H. step in H. inv H. split; reflexivity.
    - rewrite interp_state_vis in H. apply ret_equ_bind in H as (? & ? & ?). step in H0. inv H0.
    - rewrite interp_state_br in H. step in H. inv H.
  Qed.

  Lemma trans_interp_state_inv_gen (Hh : forall X (e : _ X) s, vsimple (h e s)) :
    forall Y l s (k : Y -> ctree E C X) t' (pre : ctree F D Y),
      is_simple pre ->
      trans l (x <- pre;; interp_state h (k x) s) t' ->
      exists t0 s', epsilon_det t' (interp_state h t0 s') /\
                 ((exists l t1 x, trans l pre t1 /\ epsilon_det t1 (Ret x : ctree F D Y) /\ t0 ≅ k x) \/
                    exists (x : Y), trans (val x) pre stuckD /\ trans l (interp_state h (k x) s) t' /\ transi_state l s s' (k x) t0).
  Proof.
    intros * Hpre H.
    do 3 red in H. remember (observe (x <- pre;; interp_state h (k x) s)) as oi.
    setoid_rewrite (ctree_eta t') at 1.
    setoid_rewrite (ctree_eta t') at 2.
    genobs t' ot'. clear t' Heqot'.
    assert (go oi ≅ x <- pre;; interp_state h (k x) s).
    { rewrite Heqoi, <- ctree_eta. reflexivity. } clear Heqoi.
    revert Y s k pre Hpre H0. induction H; intros.
    - symmetry in H0. apply br_equ_bind in H0 as ?.
      destruct H1 as [[] | (? & ? & ?)].
      + rewrite H1 in H0. setoid_rewrite bind_ret_l in H0. setoid_rewrite H1. clear pre Hpre H1.
        rewrite (ctree_eta (k0 x0)) in H0. destruct (observe (k0 x0)) eqn:?.
        * rewrite interp_state_ret in H0. step in H0. inv H0.
        * rewrite interp_state_vis in H0. apply br_equ_bind in H0 as ?. destruct H1 as [[] | (? & ? & ?)].
          --setoid_rewrite H1 in H0. setoid_rewrite bind_ret_l in H0.
            inv_equ.
            rewrite <- EQ in H.
            specialize (IHtrans_ _ (fst x1) (fun (_ : unit) => k1 (snd x1)) (Ret tt)).
            edestruct IHtrans_ as (? & ? & ?).
            { apply is_simple_ret. }
            { rewrite <- ctree_eta. setoid_rewrite bind_ret_l. setoid_rewrite EQ. reflexivity. }
            destruct H0. exists x2, x3. split; auto. right. destruct H2.
            { destruct H2 as (? & ? & ? & ? & ? & ?). inv_trans. subst.
              inv H3. step in H2. inv H2. step in H5. inv H5.
              exfalso; now apply void_unit_elim.
            }
            destruct H2 as (_ & _ & ? & ?). exists x0. split. etrans. split.
            ++setoid_rewrite (ctree_eta (k0 x0)). rewrite Heqc0.
              setoid_rewrite interp_state_vis. setoid_rewrite H1. setoid_rewrite bind_ret_l. apply trans_guard. apply H2.
            ++setoid_rewrite (ctree_eta (k0 x0)). rewrite Heqc0. destruct x1.
              eapply transis_obs0. etrans. 2: { rewrite H1. etrans. } cbn in H3. cbn in *. etrans.
          -- destruct (Hh _ e s).
             destruct H3. rewrite H3 in H1. step in H1. inv H1.
             destruct H3. rewrite H3 in H1. step in H1. inv H1.
        * rewrite interp_state_br in H0.
          setoid_rewrite bind_branch in H0.
          inv_equ.
          specialize (IHtrans_ _ s (fun _ : unit => k1 x) (Guard (Ret tt))).
          edestruct IHtrans_ as (? & ? & ? & ?).
          { apply is_simple_guard_ret. }
          { rewrite <- ctree_eta. setoid_rewrite bind_br. setoid_rewrite bind_ret_l. now rewrite <- EQ. }
          destruct H1.
          { destruct H1 as (? & ? & ? & ? & ? & ?). inv_trans. subst.
            inv H2. step in H1. inv H1. step in H3. inv H3.
            exfalso; now apply void_unit_elim.
          }
          destruct H1 as (? & ? & ? & ?).
          exists x1, x2. split; auto. right. exists x0. split; etrans. split.
          rewrite (ctree_eta (k0 x0)), Heqc0, interp_state_br.
          eapply trans_branch.
          2: reflexivity. apply trans_guard. apply H2.
          rewrite (ctree_eta (k0 x0)), Heqc0. eapply transis_brD; etrans.
      + specialize (IHtrans_ _ s k0 (x0 x)).
        edestruct IHtrans_ as (? & ? & ? & ?).
        { eapply is_simple_brD. red. setoid_rewrite <- H1. apply Hpre. }
        rewrite <- ctree_eta. apply H2. destruct H4 as [(? & ? & ? & ? & ? & ?) | (? & ? & ? & ?)].
        exists (k0 x5), x2. split. { now rewrite H6 in H3. }
        left. eapply trans_brD in H4. 2: reflexivity. rewrite <- H1 in H4. eauto 6.
        * exists x1, x2. split; auto. right. exists x3. rewrite H1. etrans.
    - symmetry in H0. apply br_equ_bind in H0 as ?. destruct H1 as [[] | (? & ? & ?)].
      + rewrite H1 in H0. setoid_rewrite bind_ret_l in H0.
        rewrite (ctree_eta (k0 x0)) in H0. destruct (observe (k0 x0)) eqn:?.
        * rewrite interp_state_ret in H0. step in H0. inv H0.
        * rewrite interp_state_vis in H0. apply br_equ_bind in H0 as ?.
          destruct H2 as [[] | (? & ? & ?)].
          { rewrite H2 in H0. setoid_rewrite bind_ret_l in H0. step in H0. inv H0. }
          pose proof (trans_brS c x1 x). rewrite <- H2 in H4.
          edestruct Hh. { destruct H5. rewrite H5 in H4. inv_trans. }
          destruct H5. rewrite H5 in H4. apply trans_vis_inv in H4 as (? & ? & ?). discriminate.
        * rewrite interp_state_br in H0.
          setoid_rewrite bind_branch in H0.
          inv_equ.
          specialize (EQ x). rewrite H in EQ.
          exists (k1 x), s. symmetry in EQ. split.
          { rewrite <- ctree_eta. rewrite EQ. eapply epsilon_det_tau; auto. }
          right. exists x0. rewrite H1. split; etrans.
          split; setoid_rewrite (ctree_eta (k0 x0)); setoid_rewrite Heqc0.
          { setoid_rewrite interp_state_br. rewrite EQ.
            setoid_rewrite bind_branch.
            econstructor. now rewrite <- ctree_eta. }
          econstructor; etrans.
      + pose proof (trans_brS c x0 x).
        rewrite <- H1 in H3. edestruct Hpre.
        { apply H4 in H3. inv H3. }
        apply H4 in H3 as [].
        specialize (H2 x).
        exists (k0 x1), s. rewrite H in H2. split.
        { rewrite <- ctree_eta, H2. eapply epsilon_det_bind_ret_l; eauto. }
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
          inv_equ.
          rewrite <- EQ in *. rewrite bind_ret_l in H3.
          exists (k1 (snd x)), (fst x).
          rewrite H in H3. split. { rewrite <- ctree_eta, H3. eright; eauto. }
          right.
          exists x0. rewrite H1. split; etrans.
          split; setoid_rewrite (ctree_eta (k0 x0)); setoid_rewrite Heqc.
          { setoid_rewrite interp_state_vis. rewrite H5. setoid_rewrite bind_vis.
            econstructor. rewrite bind_ret_l. rewrite <- H3, <- ctree_eta. reflexivity. }
          eapply transis_obs; etrans. rewrite H5. destruct x. etrans.
        * rewrite interp_state_br in H0. step in H0. inv H0.
      + pose proof (trans_vis e x x0).
        rewrite <- H1 in H3. edestruct Hpre.
        { apply H4 in H3. inv H3. }
        apply H4 in H3 as [].
        specialize (H2 x).
        exists (k0 x1), s. rewrite H in H2. split.
        { rewrite <- ctree_eta, H2. eapply epsilon_det_bind_ret_l; eauto. }
        left. exists (obs e x), (x0 x), x1. split; auto. rewrite H1. etrans.
    - exists stuckD, (fst r). split.
      + left. unfold stuck. rewrite interp_state_br.
        rewrite !br0_always_stuck.
        setoid_rewrite bind_branch.
        step.
        constructor; intros [].
      + right. symmetry in H0. apply ret_equ_bind in H0 as (? & ? & ?).
        exists x. rewrite H. split; etrans. split.
        rewrite H0. rewrite br0_always_stuck. etrans.
        apply interp_state_ret_inv in H0 as []. subst. rewrite H0. destruct r. cbn. apply transis_val. econstructor; etrans.
  Qed.

  Lemma trans_interp_state_inv (Hh : forall X (e : _ X) s, vsimple (h e s)) :
    forall l (t : ctree E C X) t' s,
      trans l (interp_state h t s) t' ->
      exists l t0 s', epsilon_det t' (interp_state h t0 s') /\ transi_state l s s' t t0.
  Proof.
    intros.
    assert (trans l (Guard (Ret tt);; interp_state h t s) t').
    { cbn. etrans. }
    eapply trans_interp_state_inv_gen in H0; eauto. destruct H0 as (? & ? & ? & ?).
    destruct H1 as [(? & ? & ? & ? & ? & ?) | (? & ? & ? & ?)].
    - inv_trans. subst. inv H2. step in H1. inv H1. step in H3. inv H3.
      exfalso; now apply void_unit_elim.
    - inv_trans. subst. eauto.
    - left. intros. inv_trans. subst. constructor.
  Qed.

(** The main theorem stating that fold_state preserves sbisim. *)

  Theorem interp_state_sbisim_gen {Y} (Hh : forall X (e : _ X) s, vsimple (h e s)) :
    forall s (k k' : Y -> ctree E C X) (pre pre' : ctree F D Y),
      (forall x, sbisim eq (k x) (k' x)) ->
      pre ≅ pre' ->
      vsimple pre ->
      sbisim eq (a <- pre;; Guard (interp_state h (k a) s)) (a <- pre';; Guard (interp_state h (k' a) s)).
  Proof.
    revert Y. coinduction R CH.
    (* We would like to use a symmetry argument here, as is done in the 0.1 branch *)
    symmetric using idtac.
    { intros. apply H. now symmetry. now symmetry. red. now setoid_rewrite <- H1. }
    assert (CH' : forall (t t' : ctree E C X) s, t ~ t' -> st eq R (interp_state h t s) (interp_state h t' s)).
    {
      intros.
      assert (st eq R (a <- Ret tt;; Guard (interp_state h ((fun _ => t) a) s))
                (a <- Ret tt;; Guard (interp_state h ((fun _ => t') a) s))).
      { apply CH; eauto. left; eauto. }
      setoid_rewrite bind_ret_l in H0.
      rewrite !sb_guard in H0.
      apply H0.
    }
    intros. setoid_rewrite <- H0. clear pre' H0. cbn.
    cbn; intros.
    copy H0. rewrite bind_guard_r in H0.
    eapply trans_interp_state_inv_gen in H0 as (? & ? & ? & ?); auto.
    2: { destruct H1 as [[] | []]; rewrite H1.
         rewrite bind_ret_l. apply is_simple_guard_ret.
         rewrite bind_trigger. right. intros. inv_trans. subst.
         exists x0. rewrite EQ. eright. left. reflexivity. reflexivity.
    }
    destruct H2.
    + destruct H2 as (? & ? & ? & ? & ? & ?). rewrite H4 in H0. clear x H4.
      destruct H1 as [[] | []].
      * rewrite H1, bind_ret_l in H2. rewrite H1, bind_ret_l in cpy. inv_trans. subst.
        inv H3. step in H2. inv H2. step in H4. inv H4.
        exfalso; now apply void_unit_elim.
      * rewrite H1 in *. rewrite bind_trigger in H2. apply trans_vis_inv in H2 as (? & ? & ?). subst.
        rewrite H2 in H3. inv H3. step in H4. inv H4.
        apply equ_br_invE in H5 as [_ ?].
        rewrite <- H3 in H4; auto. inv H4.
        2: { step in H6. inv H6. }
        step in H5. inv H5.
        rewrite bind_trigger in cpy. apply trans_vis_inv in cpy. destruct cpy as (? & ? & ?). subst.
        eexists. exists (Guard (interp_state h (k' x1) s)). rewrite H1. rewrite bind_trigger. split.
        now constructor.
        split; auto.
        rewrite H4, !sb_guard. apply CH'. apply H.
    + destruct H2 as (? & ? & ? & ?).
      destruct H1 as [[] | []].
      2: { rewrite H1 in H2. setoid_rewrite bind_trigger in H2. inv_trans. }
      rewrite H1 in *. rewrite bind_ret_l in H2. inv_trans. subst. clear EQ.
      eapply transis_sbisim in H4; eauto. destruct H4 as (? & ? & ?).
      apply transis_trans in H2 as (? & ? & ?); auto.
      eexists; exists x3. rewrite H1, bind_ret_l. split.
      etrans.
      assert (st eq R (interp_state h x x0) (interp_state h x1 x0)).
      { apply CH'. apply H4. }
      split; auto.
      rewrite sbisim_epsilon_det. 2: apply H0.
      apply sbisim_epsilon_det in H5; rewrite H5.
      apply H6.
  Qed.

  #[global] Instance interp_state_sbisim (Hh : forall X (e : _ X) s, vsimple (h e s)) :
    Proper (sbisim eq ==> eq ==> sbisim eq) (interp_state h (C := C) (T := X)).
  Proof.
    cbn. intros. subst.
    assert (a <- Ret tt;; Guard (interp_state h ((fun _ => x) a) y0) ~
                           a <- Ret tt;; Guard (interp_state h ((fun _ => y) a) y0)).
    apply interp_state_sbisim_gen; auto.
    red; eauto.
    setoid_rewrite bind_ret_l in H0. rewrite !sb_guard in H0. apply H0.
  Qed.

End transi_state.

Definition lift_handler {E F B} (h : E ~> ctree F B) : E ~> Monads.stateT unit (ctree F B) :=
  fun _ e s => CTree.map (fun x => (tt, x)) (h _ e).

Lemma is_simple_lift_handler {E F B} `{HasB0: B0 -< B} `{HasB1: B1 -< B} (h : E ~> ctree F B) :
  (forall Y (e : E Y), is_simple (h _ e)) ->
  forall Y (e : E Y) st, is_simple (lift_handler h _ e st).
Proof.
  intros.
  specialize (H Y e). red. destruct H; [left | right]; intros.
  - unfold lift_handler, CTree.map in H0.
    apply trans_bind_inv in H0 as ?. destruct H1 as [(? & ? & ? & ?) | (? & ? & ?)].
    + subs. now apply H in H2.
    + inv_trans. now subst.
  - unfold lift_handler, CTree.map in H0.
    apply trans_bind_inv in H0 as ?. destruct H1 as [(? & ? & ? & ?) | (? & ? & ?)].
    + apply H in H2 as []. exists (tt, x0). subs.
      eapply epsilon_det_bind with (k := fun x => Ret (tt, x)) in H2.
      rewrite bind_ret_l in H2. apply H2.
    + apply H in H1 as [].
      inversion H1.
      * inv_equ.
      * subst. step in H4. inv H4. now apply void_unit_elim in H10.
Qed.

Lemma interp_lift_handler {E F B X} {Stuck: B0 -< B} {Tau: B1 -< B}
  (h : E ~> ctree F B) (t : ctree E B X) :
  interp h t ≅ CTree.map (fun '(st, x) => x) (interp_state (lift_handler h) t tt).
Proof.
  revert t. coinduction R CH. intros.
  setoid_rewrite (ctree_eta t). destruct (observe t) eqn:?.
  - rewrite interp_ret, interp_state_ret. rewrite map_ret. reflexivity.
  - rewrite interp_vis, interp_state_vis.
    cbn. unfold lift_handler. rewrite map_bind, bind_map.
    upto_bind_eq.
    rewrite map_guard.
    constructor. intros _. apply CH.
  - rewrite interp_br, interp_state_br.
    cbn. rewrite bind_branch, map_bind, bind_branch.
    constructor. intros.
    rewrite map_guard.
    step. constructor. intros.
    apply CH.
Qed.

Lemma trans_val_interp_state {E F B X St} `{HasB0: B0 -< B} `{HasB1: B1 -< B}
  (h : E ~> stateT St (ctree F B)) :
  forall (t u : ctree E B X) (v : X) st,
  trans (val v) t u ->
  trans (val (st, v)) (interp_state h t st) stuckD.
Proof.
  intros.
  apply trans_val_epsilon in H as []. subs.
  eapply epsilon_interp_state in H.
  eapply epsilon_trans; [apply H |].
  rewrite interp_state_ret. etrans.
Qed.

Lemma trans_tau_interp_state {E F B X St} `{HasB0: B0 -< B} `{HasB1: B1 -< B}
  (h : E ~> stateT St (ctree F B)) :
  forall (t u : ctree E B X) st,
  trans tau t u ->
  trans tau (interp_state h t st) (Guard (interp_state h u st)).
Proof.
  intros.
  apply trans_tau_epsilon in H as (? & ? & ? & ? & ? & ?). subs.
  eapply epsilon_interp_state in H.
  eapply epsilon_trans; [apply H |].
  rewrite interp_state_br. cbn. rewrite bind_branch.
  apply (trans_brS _ (fun x3 : x => Guard (interp_state h (x1 x3) st))).
Qed.

Lemma trans_obs_interp_state_step {E F B X Y St} `{HasB0: B0 -< B} `{HasB1: B1 -< B}
  (h : E ~> stateT St (ctree F B)) :
  forall (t u : ctree E B X) st st' u' (e : E Y) x l,
  trans (obs e x) t u ->
  trans l (h _ e st) u' ->
  ~ is_val l ->
  epsilon_det u' (Ret (st', x)) ->
  trans l (interp_state h t st) (u';; Guard (interp_state h u st')).
Proof.
  intros.
  apply trans_obs_epsilon in H as (? & ? & ?).
  setoid_rewrite H3. clear H3.
  eapply epsilon_interp_state with (h := h) in H.
  rewrite interp_state_vis in H.
  eapply epsilon_trans. apply H.
  epose proof (epsilon_det_bind_ret_l_equ u' (fun sx => Guard (interp_state h (x0 (snd sx)) (fst sx))) (st', x) H2).
  rewrite <- H3; auto.
  apply trans_bind_l; auto.
Qed.

Lemma trans_obs_interp_state_pure {E F B X Y St} `{HasB0: B0 -< B} `{HasB1: B1 -< B}
  (h : E ~> stateT St (ctree F B)) :
  forall (t u : ctree E B X) st st' (e : E Y) x,
  trans (obs e x) t u ->
  trans (val (st', x)) (h _ e st) stuckD ->
  epsilon (interp_state h t st) (Guard (interp_state h u st')).
Proof.
  intros t u st st' e x TR TRh.
  apply trans_obs_epsilon in TR as (k & EPS & ?). subs.
  eapply epsilon_interp_state with (h := h) in EPS.
  rewrite interp_state_vis in EPS.
  apply trans_val_epsilon in TRh as [EPSh _].
  eapply epsilon_bind_ret in EPSh.
  apply (epsilon_transitive _ _ _ EPS EPSh).
Qed.

(* Direct proof that interp_state preserves ssim. *)

Import SSim'Notations.

#[global] Instance interp_state_ssim {E F B X St} {HasB0: B0 -< B} {HasB1: B1 -< B}
  (h : E ~> stateT St (ctree F B)) (Hh : forall X e st, is_simple (h X e st)) :
  Proper (ssim eq ==> eq ==> ssim eq) (interp_state (C := B) h (T := X)).
Proof.
  cbn. intros t u SIM st st' <-.
  rewrite ssim_ssim'.
  revert t u st SIM.
  red. coinduction R CH. intros.
  rewrite unfold_interp_state.
  setoid_rewrite ctree_eta at 1 in SIM. destruct (observe t) eqn:?.
  - (* Ret *)
    apply ssim_ret_l_inv in SIM as (? & ? & ? & <-).
    eapply trans_val_interp_state in H.
    apply (fbt_bt (ss_sst' eq)).
    eapply step_ss_ret_l_gen; eauto. typeclasses eauto.
  - (* Vis *)
    specialize (Hh _ e st). destruct Hh as [Hh | Hh].
    + (* pure handler *)
      assert (equ eq (interp_state h u st) (Ret tt;; interp_state h u st)) by
        now setoid_rewrite bind_ret_l. rewrite H. clear H.
      eapply ssbt'_clo_bind with (R0 := (fun sx _ => trans (val sx) (h X0 e st) stuckD)). {
        step. cbn. fold_ssim. intros l t' TR.
        apply Hh in TR as VAL.
        eapply wf_val_is_val_inv in VAL; etrans. destruct VAL as [? ->].
        apply trans_val_inv in TR as ?. exists (val tt), stuckD. subs.
        split; etrans. split.
        - apply is_stuck_ssim. apply stuckD_is_stuck.
        - now apply update_Val.
      }
      intros [st' x] _ TRh.
      simple eapply ssim_vis_l_inv in SIM.
      destruct SIM as (l & u' & TR & SIM & <-).
      eapply (fbt_bt (epsilon_ctx_r_ssim' eq)). cbn. red.
      eexists. split.
      * eapply trans_obs_interp_state_pure; eauto.
      * apply step_ss'_guard. apply CH. apply SIM.
    + (* handler that takes exactly one transition *)
      apply (fbt_bt (ss_sst' eq)). cbn. intros l t' TR.
      apply trans_bind_inv in TR as [(VAL & th & TRh & EQ) | (x & TRh & TR)].
      2: {
        apply Hh in TRh as []. inversion H; subst; inv_equ.
        step in H1. inv H1. now apply void_unit_elim in H7.
      }
      apply Hh in TRh as ?. destruct H as [[st' x] EPS].
      simple eapply ssim_vis_l_inv in SIM.
      destruct SIM as (l' & u' & TR & SIM & <-).
      exists l, (th;; Guard (interp_state h u' st')). subs.
      split; [| split; auto].
      * eapply trans_obs_interp_state_step; eauto.
      * rewrite epsilon_det_bind_ret_l_equ with (x := (st', x)).
        apply ssbt'_clo_bind_eq; eauto.
        intros []. apply step_ss'_guard. eauto. assumption.
  - (* Br *)
    unfold MonadBr_stateT, mbr, MonadBr_ctree. cbn. rewrite bind_bind, bind_branch.
    destruct vis.
    + (* BrS *)
      apply step_ss'_brS_l. intros.
      simple eapply ssim_brS_l_inv in SIM as (? & u' & TR & SIM & <-).
      exists tau, (Guard (interp_state h u' st)). split; [| split]; auto.
      * now apply trans_tau_interp_state.
      * step. rewrite bind_ret_l. apply step_ss'_guard. apply CH. apply SIM.
    + (* BrD *)
      apply step_ss'_brD_l. intros.
      eapply ssim_brD_l_inv in SIM.
      step. rewrite bind_ret_l. apply step_ss'_guard_l.
      apply CH. apply SIM.
Qed.

(* The proof that interp preserves ssim reuses the interp_state proof. *)

#[global] Instance interp_ssim {E F B R} {Stuck: B0 -< B} {Tau: B1 -< B}
  (h : E ~> ctree F B) (Hh : forall X e, is_simple (h X e)) :
  Proper (ssim eq ==> ssim eq) (interp (B := B) h (T := R)).
Proof.
  cbn. intros.
  rewrite !interp_lift_handler.
  unfold CTree.map. apply ssim_clo_bind_eq.
  apply interp_state_ssim; auto. 1: { intros. now apply is_simple_lift_handler. }
  reflexivity.
Qed.

Arguments get {S E C _}.
Arguments put {S E C _}.
Arguments run_state {S E C} [_] _ _.
Arguments fold_state {E C M S FM MM IM} h g [T].
Arguments interp_state {E C M S FM MM IM BM} h [T].
Arguments refine_state {E C M S FM MM IM TM} g [T].

From ExtLib Require Import
     Structures.Monad
     Structures.MonadState
     Data.Monads.StateMonad.

From CTree Require Import Logic.Kripke.

#[global] Instance handler_stateE{S}: stateE S ~~> state S :=
  fun _ e =>
    match e with
    | Get _ => get
    | Put s' => put s'
    end.
