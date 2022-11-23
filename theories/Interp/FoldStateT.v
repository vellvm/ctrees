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
     Eq.

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
    unfold fold_state, fold, Basics.iter, MonadIter_stateT0, iter, MonadIter_ctree.
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
    unfold interp_state, interp, Basics.iter, MonadIter_stateT0, fold, MonadIter_ctree, iter.
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
    brD (▷ branch1: C _) (fun _ => (Guard (interp_state h t s))).
  Proof.
    unfold Guard at 1.
    rewrite interp_state_br.
    cbn.
    unfold branch; rewrite bind_br.
    step; constructor; intros [].
    rewrite bind_ret_l.
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
    unfold refine_state, refine, Basics.iter, MonadIter_stateT0, fold, MonadIter_ctree, iter.
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

(* Stateful handlers [E ~> stateT S (itree F)] and morphisms
   [E ~> state S] define stateful itree morphisms
   [itree E ~> stateT S (itree F)]. *)
(* Section State. *)

(*   Variable (S : Type). *)
(*   Context {E F C D : Type -> Type} *)
(*           `{B1 -< D} *)
(*           {R : Type} *)
(*           (h : E ~> stateT S (ctree F D)) *)
(*           (h' : bool -> C ~> stateT S (ctree F D)). *)

(*   Lemma fold_state_bind {A B} *)
(*         (t : ctree E C A) (k : A -> ctree E C B) *)
(*         (s : S) : *)
(*     (fold_state h h' (t >>= k) s) *)
(*       ≅ *)
(*       (fold_state h h' t s >>= fun st => fold_state h h' (k (snd st)) (fst st)). *)
(*   Proof. *)
(*     revert s t. *)
(*     coinduction ? IH; intros. *)
(*     rewrite (ctree_eta t). *)
(*     cbn. *)
(*     rewrite unfold_bind. *)
(*     rewrite unfold_fold_state. *)
(*     destruct (observe t) eqn:Hobs; cbn. *)
(*     - rewrite fold_state_ret. rewrite bind_ret_l. cbn. *)
(*       rewrite unfold_fold_state. reflexivity. *)
(*     - rewrite fold_state_vis. *)
(*       cbn. *)
(*       rewrite bind_bind. cbn. *)
(*       upto_bind_eq. *)
(*       rewrite bind_guard. *)
(*       constructor; intros ?; apply IH. *)
(*     - rewrite unfold_fold_state. *)
(*       cbn. *)

(*       rewrite bind_bind. *)
(*       upto_bind_eq. *)
(*       rewrite bind_guard. *)
(*       constructor; intros ?; apply IH. *)
(*   Qed. *)

  (** LEF: This looks like it depends on [SBisimInterp.v]? Move there? *)
  (*
Lemma trans0_fold_state : forall {E F X} (h : E ~> stateT S (ctree F)) (t t' : ctree E X) s,
  trans0 t t' -> trans0 (fold_state h t s) (fold_state h t' s).
Proof.
  intros. red in H. setoid_rewrite (ctree_eta t). setoid_rewrite (ctree_eta t').
  genobs t ot. genobs t' ot'. clear t Heqot t' Heqot'.
  induction H.
  - constructor. rewrite H. reflexivity.
  - rewrite unfold_fold_state. cbn.
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
  transi_state h l s s' t t' -> exists t0, trans l (fold_state h t s) t0 /\ t0_det t0 (fold_state h t' s').
Proof.
  intros. induction H.
  - exists CTree.stuckD. apply trans_val_inv in H as ?.
    apply trans_val_trans0 in H as [].
    eapply trans0_fold_state in H. rewrite fold_state_ret in H. setoid_rewrite H0.
    setoid_rewrite fold_state_br. setoid_rewrite br0_always_stuck.
    eapply trans0_trans in H; etrans. split; etrans. now left.
  - exists (Guard (fold_state h t' s)). split; [| eright; eauto; now left ].
    apply trans_tau_trans0 in H as (? & ? & ? & ? & ?).
    eapply trans0_fold_state in H. setoid_rewrite H0. eapply trans0_trans; etrans.
    setoid_rewrite fold_state_br.
    econstructor. reflexivity.
  - exists (x <- t'';; Guard (fold_state h t' s')).
    split. 2: { eapply t0_det_bind_ret_l; eauto. eright; eauto. now left. }
    apply trans_obs_trans0 in H as (? & ? & ?).
    eapply trans0_fold_state in H. setoid_rewrite H2. eapply trans0_trans; etrans.
    setoid_rewrite fold_state_vis.
    eapply trans_bind_l with (k := fun sx => Guard (fold_state h (x0 (snd sx)) (fst sx))) in H1.
    setoid_rewrite t0_det_bind_ret_l_equ in H1 at 2; eauto. cbn in *. eapply H1.
    { intro. inv H3. apply trans_val_inv in H1. rewrite H1 in H0. inv H0. step in H3. inv H3. step in H4. inv H4. }
  - destruct IHtransi_state as (? & ? & ?).
    destruct (Hh Y e s). 2: { destruct H4. rewrite H4 in H1. apply trans_vis_inv in H1 as (? & ? & ?). step in H1. inv H1. }
    destruct H4. rewrite H4 in H1. inv_trans. subst.
    exists x0. split. 2: auto.
    apply trans_obs_trans0 in H as (? & ? & ?). eapply trans0_fold_state in H.
    setoid_rewrite fold_state_vis in H. setoid_rewrite H4 in H. setoid_rewrite bind_ret_l in H.
    eapply trans0_trans; etrans. setoid_rewrite <- H1. etrans.
Qed.

(** Various lemmas for the proof that fold_state preserves sbisim in some cases. *)

Lemma fold_state_ret_inv {E F X} (h : E ~> stateT S (ctree F)) : forall s (t : ctree E X) r,
  fold_state h t s ≅ Ret r -> t ≅ Ret (snd r) /\ s = fst r.
Proof.
  intros. setoid_rewrite (ctree_eta t) in H. setoid_rewrite (ctree_eta t).
  destruct (observe t) eqn:?.
  - rewrite fold_state_ret in H. step in H. inv H. split; reflexivity.
  - rewrite fold_state_vis in H. apply ret_equ_bind in H as (? & ? & ?). step in H0. inv H0.
  - rewrite fold_state_br in H. step in H. inv H.
Qed.

Lemma trans_fold_state_inv_gen {E F X Y} (h : E ~> stateT S (ctree F)) (Hh : forall X e s, vsimple (h X e s)) :
  forall l s (k : Y -> ctree E X) t' (pre : ctree F Y),
  is_simple pre ->
  trans l (x <- pre;; fold_state h (k x) s) t' ->
  exists t0 s', t0_det t' (fold_state h t0 s') /\
  ((exists l t1 x, trans l pre t1 /\ t0_det t1 (Ret x : ctree F Y) /\ t0 ≅ k x) \/
    exists (x : Y), trans (val x) pre CTree.stuckD /\ trans l (fold_state h (k x) s) t' /\ transi_state h l s s' (k x) t0).
Proof.
  intros * Hpre H.
  do 3 red in H. remember (observe (x <- pre;; fold_state h (k x) s)) as oi.
  setoid_rewrite (ctree_eta t') at 1.
  setoid_rewrite (ctree_eta t') at 2.
  genobs t' ot'. clear t' Heqot'.
  assert (go oi ≅ x <- pre;; fold_state h (k x) s).
  { rewrite Heqoi, <- ctree_eta. reflexivity. } clear Heqoi.
  revert Y s k pre Hpre H0. induction H; intros.
  - destruct n. now apply Fin.case0.
    symmetry in H0. apply br_equ_bind in H0 as ?.
    destruct H1 as [[] | (? & ? & ?)].
    + rewrite H1 in H0. setoid_rewrite bind_ret_l in H0. setoid_rewrite H1. clear pre Hpre H1.
      rewrite (ctree_eta (k0 x0)) in H0. destruct (observe (k0 x0)) eqn:?.
      * rewrite fold_state_ret in H0. step in H0. inv H0.
      * rewrite fold_state_vis in H0. apply br_equ_bind in H0 as ?. destruct H1 as [[] | (? & ? & ?)].
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
            setoid_rewrite fold_state_vis. setoid_rewrite H1. setoid_rewrite bind_ret_l. apply trans_guard. apply H3.
          ++setoid_rewrite (ctree_eta (k0 x0)). rewrite Heqc. destruct x1.
             eapply transis_obs0. etrans. 2: { rewrite H1. etrans. } cbn in H4. cbn in *. etrans.
        --destruct (Hh X0 e s).
          destruct H3. rewrite H3 in H1. step in H1. inv H1.
          destruct H3. rewrite H3 in H1. step in H1. inv H1.
      * rewrite fold_state_br in H0.
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
        rewrite (ctree_eta (k0 x0)), Heqc, fold_state_br.
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
      * rewrite fold_state_ret in H0. step in H0. inv H0.
      * rewrite fold_state_vis in H0. apply br_equ_bind in H0 as ?.
        destruct H2 as [[] | (? & ? & ?)].
        { rewrite H2 in H0. setoid_rewrite bind_ret_l in H0. step in H0. inv H0. }
        pose proof (trans_brS x1 x). rewrite <- H2 in H4.
        edestruct Hh. { destruct H5. rewrite H5 in H4. inv_trans. }
        destruct H5. rewrite H5 in H4. apply trans_vis_inv in H4 as (? & ? & ?). discriminate.
      * rewrite fold_state_br in H0.
        apply equ_br_invT in H0 as ?. destruct H2 as [-> ->].
        simple eapply equ_br_invE in H0 as ?. rewrite H in H2.
        exists (k1 x), s. symmetry in H2. split.
        { rewrite <- ctree_eta. rewrite H2. eapply t0_det_tau; auto. apply t0_det_id; auto. }
        right. exists x0. rewrite H1. split; etrans.
        split; setoid_rewrite (ctree_eta (k0 x0)); setoid_rewrite Heqc.
        { setoid_rewrite fold_state_br. rewrite H2.
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
      * rewrite fold_state_ret in H0. step in H0. inv H0.
      * rewrite fold_state_vis in H0. apply vis_equ_bind in H0 as ?.
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
        { setoid_rewrite fold_state_vis. rewrite H5. setoid_rewrite bind_vis.
          econstructor. rewrite bind_ret_l. rewrite <- H3, <- ctree_eta. reflexivity. }
        eapply transis_obs; etrans. 2: { rewrite H5. etrans. } destruct x. now left.
      * rewrite fold_state_br in H0. step in H0. inv H0.
    + pose proof (trans_vis e x x0).
      rewrite <- H1 in H3. edestruct Hpre.
      { apply H4 in H3. inv H3. }
      apply H4 in H3 as [].
      specialize (H2 x).
      exists (k0 x1), s. rewrite H in H2. split.
      { rewrite <- ctree_eta, H2. eapply t0_det_bind_ret_l; eauto. now left. }
      left. exists (obs e x), (x0 x), x1. split; auto. rewrite H1. etrans.
     - exists (CTree.stuckD), (fst r). split.
       + left. unfold CTree.stuckD. rewrite fold_state_br.
         rewrite !br0_always_stuck. reflexivity.
       + right. symmetry in H0. apply ret_equ_bind in H0 as (? & ? & ?).
         exists x. rewrite H. split; etrans. split.
         rewrite H0. rewrite br0_always_stuck. etrans.
         apply fold_state_ret_inv in H0 as []. subst. rewrite H0. destruct r. cbn. apply transis_val. econstructor; etrans.
Qed.

Lemma trans_fold_state_inv {E F X} (h : E ~> stateT S (ctree F)) (Hh : forall X e s, vsimple (h X e s)) :
  forall l (t : ctree E X) t' s,
  trans l (fold_state h t s) t' ->
  exists l t0 s', t0_det t' (fold_state h t0 s') /\ transi_state h l s s' t t0.
Proof.
  intros.
   assert (trans l (Guard (Ret tt);; fold_state h t s) t').
   { cbn. etrans. }
  eapply trans_fold_state_inv_gen in H0; eauto. destruct H0 as (? & ? & ? & ?).
  destruct H1 as [(? & ? & ? & ? & ? & ?) | (? & ? & ? & ?)].
  - inv_trans. subst. inv H2. step in H1. inv H1. step in H3. inv H3.
  - inv_trans. subst. eauto.
  - left. intros. inv_trans. subst. constructor.
Qed.

(** The main theorem stating that fold_state preserves sbisim. *)

Theorem fold_state_sbisim_gen {E F X Y} (h : E ~> stateT S (ctree F)) (Hh : forall X e s, vsimple (h X e s)) :
  forall s (k k' : X -> ctree E Y) (pre pre' : ctree F X),
  (forall x, sbisim (k x) (k' x)) ->
  pre ≅ pre' ->
  vsimple pre ->
  sbisim (a <- pre;; Guard (fold_state h (k a) s)) (a <- pre';; Guard (fold_state h (k' a) s)).
Proof.
  revert X. coinduction R CH.
  symmetric using idtac.
  { intros. apply H; eauto.  intros. rewrite H0. reflexivity. now rewrite H1. red; now setoid_rewrite <- H1. }
  assert (CH' : forall (t t' : ctree E Y) s, t ~ t' -> st R (fold_state h t s) (fold_state h t' s)).
  {
    intros.
    assert (st R (a <- Ret tt;; Guard (fold_state h ((fun _ => t) a) s))
      (a <- Ret tt;; Guard (fold_state h ((fun _ => t') a) s))).
    { apply CH; eauto. left; eauto. }
    setoid_rewrite bind_ret_l in H0.
    rewrite !sb_guard in H0.
    apply H0.
  }
  intros. setoid_rewrite <- H0. clear pre' H0. cbn. intros.
  copy H0. rewrite bind_tau_r in H0.
  eapply trans_fold_state_inv_gen in H0 as (? & ? & ? & ?); auto.
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
      exists (Guard (fold_state h (k' x1) s)). rewrite H1. rewrite bind_trigger. now constructor.
      rewrite H2, !sb_guard. apply CH'. apply H.
  - destruct H2 as (? & ? & ? & ?).
    destruct H1 as [[] | []]. 2: { rewrite H1 in H2. setoid_rewrite bind_trigger in H2. inv_trans. }
    rewrite H1 in *. rewrite bind_ret_l in H2. inv_trans. subst. clear EQ.
    eapply transis_sbisim in H4; eauto. destruct H4 as (? & ? & ?).
    apply transis_trans in H2 as (? & ? & ?); auto.
    exists x3. rewrite H1, bind_ret_l. etrans.
    assert (st R (fold_state h x x0) (fold_state h x1 x0)).
    { apply CH'. apply H4. }
    rewrite sbisim_t0_det. 2: apply H0.
    setoid_rewrite sbisim_t0_det at 3. 2: apply H5.
    apply H6.
Qed.

#[global] Instance fold_state_sbisim {E F R} (h : E ~> stateT S (ctree F)) (Hh : forall X e s, vsimple (h X e s)) :
  Proper (sbisim ==> eq ==> sbisim) (fold_state h (T := R)).
Proof.
  cbn. intros. subst.
  assert (a <- Ret tt;; Guard (fold_state h ((fun _ => x) a) y0) ~
    a <- Ret tt;; Guard (fold_state h ((fun _ => y) a) y0)).
  apply fold_state_sbisim_gen; auto.
  red; eauto.
  setoid_rewrite bind_ret_l in H0. rewrite !sb_guard in H0. apply H0.
Qed.
   *)

(* End State. *)

Arguments get {S E _}.
Arguments put {S E _}.
Arguments run_state {S E} [_] _ _.
Arguments fold_state {E C M S FM MM IM} h g [T].