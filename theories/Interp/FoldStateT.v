Unset Universe Checking.

From Stdlib Require Import Classes.RelationPairs.

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
     FoldCTree
     Eq
     Eq.Epsilon
     Eq.IterFacts
     Eq.SSimAlt
     Eq.SBisimAlt
     Eq.OldAltEquiv.TransEquiv
     Eq.OldAltEquiv.SSimEquiv
     Eq.OldAltEquiv.SBisimEquiv
     Misc.Pure.

Import SBisimNotations.
Import MonadNotation.
Open Scope monad_scope.

Set Implicit Arguments.

(* TODO MOVE *)
Arguments fequ : simpl never.

#[global] Instance MonadBr_stateT {S M C} {MM : Monad M} {AM : MonadBr C M}:
  MonadBr C (stateT S M) :=
  fun X c s => f <- mbr _ c;; ret (s,f).

#[global] Instance MonadTrigger_stateT {E S M} {MM : Monad M} {MT: MonadTrigger E M} :
  MonadTrigger E (stateT S M) :=
  fun _ e s => v <- mtrigger e;; ret (s, v).

#[global] Instance MonadStuck_stateT {S M} {MS: MonadStuck M} : MonadStuck (stateT S M) :=
  fun _ _ => @mstuck M _ _.

#[global] Instance MonadStep_ctree {S M} {MM : Monad M} {MS : MonadStep M} : MonadStep (stateT S M) :=
  fun s => _ <- mstep;; ret (s,tt).

Definition fold_state {E C M} S
  {FM : Functor M} {MM : Monad M} {IM : MonadIter M} {MV : MonadStuck M} {MS : MonadStep M}
  (h : E ~> stateT S M) (g : C ~> stateT S M) :
  ctree E C ~> stateT S M :=
  fold h g.

Definition interp_state {E C M} S
  `{FM : Functor M, MM : Monad M, IM : MonadIter M, BM : MonadBr C M, MV : MonadStuck M, MS : MonadStep M}
  (h : E ~> stateT S M) :
  ctree E C ~> stateT S M := interp h.

Definition refine_state {E C M} S
  `{FM : Functor M, MM : Monad M, IM : MonadIter M, BM : MonadTrigger E M, MV : MonadStuck M, MS : MonadStep M}
  (g : C ~> stateT S M) :
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

  Definition pure_state_choice {E C} : C ~> stateT S (ctree E C)
    := fun _ c s => br c (fun x => Ret (s, x)).

  Definition run_state {E C}
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
          {R : Type}
          (h : E ~> stateT S (ctree F D))
          (g : C ~> stateT S (ctree F D)).

  (** Unfolding of [fold]. *)
  Notation fold_state_ h g t s :=
    (match observe t with
     | RetF r => Ret (s, r)
     | StuckF => Stuck
     | GuardF t => Guard (fold_state h g t s)
     | StepF t => Step (Guard (fold_state h g t s))
     | VisF e k => bind (h _ e s) (fun xs => Guard (fold_state h g (k (snd xs)) (fst xs)))
     | BrF c k => bind (g _ c s) (fun xs => Guard (fold_state h g (k (snd xs)) (fst xs)))
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
    - now rewrite bind_stuck.
    - rewrite bind_map, bind_bind.
      setoid_rewrite bind_step.
      step; constructor.
      rewrite ?bind_ret_l.
      auto.
    - now rewrite ?bind_ret_l; cbn.
    - rewrite bind_map. cbn.
      upto_bind_eq; intros [].
      now cbn; rewrite ?bind_ret_l.
    - rewrite bind_map. cbn.
      upto_bind_eq; intros [].
      now cbn; rewrite ?bind_ret_l.
  Qed.

  #[global] Instance equ_fold_state:
    Proper (equ eq ==> eq ==> equ eq)
           (fold_state h g (T := R)).
  Proof.
    unfold Proper, respectful.
    coinduction r IH; intros * EQ1 * <-.
    rewrite !unfold_fold_state.
    step in EQ1; inv EQ1; auto.
    - constructor; auto.
    - constructor; step; constructor; auto.
    - upto_bind_eq; intros [].
      constructor; intros; auto.
    - upto_bind_eq; intros [].
      constructor; auto.
  Qed.

  Lemma fold_state_ret
        (s : S) (r : R) :
    (fold_state h g (Ret r) s) ≅ (Ret (s, r)).
  Proof.
    rewrite ctree_eta. reflexivity.
  Qed.

  Lemma fold_state_stuck (s : S) :
    (fold_state (T := R) h g Stuck s) ≅ Stuck.
  Proof.
    now rewrite ctree_eta.
  Qed.

  Lemma fold_state_guard (t : ctree E C R) (s : S) :
    fold_state h g (Guard t) s ≅ Guard (fold_state h g t s).
  Proof.
    now rewrite unfold_fold_state; cbn.
  Qed.

  Lemma fold_state_step (t : ctree E C R) (s : S) :
    fold_state h g (Step t) s ≅ Step (Guard (fold_state h g t s)).
  Proof.
    now rewrite unfold_fold_state; cbn.
  Qed.

  Lemma fold_state_vis {T : Type}
    (e : E T) (k : T -> ctree E C R) (s : S) :
    fold_state h g (Vis e k) s ≅ h e s >>= fun sx => Guard (fold_state h g (k (snd sx)) (fst sx)).
  Proof.
    rewrite unfold_fold_state; reflexivity.
  Qed.

  Lemma fold_state_br {T: Type} `{C -< D}
    (c : C T) (k : T -> ctree E C R) (s : S) :
    fold_state h g (br c k) s ≅ g c s >>= fun sx => Guard (fold_state h g (k (snd sx)) (fst sx)).
  Proof.
    rewrite !unfold_fold_state; reflexivity.
  Qed.

  Lemma fold_state_trigger (e : E R) (s : S) :
    fold_state h g (CTree.trigger e) s ≅
    h e s >>= fun x => Guard (Ret x).
  Proof.
    unfold CTree.trigger.
    rewrite fold_state_vis; cbn.
    upto_bind_eq; intros [].
    rewrite fold_state_ret; auto.
  Qed.

  Lemma fold_state_trigger_sb (e : E R) (s : S)
    : fold_state h g (CTree.trigger e) s ≃ h e s.
  Proof.
    unfold CTree.trigger. rewrite fold_state_vis.
    rewrite <- (bind_ret_r (h e s)) at 2.
    cbn.
    upto_bind_eq; intros [].
    now rewrite sbisim_guard, fold_state_ret.
  Qed.

  (** Unfolding of [interp]. *)
  Notation interp_state_ h t s :=
    (match observe t with
     | RetF r => Ret (s, r)
     | StuckF => Stuck
     | GuardF t => Guard (interp_state h t s)
     | StepF t => Step (Guard (interp_state h t s))
 	   | VisF e k => bind (h _ e s) (fun xs => Guard (interp_state h (k (snd xs)) (fst xs)))
	   | BrF c k => bind (mbr (M := stateT _ _) _ c s) (fun xs => Guard (interp_state h (k (snd xs)) (fst xs)))
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
    - now rewrite bind_stuck.
    - rewrite bind_map, bind_bind.
      setoid_rewrite bind_step.
      step; constructor.
      rewrite ?bind_ret_l.
      auto.
    - now rewrite ?bind_ret_l; cbn.
    - rewrite bind_map. cbn.
      upto_bind_eq; intros [].
      now cbn; rewrite ?bind_ret_l.
    - rewrite bind_map. cbn.
      upto_bind_eq; intros [].
      now cbn; rewrite ?bind_ret_l.
  Qed.

  Lemma equ_interp_state `{C-<D} {Q}:
    Proper (equ Q ==> eq ==> equ (eq * Q))
           (interp_state (C := C) h (T := R)).
  Proof.
    unfold Proper, respectful.
    coinduction r IH; intros * EQ1 * <-.
    rewrite !unfold_interp_state.
    step in EQ1; inv EQ1.
    - constructor. split; auto.
    - constructor.
    - constructor; auto.
    - constructor; step; constructor; auto.
    - upto_bind_eq; intros [].
      constructor; intros; auto.
    - upto_bind_eq; intros [].
      constructor; auto.
  Qed.

  #[global] Instance equ_eq_interp_state `{C-<D}:
    Proper (equ eq ==> eq ==> equ eq)
           (interp_state (C := C) h (T := R)).
  Proof.
    cbn. intros. subst.
    eapply (equ_leq (eq * eq)%signature).
    { intros [] [] []. now f_equal. }
    now apply equ_interp_state.
  Qed.

  Lemma interp_state_ret `{C-<D}
        (s : S) (r : R) :
    (interp_state (C := C) h (Ret r) s) ≅ (Ret (s, r)).
  Proof.
    rewrite ctree_eta. reflexivity.
  Qed.

  Lemma interp_state_stuck `{C-<D} (s : S) :
    interp_state (C := C) (T := R) h Stuck s ≅ Stuck.
  Proof.
    now rewrite unfold_interp_state; cbn.
  Qed.

  Lemma interp_state_guard `{C -< D}
    (t : ctree E C R) (s : S) :
    interp_state h (Guard t) s ≅
    Guard (interp_state h t s).
  Proof.
    now rewrite unfold_interp_state; cbn.
  Qed.

  Lemma interp_state_step `{C -< D}
    (t : ctree E C R) (s : S) :
    interp_state h (Step t) s ≅
    Step (Guard (interp_state h t s)).
  Proof.
    now rewrite unfold_interp_state; cbn.
  Qed.

  Lemma interp_state_vis `{C-<D} {T : Type}
    (e : E T) (k : T -> ctree E C R) (s : S) :
    interp_state h (Vis e k) s ≅ h e s >>= fun sx => Guard (interp_state h (k (snd sx)) (fst sx)).
  Proof.
    rewrite unfold_interp_state; reflexivity.
  Qed.

  Lemma interp_state_br {T: Type} `{C -< D}
    (c : C T) (k : T -> ctree E C R) (s : S) :
    interp_state h (Br c k) s ≅ branch c >>= fun x => Guard (interp_state h (k x) s).
  Proof.
    rewrite !unfold_interp_state; cbn.
    rewrite bind_bind.
    upto_bind_eq; intros ?.
    now rewrite bind_ret_l.
  Qed.

  Lemma interp_state_trigger `{C -< D} : forall (e : E R) st,
  interp_state h (CTree.trigger e : ctree E C R) st ≅ x <- h e st;; Guard (Ret x).
  Proof.
    intros. rewrite unfold_interp_state. cbn.
    upto_bind. reflexivity. intros [] [] <-.
    now rewrite interp_state_ret.
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
     | StuckF => Stuck
     | GuardF t => Guard (refine_state g t s)
     | StepF t => Step (Guard (refine_state g t s))
 	   | VisF e k => bind (mtrigger e) (fun x => Guard (refine_state g (k x) s))
	   | BrF c k => bind (g _ c s) (fun xs => Guard (refine_state g (k (snd xs)) (fst xs)))
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
    - now rewrite bind_stuck.
    - rewrite bind_map, bind_bind.
      setoid_rewrite bind_step.
      step; constructor.
      rewrite ?bind_ret_l.
      auto.
    - now rewrite ?bind_ret_l; cbn.
    - rewrite bind_map, bind_bind.
      upto_bind_eq; intros ?.
      now cbn; rewrite ?bind_ret_l.
    - rewrite bind_map. cbn.
      upto_bind_eq; intros [].
      now cbn; rewrite ?bind_ret_l.
  Qed.

  #[global] Instance equ_refine_state `{E-<F}:
    Proper (equ eq ==> eq ==> equ eq)
           (refine_state (E := E) g (T := R)).
  Proof.
    unfold Proper, respectful.
    coinduction r IH; intros * EQ1 * <-.
    rewrite !unfold_refine_state.
    step in EQ1; inv EQ1; auto.
    - constructor; auto.
    - constructor; step; constructor; auto.
    - upto_bind_eq; intros ?.
      constructor; intros; auto.
    - upto_bind_eq; intros ?.
      constructor; auto.
  Qed.

  Lemma refine_state_ret `{E-<F}
        (s : S) (r : R) :
    (refine_state (E := E) g (Ret r) s) ≅ (Ret (s, r)).
  Proof.
    rewrite ctree_eta. reflexivity.
  Qed.

  Lemma refine_state_stuck `{E-<F} (s : S) :
    refine_state (E := E) (T := R) g Stuck s ≅ Stuck.
  Proof.
    rewrite ctree_eta. reflexivity.
  Qed.

  Lemma refine_state_guard `{E -< F}
    (t : ctree E C R) (s : S) :
    refine_state g (Guard t) s ≅
    Guard (refine_state g t s).
  Proof.
    now rewrite unfold_refine_state; cbn.
  Qed.

  Lemma refine_state_step `{E -< F}
    (t : ctree E C R) (s : S) :
    refine_state g (Step t) s ≅
    Step (Guard (refine_state g t s)).
  Proof.
    now rewrite unfold_refine_state; cbn.
  Qed.

  Lemma refine_state_vis `{E-<F} {T : Type}
    (e : E T) (k : T -> ctree E C R) (s : S) :
    refine_state g (Vis e k) s ≅
      trigger e >>= fun x => Guard (refine_state g (k x) s).
  Proof.
    rewrite unfold_refine_state; reflexivity.
  Qed.

  Lemma refine_state_br {T: Type} `{E -< F}
    (c : C T) (k : T -> ctree E C R) (s : S) :
    refine_state g (Br c k) s ≅
    g c s >>= fun xs => Guard (refine_state g (k (snd xs)) (fst xs)).
  Proof.
    rewrite !unfold_refine_state; cbn.
    now upto_bind_eq.
  Qed.

End State.

#[global] Instance epsilon_det_interp_state {E F B C X St}
  `{HasB: B -< C} (h : E ~> stateT St (ctree F C)) :
  Proper (@epsilon_det E B X ==> eq ==> epsilon_det)
         (interp_state h (T := X)).
Proof.
  cbn. intros. subst.
  induction H.
  - now subs.
  - subs. rewrite interp_state_guard.
    eapply epsilon_det_guard; [| reflexivity].
    assumption.
Qed.

Section FoldBind.
  Variable (S : Type).
  Context {E F C D : Type -> Type}.

  Lemma fold_state_bind
    (h : E ~> stateT S (ctree F D))
    (g : C ~> stateT S (ctree F D))
    {A B}
    (t : ctree E C A) (k : A -> ctree E C B)
    (s : S) :
    fold_state h g (t >>= k) s
      ≅ fold_state h g t s >>= fun st => fold_state h g (k (snd st)) (fst st).
  Proof.
    revert s t.
    coinduction r IH; intros.
    rewrite (ctree_eta t).
    cbn.
    rewrite unfold_bind.
    rewrite unfold_fold_state.
    destruct (observe t) eqn:Hobs; cbn.
    - rewrite fold_state_ret. rewrite bind_ret_l. cbn.
      rewrite unfold_fold_state. reflexivity.
    - now rewrite fold_state_stuck, bind_stuck.
    - rewrite fold_state_step, bind_step, bind_guard.
      constructor; step; constructor; apply IH.
    - rewrite fold_state_guard, bind_guard.
      constructor; apply IH.
    - rewrite fold_state_vis.
      cbn.
      rewrite bind_bind. cbn.
      upto_bind_eq; intros [].
      rewrite bind_guard.
      constructor; apply IH.
    - rewrite unfold_fold_state.
      cbn.
      rewrite bind_bind.
      upto_bind_eq; intros [].
      rewrite bind_guard.
      constructor; apply IH.
  Qed.

  Lemma interp_state_bind `{C -< D}
    (h : E ~> stateT S (ctree F D))
    {A B}
    (t : ctree E C A) (k : A -> ctree E C B)
    (s : S) :
    interp_state h (CTree.bind t k) s ≅ CTree.bind (interp_state h t s) (fun xs => interp_state h (k (snd xs)) (fst xs)).
  Proof.
    eapply fold_state_bind.
  Qed.

  Lemma refine_state_bind `{E -< F}
    (g : C ~> stateT S (ctree F D))
    {A B}
    (t : ctree E C A) (k : A -> ctree E C B)
    (s : S) :
    refine_state g (CTree.bind t k) s ≅ CTree.bind (refine_state g t s) (fun xs => refine_state g (k (snd xs)) (fst xs)).
  Proof.
    eapply fold_state_bind.
  Qed.
End FoldBind.

Section InterpState.

Context {E F B C : Type -> Type} {X St : Type} `{HasB: B -< C}
  (h : E ~> stateT St (ctree F C)).

Lemma epsilon_interp_state : forall (t t' : ctree E B X) s,
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
    setoid_rewrite bind_br.
    apply epsilon_br with (x := x).
    rewrite !bind_ret_l.
    cbn.
    apply epsilon_guard.
    apply IHepsilon_.
  - rewrite unfold_interp_state; cbn.
    apply epsilon_guard.
    apply IHepsilon_.
Qed.

Lemma interp_state_ret_inv :
  forall s (t : ctree E C X) r,
    interp_state h t s ≅ Ret r -> t ≅ Ret (snd r) /\ s = fst r.
Proof.
  intros * EQ. setoid_rewrite (ctree_eta t) in EQ. setoid_rewrite (ctree_eta t).
  destruct (observe t) eqn:?.
  - rewrite interp_state_ret in EQ; inv_equ; auto.
  - rewrite interp_state_stuck in EQ; inv_equ.
  - rewrite interp_state_step in EQ; inv_equ.
  - rewrite interp_state_guard in EQ; inv_equ.
  - rewrite interp_state_vis in EQ. apply ret_equ_bind in EQ as (? & ? & ?). inv_equ.
  - rewrite interp_state_br in EQ; inv_equ.
Qed.

End InterpState.

Theorem ssim_interp_state_h {E F1 F2 C D1 D2 X St St'}
  `{HC1 : C -< D1} `{HC2 : C -< D2}
  (L : lrel F1 F2 (St * X) (St' * X)) (Rs : rel St St') :
  forall (h : E ~> stateT St (ctree F1 D1)) (h' : E ~> Monads.stateT St' (ctree F2 D2)),
  (forall (x : X) (st : St) (st' : St'), Rs st st' -> RR L (st, x) (st', x)) ->
  (forall {Z} (e : E Z) st st',
    Rs st st' ->
    h _ e st (≲upd_rel L (fun '(s, z) '(s', z') => Rs s s' /\ @eq Z z z')) h' _ e st') ->
  forall (t : ctree E C X) st0 st'0,
  Rs st0 st'0 ->
  interp_state h t st0 (≲L) interp_state h' t st'0.
Proof.
  intros * HL Hh * ST.
  unfold interp_state, interp, fold, Basics.iter, MonadIter_stateT0, Basics.iter, MonadIter_ctree.
  eapply ssim_iter with
    (Ra := fun '(st, t) '(st', t') => Rs st st' /\ t ≅ t')
    (Rb := fun b b' => L (val b) (val b')).
  2: auto. 1: reflexivity. 2: split; [assumption | reflexivity].
  clear t st0 st'0 ST.
  intros [st t] [st' t'] [ST EQ]. cbn.
  setoid_rewrite ctree_eta in EQ.
  destruct (observe t) eqn:?, (observe t') eqn:?; inv_equ.
  - rewrite !bind_ret_l. apply ssim_ret. cbn. constructor. now apply HL.
  - cbn. rewrite !bind_stuck. apply ssim_stuck.
  - rewrite ?map_bind, ?bind_bind. setoid_rewrite bind_step. apply ssim_step.
    rewrite !bind_ret_l, !map_ret, !bind_ret_l. apply ssim_ret. cbn. split; auto.
  - rewrite !bind_ret_l. apply ssim_ret. cbn. split; auto.
  - rewrite !bind_map.
    eapply ssim_bind_gen with (SS := fun '(st, z) '(st', z') => Rs st st' /\ z = z').
    + now apply Hh.
    + intros [] [] [? <-]. apply ssim_ret. cbn. auto.
  - rewrite !bind_map, !bind_bind. setoid_rewrite bind_branch. cbn.
    apply ssim_br_id; intros ?; rewrite ?bind_ret_l.
    apply ssim_ret. cbn. auto.
Qed.

Definition lift_handler {E F B} (h : E ~> ctree F B) : E ~> Monads.stateT unit (ctree F B) :=
  fun _ e s => CTree.map (fun x => (tt, x)) (h _ e).


(* Results on interp_state can be transported to interp using interp_lift_handler. *)

Lemma interp_lift_handler {E F B C X} `{HasB: B -< C}
  (h : E ~> ctree F C) (t : ctree E B X) :
  interp h t ≅ CTree.map (fun '(st, x) => x) (interp_state (lift_handler h) t tt).
Proof.
  revert t. coinduction R CH. intros.
  pose proof @map_equ.
  rewrite (ctree_eta t). destruct (observe t) eqn:?.
  - rewrite interp_ret, interp_state_ret. rewrite map_ret. reflexivity.
  - rewrite interp_stuck.
    rewrite interp_state_stuck.
    now rewrite map_stuck.
  - rewrite interp_step, interp_state_step, map_step, map_guard.
    constructor; step; constructor; auto.
  - rewrite interp_guard, interp_state_guard, ?map_guard.
    constructor; auto.
  - rewrite interp_vis, interp_state_vis.
    cbn. unfold lift_handler. rewrite map_bind, bind_map.
    upto_bind_eq; intros ?.
    rewrite map_guard.
    constructor. apply CH.
  - rewrite interp_br, interp_state_br.
    cbn. rewrite bind_branch, map_bind, bind_branch.
    constructor. intros.
    rewrite map_guard.
    step. constructor.
    apply CH.
Qed.

Theorem ssim_interp_h {E F1 F2 C D1 D2 X}
  `{HC1 : C -< D1} `{HC2 : C -< D2}
  (L : lrel F1 F2 X X) :
  forall (h : E ~> ctree F1 D1) (h' : E ~> ctree F2 D2),
  (forall (x : X), RR L x x) ->
  (forall {Z} (e : E Z), h _ e (≲upd_rel L (@eq Z)) h' _ e) ->
  forall (t : ctree E C X),
  interp h t (≲L) interp h' t.
Proof.
  intros h h' HL Hh t.
  rewrite !interp_lift_handler.
  unfold CTree.map.
  eapply ssim_bind_gen with (SS := fun (a b : unit * X) => snd a = snd b).
  2: { intros [] [] ?; cbn in *; subst. apply ssim_ret. apply HL. }
  eapply ssim_interp_state_h with (Rs := eq).
  3: reflexivity.
  - intros. cbn. reflexivity.
  - intros Z e [] [] _.
    unfold lift_handler, CTree.map.
    eapply ssim_bind_gen with (SS := eq).
    + apply Hh.
    + intros ? ? <-. apply ssim_ret. cbn. auto.
Qed.

Lemma trans_val_interp_state {E F B C X St}
  `{HasB: B -< C}
  (h : E ~> stateT St (ctree F C)) :
  forall (t u : ctree E B X) (v : X) st,
  trans (val v) t u ->
  trans (val (st, v)) (interp_state h t st) Stuck.
Proof.
  intros t u v st TR.
  apply trans_val_epsilon in TR.
  eapply epsilon_interp_state with (h := h) (s := st) in TR.
  eapply epsilon_trans; [apply TR |].
  rewrite interp_state_ret. etrans.
Qed.

Lemma trans_τ_interp_state {E F B C X St}
  `{HasB: B -< C}
  (h : E ~> stateT St (ctree F C)) :
  forall (t u : ctree E B X) st,
  trans τ t u ->
  trans τ (interp_state h t st) (Guard (interp_state h u st)).
Proof.
  cbn. intros.
  apply trans_τ_epsilon in H as (? & ? & ?); subst.
  eapply epsilon_interp_state in H.
  eapply epsilon_trans; [apply H |].
  rewrite interp_state_step.
  rewrite H0. etrans.
Qed.

Lemma trans_ask_interp_state {E F B C X Y St} `{HasB: B -< C}
  (h : E ~> stateT St (ctree F C)) :
  forall (t : ctree E B X) (k : Y -> ctree E B X) (e : E Y) st,
  trans (ask e) t (β e k) ->
  epsilon (interp_state h t st)
    (sx <- h _ e st;; Guard (interp_state h (k (snd sx)) (fst sx))).
Proof.
  intros t k e st TR.
  apply trans_ask_epsilon in TR as (k' & EPS & EQ).
  eapply epsilon_interp_state with (h := h) (s := st) in EPS.
  rewrite interp_state_vis in EPS.
  dependent destruction EQ.
  setoid_rewrite EQ. exact EPS.
Qed.

(* Direct proof that interp_state preserves ssim. *)

Lemma interp_state_ssim_aux {E F B C X Y St} `{HasB: B -< C}
  (h : E ~> stateT St (ctree F C)) (R : rel X Y) (RS : rel (St * X) (St * Y))
  (HRS : forall s x y, R x y -> RS (s, x) (s, y)) :
  forall (t : ctree E B X) (u : ctree E B Y) s,
  ssim (Lvrel R) t u ->
  ssim' (lift_L (Lvrel RS))
    (TransAlt.Active (interp_state h t s)) (TransAlt.Active (interp_state h u s)).
Proof.
  coinduction RR CH. intros t u s SIM.
  rewrite unfold_interp_state at 1.
  setoid_rewrite ctree_eta at 1 in SIM.
  destruct (observe t) eqn:Heqt.
  - apply ssim_ret_l_inv in SIM as (r' & u' & TR & HR).
    apply trans_val_epsilon in TR.
    eapply epsilon_interp_state with (h := h) (s := s) in TR.
    eapply ss'_epsilon_r_old; [exact TR |].
    rewrite interp_state_ret. apply step_ss'_ret.
    + apply (b_chain RR). apply step_ss'_stuck.
    + constructor. cbn. now apply HRS. 
  - apply ss'_stuck.
  - apply ssim_step_l_inv in SIM as (u2 & TR & SIM).
    destruct u2 as [u2 | Z e' k'];
      [| exfalso; remember (Trans.Passive e' k') as p; remember τ as l;
         induction TR; subst; try discriminate; eauto].
    apply trans_τ_epsilon in TR as (u3 & EPS & EQ).
    eapply epsilon_interp_state with (h := h) (s := s) in EPS.
    eapply ss'_epsilon_r_old; [exact EPS |].
    rewrite interp_state_step.
    apply step_ss'_step; [constructor |].
    apply (b_chain RR). apply step_ss'_guard. apply CH. now rewrite <- EQ.
  - apply step_ss'_guard_l. apply CH. now apply ssim_guard_l_inv.
  - apply ssim_vis_l_inv in SIM as (Z' & f & k' & TR & HA & HK).
    cbn in HA. dependent destruction HA.
    apply trans_ask_epsilon in TR as (k'' & EPS & SEQ).
    dependent destruction SEQ.
    eapply epsilon_interp_state with (h := h) (s := s) in EPS.
    eapply ss'_epsilon_r_old; [exact EPS |].
    rewrite interp_state_vis.
    refine (SSimAlt.bind_chain_gen _ (R := chain_b RR) _ _ _ _ eq _ _).
    + change (TransAlt.upd_rel (lift_L (Lvrel RS)) eq) with (lift_L (@Leq F (St * X0))). 
      apply (@Reflexive_ss'_chain F F C C (St * X0) (St * X0) (lift_L Leq) lift_L_Leq_reflexiveL (chain_b RR)).
    + intros [st z] ? <-. cbn. apply step_ss'_guard.
      destruct (HK z) as (y & SIM' & HR). cbn in HR. dependent destruction HR.
      apply CH. now rewrite <- EQ.
  - unfold MonadBr_stateT, mbr, MonadBr_ctree. cbn.
    rewrite bind_bind, bind_branch.
    apply step_ss'_br_l. intros x. rewrite bind_ret_l.
    apply (b_chain RR). apply step_ss'_guard_l. apply CH.
    eapply ssim_br_l_inv in SIM. apply SIM.
Qed.

#[global] Instance interp_state_ssim {E F B C X St} {R : relation X} `{HasB: B -< C} :
  forall (h : E ~> stateT St (ctree F C)),
  Proper (ssimT (Lvrel R) ==> eq ==> ssimT (Lvrel (@eq St * R)%signature))
    (interp_state (C := B) h (T := X)).
Proof.
  intros h t u SIM st st' <-. unfold ssimT in *.
  apply ssim_ssim'.
  apply interp_state_ssim_aux with (R := R); [| exact SIM].
  intros; split; cbn; auto.
Qed.

#[global] Instance interp_state_ssim_eq {E F B C X St} `{HasB: B -< C} :
  forall (h : E ~> stateT St (ctree F C)),
  Proper (ssimT Leq ==> eq ==> ssimT Leq) (interp_state (C := B) h (T := X)).
Proof.
  intros h t u SIM st st' <-. unfold ssimT in *.
  apply ssim_ssim'.
  apply interp_state_ssim_aux with (R := eq); [| exact SIM].
  intros; subst; reflexivity.
Qed.

(* The proof that interp preserves ssim reuses the interp_state proof. *)

#[global] Instance interp_ssim_eq {E F B C X} `{HasB: B -< C} :
  forall (h : E ~> ctree F C),
  Proper (ssimT Leq ==> ssimT Leq) (interp (B := B) h (T := X)).
Proof.
  intros h t u SIM.
  rewrite !interp_lift_handler.
  unfold CTree.map. eapply ssim_bind_gen with (SS := eq).
  - change (upd_rel Leq eq) with (@Leq F (unit * X)). apply interp_state_ssim_eq; auto.
  - intros [] ? <-. apply ssim_ret. reflexivity.
Qed.

(* Direct proof that interp_state preserves sbisim. *)

Arguments sb' : simpl never.

Lemma interp_state_sbisim_aux {E F B C St} `{HasB: B -< C}
  (h : E ~> stateT St (ctree F C)) :
  forall X Y (R : rel X Y) (RS : rel (St * X) (St * Y)),
  (forall s x y, R x y -> RS (s, x) (s, y)) ->
  forall (t : ctree E B X) (u : ctree E B Y) s,
  ss (Lvrel R) (sbisim (Lvrel R)) t u ->
  gfp (@sb' F F C C) true _ _ (lift_L (Lvrel RS))
    (TransAlt.Active (interp_state h t s)) (TransAlt.Active (interp_state h u s)).
Proof.
  coinduction RR CH.
  assert (BOTH : forall X Y (R : rel X Y) (RS : rel (St * X) (St * Y)),
    (forall s x y, R x y -> RS (s, x) (s, y)) ->
    forall (t : ctree E B X) (u : ctree E B Y) s, sbisim (Lvrel R) t u ->
    forall side, elem RR side _ _ (lift_L (Lvrel RS))
      (TransAlt.Active (interp_state h t s)) (TransAlt.Active (interp_state h u s))).
  { intros X Y R RS HRS t u s H [|].
    - apply (CH _ _ R RS HRS). step in H. apply H.
    - apply (proj1 (sb'_chain_flip false _ _ _)). cbn [negb].
      eapply lequiv_sb'_chain; [symmetry; apply flipL_lift_L_Lvrel |].
      apply (CH _ _ (flip R) (flip RS)); [intros s' x y HR; exact (HRS s' y x HR) |].
      apply sbisim_Lvrel_flip in H. step in H. apply H. }
  intros X Y R RS HRS t u s SIM.
  rewrite unfold_interp_state at 1.
  setoid_rewrite ctree_eta at 1 in SIM.
  destruct (observe t) eqn:Heqt.
  - edestruct SIM as (l' & u' & TR & _ & HL); [etrans |]. cbn in HL. dependent destruction HL.
    apply trans_val_epsilon in TR. eapply epsilon_interp_state with (h := h) (s := s) in TR.
    apply sb'_true_ss'. eapply ss'_epsilon_r_old; [exact TR |].
    rewrite interp_state_ret. apply step_ss'_ret.
    + intros side. apply (b_chain RR). apply sb'_stuck.
    + constructor. cbn. now apply HRS.
  - apply sb'_true_stuck.
  - edestruct SIM as (l' & u2 & TR & SIM' & HL); [etrans |]. cbn in HL. dependent destruction HL.
    destruct u2 as [u2 | Z e' k'];
      [| exfalso; clear - TR; remember (Trans.Passive e' k') as p; remember τ as l;
         induction TR; subst; try discriminate; eauto].
    apply trans_τ_epsilon in TR as (u3 & EPS & EQ).
    eapply epsilon_interp_state with (h := h) (s := s) in EPS.
    apply sb'_true_ss'. eapply ss'_epsilon_r_old; [exact EPS |].
    rewrite interp_state_step.
    apply step_ss'_step; [constructor |].
    intros side. apply (b_chain RR). apply step_sb'_guard. apply (BOTH _ _ R RS HRS). now rewrite <- EQ.
  - apply step_sb'_true_guard_l. apply (CH _ _ R RS HRS).
    intros l t' TR. apply SIM. now apply trans_guard.
  - edestruct SIM as (l' & st' & TR & SIM' & HL); [etrans |]. cbn in HL. dependent destruction HL.
    dependent destruction HR.
    apply trans_ask_epsilon in TR as (k'' & EPS & SEQ).
    rewrite SEQ in SIM'.
    assert (PK : forall z, sbisim (Lvrel R) (α k z) (α k'' z)).
    { intros z. step in SIM'. destruct SIM' as [SF _].
      edestruct (SF (rcv e z) (Trans.Active (k z))) as (l2 & st2 & TR2 & SIM2 & HL2);
        [econstructor; reflexivity |].
      cbn in HL2. dependent destruction HL2. dependent destruction HR. inv_trans. subst.
      apply rcv_inv in EQl as [_ ->]. exact SIM2. }
    eapply epsilon_interp_state with (h := h) (s := s) in EPS.
    apply sb'_true_ss'. eapply ss'_epsilon_r_old; [exact EPS |].
    apply (proj1 (sb'_true_ss' (elem RR) _ _)).
    rewrite interp_state_vis.
    refine (SBisimAlt.bind_chain_gen _ (R := chain_b RR) _ _ _ _ eq true _ _).
    + change (TransAlt.upd_rel (lift_L (Lvrel RS)) eq) with (lift_L (@Leq F (St * X0))).
      apply (@refl_sb' F C (St * X0) (lift_L Leq) lift_L_Leq_reflexiveL (chain_b RR) true).
    + intros side [st z] ? <-. cbn. apply step_sb'_guard. apply (BOTH _ _ R RS HRS). apply PK.
  - unfold MonadBr_stateT, mbr, MonadBr_ctree. cbn.
    rewrite bind_bind, bind_branch.
    apply step_sb'_true_br_l. intros x. rewrite bind_ret_l.
    apply (b_chain RR). apply step_sb'_true_guard_l. apply (CH _ _ R RS HRS).
    intros l t' TR. apply SIM. eapply trans_br with (y := x). exact TR.
Qed.

Lemma interp_state_sbisim_gen {E F B C St} `{HasB: B -< C}
  (h : E ~> stateT St (ctree F C)) :
  forall X Y (R : rel X Y) (RS : rel (St * X) (St * Y)),
  (forall s x y, R x y -> RS (s, x) (s, y)) ->
  forall (t : ctree E B X) (u : ctree E B Y) s,
  sbisim (Lvrel R) t u ->
  sbisim' (lift_L (Lvrel RS))
    (TransAlt.Active (interp_state h t s)) (TransAlt.Active (interp_state h u s)).
Proof.
  intros X Y R RS HRS t u s H [|].
  - apply interp_state_sbisim_aux with (R := R); [exact HRS |]. step in H. apply H.
  - apply (proj1 (sb'_chain_flip (c := chain_gfp _) false _ _ _)). cbn [negb].
    eapply (lequiv_sb'_chain (c := chain_gfp _)); [symmetry; apply flipL_lift_L_Lvrel |].
    apply interp_state_sbisim_aux with (R := flip R); [intros s' x y HR; exact (HRS s' y x HR) |].
    apply sbisim_Lvrel_flip in H. step in H. apply H.
Qed.

#[global] Instance interp_state_sbisim {E F B C X St} {R : relation X}
  `{HasB: B -< C} :
  forall (h : E ~> stateT St (ctree F C)),
  Proper (sbisimT (Lvrel R) ==> eq ==> sbisimT (Lvrel (@eq St * R)%signature))
    (interp_state (C := B) h (T := X)).
Proof.
  intros h t u SIM st st' <-. unfold sbisimT in *.
  apply sbisim_sbisim'. cbn [o2n_S].
  apply interp_state_sbisim_gen with (R := R); [| exact SIM].
  intros; split; cbn; auto.
Qed.

#[global] Instance interp_state_sbisim_eq {E F B C X St} `{HasB: B -< C} :
  forall (h : E ~> stateT St (ctree F C)),
  Proper (sbisimT Leq ==> eq ==> sbisimT Leq) (interp_state (C := B) h (T := X)).
Proof.
  intros h t u SIM st st' <-. unfold sbisimT in *.
  apply sbisim_sbisim'. cbn [o2n_S].
  apply interp_state_sbisim_gen with (R := eq); [| exact SIM].
  intros; subst; reflexivity.
Qed.

(* The proof that interp preserves sbisim reuses the interp_state proof. *)

#[global] Instance interp_sbisim_eq {E F B C X} `{HasB: B -< C} :
  forall (h : E ~> ctree F C),
  Proper (sbisimT Leq ==> sbisimT Leq) (interp (B := B) h (T := X)).
Proof.
  intros h t u SIM.
  rewrite !interp_lift_handler.
  unfold CTree.map. eapply sbisim_bind_gen with (SS := eq).
  - change (upd_rel Leq eq) with (@Leq F (unit * X)). apply interp_state_sbisim_eq; auto.
  - intros [] ? <-. apply sbisim_ret. reflexivity.
Qed.

Arguments get {S E C _}.
Arguments put {S E C _}.
Arguments run_state {S E C} [_] _ _.
Arguments fold_state {E C M S FM MM IM _ _} h g [T].
Arguments interp_state {E C M S FM MM IM BM _ _} h [T].
Arguments refine_state {E C M S FM MM IM _ _ _} g [T].
