From ExtLib Require Import
     Structures.Functor
     Structures.Monad.

From ITree Require Import
     Events.State
     CategoryOps.
Import Basics.Monads.

From CTree Require Import
     CTree
     Interp.Interp
     Eq.

Import SBisimNotations.
Import MonadNotation.
Open Scope monad_scope.

Set Implicit Arguments.

#[global] Instance MonadChoice_stateT {S M C} {MM : Monad M} {AM : MonadChoice M C}: MonadChoice (stateT S M) C :=
  fun b X c s => f <- Utils.choice b _ c;; ret (s,f).

Definition interp_state {E C M} S
           {FM : Functor M} {MM : Monad M} {IM : MonadIter M}
           (h : E ~> stateT S M) (h' : bool -> C ~> stateT S M) :
  ctree E C ~> stateT S M := interp h h'.

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
    := fun _ c s => Choice b c (fun x => Ret (s, x)).

  Definition run_state {E C} `{C1 -< C}
    : ctree (stateE +' E) C ~> stateT S (ctree E C) :=
    interp_state (case_ h_state pure_state) pure_state_choice.

End State.

(* Stateful handlers [E ~> stateT S (itree F)] and morphisms
   [E ~> state S] define stateful itree morphisms
   [itree E ~> stateT S (itree F)]. *)
Section State.

  Variable (S : Type).
  Context {E F C D : Type -> Type}
          `{C1 -< D}
          {R : Type}
          (h : E ~> stateT S (ctree F D))
          (h' : bool -> C ~> stateT S (ctree F D)).

  (** Facts about state (equational theory) *)
  Definition _interp_state
             (h  : E ~> stateT S (ctree F D))
             (h' : bool -> C ~> stateT S (ctree F D))
             (ot : ctreeF E C R (ctree E C R)) :
    stateT S (ctree F D) R :=
    fun s =>
      match ot with
      | RetF r        => Ret (s, r)
      | ChoiceF b c k => h' b _ c s >>= fun sx => tauI (interp_state h h' (k (snd sx)) (fst sx))
      | VisF e k      => h _ e s    >>= fun sx => tauI (interp_state h h' (k (snd sx)) (fst sx))
      end.

  Lemma interp_interp_state (t : ctree E C R) (s : S) :
    interp h h' t s ≅ interp_state h h' t s.
  Proof.
    reflexivity.
  Qed.

  Lemma unfold_interp_state t s :
    interp_state h h' t s ≅ _interp_state h h' (observe t) s.
  Proof.
    unfold interp_state, interp, Basics.iter, MonadIter_stateT0, Basics.iter, MonadIter_ctree; cbn.
    rewrite unfold_iter; destruct observe eqn:Hobs; cbn.
    - rewrite 2 bind_ret_l; reflexivity.
    - rewrite bind_map, bind_bind; cbn; setoid_rewrite bind_ret_l.
      reflexivity.
    - rewrite !bind_bind, bind_map; cbn.
      upto_bind_eq.
      rewrite bind_ret_l.
      reflexivity.
  Qed.

  (* TODO: in the following proof, [cbn] reduces too much.
     Need to diagnostic and fix
   *)
  #[global]
  Instance equ_interp_state:
    Proper (equ eq ==> eq ==> equ eq)
           (@interp_state _ _ _ _ _ _ _ h h' R).
  Proof.
    unfold Proper, respectful.
    coinduction ? IH; intros * EQ1 * <-.
    rewrite !unfold_interp_state.
    step in EQ1; inv EQ1; cbn [_interp_state]; auto.
    - simpl bind. upto_bind_eq.
      constructor; intros; auto.
    - simpl bind. upto_bind_eq.
      constructor; auto.
  Qed.

  Lemma interp_state_ret
        (s : S) (r : R) :
    (interp_state h h' (Ret r) s) ≅ (Ret (s, r)).
  Proof.
    rewrite ctree_eta. reflexivity.
  Qed.

  Lemma interp_state_vis {T : Type}
  (e : E T) (k : T -> ctree E C R) (s : S)
    : interp_state h h' (Vis e k) s
                   ≅ h e s >>= fun sx => tauI (interp_state h h' (k (snd sx)) (fst sx)).
  Proof.
    rewrite unfold_interp_state; reflexivity.
  Qed.

  Lemma interp_state_tau `{C1 -< C}
        (t : ctree E C R) (s : S)
        : interp_state h h' (tauI t) s ≅ tauI (tauI (interp_state h h' t s)).
  Proof.
    rewrite unfold_interp_state.
  Abort.

End State.

(* Stateful handlers [E ~> stateT S (itree F)] and morphisms
   [E ~> state S] define stateful itree morphisms
   [itree E ~> stateT S (itree F)]. *)
Section State.

  Variable (S : Type).
  Context {E F C D : Type -> Type}
          `{C1 -< D}
          {R : Type}
          (h : E ~> stateT S (ctree F D))
          (h' : bool -> C ~> stateT S (ctree F D)).

  Lemma interp_state_trigger_eqit
        (e : E R) (s : S)
    : (interp_state h h' (CTree.trigger e) s) ≅ (h e s >>= fun x => tauI (Ret x)).
  Proof.
    unfold CTree.trigger. rewrite interp_state_vis; cbn.
    upto_bind_eq.
    (* TODO: why is this rewrite so slow?
       TODO: proof system for [equ] similar to the one for [sbisim]
     *)
    step. constructor. intros.
    rewrite interp_state_ret.
    now destruct x1.
  Qed.

  Lemma interp_state_trigger `{C0 -< D}
        (e : E R) (s : S)
    : interp_state h h' (CTree.trigger e) s ~ h e s.
  Proof.
    unfold CTree.trigger. rewrite interp_state_vis.
    rewrite <- (bind_ret_r (h e s)).
    match goal with
      |- ?y ~ ?x => remember y; rewrite <- (bind_ret_r x); subst
    end.
    cbn.
    upto_bind_eq.
    rewrite sb_tauI, interp_state_ret.
    now destruct x.
  Qed.

  Lemma interp_state_bind {A B}
        (t : ctree E C A) (k : A -> ctree E C B)
        (s : S) :
    (interp_state h h' (t >>= k) s) 
      ≅
      (interp_state h h' t s >>= fun st => interp_state h h' (k (snd st)) (fst st)).
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
      rewrite bind_tauI.
      constructor; intros ?; apply IH.
    - rewrite unfold_interp_state.
      cbn.
      rewrite bind_bind.
      upto_bind_eq.
      rewrite bind_tauI.
      constructor; intros ?; apply IH.
  Qed.

End State.

Arguments get {S E _}.
Arguments put {S E _}.
Arguments run_state {S E} [_] _ _.
Arguments interp_state {E C M S FM MM IM} h h' [T].
