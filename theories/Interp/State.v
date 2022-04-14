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

(* Stateful handlers [E ~> stateT S (itree F)] and morphisms
   [E ~> state S] define stateful itree morphisms
   [itree E ~> stateT S (itree F)]. *)
Section State.

  Variable (S : Type).

  #[global] Instance MonadChoice_stateT {M} {MM : Monad M} {AM : MonadChoice M}: MonadChoice (stateT S M) :=
  fun b n s =>
    f <- choice b n;;
    ret (s, f).

  Definition interp_state {E M}
           {FM : Functor M} {MM : Monad M}
           {IM : MonadIter M}{MC: MonadChoice M} (h : E ~> stateT S M) :
    ctree E ~> stateT S M := interp h.
  Variant stateE : Type -> Type :=
  | Get : stateE S
  | Put : S -> stateE unit.

  Definition get {E} `{stateE -< E} : ctree E S := trigger Get.
  Definition put {E} `{stateE -< E} : S -> ctree E unit := fun s => trigger (Put s).

  Definition h_state {E} : stateE ~> stateT S (ctree E) :=
    fun _ e s =>
      match e with
      | Get => Ret (s, s)
      | Put s' => Ret (s', tt)
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
  | ChoiceF b n' k =>
      Choice b n' (fun i => TauI (interp_state f (k i) s))
  | VisF e k => f _ e s >>= (fun sx => TauI (interp_state f (k (snd sx)) (fst sx)))
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
      setoid_rewrite bind_choice.
      setoid_rewrite bind_ret_l.

      apply choice_equ; intros t'.
      step; econstructor.
      intros.
      reflexivity.
  Qed.

  (* TODO: in the following proof, [cbn] reduces too much.
     Need to diagnostic and fix
   *)
  #[global]
   Instance equ_interp_state {E F R} (h : E ~> Monads.stateT S (ctree F)) :
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
                   ≅ h T e s >>= fun sx => TauI (interp_state h (k (snd sx)) (fst sx)).
  Proof.
    rewrite unfold_interp_state; reflexivity.
  Qed.

  Lemma interp_state_tau {E F : Type -> Type} {T : Type}
        (t : ctree E T) (h : E ~> Monads.stateT S (ctree F)) (s : S)
    : interp_state h (TauI t) s ≅ TauI (TauI (interp_state h t s)).
  Proof.
    rewrite unfold_interp_state; reflexivity.
  Qed.

  Lemma interp_state_trigger_eqit {E F : Type -> Type} {R: Type}
        (e : E R) (f : E ~> Monads.stateT S (ctree F)) (s : S)
    : (interp_state f (CTree.trigger e) s) ≅ (f _ e s >>= fun x => TauI (Ret x)).
  Proof.
    unfold CTree.trigger. rewrite interp_state_vis; cbn.
    upto_bind_eq.
    (* TODO: why is this rewrite so slow?
       TODO: proof system for [equ] similar to the one for [sbisim]
     *)
    setoid_rewrite interp_state_ret.
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
    rewrite sb_tauI, interp_state_ret.
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
      rewrite bind_tauI.
      constructor; intros ?; apply IH.
    - rewrite unfold_interp_state.
      cbn.
      rewrite bind_choice.
      constructor; intros ?.
      rewrite bind_tauI.
      step; constructor; intros ?.
      apply IH.
  Qed.

End State.

Arguments get {S E _}.
Arguments put {S E _}.
Arguments run_state {S E} [_] _ _.
Arguments interp_state {S E M FM MM IM MC} h [T].
