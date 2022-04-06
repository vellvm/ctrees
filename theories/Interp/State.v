From Coq Require Import Program.Tactics Morphisms.
From ExtLib Require Import
     Structures.Functor
     Structures.Monad.

From ITree Require Import
     Subevent
     CategoryOps
     Indexed.Sum.

From Coinduction Require Import coinduction rel tactics.

Import ITree.Basics.Basics.Monads.

From CTree Require Import
     CTrees
     CTreesTheory
     Utils
     Interp
     Bisim
     Equ.

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
      Choice b n' (fun i => interp_state f (k i) s)
  | VisF e k => f _ e s >>= (fun sx => TauI (interp_state f (k (snd sx)) (fst sx)))
  end.

  Typeclasses eauto := debug 6.
  
  Lemma unfold_interp_state {E F R} (h : E ~> Monads.stateT S (ctree F))
        (t : ctree E R) s :
    interp_state h t s ≅ _interp_state h (observe t) s.
  Proof.
    unfold interp_state, interp, Basics.iter, MonadIter_stateT0, Basics.iter, MonadIter_ctree; cbn.
    rewrite unfold_iter; cbn.
    destruct observe; cbn.
    - rewrite 2 bind_ret_l; reflexivity.
    - rewrite bind_map, bind_bind; cbn; setoid_rewrite bind_ret_l.
      apply bind_equ_cong; reflexivity.
    - do 2 rewrite bind_bind; cbn; do 2 setoid_rewrite bind_ret_l; cbn.
      rewrite bind_bind.
      setoid_rewrite bind_ret_l; cbn.
      setoid_rewrite bind_choice.
      setoid_rewrite bind_ret_l.
      rewrite equ_ChoiceF; try reflexivity.
      (** Hm weird *)
      cbn; intros; unfold interp_state.
  Admitted.

  #[global]
   Instance eq_itree_interp_state {E F R} (h : E ~> Monads.stateT S (ctree F)) :
    Proper (equ eq ==> eq ==> equ eq)
           (@interp_state _ _ _ _ _ _ h R).
  Proof.
    repeat red; intros; subst.
    
    rewrite !unfold_interp_state.
    destruct observe eqn:Hobs; cbn.
    
  (**
    (** ???? *)
    ginit. pcofix CIH. intros h x y H0 x2 _ [].
    rewrite !unfold_interp_state.
    punfold H0; repeat red in H0.
    destruct H0; subst; pclearbot; try discriminate; cbn.
    - gstep; constructor; auto.
    - gstep; constructor; auto with paco.
    - guclo eqit_clo_bind. econstructor.
      + reflexivity.
      + intros [] _ []. gstep; constructor; auto with paco itree.
  Qed. *)
  Admitted.


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
    : interp_state h (TauI t) s ≅ TauI (interp_state h t s).
  Proof.
    rewrite unfold_interp_state; reflexivity.
  Qed.

  Lemma interp_state_trigger_eqit {E F : Type -> Type} {R: Type}
        (e : E R) (f : E ~> Monads.stateT S (ctree F)) (s : S)
    : (interp_state f (CTree.trigger e) s) ≅ (f _ e s >>= fun x => TauI (Ret x)).
  Proof.
    unfold CTree.trigger. rewrite interp_state_vis.
    eapply bind_equ_cong; try reflexivity.
    intros []. setoid_rewrite interp_state_ret. reflexivity.
  Qed.

  Typeclasses eauto := debug 4.
  Lemma interp_state_trigger {E F : Type -> Type} {R: Type}
        (e : E R) (f : E ~> Monads.stateT S (ctree F)) (s : S)
    : interp_state f (CTree.trigger e) s ≈ f _ e s.
  Proof.
    unfold CTree.trigger. rewrite interp_state_vis.
    match goal with
      |- ?y ≈ ?x => remember y; rewrite <- (bind_ret_r x); subst
    end.
    eapply bind_wbisim_cong; try reflexivity.
    (** Must provide a relation here? *)
    admit.
    intros []. setoid_rewrite interp_state_ret.
    cbn.
    (** This is obviously true (diff by TauI) why does reflexivity not solve it? *)
    admit.
  Admitted.

End State.

Arguments get {S E _}.
Arguments put {S E _}.
Arguments run_state {S E} [_] _ _.
Arguments interp_state {S E M FM MM IM MC} h [T].

(**
Lemma interp_state_bind {E F : Type -> Type} {A B S : Type}
      (f : forall T, E T -> S -> itree F (S * T)%type)
      (t : itree E A) (k : A -> itree E B)
      (s : S) :
  (interp_state f (t >>= k) s)
    ≅
  (interp_state f t s >>= fun st => interp_state f (k (snd st)) (fst st)).
Proof.
  revert t k s.
  ginit. pcofix CIH.
  intros t k s.
  rewrite unfold_bind.
  rewrite (unfold_interp_state f t).
  destruct (observe t).
  - cbn. rewrite !bind_ret_l. cbn.
    apply reflexivity.
  - cbn. rewrite !bind_tau, interp_state_tau.
    gstep. econstructor. gbase. apply CIH.
  - cbn. rewrite interp_state_vis, bind_bind.
    guclo eqit_clo_bind. econstructor.
    + reflexivity.
    + intros u2 ? [].
      rewrite bind_tau.
      gstep; constructor.
      ITree.fold_subst.
      auto with paco.
Qed.

#[global]
Instance eutt_interp_state {E F: Type -> Type} {S : Type}
         (h : E ~> Monads.stateT S (itree F)) R RR :
  Proper (eutt RR ==> eq ==> eutt (prod_rel eq RR)) (@interp_state E (itree F) S _ _ _ h R).
Proof.
  repeat intro. subst. revert_until RR.
  einit. ecofix CIH. intros.

  rewrite !unfold_interp_state. punfold H0. red in H0.
  induction H0; intros; subst; simpl; pclearbot.
  - eret.
  - etau.
  - ebind. econstructor; [reflexivity|].
    intros; subst.
    etau. ebase.
  - rewrite tau_euttge, unfold_interp_state; eauto.
  - rewrite tau_euttge, unfold_interp_state; eauto.
Qed.

#[global]
Instance eutt_interp_state_eq {E F: Type -> Type} {S : Type}
         (h : E ~> Monads.stateT S (itree F)) R :
  Proper (eutt eq ==> eq ==> eutt eq) (@interp_state E (itree F) S _ _ _ h R).
Proof.
  repeat intro. subst. revert_until R.
  einit. ecofix CIH. intros.

  rewrite !unfold_interp_state. punfold H0. red in H0.
  induction H0; intros; subst; simpl; pclearbot.
  - eret.
  - etau.
  - ebind. econstructor; [reflexivity|].
    intros; subst.
    etau. ebase.
  - rewrite tau_euttge, unfold_interp_state; eauto.
  - rewrite tau_euttge, unfold_interp_state; eauto.
Qed.


Lemma eutt_interp_state_aloop {E F S I I' A A'}
      (RA : A -> A' -> Prop) (RI : I -> I' -> Prop)
      (RS : S -> S -> Prop)
      (h : E ~> Monads.stateT S (itree F))
      (t1 : I -> itree E (I + A))
      (t2 : I' -> itree E (I' + A')):
  (forall i i' s1 s2, RS s1 s2 -> RI i i' ->
     eutt (prod_rel RS (sum_rel RI RA))
                     (interp_state h (t1 i) s1)
                     (interp_state h (t2 i') s2)) ->
  (forall i i' s1 s2, RS s1 s2 -> RI i i' ->
     eutt (fun a b => RS (fst a) (fst b) /\ RA (snd a) (snd b))
          (interp_state h (ITree.iter t1 i) s1)
          (interp_state h (ITree.iter t2 i') s2)).
Proof.
  intro Ht.
  einit. ecofix CIH. intros.
  rewrite 2 unfold_iter.
  rewrite 2 interp_state_bind.
  ebind; econstructor.
  - eapply Ht; auto.
  - intros [s1' i1'] [s2' i2'] [? []]; cbn.
    + rewrite 2 interp_state_tau. auto with paco.
    + rewrite 2 interp_state_ret. auto with paco.
Qed.

Lemma eutt_interp_state_iter {E F S A A' B B'}
      (RA : A -> A' -> Prop) (RB : B -> B' -> Prop)
      (RS : S -> S -> Prop)
      (h : E ~> Monads.stateT S (itree F))
      (t1 : A -> itree E (A + B))
      (t2 : A' -> itree E (A' + B')) :
  (forall ca ca' s1 s2, RS s1 s2 ->
                        RA ca ca' ->
     eutt (prod_rel RS (sum_rel RA RB))
          (interp_state h (t1 ca) s1)
          (interp_state h (t2 ca') s2)) ->
  (forall a a' s1 s2, RS s1 s2 -> RA a a' ->
     eutt (fun a b => RS (fst a) (fst b) /\ RB (snd a) (snd b))
          (interp_state h (iter (C := ktree _) t1 a) s1)
          (interp_state h (iter (C := ktree _) t2 a') s2)).
Proof.
  apply eutt_interp_state_aloop.
Qed.

Lemma eutt_interp_state_loop {E F S A B C} (RS : S -> S -> Prop)
      (h : E ~> Monads.stateT S (itree F))
      (t1 t2 : C + A -> itree E (C + B)) :
  (forall ca s1 s2, RS s1 s2 ->
     eutt (fun a b => RS (fst a) (fst b) /\ snd a = snd b)
          (interp_state h (t1 ca) s1)
          (interp_state h (t2 ca) s2)) ->
  (forall a s1 s2, RS s1 s2 ->
     eutt (fun a b => RS (fst a) (fst b) /\ snd a = snd b)
          (interp_state h (loop (C := ktree E) t1 a) s1)
          (interp_state h (loop (C := ktree E) t2 a) s2)).
Proof.
  intros.
  unfold loop, bimap, Bimap_Coproduct, case_, Case_Kleisli, Function.case_sum, id_, Id_Kleisli, cat, Cat_Kleisli, inr_, Inr_Kleisli, inl_, Inl_Kleisli, lift_ktree_; cbn.
  rewrite 2 bind_ret_l.
  eapply (eutt_interp_state_iter eq eq); auto; intros.
  rewrite 2 interp_state_bind.
  subst.
  eapply eutt_clo_bind; eauto.
  intros.
  cbn in H2; destruct (snd u1); rewrite <- (proj2 H2).
  - rewrite bind_ret_l, 2 interp_state_ret.
    pstep.
    constructor.
    split; cbn; auto using (proj1 H2).
  - rewrite bind_ret_l, 2 interp_state_ret. pstep. constructor.
    split; cbn; auto using (proj1 H2).
Qed.

(* SAZ: These are probably too specialized. *)
Definition state_eq {E S X}
  : (stateT S (itree E) X) -> (stateT S (itree E) X) -> Prop :=
  fun t1 t2 => forall s, eq_itree eq (t1 s) (t2 s).

Lemma interp_state_iter {E F } S (f : E ~> stateT S (itree F)) {I A}
      (t  : I -> itree E (I + A))
      (t' : I -> stateT S (itree F) (I + A))
      (EQ_t : forall i, state_eq (State.interp_state f (t i)) (t' i))
  : forall i, state_eq (State.interp_state f (ITree.iter t i))
                  (Basics.iter t' i).
Proof.
  unfold Basics.iter, MonadIter_stateT0, Basics.iter, MonadIter_itree in *; cbn.
  ginit. pcofix CIH; intros i s.
  rewrite 2 unfold_iter; cbn.
  rewrite !bind_bind.
  setoid_rewrite bind_ret_l.
  rewrite interp_state_bind.
  guclo eqit_clo_bind; econstructor; eauto.
  - apply EQ_t.
  - intros [s' []] _ []; cbn.
    + rewrite interp_state_tau.
      gstep; constructor.
      auto with paco.
    + rewrite interp_state_ret; apply reflexivity.
Qed.

Lemma interp_state_iter' {E F } S (f : E ~> stateT S (itree F)) {I A}
      (t  : I -> itree E (I + A))
  : forall i, state_eq (State.interp_state f (ITree.iter t i))
                       (Basics.iter (fun i => State.interp_state f (t i)) i).
Proof.
  eapply interp_state_iter.
  intros i.
  red. reflexivity.
Qed.
*)
