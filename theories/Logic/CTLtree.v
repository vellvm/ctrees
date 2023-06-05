(*|
=========================================
Modal logics over ctrees
=========================================
|*)
From Coinduction Require Import
	coinduction rel tactics.
From CTree Require Import
  Utils
  CTree
  Eq
  Logic.CTLwip.
Import CTreeNotations.
Set Implicit Arguments.


(** * Kripke structures from Labelled Transition Systems *)
Section From_LTS.

  (** Contrary, to Kripke structures, LTSs carry no information in their states,
      but annotate their transitions with labels instead. They are hence made of:
      - a domain of states [stateL]
      - a domain of labels [labelL]
      - a labelled transition relation [transL]
   *)
  Class LTS : Type :=
    {
      stateL : Type;
      labelL : Type;
      transL : stateL -> labelL -> stateL -> Prop
    }.

  (** Building Kripke structures out of LTSs.
      We think of an LTS as describing a computation processing
      an hidden internal state through operations described by
      labels.
      In order to derive a Kripke structure from an LTS, we hence
      provide:
      - a domain of observations [obs] modelling an abstraction of the
      internal state we wish to observe and reason about
      - a function describing how labels act upon observations
      Given this data, the structure goes as follows:
      - states are LTS states enriched with an observation
      - transitions are fired if the state components are related by
      a labelled transition, such that the label taken describes the
      update to the observation
      - facts are predicate over observations, rendering checks trivial
   *)
  Definition make_Kripke_of_LTS
    (L : LTS)
    (obs : Type)
    (upd : labelL -> obs -> obs)
    : Kripke :=
    {|
      stateK := stateL * obs;
      transK s1 s2 := (exists l, transL (fst s1) l (fst s2) /\ upd l (snd s1) = snd s2) ;
      factK  := obs -> Prop ;
      checkK := fun f '(_,o) => f o
    |}.

  (** Canonical observation: histories
      In particular, a canonical notion of observation is to
      record the traces of labels that have been taken up to
      this point
   *)
  Definition Kripke_of_LTS_canonical (L : LTS) :=
    @make_Kripke_of_LTS L (list labelL)
      (fun l h => cons l h).

End From_LTS.

(** * Kripke structures from ctrees *)
Section From_CTree.

  Variable (E B : Type -> Type) (R : Type).
  Context `{B0 -< B}.
  Notation computation := (ctree E B R).

  (* [ctrees] are already seen as LTS, we simply package it in the structure *)
  Definition LTS_of_ctree : LTS :=
    {|
      stateL := computation ;
      labelL := @label E ;
      transL := fun c l c' => trans l c c'
    |}
  .

  (* And hence spawn Kripke structure *)
  Definition makeK
    (obs : Type)
    (upd : @label E -> obs -> obs)
    : Kripke :=
    make_Kripke_of_LTS LTS_of_ctree upd.

  Lemma sbisim_bisimK obs (upd : @label E -> obs -> obs) :
    forall (t s : computation),
      t ~ s ->
      forall (o : obs),
        bisimK (@makeK obs upd) (t,o) (s,o).
  Proof.
    unfold bisimK.
    coinduction r CIH.
    intros * EQ *.
    split.
    - cbn; split; auto.
      intros [t' o'] (l & TR & up); cbn.
      step in EQ; apply EQ in TR; destruct TR as (? & s' & TR' & EQ' & <-).
      exists (s',o'); split.
      exists l; split; auto.
      apply CIH, EQ'.
    - cbn; split; auto.
      intros [s' o'] (l & TR & up); cbn.
      step in EQ; apply EQ in TR; destruct TR as (? & t' & TR' & EQ' & <-).
      exists (t',o'); split.
      exists x; split; auto.
      apply CIH, EQ'.
  Qed.

  (* Recurrent case: τ transitions do not impact our observations *)
  Definition obs_τ_id
    {O}
    (upd_e : {x : Type & E x & x} -> O -> O)
    (upd_r : {x : Type & x} -> O -> O) :
    @label E -> O -> O :=
    fun l => match l with
          | obs e x => upd_e (existT2 _ _ _ e x)
          | val x   => upd_r (existT _ _ x)
          | tau     => fun o => o
          end.

  (* Recurrent case: τ transitions do not impact our observations *)
  Definition obs_vis
    {O}
    (upd_e : {x : Type & E x & x} -> O -> O) :
    @label E -> O -> O :=
    fun l => match l with
          | obs e x => upd_e (existT2 _ _ _ e x)
          | val x   => fun o => o
          | tau     => fun o => o
          end.

  (* Observing sound termination *)
  Variant status : Set := | Running | Done.
  Definition upd_status : @label E -> status -> status :=
    fun l => match l with
          | val _ => fun _ => Done
          | _     => fun o => o
          end.

  (** Building a Kripke structure over a [ctree]
      Embarks:
      - that τ transitions are not observed
      - observation of safe termination
      Is parameterized by the observation returned values and interactions
   *)
  Definition makeK'
    (obs : Type)
    (upd_e : {x : Type & E x & x} -> obs -> obs)
    (upd_r : {x : Type & x} -> obs -> obs)
    : Kripke :=
    @makeK (obs * status)
      (fun l '(o,s) => (obs_τ_id upd_e upd_r l o, upd_status l s)).

  Lemma sbisim_bisimK' obs upd_e upd_r :
    forall (t s : computation),
      t ~ s ->
      forall o, bisimK (@makeK' obs upd_e upd_r) (t,o) (s,o).
  Proof.
   intros.
   now apply sbisim_bisimK.
  Qed.

  (** Building a Kripke structure over a [ctree]
      Embarks:
      - that τ transitions are not observed
      - observation of safe termination
      Is parameterized by the observation returned values and interactions
   *)
  Definition makeKV
    (obs : Type)
    (upd_e : {x : Type & E x & x} -> obs -> obs)
    : Kripke :=
    @makeK obs (obs_vis upd_e).

  Lemma sbisim_bisimKV obs upd_e :
    forall (t s : computation),
      t ~ s ->
      forall o, bisimK (@makeKV obs upd_e) (t,o) (s,o).
  Proof.
   intros.
   now apply sbisim_bisimK.
  Qed.

End From_CTree.

Lemma trans_trigger_last:
  forall {E B : Type -> Type} {X : Type} `{B0 -< B}
    (e : E X) (x : X),
    trans (Trans.obs e x) (CTree.trigger (B := B) e) (Ret x).
Proof.
  intros.
  now econstructor.
Qed.
#[export] Hint Resolve trans_trigger_last : trans.

Lemma trans_trigger_last_inv:
  forall {E B : Type -> Type} {X : Type} `{B0 -< B}
    (e : E X) l u,
    trans l (CTree.trigger (B := B) e) u ->
    exists x : X, u ≅ Ret x /\ l = obs e x.
Proof.
  intros * TR.
  unfold CTree.trigger in TR; inv_trans; eauto.
Qed.

Section Theory.

  Variable (E B : Type -> Type) (R : Type).
  Context `{B0 -< B}.
  Notation prog := (ctree E B R).

  Notation inhabited R := R.
  Variable (obs : Type) (upd_e: {x : Type & E x & x} -> obs -> obs).

  #[local] Instance K : Kripke := @makeKV E B R _ obs upd_e.
  Notation upd := (obs_vis upd_e).
  (* #[export] Instance foo {E B X} `{B0 -< B} (obs : Type) : *)
  (*   subrelation (@sbisim' E B X _ obs) (bisimK K: relation _). *)

  (* Variant sbisim' : rel K K := *)
  (* | sbisim'_ t u s (EQ : t ~ u) : sbisim' (t,s) (u,s). *)


  (* #[local] Instance K' : Kripke := @makeK E B S _ obs upd. *)

  (* Notation "t , s |= φ " := (satF φ (t,s)) (at level 80, right associativity). *)

  (* We assume total (deterministic) update functions,
     the transition in the LTS is hence enough information to
     step in the Kripke structure.
   *)
  Lemma step_stepK l (t u : prog) (s : obs):
    trans l t u ->
    transK (t,s) (u,upd l s).
  Proof.
    intros * TR; econstructor; split; [apply TR | reflexivity ].
  Qed.

  Ltac next := eapply step_stepK; eauto with trans.
  Ltac lives := econstructor; next.

  (* Characterising live states *)
  Lemma live_ret : forall (r : R) (s : obs),
      live (Ret r,s).
  Proof.
    lives.
  Qed.

  Lemma live_trigger : forall (e : E R) (s : obs),
      inhabited R ->
      live (trigger e,s).
  Proof.
    unshelve lives; auto.
  Qed.

  Create HintDb ctl.
  Hint Resolve live_ret live_trigger : ctl.

  Ltac bkK :=
    match goal with
    | h : @stateK _ |- _ => destruct h
    end.
  Ltac inv_transK :=
    (repeat bkK);
    match goal with
    | h : transK _ _ |- _ =>
        destruct h as (? & ? & ?);
        cbn in *;
        inv_trans
    end; cbn in *; subst.

  Existing Instance sat_bisim.
  (* Instance foo : Proper (sbisim eq ==> sbisim') (fun t => (t,o)). *)
  #[global] Instance foo : Proper (sbisim eq ==> eq ==> bisimK _) (Datatypes.pair).
  now repeat intro; subst; apply sbisim_bisimK.
  Qed.

  #[global] Instance foo' : Proper (equ eq ==> eq ==> bisimK _) (Datatypes.pair).
  Proof.
    repeat intro. subst. apply foo.
    apply equ_sbisim_subrelation.
    typeclasses eauto. assumption. reflexivity.
  Qed.

  (* TODO: characterize a class of formula valid in dead states.
     TODO: specialize over makeK'

     safe_ret (φ : Formula K) : Formula K' :=
      fun (t,(stat,o)) => stat = Done \/ satF φ (t,o)
   *)
  Lemma ret_AX (r : R) (φ : Formula) (s: obs) :
    satF φ (stuckD, s) ->
    satF (FAX φ) (Ret r, s).
  Proof with (eauto with ctl).
    (* intros * HS. *)
    constructor...
    intros.
    now inv_transK.
  Qed.

  Lemma ret_AX' (r : R) (p : factK) (s: obs) :
    p s ->
    satF (FAX (FNow p)) (Ret r, s).
  Proof with (eauto with ctl).
    now intros; apply ret_AX.
  Qed.
  (* and other formula.. *)

  Lemma trigger_AX (e : E _) (φ : Formula) (s: obs) :
    inhabited R ->
    (forall r, satF φ (Ret r, upd (Trans.obs e r) s)) ->
    satF (FAX φ) (trigger e,s).
  Proof with (eauto with ctl).
    intros * r Hφ.
    constructor...
    intros * TR.
    bkK.
    destruct TR as (? & TR & ?);
      cbn in *;
    eapply trans_trigger_last_inv in TR as (? & ? & ?).
    subst; rewrite H1; auto.
  Qed.
  (* and other formulae *)

  Lemma ret_AwG x (φ : Formula) (s: obs) :
    satF φ (Ret x, s) ->
    satF φ (stuckD, s) ->
    satF (FAwG φ) (Ret x, s).
  Proof.
    intros. cbn. step. split; [apply H0 |].
    intros. inv_transK.
    step. split; [subs; apply H1 |].
    intros. inv_transK. subs. now apply stuckD_is_stuck in H2.
  Qed.

  Lemma ret_AwG_now x (F : factK) (s: obs) :
    F s ->
    satF (FAwG (FNow F)) (Ret x, s).
  Proof.
    intros. cbn. step. split; [apply H0 |].
    intros. inv_transK.
    step. split; [subs; apply H0 |].
    intros. inv_transK. subs. now apply stuckD_is_stuck in H1.
  Qed.

  Lemma vis_AwG {X} (e : E X) k (φ : Formula) (s: obs) :
    satF φ (Vis e k, s) ->
    (forall x, satF (FAwG φ) (k x, upd (Trans.obs e x) s)) ->
    satF (FAwG φ) (Vis e k, s).
  Proof.
    intros. cbn. step. constructor.
    - assumption.
    - intros. inv_transK. specialize (H1 x0).
      step.
      step in H1. destruct H1.
      split.
      subs. apply H1.
      intros. specialize (H2 s'). inv_transK. subs. eauto.
  Qed.

  Existing Instance EF_bisim.

  Arguments satF : simpl never.

  Lemma bind_EF (t : prog) (k : R -> prog) (p : factK) (s: obs) :
    satF (FEF (FNow p)) (t,s) ->
    satF (FEF (FNow p)) (t >>= k,s).
  Proof with (eauto with ctl).
    intros * HS.
    remember (t,s) as S. revert t s HeqS.
    induction HS; intros; subst.
    - now constructor 1.
    - destruct IH as (s' & TR & HF).
      inv_transK.
      destruct x.
      + econstructor 2.
        exists (x <- s;; k x, upd tau s0); split.
        exists tau; split.
        apply trans_bind_l; auto with trans.
        reflexivity.
        apply HF.
        reflexivity.
      + econstructor 2.
        exists (x <- s;; k x, upd (Trans.obs e v) s0); split.
        exists (Trans.obs e v); split.
        apply trans_bind_l; auto with trans.
        reflexivity.
        apply HF.
        reflexivity.
      + cbn in *.
        specialize (HF _ _ eq_refl).
        pose proof trans_val_inv H0 as EQ.
        rewrite EQ in HF.
        inv HF.
        * cbn in *.
          now constructor 1.
        * exfalso; clear -H1.
          destruct H1 as (? & (? & TRabs & _) & _).
          cbn in *.
          apply trans_bind_inv in TRabs.
          destruct TRabs as [(_ & (? & abs & _)) | (? & abs & _)].
          all: eapply stuckD_is_stuck; eauto.
  Qed.



  (* Lemma bind_EF (t : prog) (k : R -> prog) (φ : Formula) (s: obs) : *)
  (*   satF (FEF φ) (t,s) -> *)
  (*   satF (FEF φ) (t >>= k,s). *)
  (* Proof with (eauto with ctl). *)
  (*   intros * HS. *)
  (*   induction HS. *)
  (*   - constructor 1. *)
  (*   intros * r Hφ. *)
  (*   constructor... *)
  (*   intros * TR. *)
  (*   bkK. *)
  (*   destruct TR as (? & TR & ?); *)
  (*     cbn in *; *)
  (*   eapply trans_trigger_last_inv in TR as (? & ? & ?). *)
  (*   subst; rewrite H1; auto. *)
  (* Qed. *)

(*
Section Theory.

  Variable (E B : Type -> Type) (R : Type).
  Context `{B0 -< B}.
  Notation prog := (ctree E B R).

  Notation inhabited R := R.
  Variable (obs : Type) (upd : @label E -> obs -> obs).

  #[local] Instance K  : Kripke := @makeK E B R _ obs upd.
  (* #[export] Instance foo {E B X} `{B0 -< B} (obs : Type) : *)
  (*   subrelation (@sbisim' E B X _ obs) (bisimK K: relation _). *)

  (* Variant sbisim' : rel K K := *)
  (* | sbisim'_ t u s (EQ : t ~ u) : sbisim' (t,s) (u,s). *)


  (* #[local] Instance K' : Kripke := @makeK E B S _ obs upd. *)

  (* Notation "t , s |= φ " := (satF φ (t,s)) (at level 80, right associativity). *)

  (* We assume total (deterministic) update functions,
     the transition in the LTS is hence enough information to
     step in the Kripke structure.
   *)
  Lemma step_stepK l (t u : prog) (s : obs):
    trans l t u ->
    transK (t,s) (u,upd l s).
  Proof.
    intros * TR; econstructor; split; [apply TR | reflexivity ].
  Qed.

  Ltac next := eapply step_stepK; eauto with trans.
  Ltac lives := econstructor; next.

  (* Characterising live states *)
  Lemma live_ret : forall (r : R) (s : obs),
      live (Ret r,s).
  Proof.
    lives.
  Qed.

  Lemma live_trigger : forall (e : E R) (s : obs),
      inhabited R ->
      live (trigger e,s).
  Proof.
    unshelve lives; auto.
  Qed.

  Create HintDb ctl.
  Hint Resolve live_ret live_trigger : ctl.

  Ltac bkK :=
    match goal with
    | h : @stateK _ |- _ => destruct h
    end.
  Ltac inv_transK :=
    (repeat bkK);
    match goal with
    | h : transK _ _ |- _ =>
        destruct h as (? & ? & ?);
        cbn in *;
        inv_trans
    end; cbn in *; subst.

  (* TODO: characterize a class of formula valid in dead states.
     TODO: specialize over makeK'

     safe_ret (φ : Formula K) : Formula K' :=
      fun (t,(stat,o)) => stat = Done \/ satF φ (t,o)
   *)
  Lemma ret_AX (r : R) (φ : Formula) (s: obs) :
    (forall (r : R), satF φ (stuckD, upd (val r) s)) ->
    satF (FAX φ) (Ret r, s).
  Proof with (eauto with ctl).
    intros * HS.
    constructor...
    intros.
    now inv_transK.
  Qed.
  (* and other formula.. *)

  Lemma trigger_AX (e : E _) (φ : Formula) (s: obs) :
    inhabited R ->
    (forall r, satF φ (Ret r, upd (Trans.obs e r) s)) ->
    satF (FAX φ) (trigger e,s).
  Proof with (eauto with ctl).
    intros * r Hφ.
    constructor...
    intros * TR.
    bkK.
    destruct TR as (? & TR & ?);
      cbn in *;
    eapply trans_trigger_last_inv in TR as (? & ? & ?).
    subst; rewrite H1; auto.
  Qed.
  (* and other formulae *)

  Lemma bind_EF (t : prog) (k : R -> prog) (p : factK) (s: obs) :
    satF (FEF (FNow p)) (t,s) ->
    satF (FEF (FNow p)) (t >>= k,s).
  Proof with (eauto with ctl).
    intros * HS.
    remember (t,s) as S. revert t s HeqS.
    induction HS; intros; subst.
    - now constructor 1.
    - destruct IH as (s' & TR & HF).
      inv_transK.
      destruct x.
      + econstructor 2.
        exists (x <- s;; k x, upd tau s0); split.
        exists tau; split.
        apply trans_bind_l; auto with trans.
        reflexivity.
        apply HF.
        reflexivity.
      + econstructor 2.
        exists (x <- s;; k x, upd (Trans.obs e v) s0); split.
        exists (Trans.obs e v); split.
        apply trans_bind_l; auto with trans.
        reflexivity.
        apply HF.
        reflexivity.
      + econstructor 2.
        (* Must impose that [val] label do not change the observation *)
  Admitted.

  (* Lemma bind_EF (t : prog) (k : R -> prog) (φ : Formula) (s: obs) : *)
  (*   satF (FEF φ) (t,s) -> *)
  (*   satF (FEF φ) (t >>= k,s). *)
  (* Proof with (eauto with ctl). *)
  (*   intros * HS. *)
  (*   induction HS. *)
  (*   - constructor 1. *)
  (*   intros * r Hφ. *)
  (*   constructor... *)
  (*   intros * TR. *)
  (*   bkK. *)
  (*   destruct TR as (? & TR & ?); *)
  (*     cbn in *; *)
  (*   eapply trans_trigger_last_inv in TR as (? & ? & ?). *)
  (*   subst; rewrite H1; auto. *)
  (* Qed. *)

*)
End Theory.
