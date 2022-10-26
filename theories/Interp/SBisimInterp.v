(* begin hide *)

From CTree Require Import
     CTree Eq.

From ExtLib Require Import
     Structures.Functor
     Structures.Monad.

From ITree Require Import
     Basics.Basics
     Core.Subevent
     Interp.Interp.

From CTree Require Import
     CTreeDefinitions
     CTree.

Import CTreeNotations.
Open Scope ctree_scope.
Import CTreeNotations.

(* end hide *)

(** Helper inductive t0_det t t' means that t' is Guard*(t) *)
Inductive t0_det {E C X} `{B1 -< C}: relation (ctree E C X) :=
| t0_det_id : forall t t', t ≅ t' -> t0_det t t'
| t0_det_tau : forall t t' t'',
    t0_det t t' -> t'' ≅ Guard t -> t0_det t'' t'.

#[global] Instance t0_det_equ {E C X} `{Tau: B1 -< C}:
  Proper (equ eq ==> equ eq ==> flip impl) (@t0_det E C X _).
Proof.
  cbn. intros.
  revert x H. induction H1; intros.
  - econstructor. now rewrite H0, H1.
  - eapply t0_det_tau. apply IHt0_det. apply H0. reflexivity. rewrite H2. apply H.
Qed.

#[global] Instance t0_det_equ' {E C X} `{Tau: B1 -< C}:
  Proper (equ eq ==> equ eq ==> impl) (@t0_det E C X _).
Proof.
  cbn. intros. rewrite <- H, <- H0. apply H1.
Qed.

Lemma t0_det_bind {E C X Y} `{Tau: B1 -< C}: forall (t t' : ctree E C X) (k : X -> ctree E C Y),
  t0_det t t' ->
  t0_det (t >>= k) (t' >>= k).
Proof.
  intros. induction H.
  - rewrite H. constructor. reflexivity.
  - rewrite H0. setoid_rewrite bind_guard. eapply t0_det_tau. apply IHt0_det. reflexivity.
Qed.

Lemma t0_det_bind_ret_l {E C X Y} `{Tau: B1 -< C}: forall (t : ctree E C X) t' (k : X -> ctree E C Y) x,
  t0_det t (Ret x) ->
  t0_det (k x) t' ->
  t0_det (t >>= k) t'.
Proof.
  intros. remember (Ret x) as R. revert t' k x HeqR H0. induction H; intros; subst.
  - subst. rewrite H, bind_ret_l. apply H0.
  - rewrite H0. setoid_rewrite bind_guard.
    eapply t0_det_tau. 2: reflexivity. eapply IHt0_det. reflexivity. apply H1.
Qed.

Lemma t0_det_bind_ret_l_equ {E C X Y} `{Tau: B1 -< C}:
  forall (t : ctree E C X) (k : X -> ctree E C Y) x,
  t0_det t (Ret x) ->
  x <- t;; k x ≅ t;; k x.
Proof.
  intros. remember (Ret x) as R. induction H; subst.
  - rewrite H. rewrite !bind_ret_l. reflexivity.
  - rewrite H0. rewrite !bind_guard. apply br_equ. intro. apply IHt0_det. reflexivity.
Qed.

Lemma sbisim_t0_det {E C X} `{Stuck: B0 -< C} `{Tau: B1 -< C}:
  forall (t t' : ctree E C X), t0_det t t' -> t ~ t'.
Proof.
  intros. induction H.
  - now rewrite H.
  - rewrite H0. rewrite sb_guard. apply IHt0_det.
Qed.

(* is_simple *)
Definition is_simple {E C X} `{B0 -< C} `{B1 -< C} (t : ctree E C X) :=
  (forall l t', trans l t t' -> is_val l) \/
  (forall l t', trans l t t' -> exists r, t0_det t' (Ret r)).

#[global] Instance is_simple_equ : forall {E C X} `{Stuck: B0 -< C} `{Tau: B1 -< C},
  Proper (equ eq ==> iff) (@is_simple E C X _ _).
Proof.
  cbn. intros. unfold is_simple. setoid_rewrite H. reflexivity.
Qed.

Lemma is_simple_ret : forall {E C X} `{B0 -< C} `{B1 -< C} r, is_simple (Ret r : ctree E C X).
Proof.
  cbn. red. intros. left. intros. inv_trans. subst. constructor.
Qed.

Lemma is_simple_guard_ret : forall {E C X} `{B0 -< C}`{B1 -< C}r,
    is_simple (Guard (Ret r) : ctree E C X).
Proof.
  cbn. red. intros. left. intros. inv_trans. subst. constructor.
Qed.

Lemma is_simple_br : forall {E C X} `{Stuck: B0 -< C} `{Tau: B1 -< C} (n: C X),
    is_simple (mbr false n : ctree E C X).
Proof.
  cbn. unfold mbr, MonadBr_ctree, CTree.branch. red. intros.
  left. intros. apply trans_brD_inv in H as []. inv_trans. subst. constructor.
Qed.

Lemma is_simple_brD : forall {E C X} `{Stuck: B0 -< C} `{Tau: B1 -< C} (n: C X) (k : X -> ctree E C X) x,
  is_simple (BrD n k) -> is_simple (k x).
Proof.
  intros. destruct H.
  - left. intros. eapply H. etrans.
  - right. intros. eapply H. etrans.
Qed.

Definition vsimple {E C X} (t : ctree E C X) :=
  (exists x, t ≅ Ret x) \/ exists f, t ≅ CTree.trigger f.

(** trans0 *)
(* LEF: That's not good, perhaps this is why this part of the code was
   not using [C] effects? *)
Inductive trans0_ {E C X} : ctree' E C X -> ctree' E C  X -> Prop :=
| T0Id : forall t t', t ≅ t' -> trans0_ (observe t) (observe t')
| T0Br : forall X (c: C X) k x t, trans0_ (observe (k x)) t -> trans0_ (BrDF c k) t.

Definition trans0 {E C X} (t t' : ctree E C X) := trans0_ (observe t) (observe t').

#[global] Instance trans0_equ_ {E C X} :
  Proper (going (equ eq) ==> going (equ eq) ==> impl) (@trans0_ E C X).
Proof.
  cbn. intros.
  revert y y0 H H0. induction H1; intros.
  - pose (T0Id (go y) (go y0)). cbn in t0. apply t0.
    rewrite <- H0, <- H1, H. reflexivity.
  - destruct H. step in H. inv H. invert.
    apply IHtrans0_.
    + constructor.
      rewrite <- !ctree_eta. cbn in H2. Fail apply REL. admit.
    + apply H0.
Admitted.

#[global] Instance trans0_equ_' {E C X} :
  Proper (going (equ eq) ==> going (equ eq) ==> flip impl) (@trans0_ E C X).
Proof.
  cbn. intros. now rewrite <- H, <- H0 in H1.
Qed.

#[global] Instance trans0_equ {E C X} : Proper (equ eq ==> equ eq ==> iff) (@trans0 E C X).
Proof.
  unfold trans0. split; intros.
  - now rewrite <- H, <- H0.
  - now rewrite H, H0.
Qed.

Lemma trans0_trans {E C X} `{Stuck: B0 -< C} : forall (t t' : ctree E C X),
  trans0 t t' -> forall l t'', trans l t' t'' -> trans l t t''.
Proof.
  intros. red in H. rewrite ctree_eta. rewrite ctree_eta in H0.
  genobs t ot. genobs t' ot'. clear t Heqot t' Heqot'.
  induction H.
  - rewrite H. apply H0.
  - apply IHtrans0_ in H0. eapply trans_brD in H0. apply H0. rewrite <- ctree_eta. reflexivity.
Qed.

Lemma trans0_fwd : forall {E C X} (t : ctree E C X) k x (c : C X),
  trans0 t (BrD c k) -> trans0 t (k x).
Proof.
  intros. red in H. red.
  genobs t ot. clear t Heqot.
  remember (observe (BrD c k)) as oc.
  revert c k x Heqoc. induction H.
  - intros. rewrite H, Heqoc. cbn. eapply T0Br. econstructor. reflexivity.
  - intros. subst. eapply T0Br. eapply IHtrans0_. reflexivity.
Qed.

Lemma trans0_interpE : forall {E C F X} `{Tau: B1 -< C} `{Stuck: B0 -< C}
                        (h : E ~> ctree F C) (t t' : ctree E C X),
  trans0 t t' -> trans0 (interpE h t) (interpE h t').
Proof.
  intros. red in H. setoid_rewrite (ctree_eta t). setoid_rewrite (ctree_eta t').
  genobs t ot. genobs t' ot'. clear t Heqot t' Heqot'.
  induction H.
  - constructor. rewrite H. reflexivity.
  - rewrite unfold_interpE. cbn. setoid_rewrite bind_br.
    apply T0Br with (x := x). rewrite bind_ret_l.
    simpl. eapply T0Br with (x:=tt). apply IHtrans0_.
Qed.

(* productive *)
Inductive productive {E C X} : ctree E C X -> Prop :=
| prod_ret {r t} (EQ: t ≅ Ret r) : productive t
| prod_vis {Y} {e : E Y} {k t} (EQ: t ≅ Vis e k) : productive t
| prod_tau {X} {c: C X} {k t} (EQ: t ≅ BrS c k) : productive t.

#[global] Instance productive_equ : forall {E C X}, Proper (equ eq ==> impl) (@productive E C X).
Proof.
  cbn. intros. inv H0; rewrite H in *.
  - eapply prod_ret; eauto.
  - eapply prod_vis; eauto.
  - eapply prod_tau; eauto.
Qed.

#[global] Instance productive_equ' : forall {E C X}, Proper (equ eq ==> flip impl) (@productive E C X).
Proof.
  cbn. intros. rewrite <- H in H0. apply H0.
Qed.

Lemma trans_productive {E C X} `{Stuck: B0 -< C} l (t t'' : ctree E C X) : trans l t t'' -> exists t',
  trans0 t t' /\ productive t' /\ trans l t' t''.
Proof.
  intros. do 3 red in H.
  setoid_rewrite (ctree_eta t). setoid_rewrite (ctree_eta t'').
  genobs t ot. genobs t'' ot''. clear t Heqot t'' Heqot''.
  induction H; intros.
  - destruct IHtrans_ as (? & ? & ? & ?).
    rewrite <- ctree_eta in H0. eapply T0Br in H0.
    exists x0. etrans.
  - eexists. split; [| split ].
    + left. reflexivity.
    + eapply prod_tau. reflexivity.
    + rewrite <- H, <- ctree_eta. etrans.
  - eexists. split; [| split ].
    + left. reflexivity.
    + eapply prod_vis. reflexivity.
    + rewrite <- H, <- ctree_eta. etrans.
  - eexists. split; [| split ].
    + left. reflexivity.
    + eapply prod_ret. reflexivity.
    + rewrite br0_always_stuck. etrans.
Qed.

Lemma interpE_productive {E C F X}  `{Stuck: B0 -< C} `{Tau: B1 -< C} (h : E ~> ctree F C) : forall (t : ctree E C X),
  productive (interpE h t) -> productive t.
Proof.
  intros. inversion H;
    subst;
    rewrite unfold_interpE in EQ;
    rewrite (ctree_eta t);
    destruct (observe t) eqn:?;
    (try destruct vis);
    (try step in EQ; inv EQ);
    try now econstructor.
Qed.

Lemma productive_trans0 {E C X} : forall (t t' : ctree E C X),
  productive t -> trans0 t t' -> t ≅ t'.
Proof.
  intros. setoid_rewrite ctree_eta.
  inversion H; subst; rewrite (ctree_eta t) in EQ; inversion H0; subst.
  - now rewrite H3.
  - rewrite <- H1 in EQ. step in EQ. inv EQ.
  - now rewrite H3.
  - rewrite <- H1 in EQ. step in EQ. inv EQ.
  - now rewrite H3.
  - rewrite <- H1 in EQ. step in EQ. inv EQ.
Qed.

Lemma trans_val_trans0 {E C X}  `{Stuck: B0 -< C}  : forall x (t t' : ctree E C X),
  trans (val x) t t' -> trans0 t (Ret x) /\ t' ≅ stuckD.
Proof.
  intros. apply trans_productive in H as (? & ? & ? & ?).
  inv H0.
  - rewrite EQ in H, H1. inv_trans. subst. auto.
  - rewrite EQ in H1. inv_trans.
  - rewrite EQ in H1. inv_trans.
Qed.

Lemma trans_tau_trans0 {E C X}  `{Stuck: B0 -< C} : forall (t t' : ctree E C X),
  trans tau t t' -> exists X (c: C X) k x, trans0 t (BrS c k) /\ t' ≅ k x.
Proof.
  intros. apply trans_productive in H as (? & ? & ? & ?).
  inv H0.
  - rewrite EQ in H1. inv_trans.
  - rewrite EQ in H1. inv_trans.
  - rewrite EQ in H1. inv_trans.
    do 2 eexists.
    exists k. exists x0.
    eauto.
Qed.

Lemma trans_obs_trans0 {E C X Y} `{Stuck: B0 -< C} : forall (t t' : ctree E C X) e (x : Y),
  trans (obs e x) t t' -> exists k, trans0 t (Vis e k) /\ t' ≅ k x.
Proof.
  intros. apply trans_productive in H as (? & ? & ? & ?).
  inv H0.
  - rewrite EQ in H1. inv_trans.
  - rewrite EQ in H1. inv_trans.
    apply obs_eq_invT in EQl as ?. subst.
    apply obs_eq_inv in EQl as [<- <-]. etrans.
  - rewrite EQ in H1. inv_trans.
Qed.

(* transi *)

Inductive transi {E C F X} `{Stuck: B0 -< C} `{Tau: B1 -< C} (h : E ~> ctree F C) :
  @label F -> ctree E C X -> ctree E C X -> Prop :=
| transi_val : forall (x : X) t t',
    trans (val x) t t' ->
    transi h (val x) t t'
| transi_tau : forall t t',
    trans tau t t' ->
    transi h tau t t'
| transi_obs : forall Y (e : E Y) x l t t' t'',
    trans (obs e x) t t' ->
    t0_det t'' (Ret x) ->
    trans l (h _ e) t'' ->
    transi h l t t'
| transi_obs0 : forall Y (e : E Y) l x t t' t'',
    trans (obs e x) t t' ->
    transi h l t' t'' ->
    trans (val x) (h _ e) stuckD ->
    transi h l t t''.

Lemma transi_brD {E C F X} `{Stuck: B0 -< C} `{Tau: B1 -< C} (h : E ~> ctree F C) :
  forall l (t' : ctree E C X) (c: C X) (k: X -> ctree E C X) (x: X),
  transi h l (k x) t' -> transi h l (BrD c k) t'.
Proof.
  intros. inv H.
  - apply transi_val. etrans.
  - apply transi_tau. etrans.
  - eapply transi_obs; etrans.
  - eapply transi_obs0; etrans.
Qed.

#[global] Instance transi_equ :
  forall {E C F X} `{Stuck: B0 -< C} `{Tau: B1 -< C} (h : E ~> ctree F C) l,
  Proper (equ eq ==> equ eq ==> flip impl) (@transi E C F X _ _ h l).
Proof.
  cbn. intros.
  revert x x0 H H0. induction H1; intros.
  - apply transi_val. rewrite H0, H1. apply H.
  - apply transi_tau. rewrite H0, H1. apply H.
  - rewrite <- H2, <- H3 in *. eapply transi_obs; eauto.
  - rewrite <- H2 in *. eapply transi_obs0; eauto.
Qed.

#[global] Instance transi_equ' :
  forall {E C F X}  `{Stuck: B0 -< C} `{Tau: B1 -< C} (h : E ~> ctree F C) l,
  Proper (equ eq ==> equ eq ==> impl) (@transi E C F X _ _ h l).
Proof.
  cbn. intros. rewrite <- H, <- H0. apply H1.
Qed.

Lemma trans0_transi {E C F X}  `{Stuck: B0 -< C} `{Tau: B1 -< C}  (h : E ~> ctree F C) :
  forall l (t t' t'' : ctree E C X), trans0 t t' -> transi h l t' t'' -> transi h l t t''.
Proof.
  intros.
  red in H. rewrite (ctree_eta t). rewrite (ctree_eta t') in H0.
  genobs t ot. genobs t' ot'. clear t Heqot. clear t' Heqot'.
  revert l t'' H0. induction H; intros.
  - rewrite H. apply H0.
  - (* LEF: Type error by introducing C *)
    Fail (eapply transi_brD; setoid_rewrite <- ctree_eta in IHtrans0_;
          eapply transi_brD; apply IHtrans0_; apply H0).
    admit.
Admitted.

Lemma transi_sbisim {E C F X}  `{Stuck: B0 -< C} `{Tau: B1 -< C} (h : E ~> ctree F C) :
  forall l (t t' u : ctree E C X), transi h l t t' ->
  t ~ u ->
  exists u', transi h l u u' /\ t' ~ u'.
Proof.
  intros. revert u H0.
  induction H; intros.
  - step in H0. destruct H0 as [? _]. apply H0 in H; destruct H as (? & ? & ? & ? & ?); subst.
    eexists. split. apply transi_val. apply H. apply H1.
  - step in H0. destruct H0 as [? _]. apply H0 in H. destruct H as (? & ? & ? & ? & ?); subst.
    eexists. split. apply transi_tau. apply H. apply H1.
  - step in H2. destruct H2 as [? _]. apply H2 in H. destruct H as (? & ? & ? & ? & ?); subst.
    eexists. split. eapply transi_obs; eauto. apply H3.
  - step in H2. destruct H2 as [? _]. apply H2 in H. destruct H as (? & ? & ? & ? & ?); subst.
    apply IHtransi in H3 as (? & ? & ?).
    eexists. split. eapply transi_obs0; eauto. apply H4.
Qed.

Lemma transi_trans {E C F X}  `{Stuck: B0 -< C} `{Tau: B1 -< C} (h : E ~> ctree F C)
      (Hh : forall X e, vsimple (h X e)) :
  forall l (t t' : ctree E C X),
  transi h l t t' -> exists t0, trans l (interpE h t) t0 /\ t0_det t0 (interpE h t').
Proof.
  intros. induction H.
  - exists stuckD. apply trans_val_inv in H as ?.
    apply trans_val_trans0 in H as [].
    eapply trans0_interpE in H. rewrite interpE_ret in H. setoid_rewrite H0.
    setoid_rewrite interpE_br. setoid_rewrite bind_br. setoid_rewrite br0_always_stuck.
    eapply trans0_trans in H; etrans. split; etrans. now left.
  - exists (Guard (interpE h t')). split; [| eright; eauto; now left ].
    apply trans_tau_trans0 in H as (? & ? & ? & ? & ? & ?).
    eapply trans0_interpE in H.
    eapply trans0_trans; etrans.
    setoid_rewrite interpE_br. setoid_rewrite bind_br. setoid_rewrite bind_ret_l.
    econstructor.
    (* LEF: Why does this timeout *)
    (* now setoid_rewrite <- H0. *)
    admit.
  - exists (x <- t'';; Guard (interpE h t')).
    split. 2: { eapply t0_det_bind_ret_l; eauto. eright; eauto. now left. }
    apply trans_obs_trans0 in H as (? & ? & ?).
    eapply trans0_interpE in H. eapply trans0_trans; etrans.
    setoid_rewrite interpE_vis.
    eapply trans_bind_l with (k := fun x => Guard (interpE h (x0 x))) in H1.
    setoid_rewrite t0_det_bind_ret_l_equ in H1 at 2; eauto.
    (* LEF: Why does this timeout *)
    (* now setoid_rewrite H2. *)
    admit.
    { intro. inv H3. apply trans_val_inv in H1. rewrite H1 in H0. inv H0. step in H3. inv H3. step in H4. inv H3. }
  - destruct IHtransi as (? & ? & ?).
    destruct (Hh Y e). 2: { destruct H4. rewrite H4 in H1. apply trans_vis_inv in H1 as (? & ? & ?). step in H1. inv H1. }
    destruct H4. rewrite H4 in H1. inv_trans. subst.
    exists x0. split. 2: auto.
    apply trans_obs_trans0 in H as (? & ? & ?). eapply trans0_interpE in H.
    setoid_rewrite interpE_vis in H. setoid_rewrite H4 in H. setoid_rewrite bind_ret_l in H.
    eapply trans0_trans; etrans. setoid_rewrite <- H1. etrans.
Qed.

(** Various lemmas for the proof that interpE preserves sbisim in some cases. *)
Lemma interpE_ret_inv {E F X} (h : E ~> ctree F) : forall (t : ctree E X) r,
  interpE h t ≅ Ret r -> t ≅ Ret r.
Proof.
  intros. setoid_rewrite (ctree_eta t) in H. setoid_rewrite (ctree_eta t).
  destruct (observe t) eqn:?.
  - rewrite interpE_ret in H. step in H. inv H. reflexivity.
  - rewrite interpE_vis in H. apply ret_equ_bind in H as (? & ? & ?). step in H0. inv H0.
  - rewrite interpE_br in H. setoid_rewrite bind_br in H. step in H. inv H.
Qed.

Lemma bind_tau_r {E X Y} : forall (t : ctree E X) (k : X -> ctree E Y),
  x <- t;; Guard (k x) ≅ x <- (x <- t;; Guard (Ret x));; k x.
Proof.
  intros. rewrite bind_bind. upto_bind_eq. rewrite bind_Guard. setoid_rewrite bind_ret_l. reflexivity.
Qed.

Lemma trans_interpE_inv_gen {E F X Y} (h : E ~> ctree F) (Hh : forall X e, vsimple (h X e)) :
  forall l (k : Y -> ctree E X) t' (pre : ctree F Y),
  is_simple pre ->
  trans l (x <- pre;; interpE h (k x)) t' ->
  exists t0, t0_det t' (interpE h t0) /\
    ((exists l t1 x, trans l pre t1 /\ t0_det t1 (Ret x) /\ t0 ≅ k x) \/
    exists x, trans (val x) pre CTree.stuckD /\ trans l (interpE h (k x)) t' /\ transi h l (k x) t0).
Proof.
  intros * Hpre H.
  do 3 red in H. remember (observe (x <- pre;; interpE h (k x))) as oi.
  setoid_rewrite (ctree_eta t') at 1.
  setoid_rewrite (ctree_eta t') at 2.
  genobs t' ot'. clear t' Heqot'.
  assert (go oi ≅ x <- pre;; interpE h (k x)).
  { rewrite Heqoi, <- ctree_eta. reflexivity. } clear Heqoi.
  revert Y k pre Hpre H0. induction H; intros.
  - (*apply Stepbr in H as ?.
    change (BrDF n k) with (observe (BrD n k)) in H1. rewrite H0 in H1.
       change t with (observe (go t)) in H1. rewrite trans__trans in H1.*)
    destruct n. now apply Fin.case0.
    symmetry in H0. apply br_equ_bind in H0 as ?.
    destruct H1 as [[] | (? & ? & ?)].
    + rewrite H1 in H0. rewrite bind_ret_l in H0. setoid_rewrite H1. clear pre Hpre H1.
      rewrite (ctree_eta (k0 x0)) in H0. destruct (observe (k0 x0)) eqn:?.
      * rewrite interpE_ret in H0. step in H0. inv H0.
      * rewrite interpE_vis in H0. apply br_equ_bind in H0 as ?. destruct H1 as [[] | (? & ? & ?)].
        --rewrite H1, bind_ret_l in H0.
          apply equ_br_invT in H0 as ?. destruct H2 as [? _]. apply eq_add_S in H2 as <-.
          simple apply equ_br_invE with (x := x) in H0.
          rewrite <- H0 in H.
          specialize (IHtrans_ _ (fun (_ : unit) => k1 x1) (Ret tt)).
          edestruct IHtrans_. { apply is_simple_ret. } { rewrite <- ctree_eta, bind_ret_l, H0. reflexivity. }
          destruct H2. exists x2. split; auto. right. destruct H3.
          { destruct H3 as (? & ? & ? & ? & ? & ?). inv_trans. subst.
            inv H4. step in H3. inv H3. step in H6. inv H6. }
          destruct H3 as (_ & _ & ? & ?). exists x0. split. etrans. split.
          ++setoid_rewrite (ctree_eta (k0 x0)). rewrite Heqc.
            setoid_rewrite interpE_vis. setoid_rewrite H1. setoid_rewrite bind_ret_l. apply trans_guard. apply H3.
          ++setoid_rewrite (ctree_eta (k0 x0)). rewrite Heqc.
            eapply transi_obs0; etrans. rewrite H1. etrans.
        --destruct (Hh X0 e).
          destruct H3. rewrite H3 in H1. step in H1. inv H1.
          destruct H3. rewrite H3 in H1. step in H1. inv H1.
      * rewrite interpE_br in H0. setoid_rewrite bind_br in H0. setoid_rewrite bind_ret_l in H0.
        apply equ_br_invT in H0 as ?. destruct H1 as [-> ->].
        simple apply equ_br_invE with (x := x) in H0 as ?.
        specialize (IHtrans_ _ (fun _ : unit => k1 x) (Guard (Ret tt))).
        edestruct IHtrans_ as (? & ? & ?).
        { apply is_simple_guard_ret. }
        { rewrite <- ctree_eta. setoid_rewrite bind_br. setoid_rewrite bind_ret_l. now rewrite H1. }
        destruct H3.
        { destruct H3 as (? & ? & ? & ? & ? & ?). inv_trans. subst.
          inv H4. step in H3. inv H3. step in H5. inv H5. }
        destruct H3 as (? & ? & ? & ?).
        exists x1. split; auto. right. exists x0. split; etrans. split.
        rewrite (ctree_eta (k0 x0)), Heqc, interpE_br. setoid_rewrite bind_br. setoid_rewrite bind_ret_l.
        eapply trans_brD. 2: reflexivity. apply trans_guard. apply H4.
        rewrite (ctree_eta (k0 x0)), Heqc. eapply transi_brD; etrans.
    + specialize (IHtrans_ _ k0 (x0 x)).
      edestruct IHtrans_ as (? & ? & ?).
      { apply is_simple_brD. red. setoid_rewrite <- H1. apply Hpre. }
      rewrite <- ctree_eta. apply H2. destruct H4 as [(? & ? & ? & ? & ? & ?) | (? & ? & ? & ?)].
      * (*setoid_rewrite H5 in H3. clear x1 H5.*)
        exists (k0 x4). split. { now rewrite H6 in H3. }
        left. eapply trans_brD in H4. 2: reflexivity. rewrite <- H1 in H4. eauto 6.
      * exists x1. split; auto. right. exists x2. rewrite H1. etrans.
  - destruct n. now apply Fin.case0.
    symmetry in H0. apply br_equ_bind in H0 as ?. destruct H1 as [[] | (? & ? & ?)].
    + rewrite H1 in H0. rewrite bind_ret_l in H0.
      rewrite (ctree_eta (k0 x0)) in H0. destruct (observe (k0 x0)) eqn:?.
      * rewrite interpE_ret in H0. step in H0. inv H0.
      * rewrite interpE_vis in H0. apply br_equ_bind in H0 as ?.
        destruct H2 as [[] | (? & ? & ?)].
        { rewrite H2, bind_ret_l in H0. step in H0. inv H0. }
        pose proof (trans_brS x1 x). rewrite <- H2 in H4.
        edestruct Hh. { destruct H5. rewrite H5 in H4. inv_trans. }
        destruct H5. rewrite H5 in H4. apply trans_vis_inv in H4 as (? & ? & ?). discriminate.
        (*--specialize (H3 x).
          (*rewrite H4 in H3. rewrite bind_ret_l in H3.*)
          exists (k1 x2).
          rewrite H in H3. split; auto. rewrite H3, <- ctree_eta.
          eapply t0_det_bind_ret_l; eauto. eapply t0_det_tau; eauto. constructor; auto.
          right. exists x0. rewrite H1. split; etrans.
          setoid_rewrite (ctree_eta (k0 x0)). setoid_rewrite Heqc. split.
          { setoid_rewrite interpE_vis. setoid_rewrite H2. setoid_rewrite bind_br.
            econstructor. rewrite <- ctree_eta, H3. reflexivity. }
          eapply transi_vis; eauto. rewrite H2. etrans.*)
      * rewrite interpE_br in H0. setoid_rewrite bind_br in H0.
        apply equ_br_invT in H0 as ?. destruct H2 as [-> ->].
        simple eapply equ_br_invE in H0 as ?. rewrite bind_ret_l in H2. rewrite H in H2.
        exists (k1 x). symmetry in H2. split.
        { rewrite <- ctree_eta. rewrite H2. eapply t0_det_tau; auto. apply t0_det_id; auto. }
        right. exists x0. rewrite H1. split; etrans.
        setoid_rewrite (ctree_eta (k0 x0)). setoid_rewrite Heqc. split.
        { setoid_rewrite interpE_br. rewrite H2. setoid_rewrite bind_br. setoid_rewrite bind_ret_l.
          econstructor. now rewrite <- ctree_eta. }
        econstructor; etrans.
    + pose proof (trans_brS x0 x).
      rewrite <- H1 in H3. edestruct Hpre.
      { apply H4 in H3. inv H3. }
      apply H4 in H3 as [].
      specialize (H2 x).
      (*rewrite H3, bind_ret_l in H2.*)
      exists (k0 x1). rewrite H in H2. split. { rewrite <- ctree_eta, H2. eapply t0_det_bind_ret_l; eauto. now left. }
      left. exists tau, (x0 x), x1. split; auto. rewrite H1. etrans.
  - symmetry in H0. apply vis_equ_bind in H0 as ?. destruct H1 as [[] | (? & ? & ?)].
    + rewrite H1 in H0. rewrite bind_ret_l in H0.
     rewrite (ctree_eta (k0 x0)) in H0. destruct (observe (k0 x0)) eqn:?.
      * rewrite interpE_ret in H0. step in H0. inv H0.
      * rewrite interpE_vis in H0. apply vis_equ_bind in H0 as ?.
        destruct H2 as [[] | (? & ? & ?)].
        { rewrite H2, bind_ret_l in H0. step in H0. inv H0. }
        pose proof (trans_vis e x x1). rewrite <- H2 in H4.
        edestruct Hh. { destruct H5. rewrite H5 in H4. inv H4. }
        destruct H5. rewrite H5 in H4. (*destruct H4 as [? ?].*)
        specialize (H3 x). rewrite H5 in H2.
        apply equ_vis_invT in H2 as ?. subst.
        apply equ_vis_invE in H2 as ?. destruct H6 as [-> ?].
        rewrite <- H6 in *. rewrite bind_ret_l in H3.
        exists (k1 x).
        rewrite H in H3. split. { rewrite <- ctree_eta, H3. eright; eauto. eleft; auto. }
        right.
        exists x0. rewrite H1. split; etrans.
        setoid_rewrite (ctree_eta (k0 x0)). setoid_rewrite Heqc. split.
        { setoid_rewrite interpE_vis. rewrite H5. setoid_rewrite bind_vis.
          econstructor. rewrite bind_ret_l. rewrite <- H3, <- ctree_eta. reflexivity. }
        eapply transi_obs; etrans. 2: { rewrite H5. etrans. } now left.
      * rewrite interpE_br in H0. setoid_rewrite bind_br in H0.
        step in H0. inv H0.
    + pose proof (trans_vis e x x0).
      rewrite <- H1 in H3. edestruct Hpre.
      { apply H4 in H3. inv H3. }
      apply H4 in H3 as [].
      specialize (H2 x).
      exists (k0 x1). rewrite H in H2. split.
      { rewrite <- ctree_eta, H2. eapply t0_det_bind_ret_l; eauto. now left. }
      left. exists (obs e x), (x0 x), x1. split; auto. rewrite H1. etrans.
     - exists (CTree.stuckD). split.
       + left.
         setoid_rewrite interpE_br. setoid_rewrite bind_br. rewrite !br0_always_stuck. reflexivity.
       + right. symmetry in H0. apply ret_equ_bind in H0 as (? & ? & ?).
         exists x. rewrite H. split; etrans. split.
         rewrite H0. rewrite br0_always_stuck. etrans.
         apply interpE_ret_inv in H0. rewrite H0. constructor; etrans.
Qed.

Lemma trans_interpE_inv {E F X} (h : E ~> ctree F) (Hh : forall X e, vsimple (h X e)) :
  forall l (t : ctree E X) t',
  trans l (interpE h t) t' ->
  exists l t0, t0_det t' (interpE h t0) /\ transi h l t t0.
Proof.
  intros.
   assert (trans l (Guard (Ret tt);; interpE h t) t').
   { etrans. }
  eapply trans_interpE_inv_gen in H0; eauto. destruct H0 as (? & ? & ?).
  destruct H1 as [(? & ? & ? & ? & ? & ?) | (? & ? & ? & ?)].
  - inv_trans. subst. inv H2. step in H1. inv H1. step in H3. inv H3.
  - inv_trans. subst. eauto.
  - left. intros. inv_trans. subst. constructor.
Qed.

(** The main theorem stating that interpE preserves sbisim. *)
Theorem interpE_sbisim_gen {E F X Y} (h : E ~> ctree F) (Hh : forall X e, vsimple (h X e)) :
  forall (k k' : X -> ctree E Y) (pre pre' : ctree F X),
  (forall x, sbisim (k x) (k' x)) ->
  pre ≅ pre' ->
  vsimple pre ->
  sbisim (a <- pre;; Guard (interpE h (k a))) (a <- pre';; Guard (interpE h (k' a))).
Proof.
  revert X. coinduction R CH.
  symmetric using idtac.
  { intros. apply H; eauto.  intros. rewrite H0. reflexivity. now rewrite H1. red; now setoid_rewrite <- H1. }
  assert (CH' : forall (t t' : ctree E Y), t ~ t' -> st R (interpE h t) (interpE h t')).
  {
    intros.
    assert (st R (a <- Ret tt;; Guard (interpE h ((fun _ => t) a)))
      (a <- Ret tt;; Guard (interpE h ((fun _ => t') a)))).
    { apply CH; eauto. left; eauto. }
    rewrite !bind_ret_l in H0.
    rewrite !sb_guard in H0.
    apply H0.
  }
  intros. setoid_rewrite <- H0. clear pre' H0. cbn. intros.
  copy H0. rewrite bind_tau_r in H0.
  eapply trans_interpE_inv_gen in H0 as (? & ? & ?); auto.
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
      (* todo lemma *)
      rewrite H2 in H3. inv H3. step in H4. inv H4.
      apply equ_br_invE in H5. 2: apply Fin.F1.
      rewrite <- H5 in H4. inv H4. 2: { step in H6. inv H6. }
      step in H3. inv H3. clear x1 H2 t H5.
      rewrite bind_trigger in cpy. apply trans_vis_inv in cpy. destruct cpy as (? & ? & ?). subst.
      exists (Guard (interpE h (k' x0))). rewrite H1. rewrite bind_trigger. now constructor.
      rewrite H2, !sb_guard. apply CH'. apply H.
  - destruct H2 as (? & ? & ? & ?).
    destruct H1 as [[] | []]. 2: { rewrite H1 in H2. setoid_rewrite bind_trigger in H2. inv_trans. }
    rewrite H1 in *. rewrite bind_ret_l in H2. inv_trans. subst. clear EQ.
    eapply transi_sbisim in H4; eauto. destruct H4 as (? & ? & ?).
    apply transi_trans in H2 as (? & ? & ?); auto.
    exists x2. rewrite H1, bind_ret_l. etrans.
    assert (st R (interpE h x) (interpE h x0)).
    { apply CH'. apply H4. }
    rewrite sbisim_t0_det. 2: apply H0.
    setoid_rewrite sbisim_t0_det at 3. 2: apply H5.
    apply H6.
Qed.

#[global] Instance interpE_sbisim {E F R} (h : E ~> ctree F) (Hh : forall X e, vsimple (h X e)) :
  Proper (sbisim ==> sbisim) (interpE h (T := R)).
Proof.
  cbn. intros.
  assert (a <- Ret tt;; Guard (interpE h ((fun _ => x) a)) ~
    a <- Ret tt;; Guard (interpE h ((fun _ => y) a))).
  apply interpE_sbisim_gen; auto.
  red; eauto.
  rewrite !bind_ret_l, !sb_guard in H0. apply H0.
Qed.
