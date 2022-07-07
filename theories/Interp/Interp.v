(* begin hide *)

From CTree Require Import
     CTree Eq.

From ExtLib Require Import
     Structures.Functor
     Structures.Monad.

Open Scope ctree_scope.
Import CTreeNotations.

(* end hide *)

Definition translateF {E F R} (h : E ~> F) (rec: ctree E R -> ctree F R) (t : ctreeF E R _) : ctree F R  :=
	match t with
		| RetF x => Ret x
		| VisF e k => Vis (h _ e) (fun x => rec (k x))
		| BrF b n k => Br b n (fun x => rec (k x))
	end.

Definition translate {E F} (h : E ~> F) : ctree E ~> ctree F
	:= fun R => cofix translate_ t := translateF h translate_ (observe t).

Arguments translate {E F} h [T].

(*|
Interpret
---------
|*)

(*|
An event handler [E ~> M] defines a monad morphism
[ctree E ~> M] for any monad [M] with a loop operator.
|*)

Definition interp {E M : Type -> Type}
					 {FM : Functor M} {MM : Monad M} {IM : MonadIter M} {FoM : MonadBr M}
					 (h : E ~> M) :
			ctree E ~> M := fun R =>
			iter (fun t =>
				match observe t with
				| RetF r => ret (inr r)
				| @BrF _ _ _ b n k => bind (mbr b n) (fun x => ret (inl (k x)))
				| VisF e k => fmap (fun x => inl (k x)) (h _ e)
				end).

Arguments interp {E M FM MM IM FoM} h [T].

(*|
Unfolding of [interp].
|*)
Notation interp_ h t :=
  (match observe t with
  | RetF r => Ret r
	| VisF e k => bind (h _ e) (fun x => Guard (interp h (k x)))
	| @BrF _ _ _ b n k => bind (mbr b n) (fun x => Guard (interp h (k x)))
  end)%function.

(*|
Unfold lemma.
|*)
Lemma unfold_interp {E F R} {h : E ~> ctree F} (t : ctree E R) :
  interp h t ≅ interp_ h t.
Proof.
  unfold interp, Basics.iter, MonadIter_ctree.
  rewrite unfold_iter.
  destruct (observe t); cbn.
  - now rewrite ?bind_ret_l.
  - now rewrite bind_map, ?bind_ret_l.
  - rewrite bind_bind.
    setoid_rewrite bind_ret_l.
    reflexivity.
Qed.

(*|
[interp] and constructors
-------------------------
|*)

Lemma interp_ret {E F R} {f : E ~> ctree F} (x: R):
  interp f (Ret x) ≅ Ret x.
Proof. now rewrite unfold_interp. Qed.

Lemma interp_tau {E F R} {f : E ~> ctree F} (t: ctree E R):
  interp f (Guard t) ≅ Guard (Guard (interp f t)).
Proof.
  rewrite unfold_interp.
  cbn.
  unfold mbr, MonadBr_ctree, CTree.br. cbn.
  rewrite unfold_bind.
  cbn.
  setoid_rewrite bind_ret_l.
  reflexivity.
Qed.

Lemma interp_vis {E F R S} {f : E ~> ctree F} (e: E R) (k: R -> ctree E S) :
  interp f (Vis e k) ≅ x <- f _ e;; Guard (interp f (k x)).
Proof. now rewrite unfold_interp. Qed.

Lemma interp_br {E F R} {f : E ~> ctree F} b n (k: _ -> ctree E R) :
  interp f (Br b n k) ≅ x <- mbr b n;; Guard (interp f (k x)).
Proof. now rewrite unfold_interp. Qed.

#[global] Instance interp_equ {E F R} (h : E ~> ctree F) :
  Proper (equ eq ==> equ eq) (interp h (T := R)).
Proof.
  cbn.
  coinduction ? CIH.
  intros * EQ; step in EQ.
  rewrite 2 unfold_interp.
  inv EQ; auto.
  - cbn -[ebt].
    upto_bind_eq.
    constructor; intros ?; auto.
  - cbn -[ebt].
    upto_bind_eq.
    constructor; intros ?; auto.
Qed.

(* Note: this is specialized to [ctree F] as target monad. *)
Lemma interp_bind {E F R S} (h : E ~> ctree F) (t : ctree E R) (k : R -> ctree _ S) :
  interp h (t >>= k) ≅ interp h t >>= (fun x => interp h (k x)).
Proof.
  revert t.
  coinduction R' CIH.
  intros t.
  rewrite unfold_bind, (unfold_interp t).
  desobs t; cbn -[ebt].
  - now rewrite bind_ret_l.
  - rewrite interp_vis, bind_bind.
    upto_bind_eq.
    rewrite bind_br.
    now constructor; intros.
  - rewrite interp_br, bind_bind.
    upto_bind_eq.
    rewrite bind_br.
    now constructor; intros.
Qed.

(*|
Counter-example showing that interp does not preserve sbisim in the general case.
|*)

Inductive VoidE : Type -> Type :=
| voidE : VoidE void.

#[local] Definition t1 := Ret 1 : ctree VoidE nat.
#[local] Definition t2 := brD2 (Ret 1) (x <- trigger voidE;; match x : void with end) : ctree VoidE nat.

Goal t1 ~ t2.
Proof.
  unfold t1, t2.
  rewrite brD2_commut.
  rewrite brD2_is_stuck. reflexivity.
  red. intros. intro. inv_trans.  destruct x.
Qed.

#[local] Definition h : VoidE ~> ctree VoidE.
Proof.
  intros. destruct H. exact (Step CTree.stuckD).
Defined.

Example interp_sbsisim_counterexample : ~ (interp h t1 ~ interp h t2).
Proof.
  red. intros. unfold t2 in H.
  playR in H.
  rewrite unfold_interp. cbn. setoid_rewrite bind_br.
  eapply trans_brD with (x := Fin.FS Fin.F1).
  2: { rewrite bind_ret_l. reflexivity. }
  apply trans_guard. setoid_rewrite unfold_interp. cbn. rewrite bind_br. etrans.
  rewrite unfold_interp in H. unfold t1, h in H. cbn in H. inv_trans.
Qed.

(*|
Helper inductive t0_det t t' means that t' is Guard*(t)
|*)

Inductive t0_det {E X} : relation (ctree E X) :=
| t0_det_id : forall t t', t ≅ t' -> t0_det t t'
| t0_det_tau : forall t t' t'',
    t0_det t t' -> t'' ≅ Guard t -> t0_det t'' t'.

#[global] Instance t0_det_equ : forall {E X}, Proper (equ eq ==> equ eq ==> flip impl) (@t0_det E X).
Proof.
  cbn. intros.
  revert x H. induction H1; intros.
  - econstructor. now rewrite H0, H1.
  - eapply t0_det_tau. apply IHt0_det. apply H0. reflexivity. rewrite H2. apply H.
Qed.

#[global] Instance t0_det_equ' : forall {E X}, Proper (equ eq ==> equ eq ==> impl) (@t0_det E X).
Proof.
  cbn. intros. rewrite <- H, <- H0. apply H1.
Qed.

Lemma t0_det_bind {E X Y} : forall (t t' : ctree E X) (k : X -> ctree E Y),
  t0_det t t' ->
  t0_det (t >>= k) (t' >>= k).
Proof.
  intros. induction H.
  - rewrite H. constructor. reflexivity.
  - rewrite H0. setoid_rewrite bind_Guard. eapply t0_det_tau. apply IHt0_det. reflexivity.
Qed.

Lemma t0_det_bind_ret_l {E X Y} : forall (t : ctree E X) t' (k : X -> ctree E Y) x,
  t0_det t (Ret x) ->
  t0_det (k x) t' ->
  t0_det (t >>= k) t'.
Proof.
  intros. remember (Ret x) as R. revert t' k x HeqR H0. induction H; intros; subst.
  - subst. rewrite H, bind_ret_l. apply H0.
  - rewrite H0. setoid_rewrite bind_Guard.
    eapply t0_det_tau. 2: reflexivity. eapply IHt0_det. reflexivity. apply H1.
Qed.

Lemma t0_det_bind_ret_l_equ {E X Y} : forall (t : ctree E X) (k : X -> ctree E Y) x,
  t0_det t (Ret x) ->
  x <- t;; k x ≅ t;; k x.
Proof.
  intros. remember (Ret x) as R. induction H; subst.
  - rewrite H. rewrite !bind_ret_l. reflexivity.
  - rewrite H0. rewrite !bind_Guard. apply br_equ. intro. apply IHt0_det. reflexivity.
Qed.

Lemma sbisim_t0_det {E X} : forall (t t' : ctree E X), t0_det t t' -> t ~ t'.
Proof.
  intros. induction H.
  - now rewrite H.
  - rewrite H0. rewrite sb_guard. apply IHt0_det.
Qed.

(*|
is_simple
|*)

Definition is_simple {E X} (t : ctree E X) :=
  (forall l t', trans l t t' -> is_val l) \/
  (forall l t', trans l t t' -> exists r, t0_det t' (Ret r)).

#[global] Instance is_simple_equ : forall {E X},
  Proper (equ eq ==> iff) (@is_simple E X).
Proof.
  cbn. intros. unfold is_simple. setoid_rewrite H. reflexivity.
Qed.

Lemma is_simple_ret : forall {E X} r, is_simple (Ret r : ctree E X).
Proof.
  cbn. red. intros. left. intros. inv_trans. subst. constructor.
Qed.

Lemma is_simple_guard_ret : forall {E X} r, is_simple (Guard (Ret r) : ctree E X).
Proof.
  cbn. red. intros. left. intros. inv_trans. subst. constructor.
Qed.

Lemma is_simple_br : forall {E} n, is_simple (mbr false n : ctree E _).
Proof.
  cbn. red. intros.
  left. intros. apply trans_brD_inv in H as []. inv_trans. subst. constructor.
Qed.

Lemma is_simple_brD : forall {E X} n (k : fin n -> ctree E X) x,
  is_simple (BrD n k) -> is_simple (k x).
Proof.
  intros. destruct H.
  - left. intros. eapply H. etrans.
  - right. intros. eapply H. etrans.
Qed.

Definition vsimple {E X} (t : ctree E X) :=
  (exists x, t ≅ Ret x) \/ exists f, t ≅ CTree.trigger f.

(** trans0 *)

Inductive trans0_ {E X} : ctree' E X -> ctree' E X -> Prop :=
| T0Id : forall t t', t ≅ t' -> trans0_ (observe t) (observe t')
| T0Br : forall c k x t, trans0_ (observe (k x)) t -> trans0_ (BrDF c k) t
.

Definition trans0 {E X} (t t' : ctree E X) := trans0_ (observe t) (observe t').

#[global] Instance trans0_equ_ {E X} :
  Proper (going (equ eq) ==> going (equ eq) ==> impl) (@trans0_ E X).
Proof.
  cbn. intros.
  revert y y0 H H0. induction H1; intros.
  - pose (T0Id (go y) (go y0)). cbn in t0. apply t0.
    rewrite <- H0, <- H1, H. reflexivity.
  - destruct H. step in H. inv H. invert.
    econstructor. apply IHtrans0_. constructor.
    rewrite <- !ctree_eta. apply REL. apply H0.
Qed.

#[global] Instance trans0_equ_' {E X} :
  Proper (going (equ eq) ==> going (equ eq) ==> flip impl) (@trans0_ E X).
Proof.
  cbn. intros. now rewrite <- H, <- H0 in H1.
Qed.

#[global] Instance trans0_equ {E X} : Proper (equ eq ==> equ eq ==> iff) (@trans0 E X).
Proof.
  unfold trans0. split; intros.
  - now rewrite <- H, <- H0.
  - now rewrite H, H0.
Qed.

Lemma trans0_trans {E X} : forall (t t' : ctree E X),
  trans0 t t' -> forall l t'', trans l t' t'' -> trans l t t''.
Proof.
  intros. red in H. rewrite ctree_eta. rewrite ctree_eta in H0.
  genobs t ot. genobs t' ot'. clear t Heqot t' Heqot'.
  induction H.
  - rewrite H. apply H0.
  - apply IHtrans0_ in H0. eapply trans_brD in H0. apply H0. rewrite <- ctree_eta. reflexivity.
Qed.

Lemma trans0_fwd : forall {E X} (t : ctree E X) n k (x : fin n),
  trans0 t (BrD n k) -> trans0 t (k x).
Proof.
  intros. red in H. red.
  genobs t ot. clear t Heqot.
  remember (observe (BrD n k)) as oc.
  revert n k x Heqoc. induction H.
  - intros. rewrite H, Heqoc. eapply T0Br. constructor. reflexivity.
  - intros. subst. eapply T0Br. apply IHtrans0_. reflexivity.
Qed.

Lemma trans0_interp : forall {E F X} (h : E ~> ctree F) (t t' : ctree E X),
  trans0 t t' -> trans0 (interp h t) (interp h t').
Proof.
  intros. red in H. setoid_rewrite (ctree_eta t). setoid_rewrite (ctree_eta t').
  genobs t ot. genobs t' ot'. clear t Heqot t' Heqot'.
  induction H.
  - constructor. rewrite H. reflexivity.
  - rewrite unfold_interp. cbn. setoid_rewrite bind_br.
    apply T0Br with (x := x). rewrite bind_ret_l.
    apply T0Br with (x := Fin.F1). apply IHtrans0_.
Qed.

(*|
productive
|*)

Inductive productive {E X} : ctree E X -> Prop :=
| prod_ret {r t} (EQ: t ≅ Ret r) : productive t
| prod_vis {Y} {e : E Y} {k t} (EQ: t ≅ Vis e k) : productive t
| prod_tau {n k t} (EQ: t ≅ BrS n k) : productive t.

#[global] Instance productive_equ : forall {E X}, Proper (equ eq ==> impl) (@productive E X).
Proof.
  cbn. intros. inv H0; rewrite H in *.
  - eapply prod_ret; eauto.
  - eapply prod_vis; eauto.
  - eapply prod_tau; eauto.
Qed.

#[global] Instance productive_equ' : forall {E X}, Proper (equ eq ==> flip impl) (@productive E X).
Proof.
  cbn. intros. rewrite <- H in H0. apply H0.
Qed.

Lemma trans_productive {E X} l (t t'' : ctree E X) : trans l t t'' -> exists t',
  trans0 t t' /\ productive t' /\ trans l t' t''.
Proof.
  intros. do 3 red in H.
  setoid_rewrite (ctree_eta t). setoid_rewrite (ctree_eta t'').
  genobs t ot. genobs t'' ot''. clear t Heqot t'' Heqot''.
  induction H; intros.
  - destruct IHtrans_ as (? & ? & ? & ?).
    rewrite <- ctree_eta in H0. eapply T0Br in H0.
    exists x0. auto.
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

Lemma interp_productive {E F X} (h : E ~> ctree F) : forall (t : ctree E X),
  productive (interp h t) -> productive t.
Proof.
  intros. inversion H;
    subst;
    rewrite unfold_interp in EQ;
    rewrite (ctree_eta t);
    destruct (observe t) eqn:?;
    (try destruct vis);
    (try step in EQ; inv EQ);
    try now econstructor.
Qed.

Lemma productive_trans0 {E X} : forall (t t' : ctree E X),
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

Lemma trans_val_trans0 {E X} : forall x (t t' : ctree E X),
  trans (val x) t t' -> trans0 t (Ret x) /\ t' ≅ CTree.stuckD.
Proof.
  intros. apply trans_productive in H as (? & ? & ? & ?).
  inv H0.
  - rewrite EQ in H, H1. inv_trans. subst. auto.
  - rewrite EQ in H1. inv_trans.
  - rewrite EQ in H1. inv_trans.
Qed.

Lemma trans_tau_trans0 {E X} : forall (t t' : ctree E X),
  trans tau t t' -> exists n k x, trans0 t (BrS n k) /\ t' ≅ k x.
Proof.
  intros. apply trans_productive in H as (? & ? & ? & ?).
  inv H0.
  - rewrite EQ in H1. inv_trans.
  - rewrite EQ in H1. inv_trans.
  - rewrite EQ in H1. inv_trans. etrans.
Qed.

Lemma trans_obs_trans0 {E X Y} : forall (t t' : ctree E X) e (x : Y),
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

Inductive transi {E F X} (h : E ~> ctree F) : @label F -> ctree E X -> ctree E X -> Prop :=
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
    trans (val x) (h _ e) CTree.stuckD ->
    transi h l t t''
.

Lemma transi_brD {E F X} (h : E ~> ctree F) : forall l (t' : ctree E X) n k x,
  transi h l (k x) t' -> transi h l (BrD n k) t'.
Proof.
  intros. inv H.
  - apply transi_val. etrans.
  - apply transi_tau. etrans.
  - eapply transi_obs; etrans.
  - eapply transi_obs0; etrans.
Qed.

#[global] Instance transi_equ :
  forall {E F X} (h : E ~> ctree F) l,
  Proper (equ eq ==> equ eq ==> flip impl) (@transi E F X h l).
Proof.
  cbn. intros.
  revert x x0 H H0. induction H1; intros.
  - apply transi_val. rewrite H0, H1. apply H.
  - apply transi_tau. rewrite H0, H1. apply H.
  - rewrite <- H2, <- H3 in *. eapply transi_obs; eauto.
  - rewrite <- H2 in *. eapply transi_obs0; eauto.
Qed.

#[global] Instance transi_equ' :
  forall {E F X} (h : E ~> ctree F) l,
  Proper (equ eq ==> equ eq ==> impl) (@transi E F X h l).
Proof.
  cbn. intros. rewrite <- H, <- H0. apply H1.
Qed.

Lemma trans0_transi {E F X} (h : E ~> ctree F) :
  forall l (t t' t'' : ctree E X), trans0 t t' -> transi h l t' t'' -> transi h l t t''.
Proof.
  intros.
  red in H. rewrite (ctree_eta t). rewrite (ctree_eta t') in H0.
  genobs t ot. genobs t' ot'. clear t Heqot. clear t' Heqot'.
  revert l t'' H0. induction H; intros.
  - rewrite H. apply H0.
  - eapply transi_brD. setoid_rewrite <- ctree_eta in IHtrans0_. apply IHtrans0_. apply H0.
Qed.

Lemma transi_sbisim {E F X} (h : E ~> ctree F) :
  forall l (t t' u : ctree E X), transi h l t t' ->
  t ~ u ->
  exists u', transi h l u u' /\ t' ~ u'.
Proof.
  intros. revert u H0.
  induction H; intros.
  - step in H0. destruct H0 as [? _]. apply H0 in H. destruct H.
    exists x0. split. now apply transi_val. apply H1.
  - step in H0. destruct H0 as [? _]. apply H0 in H. destruct H.
    exists x. split. now apply transi_tau. apply H1.
  - step in H2. destruct H2 as [? _]. apply H2 in H. destruct H.
    exists x0. split. eapply transi_obs; eauto. apply H3.
  - step in H2. destruct H2 as [? _]. apply H2 in H. destruct H.
    apply IHtransi in H3 as (? & ? & ?). exists x1.
    split. eapply transi_obs0; eauto. apply H4.
Qed.

Lemma transi_trans {E F X} (h : E ~> ctree F) (Hh : forall X e, vsimple (h X e)) :
  forall l (t t' : ctree E X),
  transi h l t t' -> exists t0, trans l (interp h t) t0 /\ t0_det t0 (interp h t').
Proof.
  intros. induction H.
  - exists CTree.stuckD. apply trans_val_inv in H as ?.
    apply trans_val_trans0 in H as [].
    eapply trans0_interp in H. rewrite interp_ret in H. setoid_rewrite H0.
    setoid_rewrite interp_br. setoid_rewrite bind_br. setoid_rewrite br0_always_stuck.
    eapply trans0_trans in H; etrans. split; etrans. now left.
  - exists (Guard (interp h t')). split; [| eright; eauto; now left ].
    apply trans_tau_trans0 in H as (? & ? & ? & ? & ?).
    eapply trans0_interp in H. setoid_rewrite H0. eapply trans0_trans; etrans.
    setoid_rewrite interp_br. setoid_rewrite bind_br. setoid_rewrite bind_ret_l.
    econstructor. reflexivity.
  - exists (x <- t'';; Guard (interp h t')).
    split. 2: { eapply t0_det_bind_ret_l; eauto. eright; eauto. now left. }
    apply trans_obs_trans0 in H as (? & ? & ?).
    eapply trans0_interp in H. setoid_rewrite H2. eapply trans0_trans; etrans.
    setoid_rewrite interp_vis.
    eapply trans_bind_l with (k := fun x => Guard (interp h (x0 x))) in H1.
    setoid_rewrite t0_det_bind_ret_l_equ in H1 at 2; eauto.
    { intro. inv H3. apply trans_val_inv in H1. rewrite H1 in H0. inv H0. step in H3. inv H3. step in H4. inv H4. }
  - destruct IHtransi as (? & ? & ?).
    destruct (Hh Y e). 2: { destruct H4. rewrite H4 in H1. apply trans_vis_inv in H1 as (? & ? & ?). step in H1. inv H1. }
    destruct H4. rewrite H4 in H1. inv_trans. subst.
    exists x0. split. 2: auto.
    apply trans_obs_trans0 in H as (? & ? & ?). eapply trans0_interp in H.
    setoid_rewrite interp_vis in H. setoid_rewrite H4 in H. setoid_rewrite bind_ret_l in H.
    eapply trans0_trans; etrans. setoid_rewrite <- H1. etrans.
Qed.

(** Various lemmas for the proof that interp preserves sbisim in some cases. *)

Lemma interp_ret_inv {E F X} (h : E ~> ctree F) : forall (t : ctree E X) r,
  interp h t ≅ Ret r -> t ≅ Ret r.
Proof.
  intros. setoid_rewrite (ctree_eta t) in H. setoid_rewrite (ctree_eta t).
  destruct (observe t) eqn:?.
  - rewrite interp_ret in H. step in H. inv H. reflexivity.
  - rewrite interp_vis in H. apply ret_equ_bind in H as (? & ? & ?). step in H0. inv H0.
  - rewrite interp_br in H. setoid_rewrite bind_br in H. step in H. inv H.
Qed.

Lemma bind_tau_r {E X Y} : forall (t : ctree E X) (k : X -> ctree E Y),
  x <- t;; Guard (k x) ≅ x <- (x <- t;; Guard (Ret x));; k x.
Proof.
  intros. rewrite bind_bind. upto_bind_eq. rewrite bind_Guard. setoid_rewrite bind_ret_l. reflexivity.
Qed.

Lemma trans_interp_inv_gen {E F X Y} (h : E ~> ctree F) (Hh : forall X e, vsimple (h X e)) :
  forall l (k : Y -> ctree E X) t' (pre : ctree F Y),
  is_simple pre ->
  trans l (x <- pre;; interp h (k x)) t' ->
  exists t0, t0_det t' (interp h t0) /\
    ((exists l t1 x, trans l pre t1 /\ t0_det t1 (Ret x) /\ t0 ≅ k x) \/
    exists x, trans (val x) pre CTree.stuckD /\ trans l (interp h (k x)) t' /\ transi h l (k x) t0).
Proof.
  intros * Hpre H.
  do 3 red in H. remember (observe (x <- pre;; interp h (k x))) as oi.
  setoid_rewrite (ctree_eta t') at 1.
  setoid_rewrite (ctree_eta t') at 2.
  genobs t' ot'. clear t' Heqot'.
  assert (go oi ≅ x <- pre;; interp h (k x)).
  { rewrite Heqoi, <- ctree_eta. reflexivity. } clear Heqoi.
  revert Y k pre Hpre H0. induction H; intros.
  - destruct n. now apply Fin.case0.
    symmetry in H0. apply br_equ_bind in H0 as ?.
    destruct H1 as [[] | (? & ? & ?)].
    + rewrite H1 in H0. rewrite bind_ret_l in H0. setoid_rewrite H1. clear pre Hpre H1.
      rewrite (ctree_eta (k0 x0)) in H0. destruct (observe (k0 x0)) eqn:?.
      * rewrite interp_ret in H0. step in H0. inv H0.
      * rewrite interp_vis in H0. apply br_equ_bind in H0 as ?. destruct H1 as [[] | (? & ? & ?)].
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
            setoid_rewrite interp_vis. setoid_rewrite H1. setoid_rewrite bind_ret_l. apply trans_guard. apply H3.
          ++setoid_rewrite (ctree_eta (k0 x0)). rewrite Heqc.
            eapply transi_obs0; etrans. rewrite H1. etrans.
        --destruct (Hh X0 e).
          destruct H3. rewrite H3 in H1. step in H1. inv H1.
          destruct H3. rewrite H3 in H1. step in H1. inv H1.
      * rewrite interp_br in H0. setoid_rewrite bind_br in H0. setoid_rewrite bind_ret_l in H0.
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
        rewrite (ctree_eta (k0 x0)), Heqc, interp_br. setoid_rewrite bind_br. setoid_rewrite bind_ret_l.
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
      * rewrite interp_ret in H0. step in H0. inv H0.
      * rewrite interp_vis in H0. apply br_equ_bind in H0 as ?.
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
          { setoid_rewrite interp_vis. setoid_rewrite H2. setoid_rewrite bind_br.
            econstructor. rewrite <- ctree_eta, H3. reflexivity. }
          eapply transi_vis; eauto. rewrite H2. etrans.*)
      * rewrite interp_br in H0. setoid_rewrite bind_br in H0.
        apply equ_br_invT in H0 as ?. destruct H2 as [-> ->].
        simple eapply equ_br_invE in H0 as ?. rewrite bind_ret_l in H2. rewrite H in H2.
        exists (k1 x). symmetry in H2. split.
        { rewrite <- ctree_eta. rewrite H2. eapply t0_det_tau; auto. apply t0_det_id; auto. }
        right. exists x0. rewrite H1. split; etrans.
        setoid_rewrite (ctree_eta (k0 x0)). setoid_rewrite Heqc. split.
        { setoid_rewrite interp_br. rewrite H2. setoid_rewrite bind_br. setoid_rewrite bind_ret_l.
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
      * rewrite interp_ret in H0. step in H0. inv H0.
      * rewrite interp_vis in H0. apply vis_equ_bind in H0 as ?.
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
        { setoid_rewrite interp_vis. rewrite H5. setoid_rewrite bind_vis.
          econstructor. rewrite bind_ret_l. rewrite <- H3, <- ctree_eta. reflexivity. }
        eapply transi_obs; etrans. 2: { rewrite H5. etrans. } now left.
      * rewrite interp_br in H0. setoid_rewrite bind_br in H0.
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
         setoid_rewrite interp_br. setoid_rewrite bind_br. rewrite !br0_always_stuck. reflexivity.
       + right. symmetry in H0. apply ret_equ_bind in H0 as (? & ? & ?).
         exists x. rewrite H. split; etrans. split.
         rewrite H0. rewrite br0_always_stuck. etrans.
         apply interp_ret_inv in H0. rewrite H0. constructor; etrans.
Qed.

Lemma trans_interp_inv {E F X} (h : E ~> ctree F) (Hh : forall X e, vsimple (h X e)) :
  forall l (t : ctree E X) t',
  trans l (interp h t) t' ->
  exists l t0, t0_det t' (interp h t0) /\ transi h l t t0.
Proof.
  intros.
   assert (trans l (Guard (Ret tt);; interp h t) t').
   { etrans. }
  eapply trans_interp_inv_gen in H0; eauto. destruct H0 as (? & ? & ?).
  destruct H1 as [(? & ? & ? & ? & ? & ?) | (? & ? & ? & ?)].
  - inv_trans. subst. inv H2. step in H1. inv H1. step in H3. inv H3.
  - inv_trans. subst. eauto.
  - left. intros. inv_trans. subst. constructor.
Qed.

(** The main theorem stating that interp preserves sbisim. *)

Theorem interp_sbisim_gen {E F X Y} (h : E ~> ctree F) (Hh : forall X e, vsimple (h X e)) :
  forall (k k' : X -> ctree E Y) (pre pre' : ctree F X),
  (forall x, sbisim (k x) (k' x)) ->
  pre ≅ pre' ->
  vsimple pre ->
  sbisim (a <- pre;; Guard (interp h (k a))) (a <- pre';; Guard (interp h (k' a))).
Proof.
  revert X. coinduction R CH.
  symmetric using idtac.
  { intros. apply H; eauto.  intros. rewrite H0. reflexivity. now rewrite H1. red; now setoid_rewrite <- H1. }
  assert (CH' : forall (t t' : ctree E Y), t ~ t' -> st R (interp h t) (interp h t')).
  {
    intros.
    assert (st R (a <- Ret tt;; Guard (interp h ((fun _ => t) a)))
      (a <- Ret tt;; Guard (interp h ((fun _ => t') a)))).
    { apply CH; eauto. left; eauto. }
    rewrite !bind_ret_l in H0.
    rewrite !sb_guard in H0.
    apply H0.
  }
  intros. setoid_rewrite <- H0. clear pre' H0. cbn. intros.
  copy H0. rewrite bind_tau_r in H0.
  eapply trans_interp_inv_gen in H0 as (? & ? & ?); auto.
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
      step in H3. inv H3. clear x1 H2 t H5.
      rewrite bind_trigger in cpy. apply trans_vis_inv in cpy. destruct cpy as (? & ? & ?). subst.
      exists (Guard (interp h (k' x0))). rewrite H1. rewrite bind_trigger. now constructor.
      rewrite H2, !sb_guard. apply CH'. apply H.
  - destruct H2 as (? & ? & ? & ?).
    destruct H1 as [[] | []]. 2: { rewrite H1 in H2. setoid_rewrite bind_trigger in H2. inv_trans. }
    rewrite H1 in *. rewrite bind_ret_l in H2. inv_trans. subst. clear EQ.
    eapply transi_sbisim in H4; eauto. destruct H4 as (? & ? & ?).
    apply transi_trans in H2 as (? & ? & ?); auto.
    exists x2. rewrite H1, bind_ret_l. etrans.
    assert (st R (interp h x) (interp h x0)).
    { apply CH'. apply H4. }
    rewrite sbisim_t0_det. 2: apply H0.
    setoid_rewrite sbisim_t0_det at 3. 2: apply H5.
    apply H6.
Qed.

#[global] Instance interp_sbisim {E F R} (h : E ~> ctree F) (Hh : forall X e, vsimple (h X e)) :
  Proper (sbisim ==> sbisim) (interp h (T := R)).
Proof.
  cbn. intros.
  assert (a <- Ret tt;; Guard (interp h ((fun _ => x) a)) ~
    a <- Ret tt;; Guard (interp h ((fun _ => y) a))).
  apply interp_sbisim_gen; auto.
  red; eauto.
  rewrite !bind_ret_l, !sb_guard in H0. apply H0.
Qed.
