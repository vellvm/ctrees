(*| Predicates on ctrees |*)
From Coq Require Import
  Basics
  Morphisms
  Classes.RelationClasses
  Program.Equality.

From CTree Require Import
  Utils.Utils
  CTree.Core
  CTree.Trans
  CTree.Interp.Core
  Events.Core
  CTree.SBisim
  CTree.Equ.

From Coinduction Require Import coinduction.

Import Ctree.
Import CTreeNotations.
(* end hide *)

(** The [Leaf a t] predicate expresses that [t] has (at least one) [Ret] leaf with
    value [a].
 *)
Generalizable All Variables.

(* [Leaf t x] <-> Exists a [Ret x] in [t] *)
Inductive ELeafF `{Encode E} {A: Type} (a: A) : ctree' E A -> Prop :=
 | ELeafRet:
   ELeafF a (RetF a)
 | ELeafBr b n (i: fin' n) k:
   ELeafF a (observe (k i)) ->
   ELeafF a (BrF b n k)
 | ELeafVis e k (x: encode e):
   ELeafF a (observe (k x)) ->
   ELeafF a (VisF e k).
#[global] Hint Constructors ELeafF : ctree.

Notation "a ∈ t" := (ELeafF a (observe t)) (at level 70): ctree_scope.

(* [Leaf t x] <-> Exists a [Ret x] in [t] *)
Inductive ALeafF `{Encode E} {A: Type} (a: A) : ctree' E A -> Prop :=
| ALeafRet:
  ALeafF a (RetF a)
| ALeafBr b n k:
  (forall i, ALeafF a (observe (k i))) ->
  ALeafF a (BrF b n k)
| ALeafVis e k:
  (forall (x: encode e), ALeafF a (observe (k x))) ->
  ALeafF a (VisF e k).
#[global] Hint Constructors ALeafF : ctree.

Notation "t ⇓ a" := (ALeafF a (observe t)) (at level 70): ctree_scope.

Local Open Scope ctree_scope.

(*| ELeaf forward reasoning |*)
Lemma ELeaf_Ret : forall `{Encode E} R (a: R),
  a ∈ Ret a.
Proof.
  intros; econstructor; reflexivity.
Qed.
Global Hint Resolve ELeaf_Ret: ctree.

Lemma ELeaf_Br : forall `{Encode E} R b n i
                  (k: fin' n -> ctree E R) a,
  a ∈ k i ->
  a ∈ Br b n k.
Proof.
  intros; eapply ELeafBr; eassumption.
Qed.
Global Hint Resolve ELeaf_Br: ctree.

Lemma ELeaf_Vis : forall {X Y: Type} `{Encode E} (e : E) (k : _ -> ctree E Y) b x,
  b ∈ (k x) ->
  b ∈ (Vis e k).
Proof.
  intros; eapply ELeafVis; cbn; eassumption.
Qed.
Global Hint Resolve ELeaf_Vis: ctree.

(*| ELeaf backward reasoning |*)
Lemma ELeaf_Ret_inv : forall `{Encode E} R (a b : R),
  b ∈ (Ret a: ctree E R) ->
  b = a.
Proof.
  intros * IN; inv IN; cbn in *; try congruence.
Qed.
Global Hint Resolve ELeaf_Ret_inv: ctree.

Lemma ELeaf_Br_inv : forall `{Encode E} R n (k: fin' n -> ctree E R) x b,
  x ∈ Br b n k ->
  exists (i: fin' n), x ∈ k i.
Proof.
  intros * IN; dependent destruction IN; cbn in *; now (exists i).
Qed.
Global Hint Resolve ELeaf_Br_inv: ctree.

Lemma ELeaf_Vis_inv : forall `{Encode E} Y (e : E) (k : encode e -> ctree E Y) b,
  b ∈ Vis e k ->
  exists x, b ∈ k x.
Proof.
  intros * IN *; dependent destruction IN; cbn in *; try congruence.
  now (exists x).
Qed.
Global Hint Resolve ELeaf_Vis_inv: ctree.

(*| ALeaf forward reasoning |*)
Lemma ALeaf_Ret : forall `{Encode E} R (a: R),
  Ret a ⇓ a.
Proof.
  intros; econstructor; reflexivity.
Qed.
Global Hint Resolve ALeaf_Ret: ctree.

Lemma ALeaf_Br : forall `{Encode E} R b n
                  (k: fin' n -> ctree E R) a,
  (forall i, k i ⇓ a) ->
  Br b n k ⇓ a.
Proof.
  intros; eapply ALeafBr; eassumption.
Qed.
Global Hint Resolve ALeaf_Br: ctree.

Lemma ALeaf_Vis : forall {X Y: Type} `{Encode E} (e : E) (k : _ -> ctree E Y) b,
  (forall x, k x ⇓ b) ->
  Vis e k ⇓ b.
Proof.
  intros; eapply ALeafVis; cbn; eassumption.
Qed.
Global Hint Resolve ALeaf_Vis: ctree.

(*| ALeaf backward reasoning |*)
Lemma ALeaf_Ret_inv : forall `{Encode E} R (a b : R),
  (Ret a: ctree E R) ⇓ b->
  b = a.
Proof.
  intros * IN; inv IN; cbn in *; try congruence.
Qed.
Global Hint Resolve ALeaf_Ret_inv: ctree.

Lemma ALeaf_Br_inv : forall `{Encode E} R n (k: fin' n -> ctree E R) x b i,
    Br b n k ⇓ x ->
    k i ⇓ x.
Proof.
  intros * IN; dependent destruction IN; cbn in *; auto.
Qed.
Global Hint Resolve ALeaf_Br_inv: ctree.

Lemma ALeaf_Vis_inv : forall `{Encode E} Y (e : E) (k : encode e -> ctree E Y) a x,
    Vis e k ⇓ a ->
    k x ⇓ a.
Proof.
  intros * IN *; dependent destruction IN; cbn in *; auto.
Qed.
Global Hint Resolve ALeaf_Vis_inv: ctree.

(*| Helper inductive: [epsilon_det t t'] judges that [t' ≡ Guard* t] |*)
Inductive epsilon_det `{Encode E} {X}: relation (ctree E X) :=
| epsilon_det_id : forall t t', t ≅ t' -> epsilon_det t t'
| epsilon_det_tau : forall t t' t'',
    epsilon_det t t' -> t'' ≅ guard t -> epsilon_det t'' t'.

(*| Helper inductive: [epsilon t t'] judges that [t'] is reachable from [t] by all paths made of [BrD] branches. |*)
Inductive epsilon_ `{Encode E} {X} : ctree' E X -> ctree' E X -> Prop :=
| EpsilonId : forall t t', t ≅ t' -> epsilon_ (observe t) (observe t')
| EpsilonBr : forall n k x t, epsilon_ (observe (k x)) t -> epsilon_ (BrF false n k) t.

Definition epsilon `{Encode E} {X} (t t' : ctree E X) :=
  epsilon_ (observe t) (observe t').

(*| Helper inductive: [productive t] judges that [t]'s head constructor is not a [BrD] |*)
Inductive productive `{Encode E} {X} : ctree E X -> Prop :=
| prod_ret {r t} (EQ: t ≅ Ret r) : productive t
| prod_vis {e : E} {k t} (EQ: t ≅ Vis e k) : productive t
| prod_tau {n} {k t} (EQ: t ≅ BrS n k) : productive t.

Section epsilon_det_theory.
  #[global] Instance epsilon_det_equ `{Encode E} {X}:
  Proper (equ eq ==> equ eq (X2:=X) ==> flip impl) (@epsilon_det E _ X).
  Proof.
    repeat red; intros.
    revert x H0. induction H2; intros.
    - econstructor. now rewrite H1, H2.
    - eapply epsilon_det_tau.
      apply IHepsilon_det; auto.
      now rewrite H3. 
  Qed.

  #[global] Instance epsilon_det_equ' `{Encode E} {X}:
    Proper (equ eq ==> equ eq ==> impl) (@epsilon_det E _ X).
  Proof.
    repeat red; intros.
    now rewrite <- H1, <- H0. 
  Qed.

  #[global] Instance epsilon_det_refl `{Encode E} {X}:
    Reflexive (@epsilon_det E _ X).
  Proof. now left. Qed.

  Local Typeclasses Transparent equ.
  Lemma epsilon_det_bind `{Encode E} {X Y}: forall (t t' : ctree E X) (k : X -> ctree E Y),
      epsilon_det t t' ->
      epsilon_det (t >>= k) (t' >>= k).
  Proof.
    intros. induction H0.
    - rewrite H0. constructor. reflexivity.
    - rewrite H1. setoid_rewrite bind_guard. eapply epsilon_det_tau.
      apply IHepsilon_det. reflexivity.
  Qed.

  Lemma epsilon_det_bind_ret_l `{Encode E} {X Y}: forall (t : ctree E X) t' (k : X -> ctree E Y) x,
      epsilon_det t (Ret x) ->
      epsilon_det (k x) t' ->
      epsilon_det (t >>= k) t'.
  Proof.
    intros.
    remember (Ret x) as R. revert t' k x HeqR H1.
    induction H0; intros; subst.
    - subst. now rewrite H0, bind_ret_l. 
    - rewrite H1. setoid_rewrite bind_guard.
      eapply epsilon_det_tau.
      2: reflexivity.
      now eapply IHepsilon_det. 
  Qed.

  Lemma epsilon_det_bind_ret_l_equ `{Encode E} {X Y}:
    forall (t : ctree E X) (k : X -> ctree E Y) x,
      epsilon_det t (Ret x) ->
      x <- t;; k x ≅ t;; k x.
  Proof.
    intros. remember (Ret x) as R. induction H0; subst.
    - rewrite H0. rewrite !bind_ret_l. reflexivity.
    - rewrite H1. rewrite !bind_guard. apply br_equ. intro.
      apply IHepsilon_det.
      reflexivity.
  Qed.

  Lemma epsilon_det_trans `{Encode E} {X}:
    forall l (t t' t'' : ctree E X),
      epsilon_det t t' -> trans l t' t'' -> trans l t t''.
  Proof.
    intros; induction H0.
    - now rewrite H0.
    - apply IHepsilon_det in H1.
      apply trans_guard in H1.
      now rewrite <- H2 in H1.
  Qed.

  Lemma sbisim_epsilon_det `{Encode E} {X}:
    forall (t t' : ctree E X), epsilon_det t t' -> t ~ t'.
  Proof.
    intros. induction H0.
    - rewrite H0; reflexivity.
    - rewrite H1. rewrite sb_guard. apply IHepsilon_det.
  Qed.

End epsilon_det_theory.

Section productive_theory.
  
  #[global] Instance productive_equ `{HE: Encode E}{X}:
    Proper (equ eq ==> impl) (@productive E _ X).
  Proof.
    repeat red.
    intros. inv H0; rewrite H in *.
    - eapply prod_ret; eauto.
    - eapply prod_vis; eauto.
    - eapply prod_tau; eauto.
  Qed.

  #[global] Instance productive_equ' `{HE: Encode E}{X}:
    Proper (equ eq ==> flip impl) (@productive E _ X).
  Proof.
    repeat red.
    intros. rewrite <- H in H0. apply H0.
  Qed.

  #[local] Hint Constructors productive : trans.

  Lemma ctree_case_productive `{Encode E} {X} : forall (t: ctree E X),
      productive t \/ exists n k, t ≅ BrD n k.
  Proof.
    intros. setoid_rewrite (ctree_eta t). desobs t; etrans.
    destruct b.
    - left; now eapply prod_tau.
    - right. eauto.
  Qed.

  Lemma productive_br `{HE: Encode E} {X} : forall vis n (k : fin' n -> ctree E X),
      productive (Br vis n k) -> vis = true.
  Proof.
    intros. inv H; step in EQ; cbn in EQ; dependent destruction EQ.
    reflexivity.
  Qed.

  Lemma productive_brD `{HE: Encode E} {X}: forall n (k : fin' n -> ctree E X),
      ~ productive (BrD n k).
  Proof.
    intros ** ?. inversion H; inv_equ.
  Qed.

  Lemma productive_bind `{HE: Encode E} {X n}: forall t (k : fin' n -> ctree E X),
      productive (t >>= k) -> productive t.
  Proof.
    intros. inversion H; inv_equ; subst.
    - apply ret_equ_bind in EQ as (? & ? & ?).
      rewrite H0; now eapply prod_ret.
    - apply vis_equ_bind in EQ as [(? & ?) | (? & ? & ?)]; rewrite H0.
      + now eapply prod_ret.
      + now eapply prod_vis.
    - apply br_equ_bind in EQ as [(? & ?) | (? & ? & ?)]; rewrite H0.
      + now eapply prod_ret.
      + now eapply prod_tau.
  Qed.
  
End productive_theory.

Section epsilon_theory.
  #[global] Instance epsilon_equ_ `{HE: Encode E} {X} :
    Proper (going (equ eq) ==> going (equ eq) ==> impl) (@epsilon_ E _ X).
  Proof.
    repeat red.
    intros.
    revert y y0 H H0. induction H1; intros.
    - pose (EpsilonId (go y) (go y0)). cbn in e. apply e.
      rewrite <- H0, <- H1, H. reflexivity.
    - destruct H. step in H. inv H. invert.
      cbn in H3; subst.
      econstructor; auto.
      apply IHepsilon_.
      + constructor.
        now rewrite <- !ctree_eta. 
      + apply H0.
  Qed.

  #[global] Instance epsilon_equ_' `{HE: Encode E} {X} :
    Proper (going (equ eq) ==> going (equ eq) ==> flip impl) (@epsilon_ E _ X).
  Proof.
    repeat red; intros. now rewrite <- H, <- H0 in H1.
  Qed.

  #[global] Instance epsilon_equ `{HE: Encode E} {X}:
    Proper (equ eq ==> equ eq ==> iff) (@epsilon E _ X).
  Proof.
    unfold epsilon. split; intros.
    - now rewrite <- H, <- H0.
    - now rewrite H, H0.
  Qed.

  #[global] Instance epsilon_refl `{Encode E} {X} :
    Reflexive (@epsilon E _ X).
  Proof. now left. Qed.

  Lemma epsilon_br `{Encode E} {X} : forall (t' : ctree E X) n k (c : fin' n) x,
      epsilon (k x) t' -> epsilon (BrD n k) t'.
  Proof. intros. eright; eauto. Qed.

  Lemma epsilon_case `{HE: Encode E} {X} : forall (t t' : ctree E X),
      epsilon t t' ->
      t ≅ t' \/ exists n (c : fin' n) k x, t ≅ BrD n k /\ epsilon (k x) t'.
  Proof.
    intros * EPS.
    inversion EPS; [left | right].
    - setoid_rewrite ctree_eta. now rewrite <- H, H1, H0.
    - subst. exists n, x, k, x. split; auto. now rewrite H, <- ctree_eta.
  Qed.

  Lemma epsilon_trans `{HE: Encode E} {X} : forall (t t' : ctree E X),
      epsilon t t' -> forall l t'', trans l t' t'' -> trans l t t''.
  Proof.
    intros. red in H. rewrite ctree_eta. rewrite ctree_eta in H0.
    remember (observe t) as ot.
    remember (observe t') as ot'.
    clear t Heqot t' Heqot'.
    induction H.
    - rewrite H. apply H0.
    - apply IHepsilon_ in H0. eapply trans_brD in H0. apply H0.
      rewrite <- ctree_eta. reflexivity.
  Qed.

  Lemma epsilon_fwd `{HE: Encode E} {X} : forall (t : ctree E X) n k x (c : fin' n),
      epsilon t (BrD n k) -> epsilon t (k x).
  Proof.
    intros. red in H. red.
    remember (observe t) as ot.
    clear t Heqot.
    remember (observe (BrD n k)) as oc.
    revert c k x Heqoc.
    induction H; intros.
    - rewrite H, Heqoc. cbn. eapply EpsilonBr; auto.
      now left.
    - subst. eapply EpsilonBr; auto. 
  Qed.

  Lemma trans_epsilon `{HE: Encode E} {X} l (t t'' : ctree E X):
    trans l t t'' -> exists t',
        epsilon t t' /\ productive t' /\ trans l t' t''.
  Proof.
    unfold trans. 
    setoid_rewrite (ctree_eta t).
    setoid_rewrite (ctree_eta t'').
    remember (observe t) as ot.
    remember (observe t'') as ot''.
    clear t Heqot t'' Heqot''.
    cbn; induction 1; intros.
    - destruct IHtrans_ as (? & ? & ? & ?).
      exists x0; split; auto.
      eapply epsilon_br with x; auto. 
    - eexists. split; [| split ].
      + left. reflexivity.
      + eapply prod_tau. reflexivity.
      + rewrite <- H; cbn; now econstructor. 
    - eexists. split; [| split ].
      + left. reflexivity.
      + eapply prod_vis. reflexivity.
      + rewrite <- H; cbn; now econstructor. 
    - eexists. split; [| split ].
      + left. reflexivity.
      + eapply prod_ret. reflexivity.
      + now econstructor.
  Qed.

  Lemma trans_val_epsilon `{HE: Encode E} {X}: forall x (t t' : ctree E X),
      trans (val x) t t' -> epsilon t (Ret x) /\ t' ≅ stuck.
  Proof.
    intros. apply trans_epsilon in H as (? & ? & ? & ?).
    inv H0.
    - rewrite EQ in H, H1.
      trans in H1.
      now dependent destruction Eql. 
    - rewrite EQ in H1. inv H1.
    - rewrite EQ in H1. inv H1.
  Qed.

  Lemma trans_tau_epsilon `{HE: Encode E} {X}: forall (t t' : ctree E X),
      trans tau t t' -> exists n (c: fin' n) k x, epsilon t (BrS n k) /\ t' ≅ k x.
  Proof.
    intros. apply trans_epsilon in H as (? & ? & ? & ?).
    inv H0.
    - rewrite EQ in H1. inv H1. 
    - rewrite EQ in H1. inv H1. 
    - rewrite EQ in H, H1. trans in H1.
      exists n, n0, k, n0; split; auto.
  Qed.

  Lemma trans_obs_epsilon `{HE: Encode E} {X}:
    forall (t t' : ctree E X) e (x : encode e),
      trans (obs e x) t t' -> exists k, epsilon t (Vis e k) /\ t' ≅ k x.
  Proof.
    intros. apply trans_epsilon in H as (? & ? & ? & ?).
    inv H0; rewrite EQ in H1.
    - inv H1. 
    - rewrite EQ in H.
      trans in H1; dependent destruction Eql.
      exists k; eauto. 
    - inv H1.
  Qed.

  Lemma productive_epsilon `{HE: Encode E} {X} : forall (t t' : ctree E X),
      productive t -> epsilon t t' -> t ≅ t'.
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

  Lemma epsilon_transitive `{HE: Encode E} {X} : forall (t u v : ctree E X),
      epsilon t u -> epsilon u v -> epsilon t v.
  Proof.
    intros t u v.
    rewrite (ctree_eta t), (ctree_eta u).
    remember (observe t) as ot.
    remember (observe u) as ou.      
    clear t Heqot u Heqou.
    intro H; unfold epsilon in H; cbn in H; revert v.
    induction H; intros.
    - now rewrite H.
    - eright; auto.
      now apply IHepsilon_.
    Qed.

  Local Typeclasses Transparent equ.
  Lemma epsilon_bind_l `{HE: Encode E} {X Y} : forall t t' (k : Y -> ctree E X),
      epsilon t t' -> epsilon (t >>= k) (t' >>= k).
  Proof.
    intros. setoid_rewrite (ctree_eta t). setoid_rewrite (ctree_eta t').
    red in H.
    remember (observe t) as ot.
    remember (observe t') as ot'.      
    clear t Heqot t' Heqot'.
    induction H. 
    - rewrite H. reflexivity.
    - rewrite bind_br. eright; auto.
      rewrite (ctree_eta (k0 x)). apply IHepsilon_.
  Qed.

  Lemma epsilon_bind_ret `{HE: Encode E} {X Y} : forall t (k : Y -> ctree E X) v,
      epsilon t (Ret v) -> epsilon (t >>= k) (k v).
  Proof.
    intros. rewrite <- (bind_ret_l v k).
    now apply epsilon_bind_l.
  Qed.

  Lemma epsilon_bind `{HE: Encode E} {X Y} : forall t u (k : Y -> ctree E X) v,
      epsilon t (Ret v) -> epsilon (k v) u -> epsilon (t >>= k) u.
  Proof.
    intros. eapply epsilon_bind_ret in H.
    eapply epsilon_transitive; eassumption.
  Qed.

  Lemma epsilon_det_epsilon `{HE: Encode E} {X}: forall (t t' : ctree E X),
      epsilon_det t t' -> epsilon t t'.
  Proof.
    intros. induction H.
    - now left.
    - rewrite H0. right; auto; exact Fin.F1.
  Qed.

  Lemma ss_epsilon_l `{HE: Encode E} `{HF: Encode F} {X Y L R} (t : ctree E X) (u : ctree F Y) :
    (forall t0, epsilon t t0 -> productive t0 -> ss L R t0 u) ->
    ss L R t u.
  Proof.
    intros. cbn. intros. apply trans_epsilon in H0 as (? & ? & ? & ?).
    red in H0.
    setoid_rewrite (ctree_eta t) in H.
    rewrite (ctree_eta x) in H1, H2.
    remember (observe t) as ot.
    remember (observe x) as ox.
    clear t x Heqot Heqox.
    induction H0.
    - apply H in H1 as ?.
      2: { rewrite H0. now left. }
      apply H3 in H2. apply H2.
    - apply IHepsilon_; auto. intros. apply H; auto. eright; auto. apply H3.
  Qed.
  
  Lemma ss_epsilon_r `{HE: Encode E} `{HF: Encode F} {X Y L R}
        (t : ctree E X) (u u0 : ctree F Y) :
      epsilon u u0 ->
      ss L R t u0 ->
      ss L R t u.
  Proof.
    intros. cbn. intros. apply H0 in H1 as (? & ? & ? & ? & ?).
    eapply epsilon_trans in H1; eauto.
  Qed.
  
  Lemma ssim_epsilon_l `{HE: Encode E} `{HF: Encode F} {X Y L}
    (t : ctree E X) (u : ctree F Y) :
    (forall t0, epsilon t t0 -> productive t0 -> ssim L t0 u) ->
    ssim L t u.
  Proof.
    intros. step. apply ss_epsilon_l.
    intros. apply H in H1. now step in H1. assumption.
  Qed.
  
  Lemma ssim_epsilon_r `{HE: Encode E} `{HF: Encode F} {X Y L}
    (t : ctree E X) (u u0 : ctree F Y) :
    epsilon u u0 ->
    ssim L t u0 ->
    ssim L t u.
  Proof.
    intros. cbn. intros.
    step in H0. step. eapply ss_epsilon_r in H0; eauto.
  Qed.
  
  Lemma ssim_ret_epsilon `{HE: Encode E} `{HF: Encode F} {X Y L} :
    forall r (u : ctree F Y),
      respects_val L ->
      (Ret r : ctree E X) (≲L) u ->
      exists r', epsilon u (Ret r') /\ L (val r) (val r').
  Proof.
    intros * RV SIM *.
    step in SIM. specialize (SIM (val r) stuck (trans_ret _)).
    destruct SIM as (l' & u' & TR & _ & EQ).
    apply RV in EQ as ?. destruct H as [? _]. specialize (H (Is_val _)). inv H.
    apply trans_val_invT in TR as ?. subst.
    apply trans_val_epsilon in TR as []. eauto.
  Qed.

  Lemma ssim_vis_epsilon `{HE: Encode E} `{HF: Encode F} {X Y L}: 
    forall e (k : encode e -> ctree E X) (u : ctree F Y),
      respects_val L ->
      respects_tau L ->
      Vis e k (≲L) u ->
      forall x, exists (e' : F) k' y, epsilon u (Vis e' k') /\ k x (≲L) k' y /\ L (obs e x) (obs e' y).
  Proof.
    intros * RV RT SIM *.
    step in SIM. cbn in SIM. specialize (SIM (obs e x) (k x) (trans_vis _ _ _)).
    destruct SIM as (l' & u'' & TR & SIM & EQ).
    apply trans_epsilon in TR. destruct TR as (u' & EPS & PROD & TR).
    destruct PROD.
    1: {
      rewrite EQ0 in *. trans in TR. subst.
      apply RV in EQ. destruct EQ as [_ ?]. specialize (H (Is_val _)). inv H.
    }
    2: {
      rewrite EQ0 in *. trans in TR. subst.
      apply RT in EQ. destruct EQ as [_ ?]. specialize (H eq_refl). inv H.
    }
    rewrite EQ0 in *. trans in TR. subst.
    exists e0, k0, x0; split; [eauto|split]; auto.
    now rewrite Eqt in SIM.
  Qed.

  Lemma ssim_brS_epsilon `{HE: Encode E} `{HF: Encode F} {X Y L}:
    forall n (k : fin' n -> ctree E X) (u : ctree F Y),
      respects_tau L ->
      L tau tau ->
      BrS n k (≲L) u ->
      forall x, exists n' k' y, epsilon u (BrS n' k') /\ k x (≲L) k' y.
  Proof.
    intros * RT HL SIM *.
    step in SIM. cbn in SIM.
    pose proof ((@trans_brS _ _ _ _ k (k x) x (@reflexivity _ (equ eq) _ (k x)))) as HbrS.
    specialize (SIM tau (k x) HbrS). 
    destruct SIM as (l' & u'' & TR & SIM & EQ).
    apply trans_epsilon in TR. destruct TR as (u' & EPS & PROD & TR).
    destruct PROD.
    1: {
      rewrite EQ0 in *; trans in TR; subst.
      apply RT in EQ. destruct EQ as [? _]. specialize (H eq_refl). inv H.
    }
    1: {
      rewrite EQ0 in *; trans in TR; subst.
      apply RT in EQ. destruct EQ as [? _]. specialize (H eq_refl). inv H.
    }
    rewrite EQ0 in *; trans in TR; subst.
    exists n0, k0, n1; split; auto.
    now rewrite Eqt in SIM.
  Qed.

End epsilon_theory.

#[global] Hint Resolve epsilon_trans : trans.

(*
(** Closure under [eutt]

  General asymmetric lemmas for [eutt R], where we naturally get
  a different point related by [R], and [Proper] instances for
  [eutt eq]. *)
Lemma Leaf_eutt_l {E A B R}:
  forall (t : ktree E A) (u : ktree E B) (a : A),
  eutt R t u ->
  a ∈ t ->
  exists b, b ∈ u /\ R a b.
Proof.
  intros * EQ FIN;
  revert u EQ.
  induction FIN; intros u2 EQ.
  - punfold EQ.
    red in EQ; rewrite H in EQ; clear H t.
    remember (RetF a); genobs u2 ou.
    hinduction EQ before R; intros; try now discriminate.
    + inv Heqi; eauto with ktree.
    + edestruct IHEQ as (b & IN & HR); eauto with ktree.
  - punfold EQ; red in EQ; rewrite H in EQ; clear H t.
    remember (TauF u); genobs u2 ou2.
    hinduction EQ before R; intros; try discriminate; pclearbot; inv Heqi.
    + edestruct IHFIN as (? & ? & ?); [ .. | eexists ]; eauto with ktree.
    + eauto with ktree.
    + edestruct IHEQ as (? & ? & ?); [ .. | eexists ]; eauto with ktree.
  - punfold EQ; red in EQ; rewrite H in EQ; clear H t.
    remember (VisF e k); genobs u2 ou2.
    hinduction EQ before R; intros; try discriminate; pclearbot.
    + revert x FIN IHFIN.
      refine (match Heqi in _ = u return match u with VisF e0 k0 => _ | RetF _ | TauF _ => False end with eq_refl => _ end).
      intros. edestruct IHFIN as (? & ? & ?); [ | eexists ]; eauto with ktree.
    + edestruct IHEQ as (? & ? & ?); [.. | exists x0 ]; eauto with ktree.
Qed.

Lemma Leaf_eutt_r {E A B R}:
  forall (t : ktree E A) (u : ktree E B) (b : B),
  eutt R t u ->
  b ∈ u ->
  exists a, a ∈ t /\ R a b.
Proof.
  intros * EQ FIN.
  apply eqit_flip in EQ.
  revert EQ FIN.
  apply @Leaf_eutt_l.
Qed.

#[global] Instance Leaf_eutt {E A}:
  Proper (eq ==> eutt eq ==> iff) (@Leaf E A).
Proof.
  apply proper_sym_impl_iff_2; [ exact _ .. | ].
  unfold Proper, respectful, impl. intros; subst.
  edestruct @Leaf_eutt_l as [? []]; try eassumption; subst; assumption.
Qed.

(** Compatibility with [bind], forward and backward *)

Lemma Leaf_bind : forall {E R S}
  (t : ktree E R) (k : R -> ktree E S) a b,
  b ∈ t ->
  a ∈ k b ->
  a ∈ t >>= k.
Proof.
  intros * INt INk; induction INt.
  - rewrite (ktree_eta t), H, bind_ret_l; auto.
  - rewrite (ktree_eta t), H, tau_eutt; auto.
  - rewrite (ktree_eta t), H, bind_vis.
    apply Leaf_Vis with x; auto.
Qed.

Lemma Leaf_bind_inv : forall {E R S}
  (t : ktree E R) (k : R -> ktree E S) a,
  a ∈ t >>= k ->
  exists b, b ∈ t /\ a ∈ k b.
Proof.
  intros * FIN;
  remember (Ktree.bind t k) as u.
  revert t k Hequ.
  induction FIN; intros t' k' ->; rename t' into t.
  - unfold observe in H; cbn in H.
    desobs t EQ; cbn in *; try congruence.
    exists r; auto with ktree.
  - unfold observe in H; cbn in H.
    desobs t EQ; cbn in *; try congruence; [ eexists; eauto with ktree | ].
    inversion H; clear H; symmetry in H1.
    edestruct IHFIN as (? & ? & ?); [ eauto | eexists; eauto with ktree ].
  - unfold observe in H; cbn in H.
    desobs t EQ; cbn in *; try congruence; [ eexists; eauto with ktree | ].
    revert x FIN IHFIN.
    refine (match H in _ = u return match u with VisF e0 k0 => _ | RetF _ | TauF _ => False end with eq_refl => _ end).
    intros.
    edestruct IHFIN as (? & ? & ?); [ reflexivity | eexists; eauto with ktree ].
Qed.

(** Leaf-aware up-to bind closure
    This construction generalizes [eqit_bind_clo]: one can
    indeed provide an arbitrary cut at the relational
    redicate [RU] of one's choice, but the continuations
    are only required to be related pointwise at the intersection
    of [RU] with the respective leaves of the prefixes.
  *)
Section LeafBind.

  Context {E : Type -> Type} {R S : Type}.

  Local Open Scope ktree.

  Inductive eqit_Leaf_bind_clo b1 b2 (r : ktree E R -> ktree E S -> Prop) :
    ktree E R -> ktree E S -> Prop :=
  | pbc_intro_h U1 U2 (RU : U1 -> U2 -> Prop)
                (t1 : ktree E U1) (t2 : ktree E U2)
                 (k1 : U1 -> ktree E R) (k2 : U2 -> ktree E S)
                (EQV: eqit RU b1 b2 t1 t2)
                (REL: forall u1 u2,
                      u1 ∈ t1 -> u2 ∈ t2 -> RU u1 u2 ->
                      r (k1 u1) (k2 u2))
      : eqit_Leaf_bind_clo b1 b2 r
            (Ktree.bind t1 k1) (Ktree.bind t2 k2)
    .
  Hint Constructors eqit_Leaf_bind_clo : ktree.

  Lemma eqit_Leaf_clo_bind  (RS : R -> S -> Prop) b1 b2 vclo
        (MON: monotone2 vclo)
        (CMP: compose (eqitC RS b1 b2) vclo <3= compose vclo (eqitC RS b1 b2))
        (ID: id <3= vclo):
    eqit_Leaf_bind_clo b1 b2 <3= gupaco2 (eqit_ RS b1 b2 vclo) (eqitC RS b1 b2).
  Proof.
    gcofix CIH. intros. destruct PR.
    guclo eqit_clo_trans.
    econstructor; auto_ctrans_eq; try (rewrite (ktree_eta (x <- _;; _ x)), unfold_bind; reflexivity).
    punfold EQV. unfold_eqit.
    genobs t1 ot1.
    genobs t2 ot2.
    hinduction EQV before CIH; intros; pclearbot.
    - guclo eqit_clo_trans.
      econstructor; auto_ctrans_eq; try (rewrite <- !ktree_eta; reflexivity).
      gbase; cbn.
      apply REL0; auto with ktree.
    - gstep. econstructor.
      gbase.
      apply CIH.
      econstructor; eauto with ktree.
    - gstep. econstructor.
      intros; apply ID; unfold id.
      gbase.
      apply CIH.
      econstructor; eauto with ktree.
    - destruct b1; try discriminate.
      guclo eqit_clo_trans.
      econstructor.
      3:{ eapply IHEQV; eauto with ktree. }
      3,4:auto_ctrans_eq.
      2: reflexivity.
      eapply eqit_Tau_l. rewrite unfold_bind, <-ktree_eta. reflexivity.
    - destruct b2; try discriminate.
      guclo eqit_clo_trans.
      econstructor; auto_ctrans_eq; eauto with ktree; try reflexivity.
      eapply eqit_Tau_l. rewrite unfold_bind, <-ktree_eta. reflexivity.
  Qed.

End LeafBind.

(** General cut rule for [eqit]
    This result generalizes [eqit_clo_bind].  *)
Lemma eqit_clo_bind_gen :
  forall {E} {R1 R2} (RR : R1 -> R2 -> Prop) {U1 U2} {UU : U1 -> U2 -> Prop}
          b1 b2
           (t1 : ktree E U1) (t2 : ktree E U2)
          (k1 : U1 -> ktree E R1) (k2 : U2 -> ktree E R2),
    eqit UU b1 b2 t1 t2 ->
    (forall (u1 : U1) (u2 : U2),
      u1 ∈ t1 -> u2 ∈ t2 -> UU u1 u2 ->
      eqit RR b1 b2 (k1 u1) (k2 u2)) ->
    eqit RR b1 b2 (x <- t1;; k1 x) (x <- t2;; k2 x).
Proof.
    intros.
    ginit. guclo (@eqit_Leaf_clo_bind E R1 R2).
    econstructor; eauto.
    intros * IN1 IN2 HR.
    gfinal; right.
    apply H0; auto.
Qed.

(** Specialization of the cut rule to [eutt] *)
Lemma eutt_clo_bind_gen :
  forall {E} {R1 R2} (RR : R1 -> R2 -> Prop) {U1 U2} {UU : U1 -> U2 -> Prop}
           (t1 : ktree E U1) (t2 : ktree E U2)
          (k1 : U1 -> ktree E R1) (k2 : U2 -> ktree E R2),
    eutt UU t1 t2 ->
    (forall (u1 : U1) (u2 : U2),
      u1 ∈ t1 -> u2 ∈ t2 -> UU u1 u2 ->
      eutt RR (k1 u1) (k2 u2)) ->
    eutt RR (x <- t1;; k1 x) (x <- t2;; k2 x).
Proof.
  intros *; apply eqit_clo_bind_gen.
Qed.

(** Often useful particular case of identical prefixes *)
Lemma eutt_eq_bind_gen {E R S T} (RS : R -> S -> Prop)
      (t: ktree E T) (k1: T -> ktree E R) (k2 : T -> ktree E S) :
    (forall u, u ∈ t -> eutt RS (k1 u) (k2 u)) ->
    eutt RS (t >>= k1) (t >>= k2).
Proof.
  intros; eapply eutt_clo_bind_gen.
  reflexivity.
  intros * IN _ <-; eauto.
Qed.

Lemma eqit_bind_Leaf_inv {E} {R S T} (RS : R -> S -> Prop)
      (t : ktree E T)  (k1: T -> ktree E R) (k2 : T -> ktree E S) :
  (eutt RS  (Ktree.bind t k1) (Ktree.bind t k2)) ->
  (forall r, Leaf r t -> eutt RS (k1 r) (k2 r)).
Proof.
  intros EQIT r HRET.
  revert k1 k2 EQIT.
  induction HRET; intros;
    rewrite 2 unfold_bind, H in EQIT.
  - assumption.
  - rewrite 2 tau_eutt in EQIT. auto.
  - apply IHHRET. eapply eqit_inv_Vis in EQIT; eauto.
Qed.

(** Correspondence with has_post *)

Lemma has_post_Leaf {E R} (t: ktree E R) Q r:
  has_post t Q -> r ∈ t -> Q r.
Proof.
  intros Hcond Himage.
  rewrite has_post_post_strong in Hcond.
  destruct (Leaf_eutt_l t t r Hcond Himage).
  intuition; now subst.
Qed.

Lemma has_post_Leaf_equiv {E R} (t: ktree E R) Q:
  has_post t Q <-> (forall r, r ∈ t -> Q r).
Proof.
  intuition. eapply has_post_Leaf; eauto.
  revert t H. pcofix CIH; intros t Hpost. pstep; red.
  setoid_rewrite (ktree_eta t) in Hpost.
  desobs t Ht; clear t Ht.
  - constructor. apply Hpost, Leaf_Ret.
  - constructor. right; apply CIH. intros. apply Hpost, Leaf_Tau, H.
  - constructor. intros. right. apply CIH. intros. eapply Hpost, Leaf_Vis, H.
Qed.

(** Leaf-based inversion principles for iter *)

(* Inverts [r ∈ Ktree.iter body entry] into any post-condition on r which is
   satisfied by terminating iterations of the body. *)
Lemma Leaf_iter_inv {E R I}:
  forall (body: I -> ktree E (I + R)) (entry: I) (Inv: I -> Prop) (Q: R -> Prop),
  (forall i r, Inv i -> r ∈ body i -> sum_pred Inv Q r) ->
  Inv entry ->
  forall r, r ∈ (Ktree.iter body entry) -> Q r.
Proof.
  intros * Hinv Hentry.
  rewrite <- has_post_Leaf_equiv.
  eapply has_post_iter_strong; eauto.
  setoid_rewrite has_post_Leaf_equiv. eauto.
Qed.

Lemma Leaf_interp_iter_inv {E F R I} (h: E ~> ktree F):
  forall (body: I -> ktree E (I + R)) (entry: I) (Inv: I -> Prop) (Q: R -> Prop),
  (forall i r, Inv i -> r ∈ interp h (body i) -> sum_pred Inv Q r) ->
  Inv entry ->
  forall r, r ∈ interp h (Ktree.iter body entry) -> Q r.
Proof.
  intros * Hbody Hentry r Hr.
  apply (Leaf_iter_inv (fun i => interp h (body i)) entry Inv); auto.
  rewrite (interp_iter'  _ _ (fun i => interp h (body i))) in Hr.
  apply Hr. reflexivity.
Qed.

(* Inverts [sr' ∈ interp_state h (Ktree.iter body i)] into a post-condition on
   both retun value and state, like Leaf_iter_inv. *)
Lemma Leaf_interp_state_iter_inv {E F S R I}:
  forall (h: E ~> Monads.stateT S (ktree F)) (body: I -> ktree E (I + R))
         (RS: S -> Prop) (RI: I -> Prop) (RR: R -> Prop) (s: S) (i: I),
  (forall s i, RS s -> RI i -> (forall sx', sx' ∈ interp_state h (body i) s ->
                    prod_pred RS (sum_pred RI RR) sx')) ->
  RS s -> RI i ->
  forall sr', sr' ∈ interp_state h (Ktree.iter body i) s -> prod_pred RS RR sr'.
Proof.
  setoid_rewrite <- has_post_Leaf_equiv.
  setoid_rewrite has_post_post_strong.
  intros * Hinv Hentrys Hentryi.
  set (eRI := fun (i1 i2: I) => i1 = i2 /\ RI i1).
  set (eRR := fun (r1 r2: R) => r1 = r2 /\ RR r1).
  set (eRS := fun (s1 s2: S) => s1 = s2 /\ RS s1).

  set (R1 := (fun x y : S * R => x = y /\ prod_pred RS RR x)).
  set (R2 := (fun a b : S * R => eRS (fst a) (fst b) /\ eRR (snd a) (snd b))).
  assert (HR1R2: eq_rel R1 R2) by (compute; intuition; subst; now try destruct y).
  unfold has_post_strong; fold R1; rewrite (eutt_equiv _ _ HR1R2).

  unshelve eapply (eutt_interp_state_iter eRI eRR eRS h body body _ i i s s _ _);
  [| subst eRS; intuition | subst eRI; intuition].
  intros i1 ? s1 ? [<- Hs1] [<- Hi1].

  set (R3 := (fun x y : S * (I + R) => x = y /\ prod_pred RS (sum_pred RI RR) x)).
  set (R4 := (prod_rel eRS (sum_rel eRI eRR))).
  assert (HR3R4: eq_rel R3 R4).
  { split; intros [? [|]] [? [|]]; compute.
    1-4: intros [[]]; dintuition; cbn; intuition.
    all: intros [[[=->] ?] HZ]; inversion HZ; intuition now subst. }

  rewrite <- (eutt_equiv _ _ HR3R4).
  now apply Hinv.
Qed.

(** Inversion of Leaf through interp.
    Since interp does not change leaves, we have [x ∈ interp h t -> x ∈ t].
    However this is not easy to see from the Leaf predicate; we must use t. *)

Module Subtree.

Inductive subtree {E R}: ktree E R -> ktree E R -> Prop :=
  | SubtreeRefl u t:
      u ≅ t -> subtree u t
  | SubtreeTau u t:
      subtree (Tau u) t -> subtree u t
  | SubtreeVis {T} u (e: E T) k x t:
      u ≅ k x -> subtree (Vis e k) t -> subtree u t.

#[global] Instance subtree_cong_eqktree {E R}:
  Proper (eq_ktree eq ==> eq_ktree eq ==> flip impl) (@subtree E R).
Proof.
  intros t t' Ht u u' Hu Hsub.
  revert t Ht u Hu; induction Hsub; intros.
  - apply SubtreeRefl. now rewrite Ht, Hu.
  - apply SubtreeTau, IHHsub; auto. apply eqit_Tau, Ht.
  - eapply SubtreeVis. now rewrite Ht, H. apply IHHsub; auto. reflexivity.
Qed.

Lemma subtree_image {E R} (t u: ktree E R) x:
  subtree u t -> x ∈ u -> x ∈ t.
Proof.
  intros * Hsub. induction Hsub; intros.
  - intros. rewrite <- H; auto.
  - apply IHHsub, Leaf_Tau, H.
  - eapply IHHsub, Leaf_Vis. rewrite H in H0; eauto.
Qed.

Lemma Leaf_interp_subtree_inv {E F R} (h: E ~> ktree F) (t u: ktree E R):
  subtree u t -> has_post (interp h u) (fun x : R => x ∈ t).
Proof.
  revert t u. ginit. gcofix CIH; intros * Hsub.
  rewrite (ktree_eta u) in Hsub.
  rewrite ! unfold_interp.
  desobs u Hu; clear u Hu; cbn.
  - gstep; red. constructor. eapply subtree_image; eauto. apply Leaf_Ret.
  - gstep; red. constructor. gfinal; left. apply CIH. apply SubtreeTau, Hsub.
  - guclo eqit_clo_bind; econstructor. reflexivity. intros u _ <-.
    gstep; red. constructor. gfinal; left. apply CIH. eapply SubtreeVis, Hsub.
    reflexivity.
Qed.

Lemma Leaf_interp_state_subtree_inv {E F S R} (h: E ~> Monads.stateT S (ktree F))
  (t u: ktree E R) (s: S):
  subtree u t -> has_post (interp_state h u s) (fun x => snd x ∈ t).
Proof.
  revert t u s. ginit. gcofix CIH; intros * Hsub.
  rewrite (ktree_eta u) in Hsub.
  rewrite ! unfold_interp_state.
  desobs u Hu; clear u Hu; cbn.
  - gstep; red. constructor. eapply subtree_image; eauto. apply Leaf_Ret.
  - gstep; red. constructor. gfinal; left. apply CIH. apply SubtreeTau, Hsub.
  - guclo eqit_clo_bind; econstructor. reflexivity. intros [u1 u2] _ <-; cbn.
    gstep; red. constructor. gfinal; left. apply CIH. eapply SubtreeVis, Hsub.
    reflexivity.
Qed.

End Subtree.
Import Subtree.

Lemma Leaf_interp_inv {E F R} (h: E ~> ktree F) (t: ktree E R) x:
  x ∈ interp h t -> x ∈ t.
Proof.
  intros Hleaf. apply (has_post_Leaf (interp h t) (fun x => x ∈ t)); auto.
  apply Leaf_interp_subtree_inv. apply SubtreeRefl; reflexivity.
Qed.

Lemma Leaf_interp_state_inv {E F S R} (h: E ~> Monads.stateT S (ktree F))
  (t: ktree E R) s x:
  x ∈ interp_state h t s -> snd x ∈ t.
Proof.
  intros Hleaf.
  apply (has_post_Leaf (interp_state h t s) (fun x => snd x ∈ t)); auto.
  apply Leaf_interp_state_subtree_inv. apply SubtreeRefl; reflexivity.
Qed.

(** Inversion through translate. *)

Lemma Leaf_translate_inv {E F R} `{Inj: E -< F}: forall (t: ktree E R) v,
  v ∈ translate (@subevent E F _) t -> v ∈ t.
Proof.
  intros. rewrite translate_to_interp in H.
  eapply Leaf_interp_inv; eauto.
Qed.

*)
