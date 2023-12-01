(*| Predicates on ctrees |*)

(* begin hide *)
From CTree Require Import
  Utils.Utils
  CTree.Core
  CTree.Trans
  CTree.Interp.Core
  Events.Core
  CTree.Equ.

From Coinduction Require Import coinduction.
From Coq Require Import Morphisms Basics Program.Equality.

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

(*| WEAK (exists) |*)
Definition may_ret `{Encode E} {X} (t: ctree E X)(x: X) := trans (val x) t stuck.
Arguments may_ret /.

(*| CTree can only take [val x] steps, inductively |*)
Inductive only_ret_`{Encode E} {X}: ctree' E X -> X -> Prop :=
| IsBrD: forall n k x,
    (forall (i: fin' n), only_ret_ (observe (k i)) x) ->
    only_ret_ (BrF false n k) x
| IsRet: forall x,
    only_ret_ (RetF x) x.
Global Hint Constructors only_ret_: ctree.

Definition only_ret `{Encode E} {X}(t: ctree E X)(x: X) := only_ret_ (observe t) x.
Arguments only_ret /.
Global Hint Unfold only_ret: ctree.

(*| [only_ret] is deterministic |*)
Lemma only_ret_det`{Encode E} {X}: forall (t: ctree E X) (x y: X),
    only_ret t x ->
    only_ret t y ->
    x = y.
Proof.
  unfold only_ret.
  intros.
  generalize dependent y.
  induction H0; intros.
  - dependent destruction H2.
    apply H1 with Fin.F1.
    apply H2.
  - dependent destruction H1.
    reflexivity.
Qed.
Global Hint Resolve only_ret_det: ctree.

(*| The LTS can not take a step [tau, vis, ret] |*)
Definition is_stuck `{Encode E} {X} (t: ctree E X) := (~ exists l u, trans l t u).
Arguments is_stuck /.

#[global] Instance is_stuck_equ `{HE: Encode E} {X}: Proper (@equ E HE X X eq ==> iff) is_stuck.
Proof.
  unfold Proper, respectful, is_stuck.
  intros t u EQ; split; intros Hn Ht; destruct Ht as (x & t' & TR);
    apply Hn.
  - exists x, t'; now rewrite EQ.
  - exists x, t'; now rewrite <- EQ.
Qed.

Lemma stuck_is_stuck `{HE: Encode E} {X}: @is_stuck E HE X stuck.
Proof.
  red; intros * abs; inv abs.
  destruct H as (s' & TR).
  ind_trans TR.
  eapply IHTR; reflexivity.
Qed.
Global Hint Resolve stuck_is_stuck: ctree.

Lemma trans_onlyret `{HE: Encode E} {X}: forall (t: ctree E X) r,
    only_ret t r ->
    trans (val r) t stuck.
Proof.
  intros.
  unfold only_ret in H.
  dependent induction H; unfold trans; rewrite <- x.
  - eapply trans_brD.
    eapply H0 with (i:= Fin.F1).
    reflexivity.
    reflexivity.
  - apply trans_ret.
Qed.

Lemma stuck_is_not_onlyret`{HE: Encode E} {X}:
  ~ (exists (x: X), only_ret (E:=E) stuck x).
Proof.
  intros (? & Hcontra).
  cbn in Hcontra.
  dependent induction Hcontra.
  apply H0.
  exact Fin.F1.
  reflexivity.
Qed.
Global Hint Resolve stuck_is_not_onlyret: ctree.

Lemma spin_is_not_onlyret`{HE: Encode E} {X}:
  ~ (exists (x: X), only_ret (E:=E) spin x).
Proof.
  intros (? & Hcontra).
  cbn in Hcontra.
  dependent induction Hcontra.
Qed.
Global Hint Resolve spin_is_not_onlyret: ctree.

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
