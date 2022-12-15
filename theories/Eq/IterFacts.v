From Coq Require Import Basics Fin.

From Coinduction Require Import
     coinduction rel tactics.

From ITree Require Import
     Basics.CategoryTheory
     Basics.CategoryKleisli.

From CTree Require Import
     CTree
     Utils
     Eq
     (*Eq.Equg*).

Import CTree.
Import CTreeNotations.

Definition iter_gen {E B X I} `{B1 -< B}
    (step : I -> ctree E B (I + X)) (t : ctree E B (I + X)) :=
  r <- t;;
  match r with
  | inl i => Guard (iter step i)
  | inr x => Ret x
  end.

Section SBisimIter.

Context {E B : Type -> Type} {X : Type} {I : Type}.
Context `{HasB0 : B0 -< B} `{HasB1 : B1 -< B}.
Context (step : I -> ctree E B (I + X)).

Lemma iter_iter_gen : forall (i : I),
  iter step i ≅ iter_gen step (step i).
Proof.
  intros. unfold iter_gen.
  rewrite unfold_iter.
  reflexivity.
Qed.

Inductive trans_it (step : I -> ctree E B (I + X)) (t : ctree E B (I + X)) l T : Prop :=
| it_next i :
    trans (val (inl i : I + X)) t stuckD ->
    trans_it step (step i) l T ->
    trans_it step t l T
| it_ex t' :
    trans l t t' /\ T ≅ iter_gen step t' /\ ~is_val l ->
    trans_it step t l T
| it_val r :
    trans (val (inr r : I + X)) t stuckD ->
    l = val r ->
    T ≅ stuckD ->
    trans_it step t l T.

Lemma trans_it_brD : forall {Y} t l (c : B Y) k x T,
  t ≅ BrD c k ->
  trans_it step (k x) l T ->
  trans_it step t l T.
Proof.
  intros.
  remember (k x) as kx. assert (kx ≅ k x). { now subst. } clear Heqkx.
  revert t k x H H1. induction H0; intros; subst.
  - eapply it_next. rewrite H1. eapply trans_brD with (x := x).
    apply H. now rewrite H2. apply H0.
  - eapply it_ex. split. rewrite H0. eapply trans_brD.
    apply H. now rewrite H1. apply H.
  - eapply it_val; auto. rewrite H2. eapply trans_brD.
    apply H. now rewrite H3.
Qed.

Lemma iter_gen_brS : forall {Y} t (c : B Y) K,
  iter_gen step t ≅ BrS c K ->
  exists k, t ≅ BrS c k /\ forall x, iter_gen step (k x) ≅ K x.
Proof.
  intros.
  unfold iter_gen in H.
  setoid_rewrite (ctree_eta t) in H.
  setoid_rewrite (ctree_eta t).
  desobs t.
  - rewrite bind_ret_l in H.
    destruct r; step in H; inv H.
  - step in H. inv H.
  - rewrite bind_br in H.
    apply equ_br_invT in H as ?. destruct H0 as [-> ->].
    exists k. split. { apply equ_br_invE in H as [-> _]. reflexivity. }
    intros.
    apply equ_br_invE in H as [<- ?]. apply H.
Qed.

Lemma iter_gen_vis {Y} : forall t (e : E Y) K,
  iter_gen step t ≅ Vis e K ->
  exists k, t ≅ Vis e k /\ forall x, iter_gen step (k x) ≅ K x.
Proof.
  intros.
  unfold iter_gen in H.
  setoid_rewrite (ctree_eta t) in H.
  setoid_rewrite (ctree_eta t).
  desobs t.
  - rewrite bind_ret_l in H.
    destruct r; step in H; inv H.
  - rewrite bind_vis in H.
    apply equ_vis_invT in H as ?. subst.
    apply equ_vis_invE in H as []. subst.
    exists k. split. reflexivity. intros.
    apply H0.
  - step in H. inv H.
Qed.

Theorem trans_iter_gen : forall l t T, trans l (iter_gen step t) T -> trans_it step t l T.
Proof.
  intros. do 3 red in H.
  remember (observe (iter_gen step t)) as oi.
  genobs T oT.
  assert (go oi ≅ iter_gen step t \/ go oi ≅ Guard (iter_gen step t)).
  { left. now rewrite Heqoi, <- ctree_eta. } clear Heqoi.
  revert t H0 T HeqoT. induction H; intros; subst.
  - destruct H0.
    + unfold iter_gen in H0.
      symmetry in H0. apply br_equ_bind in H0 as ?. destruct H1.
      * destruct H1. rewrite H1, bind_ret_l in H0. destruct x0.
        2: { step in H0. inv H0. }
        eapply it_next.
        --rewrite H1. etrans.
        --apply IHtrans_; auto.
          apply equ_br_invT in H0 as ?.
          destruct H2 as [? _]. subst.
          apply equ_br_invE in H0 as []. subst.
          left. rewrite <- H2, <- ctree_eta. apply iter_iter_gen.
      * destruct H1 as (? & ? & ?).
        eapply trans_it_brD. apply H1.
        apply IHtrans_. left. rewrite <- ctree_eta. apply H2. reflexivity.
    + apply equ_br_invT in H0 as ?. destruct H1 as [-> _].
      apply equ_br_invE in H0 as []. subst.
      apply IHtrans_; auto. left. rewrite <- ctree_eta. apply H1.
  - destruct H0. 2: { step in H0. inv H0. }
    symmetry in H0. apply iter_gen_brS in H0 as (? & ? & ?).
    eapply it_ex. split. { rewrite H0. etrans. }
    split.
    now rewrite ctree_eta, <- HeqoT, <- ctree_eta, <- H, <- H1.
    intro. inv H2.
  - destruct H0. 2: { step in H0. inv H0. }
    symmetry in H0. apply iter_gen_vis in H0 as (? & ? & ?).
    eapply it_ex. split. { rewrite H0. etrans. }
    split.
    now rewrite ctree_eta, <- HeqoT, <- ctree_eta, <- H, <- H1.
    intro. inv H2.
  - destruct H0. 2: { step in H. inv H. }
    unfold iter_gen in H.
    symmetry in H. apply ret_equ_bind in H as (? & ? & ?).
    destruct x. step in H0. inv H0. step in H0. inv H0.
    eapply it_val. rewrite H. etrans. reflexivity. rewrite ctree_eta, <- HeqoT.
    apply br0_always_stuck.
Qed.

End SBisimIter.

#[global] Instance sbisim_iter_gen {E B X Y} `{HasB0 : B0 -< B} `{HasB1 : B1 -< B} :
  @Proper ((X -> ctree E B (X + Y)) -> ctree E B (X + Y) -> ctree E B Y)
    (pointwise_relation _ (sbisim eq) ==> (sbisim eq) ==> (sbisim eq))
    iter_gen.
Proof.
  repeat intro.
  rename x into step. rename y into step'.
  revert step step' x0 y0 H H0.
  coinduction R CH.
  (*symmetric using idtac.
     { intros. apply H. symmetry. apply H0. symmetry. apply H1. }*)
  split. 2: admit.
  cbn. intros.
  apply trans_iter_gen in H1.
  revert y0 H0. induction H1; intros.
  - step in H2. apply H2 in H0 as (? & ? & ? & ? & ?). subst.
    apply trans_val_inv in H0 as ?. rewrite H4 in H0. clear x0 H3 H4.
    apply IHtrans_it in H as (? & ? & ? & ? & ?). subst. clear IHtrans_it.
    exists x, x0; auto. split; auto.
    unfold iter_gen.
    apply trans_bind_r with (x := inl i); auto.
    apply trans_guard. apply H.
  - destruct H0 as (? & ? & ?).
    step in H1. apply H1 in H0 as (? & ? & ? & ? & ?). subst.
    exists x, (iter_gen step' x0). split; [| split]; auto.
    + apply trans_bind_l; auto.
    + rewrite H2. apply CH; auto.
  - subst.
    step in H3. apply H3 in H0 as (? & ? & ? & ? & ?). subst.
    apply trans_val_inv in H0 as ?. rewrite H4 in H0. clear x0 H1 H4.
    exists (val r), stuckD. split. 2: { split. now rewrite H2. reflexivity. }
    eapply trans_bind_r. apply H0. cbn. etrans.
Admitted.

#[global] Instance sbisim_iter {E B X Y} `{HasB0 : B0 -< B} `{HasB1 : B1 -< B} :
  @Proper ((X -> ctree E B (X + Y)) -> X -> ctree E B Y)
    (pointwise_relation _ (sbisim eq) ==> pointwise_relation _ (sbisim eq))
    iter.
Proof.
  repeat intro.
  rewrite !iter_iter_gen.
  apply sbisim_iter_gen. apply H. apply H.
Qed.

(*Lemma iter_natural_ctree {E A B C} :
  forall (f : A -> ctree E (A + B)) (g : B -> ctree E C) (a : A),
  CTree.bind (CTree.iter f a) (fun y : B => g y)
  ≅ CTree.iter
    (fun x : A =>
     CTree.bind (f x)
       (fun ab : A + B =>
        match ab with
        | inl a => CTree.bind (Ret a) (fun a : A => Ret (inl a))
        | inr b => CTree.bind (g b) (fun c : C => Ret (inr c))
        end)) a.
Proof.
  intros until g. unfold equ. coinduction R CH. intros.
  setoid_rewrite unfold_iter.
  rewrite !bind_bind. upto_bind_eq.
  destruct x.
  - rewrite !bind_ret_l, bind_br. constructor. intros _.
    apply CH.
  - rewrite bind_bind. setoid_rewrite bind_ret_l. rewrite bind_ret_r.
    reflexivity.
Qed.

Import EqugNotations.

Lemma iter_dinatural_ctree_inner {E A B C} :
  forall (f : A -> ctree E (B + C)) (g : B -> ctree E (A + C)) (a : A),
  iter
    (fun x : A =>
     CTree.bind (f x)
       (fun bc : B + C =>
        match bc with
        | inl b => g b
        | inr c => Ret (inr c)
        end)) a
  (G≅) CTree.bind (f a)
      (fun bc : B + C =>
       match bc with
       | inl b =>
           Guard (iter
             (fun b : B =>
              CTree.bind (g b)
                (fun ac : A + C =>
                 match ac with
                 | inl a => f a
                 | inr c => Ret (inr c)
                 end)) b)
       | inr c => Ret c
       end).
Proof.
  red. coinduction R CH. intros.
  rewrite unfold_iter, bind_bind. __upto_bind_eq_equg.
  destruct x.
  2: { rewrite bind_ret_l. constructor. reflexivity. }
  destruct (observe (g b)) eqn:?.
  - setoid_rewrite (ctree_eta (g b)). rewrite Heqc.
    rewrite bind_ret_l. destruct r.
    + constructor. intros _.
      setoid_rewrite unfold_iter at 2.
      rewrite (ctree_eta (g b)), Heqc, bind_ret_l.
      apply CH.
    + eapply Eqg_GuardR. intros _. reflexivity.
      rewrite equgb_fequg.
      rewrite unfold_iter, bind_bind. assert (equ eq (g b) (Ret (inr c))). { rewrite ctree_eta, Heqc. reflexivity. } rewrite H, bind_ret_l, bind_ret_l. cbn. constructor. reflexivity.
  - setoid_rewrite (ctree_eta (g b)). rewrite Heqc, bind_vis.
    eapply Eqg_GuardR. intros _. reflexivity.
    rewrite equgb_fequg.
    rewrite unfold_iter, bind_bind, (ctree_eta (g b)), Heqc, bind_vis.
    constructor. intros. __upto_bind_eq_equg. destruct x0.
    + apply (ft_t utg_t). cbn. right.
      apply CH.
    + rewrite bind_ret_l. step. constructor. reflexivity.
  - setoid_rewrite (ctree_eta (g b)). rewrite Heqc, bind_br.
    eapply Eqg_GuardR. intros _. reflexivity.
    rewrite equgb_fequg.
    rewrite unfold_iter, bind_bind, (ctree_eta (g b)), Heqc, bind_br.
    constructor. intros. __upto_bind_eq_equg. destruct x.
    + apply (ft_t utg_t). right.
      apply CH.
    + rewrite bind_ret_l. step. constructor. reflexivity.
Qed.

Lemma iter_dinatural_ctree {E A B C} :
  forall (f : A -> ctree E (B + C)) (g : B -> ctree E (A + C)) (a : A),
  iter
    (fun x : A =>
     CTree.bind (f x)
       (fun bc : B + C =>
        match bc with
        | inl b => g b
        | inr c => Ret (inr c)
        end)) a
  ~ CTree.bind (f a)
      (fun bc : B + C =>
       match bc with
       | inl b =>
           iter
             (fun b : B =>
              CTree.bind (g b)
                (fun ac : A + C =>
                 match ac with
                 | inl a => f a
                 | inr c => Ret (inr c)
                 end)) b
       | inr c => Ret c
       end).
Proof.
  intros.
  rewrite unfold_iter, bind_bind. upto_bind_eq.
  destruct x.
  2: { rewrite bind_ret_l. reflexivity. }
  rewrite unfold_iter, bind_bind. upto_bind_eq.
  destruct x.
  2: { rewrite bind_ret_l. reflexivity. }
  rewrite sb_guard. apply equg_sbisim. apply iter_dinatural_ctree_inner.
Qed.

Theorem iter_codiagonal_ctree {E A B} :
  forall (f : A -> ctree E (A + (A + B))) (a : A),
  iter (iter f) a
  ≅ iter
    (fun x : A =>
     CTree.bind (f x)
       (fun y : A + (A + B) =>
        match y with
        | inl a => Ret (inl a)
        | inr b => Ret b
        end)) a.
Proof.
  intro. unfold equ. coinduction R CH. intros.
  rewrite !unfold_iter.
  rewrite !bind_bind. upto_bind_eq.
  destruct x.
  - rewrite bind_ret_l, bind_br. constructor. intros _.
    rewrite <- unfold_iter. apply CH.
  - rewrite !bind_ret_l. destruct s; [| reflexivity ].
    constructor. intros _. apply CH.
Qed.*)
