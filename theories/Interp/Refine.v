From ExtLib Require Import
     Structures.Functor
     Structures.Monad.

From CTree Require Import
     Eq
     Eq.Epsilon
     Eq.SSimAlt
     Interp.Fold
     Interp.FoldCTree
     Interp.FoldStateT.

Import ITree.Basics.Basics.Monads.
Import MonadNotation.
Open Scope monad_scope.

Variant pureb {E C X} (rec : ctree E C X -> Prop) : ctree' E C X -> Prop :=
  | pure_ret   (v : X) : pureb rec (RetF v)
  | pure_delay {Y} (c: C Y) k (REC: forall v, rec (k v)) : pureb rec (BrDF c k).

Definition pureb_ {E C X} rec (t : ctree E C X) := pureb rec (observe t).

Program Definition fpure {E C R} : mon (ctree E C R -> Prop) := {|body := pureb_|}.
Next Obligation.
  red in H0 |- *.
  inversion_clear H0; econstructor; auto.
Qed.

Definition pure {E C R} := gfp (@fpure E C R).

Inductive pure_finite {E C X} : ctree E C X -> Prop :=
  | puref_ret (v : X) : pure_finite (Ret v)
  | puref_delay {Y} (c: C Y) (k : Y -> ctree E C X) (REC: forall v, pure_finite (k v)) : pure_finite (BrD c k).

Definition refine' {E C M : Type -> Type}
           {FM : Functor M} {MM : Monad M}
           {IM : MonadIter M} {FoM : MonadTrigger E M}
           {CM : MonadBr B01 M}
           (h : C ~> M) :
  ctree E (B01 +' C) ~> M :=
  refine (fun b X (c: (B01 +' C) X) =>
    match c, X return M X with
    | inl1 c, X => mbr b c
    | inr1 c, X => r <- h X c;; mbr b (inr1 branch1);; ret r
    end).

#[global] Instance MonadBr_subevent_l : forall {E B B'}, MonadBr B (ctree E (B +' B')).
Proof.
  red. intros. eapply MonadBr_ctree; eauto.
  Unshelve. now left.
Defined.
#[global] Instance MonadBr_stateT_subevent_l : forall {E B B' St}, MonadBr B (stateT St (ctree E (B +' B'))).
Proof.
  typeclasses eauto.
Defined.

Definition refine'_state {E C D St} (f : C ~> stateT St (ctree E (B01 +' D))) :
  ctree E (B01 +' C) ~> stateT St (ctree E (B01 +' D)) :=
  refine' (CM := MonadBr_stateT) f.

Unset Universe Checking.

Import SSim'Notations.

Theorem ssim_pure {E F B C X} `{HasB0: B0 -< B} `{HasB0': B0 -< C} : forall (L : rel _ _) (t : ctree E B X),
  pure_finite t ->
  (forall x : X, L (val x) (val tt)) ->
  ssim L t (Ret tt : ctree F C unit).
Proof.
  intros. induction H.
  - now apply ssim_ret.
  - now apply ssim_brD_l.
Qed.

Theorem refine_ctree_ssim {E B B' X} `{HasB0: B0 -< B'} `{HasB1: B1 -< B'} :
  forall (t : ctree E (B01 +' B) X) (h : B ~> ctree E (B01 +' B')),
  (forall X c, pure_finite (h X c)) ->
  refine' h _ t ≲ t.
Proof.
  intros. rewrite ssim_ssim'. red. revert t. coinduction R CH. intros.
  rewrite (ctree_eta t) at 2.
  setoid_rewrite unfold_refine. cbn.
  destruct (observe t) eqn:?.
  - apply step_ss'_ret. reflexivity.
  - setoid_rewrite bind_trigger.
    apply step_ss'_vis_id. intros. split; [|auto].
    step. apply step_ss'_guard_l. apply CH.
  - unfold mbr, MonadBr_subevent_l, MonadBr_ctree. destruct c.
    + setoid_rewrite bind_branch. destruct vis.
      * apply step_ss'_brS_id; auto. intros.
        step. apply step_ss'_guard_l. apply CH.
      * apply step_ss'_brD_id. intros.
        step. apply step_ss'_guard_l. apply CH.
    + rewrite bind_bind.
      change (Br vis (inr1 b) k) with ((fun _ => Br vis (inr1 b) k) tt).
      setoid_rewrite <- bind_ret_l at 10.
      __upto_bind_ssim' (fun _ _ => True).
      { apply ssim_pure. apply H. intros. now constructor. }
      red. intros ? _ _. rewrite bind_bind, bind_branch.
      destruct vis.
      * apply step_ss'_brS; auto. intros _. exists x.
        rewrite bind_ret_l. step. apply step_ss'_guard_l. apply CH.
      * apply step_ss'_brD. intros _. exists x.
        rewrite bind_ret_l. step. apply step_ss'_guard_l. apply CH.
Qed.

Variant lift_val_rel {E X Y} (R : rel X Y): @label E -> @label E -> Prop :=
| Rel_Val (v1 : X) (v2 : Y) : R v1 v2 -> lift_val_rel R (val v1) (val v2)
| Rel_Tau : lift_val_rel R tau tau
| Rel_Obs : forall {X X'} e e' (x : X) (x' : X'), obs e x = obs e' x' -> lift_val_rel R (obs e x) (obs e' x')
.
#[global] Hint Constructors lift_val_rel : trans.

Definition Rrr {St X} (p : St * X) (x : X) := snd p = x.
Definition Lrr {St E X} := @lift_val_rel E _ X (@Rrr St X).

Theorem refine_state_ssim {E B B' X St} `{HasB0: B0 -< B'} `{HasB1: B1 -< B'} :
  forall (t : ctree E (B01 +' B) X) (h : B ~> stateT St (ctree E (B01 +' B'))),
  (forall X c s, pure_finite (h X c s)) ->
  forall s, refine' h _ t s (≲@Lrr St E X) t.
Proof.
  intros. rewrite ssim_ssim'. red. revert t s. coinduction R CH. intros.
  rewrite (ctree_eta t) at 2.
  setoid_rewrite unfold_fold_state. cbn.
  destruct (observe t) eqn:?.
  - apply step_ss'_ret. constructor. reflexivity.
  - setoid_rewrite bind_trigger.
    rewrite bind_vis. apply step_ss'_vis_id. intros. split; [| constructor; auto].
    step. rewrite bind_ret_l. apply step_ss'_guard_l. apply CH.
  - unfold mbr, MonadBr_subevent_l, MonadBr_ctree. destruct c.
    + setoid_rewrite bind_branch. setoid_rewrite bind_br. destruct vis.
      * apply step_ss'_brS_id; [| constructor]. intros.
        step. setoid_rewrite bind_ret_l. apply step_ss'_guard_l. apply CH.
      * apply step_ss'_brD_id. intros.
        step. setoid_rewrite bind_ret_l. apply step_ss'_guard_l. apply CH.
    + rewrite bind_bind.
      change (Br vis (inr1 b) k) with ((fun _ => Br vis (inr1 b) k) tt).
      setoid_rewrite <- bind_ret_l at 12.
      __upto_bind_ssim' (fun _ _ => True).
      { apply ssim_pure. apply H. intros. now constructor. }
      red. intros ? _ _. rewrite bind_bind, bind_branch, bind_br.
      destruct vis.
      * apply step_ss'_brS; [| constructor]. intros ?. exists (snd x).
        rewrite bind_ret_l. step. rewrite bind_ret_l. apply step_ss'_guard_l. apply CH.
      * apply step_ss'_brD. intros ?. exists (snd x).
        rewrite bind_ret_l. step. rewrite bind_ret_l. apply step_ss'_guard_l. apply CH.
Qed.
