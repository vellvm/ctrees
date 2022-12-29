From ExtLib Require Import
     Structures.Functor
     Structures.Monad.

From CTree Require Import
     Eq.SSim
     Eq
     Interp.Fold
     Interp.FoldStateT.

Import ITree.Basics.Basics.Monads.
Import MonadNotation.
Open Scope monad_scope.

Variant pureb {E C X} (rec : ctree E C X -> Prop) : ctree' E C X -> Prop :=
  | pure_ret   (v : X) : pureb rec (RetF v)
  | pure_delay (c: C X) k (REC: forall v, rec (k v)) : pureb rec (BrDF c k).
#[global] Hint Constructors equb: core.

Definition pureb_ {E C X} rec (t : ctree E C X) := pureb rec (observe t).

Program Definition fpure {E C R} : mon (ctree E C R -> Prop) := {|body := pureb_|}.
Next Obligation.
  red in H0 |- *.
  inversion_clear H0; econstructor; auto.
Qed.

Definition pure {E C R} := gfp (@fpure E C R).

(* LEF: Progress pointer *)
Definition refine_cst {E C} (h : bool -> forall n, fin (S n)) : ctree E C ~> ctree E C :=
  refine (fun b n =>
    match n with
    | O => CTree.stuck b
    | S n => Br b 1 (fun _ => Ret (h b n))
    end).

Definition round_robin {E} : ctree E ~> stateT nat (ctree E).
Proof.
  refine (refine
            (fun b n m =>
               (* m: branch to be refined
                  n: arity of the new node
                *)
               match n as n' return (ctree E (nat * fin n')) with
               | O => CTree.stuck b
               | S n => (Ret (S m, @Fin.of_nat_lt (Nat.modulo m (S n)) _ _))
               end
         )).
  apply (NPeano.Nat.mod_upper_bound).
  auto with arith.
Defined.

Theorem refine_cst_refinement :
  forall {E X} (h : bool -> forall n, fin (S n)) (t : ctree E X),
  ssim0 (refine_cst h _ t) t.
Proof.
  intros until h. coinduction R CH. repeat intro.
  do 3 red in H. remember (observe _) as os. genobs t' ot'.
  assert (EQ : go os ≅ refine_cst h X t \/ go os ≅ Guard (refine_cst h X t)).
  { left. rewrite Heqos. now rewrite <- ctree_eta. } clear Heqos.
  apply (f_equal go) in Heqot'. eq2equ Heqot'.
  rewrite <- ctree_eta in EQ0.
  assert (exists u' : Trans.SS, trans l t u' /\ sst0 R t' u').
  2: { destruct H0; exists x; destruct H0; assumption. }
  setoid_rewrite <- EQ0. clear t' EQ0.
  revert t EQ.
  induction H; intros; subst.
  - destruct EQ as [EQ|EQ]; symmetry in EQ.
    setoid_rewrite unfold_iter in EQ.
    setoid_rewrite (ctree_eta t0).
    genobs t0 ot0. clear t0 Heqot0.
    destruct ot0 eqn:?; subst.
    + step in EQ. inv EQ.
    + step in EQ. inv EQ.
    + setoid_rewrite bind_bind in EQ.
      setoid_rewrite bind_ret_l in EQ.
      change t with (observe (go t)) in H.
      rewrite trans__trans in H.
      destruct n0.
      * setoid_rewrite bind_br in EQ.
        apply equ_br_invT in EQ as ?. destruct H0 as [<- _].
        now eapply Fin.case0.
      * setoid_rewrite bind_br in EQ.
        apply equ_br_invT in EQ as ?. destruct H0 as [<- _].
        destruct vis. { step in EQ. inv EQ. }
        simple eapply equ_br_invE with (x := x) in EQ.
        rewrite bind_ret_l in EQ.
        lapply (IHtrans_ (k0 (h false n0))).
        -- intro. destruct H0 as (? & ? & ?).
           etrans.
        -- right. rewrite <- ctree_eta. now rewrite <- EQ.
    + apply IHtrans_. left.
      apply equ_br_invT in EQ as ?. destruct H0 as [<- _]. rewrite <- ctree_eta.
      simple apply equ_br_invE with (x := x) in EQ. now rewrite EQ.
  - destruct EQ. 2: { step in H0. inv H0. }
    setoid_rewrite unfold_iter in H0. cbn in H0.
    destruct (observe t0) eqn:?;
      (try setoid_rewrite bind_br in H0);
      (try setoid_rewrite bind_trigger in H0);
      (try destruct vis);
      subst; try now step in H0; inv H0.
    rewrite bind_bind in H0.
    destruct n0.
    + setoid_rewrite bind_br in H0.
      apply equ_br_invT in H0 as ?. destruct H1 as [-> _].
      now eapply Fin.case0.
    + rewrite bind_br in H0.
      do 2 setoid_rewrite bind_ret_l in H0.
      apply equ_br_invT in H0 as ?. destruct H1 as [-> _].
      simple apply equ_br_invE with (x := x) in H0.
      exists (k0 (h true n0)).
      rewrite ctree_eta, Heqc. split; etrans.
      rewrite <- H, H0, <- ctree_eta, sb_guard.
      apply CH.
    + destruct n0; step in H0; inv H0.
  - destruct EQ. 2: { step in H0. inv H0. }
    setoid_rewrite unfold_iter in H0. cbn in H0.
    destruct (observe t0) eqn:?;
      try ((try destruct n); now step in H0; inv H0).
    setoid_rewrite bind_trigger in H0. setoid_rewrite bind_vis in H0.
    apply equ_vis_invT in H0 as ?. destruct H1.
    apply equ_vis_invE in H0 as [-> ?].
    setoid_rewrite bind_ret_l in H0.
    exists (k0 x). eexists.
    { rewrite ctree_eta, Heqc. etrans. }
    rewrite <- H, H0, <- ctree_eta, sb_guard. apply CH.
  - destruct EQ. 2: { step in H. inv H. }
    exists CTree.stuckD.
    setoid_rewrite unfold_iter in H.
    destruct (observe t) eqn:?;
      try ((try destruct n); now step in H; inv H).
    setoid_rewrite bind_ret_l in H.
    + step in H. inv H. rewrite ctree_eta, Heqc.
      split; etrans. rewrite br0_always_stuck. reflexivity.
Qed.
