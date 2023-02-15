From ITree Require Import
     Indexed.Sum.

From Coq Require Import Vector.

From CTree Require Import
     CTree
     Eq
     Misc.Take
     Misc.Vectors
     Logic.Ctl
     Fold
     Combinators.

From Equations Require Import Equations.

Set Implicit Arguments.

Import CTreeNotations VectorNotations CtlNotations.
Local Open Scope ctree_scope.

Variant obs_eq{E F U X}`{U +' F -< E}: F X -> @label E -> Prop :=
| obs_refl: forall (e: F X) (x: X),
  obs_eq e (obs ▷ (inr1 e) x).
Hint Constructors obs_eq: core.

Notation obs_id i := (lift (obs_eq (Switch i))) (only parsing).

Ltac fold_af :=
  match goal with
  | H: context [ @au ?E ?C ?X ?HasStuck Top ?R ?t ?l ] |- _ => fold (@af E C X HasStuck R t l)
  | |- context [ @au ?E ?C ?X ?HasStuck Top ?R ?t ?l ] => fold (@af E C X HasStuck R t l)
  end. 
Section FairFacts.
  Context {E C: Type -> Type}{HasStuck: B0 -< C} {HasTau: B1 -< C}.
  
  Lemma rr_is_fair:
    forall (n: nat) (v: vec (S n) (ctree E C void)) (i: id n) l,
      rr v, l |= AG (AF (obs_id i)).
    Proof.
      Opaque preempt.
      intro n.
      coinduction R CIH.
      econstructor.
      revert l v.
      induction n; intros.
      - (* i = 1 *)
        repeat dependent destruction v. (* v = [h] *)
        repeat dependent destruction i. (* i = i1 *)
        rewrite unfold_0_rr, unfold_Sn_preempt, bind_bind.
        apply ctl_af_ax; right; unfold ax; cbn; intros * TR.
          eapply trans_trigger_inv in TR as ([] & ? & ->).
          now apply MatchA.
      - dependent destruction v. (* v = h :: ts *)
        dependent destruction i; 
          rewrite unfold_Sn_rr,
          unfold_Sn_preempt,
          bind_trigger,
          bind_vis;
          eapply StepA; auto; intros;  (* i = i1 *)
          apply trans_vis_inv in H as ([] & ? & ->).
        + now apply MatchA.
        + rewrite H; clear H t'.
          apply StepA; auto; intros.    (* i = FS i' *)
           desobs h; try contradiction.
          * rewrite bind_vis in H.
            apply trans_vis_inv in H as (x & ? & ->).
            rewrite H; clear H t'.
            rewrite unfold_0_take, translate_ret, bind_ret_l; fold_af.
            
            replace (xs <- rr' v;; Guard (rr (k x :: xs))) with
              ( x <- preempt i1 1 (k x) ;; xs <- rr' xs ;; Guard (rr (x :: xs)).
            rewrite unfold_Sn_rr.
            rewrite <- ctl_af_guard.
               apply CIH.
            -- destruct vis; rewrite bind_br in H.
               ++ apply trans_brS_inv in H as (i & ? & ->).
                  rewrite H; clear H t'0.
                  rewrite unfold_0_take, translate_ret, bind_ret_l.
                  rewrite <- ctl_t_ag_af_guard.
                  apply CIH.
          rewrite H
        rewrite unfold_0_rr, unfold_Sn_preempt, bind_bind. TR.
          step; econstructor.
          * eapply trans_trigger_inv in TR as ([] & ? & ->).
            now apply MatchA.
          * intros.
            eapply trans_trigger_inv in TR as ([] & ? & ->).
            rewrite H0 in *; clear H0; clear t'.
            desobs h; try contradiction.
            -- rewrite bind_vis in H.
               apply trans_vis_inv in H as (x & ? & ->).
               rewrite H; clear H t'0.
               rewrite unfold_0_take, translate_ret, bind_ret_l.
               rewrite <- ctl_t_ag_af_guard.
               apply CIH.
            -- destruct vis; rewrite bind_br in H.
               ++ apply trans_brS_inv in H as (i & ? & ->).
                  rewrite H; clear H t'0.
                  rewrite unfold_0_take, translate_ret, bind_ret_l.
                  rewrite <- ctl_t_ag_af_guard.
                  apply CIH.
               ++ (* TODO: Here; need an inversion lemma for BrD *)
                 admit.
      - (* i = S n, n > 0 *)
        dependent destruction v. (* v = h :: ts *)
        dependent destruction i. (* i = i1 \/ FS i' *)
        + econstructor.
          * rewrite unfold_Sn_rr, unfold_Sn_preempt.
            rewrite bind_trigger, bind_vis.
            eapply StepA; auto; intros.
            apply trans_vis_inv in H as ([] & ? & ->).
            now apply MatchA.
          * intros.
            step; econstructor.
            -- rewrite unfold_Sn_rr, unfold_Sn_preempt in H.
               rewrite bind_trigger, bind_vis in H.
               apply trans_vis_inv in H as ([] & ? & ->).
               now apply MatchA.
            -- intros.
               rewrite unfold_Sn_rr, unfold_Sn_preempt in H.
               rewrite bind_trigger, bind_vis in H.
               apply trans_vis_inv in H as ([] & ? & ->).
               rewrite H in H0; clear H t'.
               desobs h; try contradiction.
               ++ rewrite bind_vis in H0.
                  eapply trans_vis_inv in H0 as (x & ? & ->).
                  rewrite H; clear H t'0.
                  rewrite unfold_0_take,
                    translate_ret, bind_ret_l.
                  step.
                  econstructor.
          unfold rr'.
          cbn.
          Set Printing All.
          simpl.
    Qed.
  End FairFacts.

  
End CTreeCombinators.
