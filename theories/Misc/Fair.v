From ITree Require Import
     Indexed.Sum
     Core.Subevent.

From Coq Require Import
     Logic.Eqdep
     Program.Equality
     Vector.

From CTree Require Import
     CTree
     Misc.Vectors
     Interp.Par
     Interp.Fold
     Take
     Eq.

Set Implicit Arguments.

Import CTreeNotations VectorNotations.
Local Open Scope ctree_scope.

Section RR.
  Context {E C: Type -> Type} {X: Type} {HasTau: B1 -< C}.
    
  (*| Schedule [m] processes in round-robin.
      [m] is the total length of the vector
      [i] counts in reverse m .. 0 
      [j] counts from 0 .. m,
      in every step [i + j = m] is invariant. 
  Equations rr'' (m: nat) (i j: nat) (H: m = i + j) (x: id j) (v: vec (S i) (ctree E C X)):
    ctree (E +' parE m) C (vec (S i) (ctree E C X)) by wf i :=
    @rr'' _ 0 j _ _ (h :: []) :=      (* j = m /\ i = 0 *)
      (p <- preempt (eq_rec_r (fun m => id m) x H) 1 h;;
       Ret [p]
      );
    @rr'' _ (S i') j _ _ (h :: ts) := (* S i' + j = m *)
      (p <- preempt (eq_rec_r (fun m => id m) (Fin.R (S i') x) _) 1 h ;; 
       ps <- @rr'' m i' (S j) _ (FS x) ts ;;
       Ret (p :: ps)
      ).
   *)

  (*| Map [preempt i 1] over a vector [v] -- inductive |*)
  Notation rr' v := (Vector.rectS (fun n _ => ctree (E +' parE) C (vec (S n) (ctree E C X)))
                                  (fun h => x <- preempt 0 1 h ;; Ret [x])
                                  (fun h n t ts => x <- preempt (S n) 1 h ;; xs <- ts ;; Ret (x :: xs)) v).

  (*| Guarded coinduction of [rr'] |*)
  Definition rr {n}: vec (S n) (ctree E C X) -> ctree (E +' parE) C X :=
    cofix F v :=
      v' <- rr' v ;; Guard (F v').

  Lemma unfold_rr {n}: forall (v: vec (S n) (ctree E C X)),
      rr v  ≅  v' <- rr' v ;; Guard (rr v'). 
  Proof. intros; step; cbn; auto. Qed.

  Lemma unfold_0_rr: forall (h: ctree E C X),
      rr [h] ≅ x <- preempt 0 1 h ;; Guard (rr [x]).
  Proof.
    intros.
    rewrite unfold_rr.
    cbn.
    rewrite bind_bind.    
    upto_bind_eq.
    now rewrite bind_ret_l.
  Qed.

  Lemma unfold_Sn_rr {n}:
    forall (h: ctree E C X) (ts: vec (S n) (ctree E C X)),
      rr (h :: ts) ≅
         (x <- preempt (S n) 1 h ;;
          xs <- rr' ts ;;
          Guard (rr (x :: xs))).
  Proof.
    destruct n; intros; rewrite unfold_rr.
    - repeat dependent destruction ts. 
      cbn.
      rewrite !bind_bind.
      upto_bind_eq.
      rewrite !bind_bind.
      upto_bind_eq.
      now rewrite !bind_ret_l.
    - do 2 dependent destruction ts.
      simpl.
      repeat (rewrite !bind_bind; upto_bind_eq).
      rewrite !bind_ret_l.
      reflexivity.
  Qed.

End RR.

(* Fair parallel composition *)
(*| Fair parallel operator, warning: not associative |*)
(*| A || B -> br (A^* ; B) (B^*; A) *) (* (A || B) || C == A || (B || C) *)
Definition fair{E C X}`{B1 -< C}`{B2 -< C}`{BN -< C} : 
  ctree E C X -> ctree E C X -> ctree (E +' parE) C X :=
  cofix R (P : ctree E C X) (Q : ctree E C X) :=
    brD2 
      (n <- branch false (branchN) ;;
       p <- preempt 0 n P ;;
       q <- preempt 1 1 Q ;;
       R p q)
      (n <- branch false (branchN) ;;
       q <- preempt 1 n Q ;;
       p <- preempt 0 1 P ;;
       R p q).

Notation fair_ P Q :=
  (brD2
      (n <- branch false (branchN) ;;
       p <- preempt 0 n P ;;
       q <- preempt 1 1 Q ;;
       fair p q)
      (n <- branch false (branchN) ;;
       q <- preempt 1 n Q ;;
       p <- preempt 0 1 P ;;
       fair p q)
   ).

Lemma unfold_fair {E C X}`{B1 -< C}`{B2 -< C}`{BN -< C}:
  forall (a: ctree E C X) (b: ctree E C X),
    (fair a b) ≅ (fair_ a b).
Proof. intros; step; cbn; auto. Qed.


Section FairFacts.
  Context {E C: Type -> Type}{HasStuck: B0 -< C} {HasTau: B1 -< C}.

  Lemma rr_is_fair:
    forall (n: nat) (v: vec (S n) (ctree E C void)) l,
      rr v, l |= AG (AF (obs_id n)).
    Proof.
      Opaque Take.take.
      coinduction R CIH.
      induction n; intros; econstructor.
      - (* i = 1, AF *)
        repeat dependent destruction v. (* v = [h] *)
        rewrite unfold_0_rr,
          unfold_Sn_preempt,
          bind_bind.
        apply ctl_af_ax; right; unfold ax; cbn; intros * TR.
        eapply trans_trigger_inv in TR as ([] & ? & ->).
        now apply MatchA.
      - (* i = 1, { AG } *)
        do 2 dependent destruction v. (* v = h :: ts *)
        intros.
        rewrite unfold_0_rr,
          unfold_Sn_preempt,
          bind_trigger,
          bind_vis in H.
        apply trans_vis_inv in H as ([] & ? & ->).
        step; econstructor.
        + now apply MatchA.
        + intros.
          (* Magic induction incantation *)
          unfold trans, transR in H0; cbn in H0.
          remember (observe t') as obst'.
          remember (observe t'0) as obst'0.
          revert t'0 Heqobst'0  t' Heqobst' h H.  
          induction H0; try contradiction; intros; cbn in t', t'0; subst.            
          * eapply IHtrans_; auto. 
            rewrite (ctree_eta t') in H.
            rewrite <- Heqobst' in H.            
            desobs h; try contradiction.
            -- rewrite bind_vis in H; step in H; inv H.
            -- destruct vis; rewrite bind_br in H.
               ++ step in H; inv H.
               ++ apply equ_br_invT in H as H1.
                  destruct H1 as (-> & _).
                  apply equ_br_invE in H as (-> & ?).                    
                  rewrite H.
                  instantiate (1:= BrD _ _).
                  cbn.
                  Fail rewrite (ctree_eta (k0 x)). (* why this fails? *)
                  admit.
          * rewrite (ctree_eta t') in H0.
            rewrite <- Heqobst' in H0.
            desobs h; try contradiction.
            -- rewrite bind_vis in H0; step in H0; inv H0.
            -- destruct vis; rewrite bind_br in H0.
               ++ apply equ_br_invT in H0 as H1.
                  destruct H1 as (-> & _).
                  apply equ_br_invE in H0 as (-> & ?).
                  apply observe_equ_eq in Heqobst'0. 
                  rewrite <- Heqobst'0 in *; clear t'0 Heqobst'0.
                  rewrite <- H, H0.
                  rewrite unfold_0_take,
                    translate_ret,
                    bind_ret_l,
                    ctl_t_ag_af_guard.
                  apply CIH.
               ++ step in H0; inv H0.
          * apply observe_equ_eq in Heqobst'0.
            rewrite <- Heqobst'0 in *; clear t'0 Heqobst'0.
            rewrite (ctree_eta t') in H0.
            rewrite <- Heqobst' in H0.
            rewrite <- H.
            desobs h; try contradiction.
            -- rewrite bind_vis in H0.
               apply equ_vis_invT in H0 as H1; subst.
               apply equ_vis_invE in H0 as (-> & ?).
               rewrite H0.
               rewrite unfold_0_take,
                    translate_ret,
                    bind_ret_l,
                    ctl_t_ag_af_guard.
               apply CIH.
            -- destruct vis; rewrite bind_br in H0; step in H0; inv H0.
      - (* i = S n, AF *)
        dependent destruction v.
        rewrite unfold_Sn_rr,
          unfold_Sn_preempt,
          bind_bind.
        apply ctl_af_ax; right; unfold ax; cbn; intros * TR.
        eapply trans_trigger_inv in TR as ([] & ? & ->).
        now apply MatchA.
      - (* i = S n, { AG } *)
        do 2 dependent destruction v. (* v = h :: ts *)
        intros.
        rewrite unfold_Sn_rr,
          unfold_Sn_preempt,
          bind_trigger,
          bind_vis in H.
        apply trans_vis_inv in H as ([] & ? & ->).
        step; econstructor.
        + now apply MatchA.
        + intros.
          (* Magic induction incantation *)
          unfold trans, transR in H0; cbn in H0.
          remember (observe t') as obst'.
          remember (observe t'0) as obst'0.
          revert t'0 Heqobst'0  t' Heqobst' h H.  
          induction H0; try contradiction; intros; cbn in t', t'0; subst.            
          * eapply IHtrans_; auto. 
            rewrite (ctree_eta t') in H.
            rewrite <- Heqobst' in H.            
            desobs h; try contradiction.
            -- rewrite bind_vis in H; step in H; inv H.
            -- destruct vis; rewrite bind_br in H.
               ++ step in H; inv H.
               ++ apply equ_br_invT in H as H1.
                  destruct H1 as (-> & _).
                  apply equ_br_invE in H as (-> & ?).                    
                  rewrite H.
                  instantiate (1:= BrD _ _).
                  cbn.
                  Fail rewrite (ctree_eta (k0 x)). (* why this fails? *)
                  admit.
          * rewrite (ctree_eta t') in H0.
            rewrite <- Heqobst' in H0.
            desobs h; try contradiction.
            -- rewrite bind_vis in H0; step in H0; inv H0.
            -- destruct vis; rewrite bind_br in H0.
               ++ apply equ_br_invT in H0 as H1.
                  destruct H1 as (-> & _).
                  apply equ_br_invE in H0 as (-> & ?).
                  apply observe_equ_eq in Heqobst'0. 
                  rewrite <- Heqobst'0 in *; clear t'0 Heqobst'0.
                  rewrite <- H, H0; clear H H0.
                  rewrite unfold_0_take,
                    translate_ret,
                    bind_ret_l.
                  dependent destruction v; cbn.
                  ** rewrite bind_bind,
                       unfold_Sn_preempt,
                       bind_trigger,
                       bind_vis.
                     desobs h0; try contradiction.
                     --- 
                     admit.
                  ** admit.
               ++ step in H0; inv H0.
          * apply observe_equ_eq in Heqobst'0.
            rewrite <- Heqobst'0 in *; clear t'0 Heqobst'0.
            rewrite (ctree_eta t') in H0.
            rewrite <- Heqobst' in H0.
            rewrite <- H.
            desobs h; try contradiction.
            -- rewrite bind_vis in H0.
               apply equ_vis_invT in H0 as H1; subst.
               apply equ_vis_invE in H0 as (-> & ?).
               rewrite H0.
               rewrite unfold_0_take,
                    translate_ret,
                 bind_ret_l.
               cbn.
               admit.
            -- destruct vis; rewrite bind_br in H0; step in H0; inv H0.
    Admitted.
  End FairFacts.
