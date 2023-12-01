From ExtLib Require Import
  Structures.MonadWriter
  Structures.Monads
  Structures.MonadState
  Data.Monads.StateMonad.

From Coq Require Import
  List
  Basics
  Fin
  Relations.Relation_Definitions
  Classes.SetoidClass
  Classes.RelationPairs.

From CTree Require Import
  CTree.Core
  CTree.Pred
  CTree.Equ
  CTree.Trans
  Events.Writer
  Logic.Kripke
  Events.Writer.

Generalizable All Variables.

Import Ctree CTreeNotations.
Local Open Scope ctree_scope.

(*| [Bar E] is the dependent product of an event [e: E] and its response (x: encode e) |*)
Variant Bar (E: Type) `{Encode E} :=
  | Obs (e: E) (x: encode e).

Arguments Obs {E} {_} e x.

Notation ctreeW W := (ctree (writerE W)).
Notation ctreeEW E := (ctree (writerE (Bar E))).

Section CTreeTrans.
  Context {E: Type} `{HE: Encode E} {X: Type}.
  Notation opt E := (option (Bar E)).

  Variant ktrans_: relation (ctree E X * opt E) :=    
    | KtransObs (ts: opt E) (e: E) (x: encode e)
        (t t': ctree E X):
      trans (obs e x) t t' ->
      ktrans_ (t, ts) (t', Some (Obs e x))
    | KtransTau (ts: opt E) (t t': ctree E X):
      trans tau t t' ->
      ktrans_ (t, ts) (t', ts).

  (*| DELETE ME, replace with [ktrans_trans_ind] that is amenable to induction |*)
  Lemma ktrans_trans: forall t t' w w',
      ktrans_ (t, w) (t', w') <->
      (trans tau t t' /\ w = w')
      \/ (exists e (x: encode e), trans (obs e x) t t' /\ w' = Some (Obs e x)).
  Proof.
    intros; split; intro H.
    inv H.    
    - right; exists e, x; auto.
    - left; auto.
    - destruct H as [(? & ->) | (? & ? & ? & ->)].
      + now apply KtransTau.
      + now apply KtransObs.
  Qed.

  (*| This version is more amenable to induction |*)
  Lemma ktrans_trans_ind: forall t t' w w',
      ktrans_ (t, w) (t', w') <->
        (exists l, trans_ l (observe t) (observe t') /\
                ((l = tau /\ w' = w)
                 \/ (exists e (x: encode e), l = obs e x /\ w' = Some (Obs e x)))).
  Proof.
    intros; split; intro H.
    inv H. 
    - exists (obs e x); split; auto.
      right; exists e, x; auto.
    - exists tau; split; auto.
    - destruct H as (l & H & [(-> & ->) | (e & x & -> & ->)]). 
      + now apply KtransTau.
      + now apply KtransObs.
  Qed.
  
  Global Instance trans_equ_proper:
    Proper (equ eq * eq ==> equ eq * eq ==> iff) ktrans_.
  Proof.
    unfold Proper, respectful, RelCompFun, fst, snd;
      cbn; intros.
    destruct2 H0; destruct2 H; destruct x, y, x0, y0; subst.
    split; intros TR; inv TR.
    - apply KtransObs; now rewrite <- Heqt0, <- Heqt. 
    - apply KtransTau; now rewrite <- Heqt0, <- Heqt.
    - apply KtransObs; now rewrite Heqt0, Heqt.
    - apply KtransTau; now rewrite Heqt0, Heqt.
  Qed.
End CTreeTrans.

(** This import messes up instance resolution for [equ eq] *)
From CTree Require Import CTree.SBisim.

Ltac ktrans_inv H :=
  let Heqw := fresh "Heqw" in
  let e := fresh "e" in
  let x := fresh "x" in
  simpl ktrans in H; apply ktrans_trans in H as [(H & Heqw) | (e & x & H & Heqw)]; subst.

Ltac ktrans_goal :=
  simpl ktrans; apply ktrans_trans.

Global Hint Constructors ktrans_: core.

Section CTreeTrans.
  Context {E: Type} `{HE: Encode E}.
  Local Open Scope ctl_scope.
  Notation opt E := (option (Bar E)).
  
  (*| CTree is a kripke automaton with [Sb] equivalence |*)
  Global Program Instance ctree_kripke : Kripke (ctree E) (opt E) :=
    {|
      ktrans X := ktrans_ (X:=X);
      mequ X := @sbisim E E HE HE X X eq
    |}.
  Next Obligation.
    ktrans_inv H0.
    - destruct (SBisim.sbisim_trans (X:=X) _ _ _ tau eq H H0)
        as (l & c1' & ? & <- & ?).
      exists c1'; split; [econstructor|]; auto.      
    - destruct (SBisim.sbisim_trans (X:=X) _ _ _ (obs e x) eq H H0)
        as (l & c1' & ? & <- & ?).
      exists c1'; split; [econstructor|]; auto.
  Qed.

  (*| Lemmas that depend on structure of [ctrees] |*)
  Lemma ktrans_brD {X}: forall n (t': ctree E X) (k: fin' n -> ctree E X) w w',
      (BrD n k, w) ↦ (t', w') <->
        (exists (i: fin' n), (k i, w) ↦ (t', w')).
  Proof.
    split; intro H.
    - ktrans_inv H; apply trans_brD_inv in H as (n' & ?); exists n'; ktrans_goal.
      + left; auto.
      + right; exists e, x; auto.
    - destruct H as (n' & H); ktrans_inv H; ktrans_goal.
      + left; split; [econstructor | reflexivity]; apply H. 
      + right; exists e, x; esplit; [econstructor | reflexivity]; apply H. 
  Qed.

  Lemma ktrans_brS {X}: forall n (t: ctree E X)
                          (k: fin' n -> ctree E X) w w',
      (BrS n k, w) ↦ (t, w') <->
        (exists (i: fin' n), t ≅ k i /\ w = w').
  Proof.
    split; intro H.
    - ktrans_inv H; apply trans_brS_inv in H as (n' & ? & ?);
        exists n'; subst; inv H0; auto.
    - destruct H as (n' & H & ->).
      ktrans_goal.
      left; split; auto.
      econstructor.
      (* HACK *)
      Set Typeclasses Filtered Unification.
      symmetry.
      Unset Typeclasses Filtered Unification.
      apply H.
  Qed.
  
  Lemma ktrans_guard {X}: forall (t t': ctree E X) s s',
      (guard t, s) ↦ (t', s') <-> (t, s) ↦ (t', s').
  Proof.
    intros; split; intros.
    - now apply ktrans_brD in H as (i & ?). 
    - apply ktrans_brD; now (exists (F1)).
  Qed.

  Lemma ktrans_ret {X}: forall (t: ctree E X) s s' x,
      (Ret x, s) ↦ (t, s') -> False.
  Proof.
    intros.
    ktrans_inv H; inv H.
  Qed.

  Lemma ktrans_vis {X}: forall (t: ctree E X) s s' e (k: encode e -> ctree E X),
    (Vis e k, s) ↦ (t, s') <->
      (exists (x: encode e), k x ≅ t /\ s' = Some (Obs e x)).
  Proof.
    intros; split; intro TR.
    - ktrans_inv TR.
      + inv TR.
      + cbn in TR.
        unfold trans in TR.
        dependent induction TR.        
        exists x0; split. 
        * step; step in H; cbn in *; rewrite <- x; auto.
        * reflexivity.
    - destruct TR as (? & ? & ->).
      ktrans_goal.
      right; exists e, x; split; [econstructor|]; auto.
  Qed.

  Lemma ktrans_bind_inv_strong: forall {X Y} (w w': opt E)
                           (t: ctree E Y) (u: ctree E X) (k: Y -> ctree E X),
      (x <- t ;; k x, w) ↦ (u, w') ->
      (exists t', (t, w) ↦ (t', w') /\ u ≅ x <- t' ;; k x) \/
        (exists x, only_ret t x /\ (k x, w) ↦ (u, w')).
  Proof.
    intros * TR.
    apply ktrans_trans_ind in TR as (l & TR & [(-> & ->) | ?]);
    destruct (trans_bind_inv _ _ TR) as
      [(Hv & t' & TR' & Heq) | (x' & TRv & TR')].
    - left; exists t'; split; cbn; auto.
    - 
  Admitted.
  
  Lemma ktrans_bind_inv: forall {X Y} (w w': opt E)
                           (t: ctree E Y) (u: ctree E X) (k: Y -> ctree E X),
      (x <- t ;; k x, w) ↦ (u, w') ->
      (exists t', (t, w) ↦ (t', w') /\ u ≅ x <- t' ;; k x) \/
        (exists x, may_ret t x /\ (k x, w) ↦ (u, w')).
  Proof.
    intros * TR.
    ktrans_inv TR; destruct (trans_bind_inv _ _ TR) as
      [(Hv & t' & TR' & Heq) | (x' & TRv & TR')].
    + left; exists t'; split; cbn; auto.
    + right; exists x'; split; cbn; auto.
    + left; exists t'; split; cbn; auto.
    + right; exists x'; split; cbn; auto.
  Qed.

  Lemma ktrans_bind_l:forall {X Y} (w w': opt E)
                           (t t': ctree E Y) (k: Y -> ctree E X),
      (t, w) ↦ (t', w') ->
      (x <- t ;; k x, w) ↦ (x <- t' ;; k x, w').
  Proof.
    intros.
    ktrans_inv H; apply ktrans_trans_ind.    
    - exists tau; split. (* BrS *)
      + apply trans_bind_l.
        * intro Hcontra.
          inversion Hcontra.
        * apply H. 
      + left; auto. 
    - exists (obs e x); split. (* Vis *)
      + apply trans_bind_l.
        * intro Hcontra.
          inversion Hcontra.
        * apply H. 
      + right; eauto.
  Qed.

  Lemma ktrans_bind_r: forall {X Y} (w w': opt E)
                         (t: ctree E Y) (u: ctree E X) (k: Y -> ctree E X) (x: Y),
      may_ret t x ->
      (k x, w) ↦ (u, w') ->
      (x <- t ;; k x, w) ↦ (u, w').
  Proof.
    intros.
    ktrans_inv H0; apply ktrans_trans_ind.
    - exists tau; split.
      + apply trans_bind_r with x; eauto.
      + left; auto.
    - exists (obs e x0); split.
      + apply trans_bind_r with x; eauto.
      + right; eauto.
  Qed.

  Lemma ktrans_bind_inv_l: forall {X Y} (w w': opt E)
                             (t: ctree E Y) (u: ctree E X) (k: Y -> ctree E X),
      (x <- t ;; k x, w) ↦ (u, w') ->
      ~ (exists (x: Y), may_ret t x) ->
      (exists t', (t, w) ↦ (t', w') /\ u ≅ x <- t' ;; k x).
  Proof.
    intros.
    apply ktrans_bind_inv in H.
    destruct H as [(? & ?) | (x0 & Hret & Hcont)]; eauto.
    exfalso.
    apply H0.
    now exists x0.
  Qed.

  Lemma ktrans_bind_inv_noret{X Y}: forall (w w': opt E)
     (t: ctree E X) (u: ctree E Y) (u': ctree E Y),
      (t ;; u, w) ↦ (u', w') ->
      (exists t', (t, w) ↦ (t', w') /\ u' ≅ t' ;; u) \/
        (exists (x: X), may_ret t x /\ (u, w) ↦ (u', w')).
  Proof.
    intros.
    apply ktrans_bind_inv in H.
    destruct H as [(? & ?) | (x0 & Hret & Hcont)]; eauto.
  Qed.

  Hint Extern 2 =>
         match goal with
         | [ H: ?m ↦ ?m' |- can_step ?m ] => exists (fst m'), (snd m'); apply H
  end: core.

  Lemma can_step_bind_inv_l{X Y}: forall (t: ctree E Y) (k: Y -> ctree E X) w,
      can_step (x <- t ;; k x, w) ->
      ~ (exists x, may_ret t x) ->
      can_step (t, w).
  Proof.
    intros.
    unfold can_step. 
    destruct H as (t' & w' & TR).
    destruct (ktrans_bind_inv_l _ _ _ _ _ TR); auto.
    destruct H.
    now (exists x, w').
  Qed.
  
  (*| DELETE this weak version after completing the proof [ktrans_bind_inv_strong] |*)
  Lemma can_step_bind_inv{X Y}: forall (t: ctree E Y) (k: Y -> ctree E X) w,
      can_step (x <- t ;; k x, w) ->
      can_step (t, w) \/ (exists x, may_ret t x /\ can_step (k x, w)).
  Proof.    
    intros.    
    destruct H as (t' & w' & TR).    
    destruct (ktrans_bind_inv _ _ _ _ _ TR) as [(t0 & ? & ?) | (x0 & ?)].
    - left.
      now (exists t0, w').
    - destruct H as (Hret & TR').
      right.
      exists x0; split; eauto.
  Qed.
  
  (*| Keep this strong version |*)
  Lemma can_step_bind_inv_strong{X Y}: forall (t: ctree E Y) (k: Y -> ctree E X) w,
      can_step (x <- t ;; k x, w) ->
      can_step (t, w) \/ (exists x, only_ret t x /\ can_step (k x, w)).
  Proof.    
    intros.    
    destruct H as (t' & w' & TR).    
    destruct (ktrans_bind_inv_strong _ _ _ _ _ TR)
      as [(t0 & ? & ?) | (x0 & ?)].
    - left.
      now (exists t0, w').
    - destruct H as (Hret & TR').
      right.
      exists x0; split; eauto.
  Qed.

  (*| If [t] steps then [t >>= k] steps |*)
  Lemma can_step_bind_l{X Y}: forall (t: ctree E Y) (k: Y -> ctree E X) w,
      can_step (t, w) ->
      can_step (x <- t;; k x, w).
  Proof.
    intros.
    destruct H as (t' & w' & TR).
    exists (x <- t';; k x), w'.
    now apply ktrans_bind_l.
  Qed.
  Hint Resolve can_step_bind_l: core.
  
  (*| If there exists a [t -(val x)-> t'] transition,
      and [k x] can step then [t >>= k] can step |*)
  Lemma can_step_bind_r{X Y}: forall (t: ctree E Y) (k: Y -> ctree E X) w x,
      may_ret t x ->
      can_step (k x, w) ->
      can_step (x <- t;; k x, w).
  Proof.
    intros.
    destruct H0 as (t' & w' & TR).
    exists t', w'.
    apply ktrans_bind_r with x; auto.
  Qed.
  Hint Resolve can_step_bind_r: core.

  
    (*| [can_step] and [only_ret] are mutually exclusive |*)
  Lemma can_step_only_ret{X}: forall (t: ctree E X) w,
      can_step (t, w) ->  ~ (exists x, only_ret t x).
  Proof.
    intros * (? & ? & ?) (? & Hcontra).
    unfold only_ret in Hcontra.
    apply ktrans_trans_ind in H as (l & TR & ?).
    remember (observe t) as T.
    generalize dependent t.
    generalize dependent H.
    generalize dependent TR.
    revert l x0 x w.
    induction Hcontra; intros.
    - (* OnlyBrD *)
      apply trans_brD_inv in TR as (i & ?).
      eapply H0; eauto.
    - (* OnlyRet *)
      apply trans_ret_inv in TR as (? & ->).
      destruct H as [(? & ?) | (? & ? & ? & ? )];
        inversion H.
  Qed.
  Hint Resolve can_step_only_ret: core.
  
  Lemma only_ret_can_step{X}: forall (t: ctree E X) x,
      only_ret t x -> ~ (exists w, can_step (t, w)).
  Proof.
    intros.
    unfold only_ret in H.
    unfold can_step.
    setoid_rewrite ktrans_trans_ind.
    dependent induction H; rewrite <- x.
    - (* OnlyBrD *)
      intros (e & t' & e' & l & TR & Hl).
      apply trans_brD_inv in TR as (i & ?).
      eapply H0 with (i:=i).
      + reflexivity.
      + do 4 eexists; split; eauto.
    - (* OnlyRet *)
      intros (e & t' & e' & l & TR & Hl).
      apply trans_ret_inv in TR as (? & ->).
      destruct Hl as [(Hcontra & ->)|(? & ? & Hcontra & ?)];
        inversion Hcontra.
  Qed.
  Hint Resolve only_ret_can_step: core.
  
  (*| [ktrans] with [bind] of [only_ret] means [k x] must step |*)
  Lemma ktrans_bind_inv_r_strong{X Y}: forall (w w': opt E) (t: ctree E Y)
                                (u: ctree E X) (k: Y -> ctree E X) r,
    (x <- t;; k x, w) ↦ (u, w') ->
    only_ret t r ->
    (k r, w) ↦ (u, w').
  Proof.
    intros.
    apply ktrans_bind_inv_strong in H as [(? & ? & Heq) | (x & ? & H')].
    - apply only_ret_can_step in H0.
      exfalso.
      apply H0.
      exists w; eauto.
    - pose proof (only_ret_det _ _ _ H H0); subst.
      apply H'.
  Qed.
  Hint Resolve ktrans_bind_inv_r_strong: core.

  Lemma ktrans_bind_inv_l_strong{X Y}: forall (w w' : opt E) (t : ctree E Y)
                                  (u : ctree E X) (k : Y -> ctree E X),
      (x <- t;; k x, w) ↦ (u, w') ->
      can_step (t, w) ->
      exists t' : ctree E Y, (t, w) ↦ (t', w') /\ u ≅ x <- t';; k x.
  Proof.
    intros.
    apply ktrans_bind_inv_strong in H as [(t' & ? & Heq) | (x & ? & H')].
    - exists t'; auto.
    - apply only_ret_can_step in H.
      exfalso.
      apply H.
      now (exists w).
  Qed.
  Hint Resolve ktrans_bind_inv_l_strong: core.
  
  Lemma ktrans_bind_r_strong{X Y}: forall (w w': opt E) (t: ctree E Y)
                                       (u: ctree E X) (k: Y -> ctree E X) r,
      (k r, w) ↦ (u, w') ->
      only_ret t r ->
      (x <- t;; k x, w) ↦ (u, w').
  Proof.
    intros.
    apply ktrans_trans_ind in H as (l & ? & ?).
    pose proof (trans_onlyret _ _ H0).
    unfold only_ret in H0.
    dependent induction H0; apply ktrans_trans_ind.
    - exists l; split.
      now apply trans_bind_r with x0.
      apply H1.
    - exists l; split.
      now apply trans_bind_r with x0.
      apply H1.
  Qed.
  Hint Resolve ktrans_bind_r_strong: core.

  Lemma can_step_bind_r_strong{X Y}: forall (t: ctree E Y) (k: Y -> ctree E X) w x,
      only_ret t x ->
      can_step (k x, w) ->
      can_step (x <- t;; k x, w).
  Proof.
    intros.
    destruct H0 as (t' & w' & TR).
    exists t', w'.
    apply ktrans_bind_r_strong with x; auto.
  Qed.
  Hint Resolve can_step_bind_r: core.
  
  (*
  Lemma ktrans_trigger_inv_noret: forall {X} (w w': opt E) (e: E)
                                 (u: ctree E X) (u': ctree E X),
      (trigger e ;; u, w) ↦ (u', w') ->
      exists (x: encode e), u' ≅ u /\ w' = Some (Obs e x).
  Proof.    
    intros.
    apply ktrans_bind_inv in H.
    destruct H as [(t' & ? & ?) | (x0 & Hret & Hcont)].
    - unfold trigger in H.      
      apply ktrans_vis in H as (x & ? & ->).
      unfold resum, resum_ret, ReSum_refl, ReSumRet_refl in *.
      exists x; split; [|reflexivity].
      rewrite H0, <- H, bind_ret_l. (** WHY DO THESE REWRITES TAKE SO LONG? *)
      

      (* TO DEBUG unification
         ---------------------
        Set Debug "unification,tactic-unification".

         TRIED BUT DID NOT HELP
         ----------------------
        Set Typeclasses Iterative Deepening.
        Remove Hints Eq.SBisim.equ_sbisim_subrelation: typeclass_instances.
        Typeclasses eauto := debug 6.       
       *)
      Set Typeclasses Filtered Unification.
      reflexivity.
      Unset Typeclasses Filtered Unification.
      - inv Hret.
  Qed. *)

  (*| [Some e] always transitions to [Some e'] |*)
  Lemma ktrans_some_inv {X}:
    forall (e : Bar E) (t: ctree E X) (m: ctree E X * opt E),
      (t, Some e) ↦ m ->
      exists e', snd m = Some e'.  
  Proof. intros; inv H; eauto. Qed.
  
End CTreeTrans.

From CTree Require Import Logic.Semantics.
Check ctl_contramap.
Notation "m |=e φ " :=
  (entailsF
     (ctl_contramap (fun '(Obs (Log e) _) => e)
        (ctl_option φ))
     m)
    (in custom ctl at level 81,
        φ custom ctl,
        right associativity): ctl_scope.
