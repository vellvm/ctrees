(** * Properties of [Recursion.mrec] and [Recursion.rec]. *)

(** The main facts to take away are [mrec_as_interp] and [rec_as_interp]:
    [mrec] and [rec] are special cases of [interp], using [mrecursive] and
    [recursive] as handlers.
 *)

From ExtLib Require Import
     Structures.Functor
     Structures.Monad.

Unset Universe Checking.
From CTree Require Import
  CTreeDefinitions
  Eq
  Eq.Epsilon
  Eq.SSimAlt
  Eq.SBisimAlt
  Interp.Fold
  Interp.FoldCTree
  Misc.Pure
  Recursion.


Import CTreeNotations.
Open Scope ctree_scope.

From Stdlib Require Import
     Program.Tactics
     Setoid
     Morphisms
     RelationClasses.

From ITree Require Import
     Basics.Utils
     Basics.Category
     Basics.Basics
     Basics.Function
     Indexed.Sum
     Indexed.Function
     Indexed.Relation.

Import CoindNotations.

Section Facts.

Context {D E B : Type -> Type} (ctx : D ~> ctree (D +' E) B).

(** Unfolding of [interp_mrec]. *)

Definition _interp_mrec {R : Type} (ot : ctreeF (D +' E) B R _) : ctree E B R :=
  match ot with
  | RetF r => Ret r
  | StuckF => Stuck
  | StepF t => Step (Guard (interp_mrec ctx t))
  | GuardF t => Guard (interp_mrec ctx t)
  | VisF e k => 
    match e with
    | inl1 d => Guard (interp_mrec ctx (ctx _ d >>= k))
    | inr1 e => Vis e (fun x => Guard (interp_mrec ctx (k x)))
    end
  | BrF c k => Br c (fun x => Guard (interp_mrec ctx (k x)))
  end.

Lemma unfold_interp_mrec R (t : ctree (D +' E) B R) :
  interp_mrec ctx t ≅ _interp_mrec (observe t).
Proof.
  unfold interp_mrec.
  rewrite unfold_iter.
  destruct observe; cbn.
  - rewrite bind_ret_l; reflexivity.
  - rewrite bind_stuck; reflexivity.
  - rewrite bind_step. rewrite bind_ret_l.
    step. constructor.
    step. constructor. reflexivity.
  - rewrite bind_ret_l; reflexivity.
  - destruct e; cbn.
    + rewrite bind_ret_l; reflexivity.
    + rewrite bind_vis.
      step. constructor. intros.
      rewrite bind_ret_l. 
      reflexivity.
  - rewrite bind_br.
    step. constructor. intros.
    rewrite bind_ret_l.
    reflexivity.
Qed.

(** [mrec ctx] is equivalent to [interp (mrecursive ctx)],
    where [mrecursive] is defined as follows. *)
Definition mrecursive (f : D ~> ctree (D +' E) B)
  : (D +' E) ~> ctree E B :=
  case_ (mrec f) CTree.trigger.

Global Instance eq_itree_mrec {R} :
  Proper (equ eq ==> equ eq) (@interp_mrec _ _ _ ctx R).
Proof.
  cbn.
  coinduction C CIH.
  intros.
  rewrite !unfold_interp_mrec.
  step in H. inv H; cbn; try econstructor.
  - reflexivity.
  - eapply CIH; eauto.
  - step. constructor. eapply CIH; auto.
  - destruct e.
    + constructor.
      apply CIH.
      upto_bind_eq. assumption.
    + constructor.
      intros.
      step.
      constructor.
      apply CIH.
      apply REL.
  - intros.
    step. constructor. apply CIH. apply REL.
Qed.

Theorem interp_mrec_bind {U T} (t : ctree _ B U) (k : U -> ctree _ B T) :
  interp_mrec ctx (CTree.bind t k) ≅
  CTree.bind (interp_mrec ctx t) (fun x => interp_mrec ctx (k x)).
Proof.
  revert t k.
  coinduction C CIH.
  intros t k.
  rewrite (unfold_interp_mrec _ t).
  rewrite (unfold_bind t). 
  destruct (observe t); cbn.
  - rewrite bind_ret_.
    reflexivity.
  - reflexivity.
  - constructor. fold_subst.
    rewrite bind_ret_l.
    rewrite bind_guard.
    step. constructor. apply CIH.
  - constructor. apply CIH.
  - destruct e.
    + cbn.
      constructor.
      rewrite <- bind_bind.
      apply CIH.
    + cbn. constructor.
      intros x.
      fold_subst.
      rewrite bind_guard.
      rewrite bind_ret_l.
      step. constructor.
      apply CIH.
  - constructor.
    intros x.
    fold_subst.
    rewrite bind_guard.
    rewrite bind_ret_l.
    step. constructor.
    apply CIH.
Qed.

Theorem interp_mrec_trigger {U} (a : (D +' E) U) :
    interp_mrec ctx (CTree.trigger a)
  ≲ mrecursive ctx _ a.
Proof.
  rewrite unfold_interp_mrec; unfold mrecursive.
  destruct a; cbn.
  rewrite bind_ret_r.  apply ssim_guard_l. reflexivity.
  unfold CTree.trigger.
  apply ssim_vis_id.
  intros. split; auto.
  apply ssim_guard_l. rewrite unfold_interp_mrec. cbn.  reflexivity.
Qed.

Lemma interp_mrec_guard {T} (c : ctree _ _ T) :
  Guard (interp_mrec ctx c) ~ interp_mrec ctx (Guard c).
Proof.
  rewrite (unfold_interp_mrec _ (Guard c)).
  unfold _interp_mrec, fold.
  cbn.
  reflexivity.
Qed.  



Theorem interp_mrec_as_interp {T} (c : ctree _ _ T) :
  interp_mrec ctx c ~ interp (mrecursive ctx) c.
Proof.
  rewrite <- (sb_guard (interp (mrecursive ctx) c)).
  apply sbisim_sbisim'.
  red.
  revert_until T.
  coinduction R CIH. intros.
  rewrite unfold_interp_mrec. unfold _interp_mrec, fold.
  unfold interp, fold. 
  setoid_rewrite unfold_iter.
  destruct (observe c).
  - unfold ret, Monad_ctree. 
    apply step_sb'_guard_r.
    rewrite bind_ret_l.    
    reflexivity.
  - unfold mstuck, MonadStuck_ctree. rewrite bind_stuck.
    apply step_sb'_guard_r.
    reflexivity.
  - unfold mstep, MonadStep_ctree.
    unfold fmap, Functor_ctree.  rewrite bind_map.
    apply step_sb'_guard_r.
    rewrite bind_step. rewrite bind_ret_l.
    apply step_sb'_step; auto.
    intros side'.
    apply step_sb'_guard_l'.
    intros. 
    apply CIH.
  - unfold ret, Monad_ctree. rewrite bind_ret_l.
    apply step_sb'_guard.
    apply CIH.
  - destruct e.
    + unfold mrecursive, case_, Case_sum1, case_sum1.
      unfold fmap at 1, Functor_ctree at 1.
      rewrite bind_map.
      apply step_sb'_guard.
      rewrite interp_mrec_bind.
      apply st'_clo_bind_eq. reflexivity.
      intros.
      apply CIH.
    + unfold mrecursive, case_, Case_sum1, case_sum1.
      unfold CTree.trigger. 
      unfold fmap, Functor_ctree.
      rewrite bind_map.
      rewrite bind_vis.
      setoid_rewrite bind_ret_l.
      apply step_sb'_guard_r.
      apply step_sb'_vis_id. intros. split; auto.
      intros.
      apply step_sb'_guard_l'.
      intros.
      apply CIH.
  - apply step_sb'_guard_r.
    unfold mbr, MonadBr_ctree, branch.
    unfold fmap, Functor_ctree.
    rewrite bind_map.
    rewrite bind_br.
    setoid_rewrite bind_ret_l.
    apply step_sb'_br.
    intros x. exists x.
    apply step_sb'_guard_l'.
    intros.
    apply CIH.
    intros x. exists x.
    apply step_sb'_guard_l'.
    intros.
    apply CIH.
Qed.    
    

Theorem mrec_as_interp {T} (d : D T) :
  mrec ctx d ~ interp (mrecursive ctx) (ctx _ d).
Proof.
  apply interp_mrec_as_interp.
Qed.

(* SAZ: Todo:
 - why don't typeclasses for MonadBr find the [B -< B] instance?
 - where should this live?

Lemma interp_trigger {E' D' F' C U} `{C -< D'} (h : E' ~> ctree F' D')  (e: E' U) :
  interp h (CTree.trigger e) ~ Guard (h _ e).
 *)

Lemma interp_trigger {E' F' B' U} (h : E' ~> ctree F' B')  (e: E' U) :
  interp h (@CTree.trigger _ B' _ e) ~ Guard (h _ e).
Proof.
  unfold CTree.trigger.
  rewrite interp_vis.
  setoid_rewrite interp_ret.
  setoid_rewrite sb_guard.
  rewrite bind_ret_r.
  reflexivity.
Qed.

Lemma interp_mrecursive {T} (d : D T) :
  interp (mrecursive ctx) (@trigger_inl1 D E B _ d) ~ mrec ctx d.
Proof.
  unfold mrecursive. unfold trigger_inl1.
  rewrite interp_trigger.
  cbn.
  setoid_rewrite sb_guard.
  reflexivity.
Qed.

(* SAZ: not sure where this is needed, and the typeclasses around `bif` don't seem to work.

 *)
(*
Theorem unfold_interp_mrec_h {T} (t : ctree (D +' E) B T)
  : interp_mrec ctx (interp (case_ ctx inr_) t)
  ~ interp_mrec ctx t.
Proof.
  rewrite <- tau_eutt.
  revert t. ginit; gcofix CIH. intros.
  rewrite (itree_eta t); destruct (observe t);
    try (rewrite 2 unfold_interp_mrec; cbn; gstep; repeat constructor; auto with paco; fail).
  rewrite interp_vis.
  rewrite (unfold_interp_mrec _ (Vis _ _)).
  destruct e; cbn.
  - rewrite 2 interp_mrec_bind.
    gstep; constructor.
    guclo eqit_clo_bind; econstructor; [reflexivity|].
    intros ? _ []; rewrite unfold_interp_mrec; cbn; auto with paco.
  - unfold inr_, Handler.Inr_sum1_Handler, Handler.Handler.inr_, Handler.Handler.htrigger.
    rewrite bind_trigger, unfold_interp_mrec; cbn.
    rewrite tau_euttge.
    gstep; constructor.
    intros; red. gstep; constructor.
    rewrite unfold_interp_mrec; cbn.
    auto with paco.
Qed.
*)
End Facts.



Global Instance Proper_interp_mrec {D E B} :
  @Proper ((D ~> ctree (D +' E) B) -> (ctree (D +' E) B ~> ctree E B))
          (Relation.i_pointwise (fun _ => sbisim eq) ==>
           Relation.i_respectful (fun _ => sbisim eq) (fun _ => sbisim eq))
          interp_mrec.
Proof.
  
  intros f g Hfg R t1 t2 H.
  apply sbisim_sbisim'. 
  revert t1 t2 H.
Admitted.

Local Opaque interp_mrec.


(** [rec body] is equivalent to [interp (recursive body)],
    where [recursive] is defined as follows. *)
Definition recursive {E B } {X Y} (f : X -> ctree (callE X Y +' E) B Y) : (callE X Y +' E) ~> ctree E B :=
  case_ (calling' (rec f)) CTree.trigger.

(* SAZ: TODO - update this after the change to sbisim *)
Lemma rec_as_interp {E B} {X Y} (f : X -> ctree (callE X Y +' E) B Y) (x : X) :
  rec f x ~ interp (recursive f) (f x).
Proof.
  unfold rec.
  rewrite mrec_as_interp.
Admitted.

Lemma interp_recursive_call {E B} {X Y} (f : X -> ctree ((callE X Y) +' E) B Y) (x:X) :
  interp (recursive f) (@call E B X Y x) ~ rec f x.
Proof.
  unfold recursive. unfold call.
  rewrite interp_trigger. cbn.
  setoid_rewrite sb_guard.
  reflexivity.
Qed.

(*
  SAZ: TODO: Not sure what the appropriate analogue of this is for ctrees
 *)
(*
Global Instance euttge_interp_mrec {D E} :
  @Proper ((D ~> ctree (D +' E)) -> (ctree (D +' E) ~> ctree E))
          (Relation.i_pointwise (fun _ => euttge eq) ==>
           Relation.i_respectful (fun _ => euttge eq) (fun _ => euttge eq))
          interp_mrec.
Proof.
  intros f g Hfg R.
  ginit; gcofix CIH; intros t1 t2 Ht.
  rewrite 2 unfold_interp_mrec.
  punfold Ht; induction Ht; cbn; pclearbot.
  3: { destruct e; gstep; constructor.
    + gfinal; left. apply CIH.
      eapply eqit_bind; auto. apply Hfg.
    + gstep; constructor. auto with paco.
  }
  1,2: gstep; constructor; auto with paco.
  1: rewrite unfold_interp_mrec, tau_euttge; auto.
  discriminate.
Qed.
*)

(*
  SAZ: TODO: Need the appropriate analogue for ctrees 
Global Instance euttge_interp_mrec' {E D R} (ctx : D ~> ctree (D +' E)) :
  Proper (euttge eq ==> euttge eq) (@interp_mrec _ _ ctx R).
Proof.
  do 4 red. eapply euttge_interp_mrec. reflexivity.
Qed.
*)
