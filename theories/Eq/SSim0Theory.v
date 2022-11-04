From Coq Require Import
     Lia Basics Fin
     RelationClasses
     Logic.Eqdep.

From Coinduction Require Import
     coinduction rel tactics.

From ITree Require Import Core.Subevent.

From CTree Require Import
     CTree
     Utils
     Eq.Equ
     Eq.SBisim
     Eq.Shallow
     Eq.Trans.

From RelationAlgebra Require Export
     rel srel.

Import CTree.

Set Implicit Arguments.

(* TODO: Decide where to set this *)
Arguments trans : simpl never.

#[local] Tactic Notation "step" := __step_sbisim || step.
#[local] Tactic Notation "coinduction" simple_intropattern(R) simple_intropattern(H) :=
  __coinduction_sbisim R H || coinduction R H.
#[local] Tactic Notation "step" "in" ident(H) := __step_in_sbisim H || step in H.

Import CTreeNotations.
Import EquNotations.
Import SBisimNotations.

Section ssim0_homogenous_theory.
  Context {E C: Type -> Type} {X: Type}
          {L: relation (@label E)}
          {HasStuck1: B0 -< C}.

  Notation ss0 := (@ss0 E E C C X X _ _).
  Notation ssim0 := (@ssim0 E E C C X X _ _).
  Notation sst0 L := (coinduction.t (ss0 L)).
  Notation ssbt0 L := (coinduction.bt (ss0 L)).
  Notation ssT0 L := (coinduction.T (ss0 L)).

  (*|
    Various results on reflexivity and transitivity.
  |*)
  Lemma refl_sst0 `{Reflexive _ L}: const seq <= (sst0 L).
  Proof.
    apply leq_t. cbn.
    intros. unfold seq in H0. subst. eauto.
  Qed.

  Lemma square_sst0 `{Transitive _ L}: square <= (sst0 L).
  Proof.
    apply Coinduction; cbn.
    intros R x z [y xy yz] l x' xx'.
    destruct (xy _ _ xx') as (l' & y' & yy' & ? & ?).
    destruct (yz _ _ yy') as (l'' & z' & zz' & ? & ?).
    exists l'', z'.
    split.
    assumption.
    split.
    apply (f_Tf (ss0 L)).
    exists y'; eauto.
    transitivity l'; auto.
  Qed.

  (*| Reflexivity |*)
  #[global] Instance Reflexive_sst0 R `{Reflexive _ L}: Reflexive (sst0 L R).
  Proof. apply build_reflexive; apply ft_t; apply (refl_sst0). Qed.

  Corollary Reflexive_ssim0 `{Reflexive _ L}: Reflexive (ssim0 L).
  Proof. now apply Reflexive_sst0. Qed.

  #[global] Instance Reflexive_ssbt0 R `{Reflexive _ L}: Reflexive (ssbt0 L R).
  Proof. apply build_reflexive; apply fbt_bt; apply refl_sst0. Qed.

  #[global] Instance Reflexive_ssT0 f R `{Reflexive _ L}: Reflexive (ssT0 L f R).
  Proof. apply build_reflexive; apply fT_T; apply refl_sst0. Qed.

  (*| Transitivity |*)
  #[global] Instance Transitive_sst0 R `{Transitive _ L}: Transitive (sst0 L R).
  Proof. apply build_transitive; apply ft_t; apply (square_sst0). Qed.

  Corollary Transitive_ssim0 `{Transitive _ L}: Transitive (ssim0 L).
  Proof. now apply Transitive_sst0. Qed.

  #[global] Instance Transitive_ssbt0 R `{Transitive _ L}: Transitive (ssbt0 L R).
  Proof. apply build_transitive; apply fbt_bt; apply square_sst0. Qed.

  #[global] Instance Transitive_ssT0 f R `{Transitive _ L}: Transitive (ssT0 L f R).
  Proof. apply build_transitive; apply fT_T; apply square_sst0. Qed.
  
  (*| PreOrder |*)
  #[global] Instance PreOrder_sst0 R `{PreOrder _ L}: PreOrder (sst0 L R).
  Proof. split; typeclasses eauto. Qed.

  Corollary PreOrder_ssim0 `{PreOrder _ L}: PreOrder (ssim0 L).
  Proof. split; typeclasses eauto. Qed.

  #[global] Instance PreOrder_ssbt0 R `{PreOrder _ L}: PreOrder (ssbt0 L R).
  Proof. split; typeclasses eauto. Qed.

  #[global] Instance PreOrder_ssT0 f R `{PreOrder _ L}: PreOrder (ssT0 L f R).
  Proof. split; typeclasses eauto. Qed.
   
  (*|
    Aggressively providing instances for rewriting hopefully faster
    [sbisim] under all [ss1]-related contexts (consequence of the transitivity
    of the companion).
    |*)
  #[global] Instance sbisim_clos_ssim0_goal `{Symmetric _ L} `{Transitive _ L} :
    Proper (sbisim L ==> sbisim L ==> flip impl) (ssim0 L).
  Proof.
    repeat intro.
    transitivity y0. transitivity y.
    - now apply sbisim_ssim0 in H1.
    - now exact H3.
    - symmetry in H2; now apply sbisim_ssim0 in H2.
  Qed.

  #[global] Instance sbisim_clos_ssim0_ctx `{Equivalence _ L}:
    Proper (sbisim L ==> sbisim L ==> impl) (ssim0 L).
  Proof.
    repeat intro. symmetry in H0, H1. eapply sbisim_clos_ssim0_goal; eauto.
  Qed.

  #[global] Instance sbisim_clos_sst_goal RR `{Equivalence _ L}:
    Proper (sbisim L ==> sbisim L ==> flip impl) (sst0 L RR).
  Proof.
    cbn; intros ? ? eq1 ? ? eq2 H0.
    symmetry in eq2. apply sbisim_ssim0 in eq1, eq2.
    rewrite eq1, <- eq2.
    auto.
  Qed.

  #[global] Instance sbisim_clos_sst_ctx RR `{Equivalence _ L}:
    Proper (sbisim L ==> sbisim L ==> impl) (sst0 L RR).
  Proof.
    cbn; intros ? ? eq1 ? ? eq2 ?.
    rewrite <- eq1, <- eq2.
    auto.
  Qed.

  #[global] Instance sbisim_clos_ssT_goal RR f `{Equivalence _ L}:
    Proper (sbisim L ==> sbisim L ==> flip impl) (ssT0 L f RR).
  Proof.
    cbn; intros ? ? eq1 ? ? eq2 ?.
    symmetry in eq2. apply sbisim_ssim0 in eq1, eq2.
    rewrite eq1, <- eq2.
    auto.
  Qed.

  #[global] Instance sbisim_clos_ssT_ctx RR f `{Equivalence _ L}:
    Proper (sbisim L ==> sbisim L ==> impl) (ssT0 L f RR).
  Proof.
    cbn; intros ? ? eq1 ? ? eq2 ?.
    rewrite <- eq1, <- eq2.
    auto.
  Qed.

End ssim0_homogenous_theory.

(*| Parametric theory of [ss0] with heterogenous [L] |*)
Section ssim0_heterogenous_theory.
  Arguments label: clear implicits.
  Context {E F C D: Type -> Type} {X Y: Type}
          {L: rel (@label E) (@label F)}
          {HasStuck1: B0 -< C} {HasStuck2: B0 -< D}.
  
  Notation ss0 := (@ss0 E F C D X Y _ _).
  Notation ssim0  := (@ssim0 E F C D X Y _ _).
  Notation sst0 L := (coinduction.t (ss0 L)).
  Notation ssbt0 L := (coinduction.bt (ss0 L)).
  Notation ssT0 L := (coinduction.T (ss0 L)).

  (*|
   Strong simulation up-to [equ] is valid
   ----------------------------------------
  |*)
  Lemma equ_clos_sst0 : equ_clos <= (sst0 L).
  Proof.
    apply Coinduction; cbn.
    intros R x y [x' y' x'' y'' EQ' EQ''] l z x'z.
    rewrite EQ' in x'z.
    destruct (EQ'' _ _ x'z) as (l' & ? & ? & ? & ?).
    exists l', x0.
    split.
    - rewrite <- Equu; auto.
    - split; auto.
      eapply (f_Tf (ss0 L)).
      econstructor; auto; auto.
  Qed.

  #[global] Instance equ_clos_sst0_goal {RR} :
    Proper (equ eq ==> equ eq ==> flip impl) (sst0 L RR).
  Proof.
    cbn; intros ? ? eq1 ? ? eq2 H.
    apply (ft_t equ_clos_sst0); econstructor; [eauto | | symmetry; eauto]; assumption.
  Qed.

  #[global] Instance equ_clos_sst0_ctx {RR} :
    Proper (equ eq ==> equ eq ==> impl) (sst0 L RR).
  Proof.
    cbn; intros ? ? eq1 ? ? eq2 H.
    apply (ft_t equ_clos_sst0); econstructor; [symmetry; eauto | | eauto]; assumption.
  Qed.

  #[global] Instance equ_ssbt0_closed_goal {r} :
    Proper (equ eq ==> equ eq ==> flip impl) (ssbt0 L r).
  Proof.
    cbn. intros.
    apply (fbt_bt equ_clos_sst0); econstructor; eauto.
    now symmetry.
  Qed.

  #[global] Instance equ_ssbt0_closed_ctx {r} :
    Proper (equ eq ==> equ eq ==> impl) (ssbt0 L r).
  Proof.
    cbn; intros.    
    now rewrite H, H0 in H1.
  Qed.

  #[global] Instance equ_clos_ssT0_goal RR f :
    Proper (equ eq ==> equ eq ==> flip impl) (ssT0 L f RR).
  Proof.
    cbn; intros ? ? eq1 ? ? eq2 H.
    apply (fT_T equ_clos_sst0); econstructor; [eauto | | symmetry; eauto]; assumption.
  Qed.

  #[global] Instance equ_clos_ssT0_ctx RR f :
    Proper (equ eq ==> equ eq ==> impl) (ssT0 L f RR).
  Proof.
    cbn; intros ? ? eq1 ? ? eq2 H.
    apply (fT_T equ_clos_sst0); econstructor; [symmetry; eauto | | eauto]; assumption.
  Qed.

  #[global] Instance equ_clos_ssim0_goal :
    Proper (equ eq ==> equ eq ==> flip impl) (ssim0 L).
  Proof.
    cbn; intros ? ? eq1 ? ? eq2 H.
    apply (ft_t equ_clos_sst0); econstructor; [eauto | | symmetry; eauto]; assumption.
  Qed.

  #[global] Instance equ_clos_ssim0_ctx :
    Proper (equ eq ==> equ eq ==> impl) (ssim0 L).
  Proof.
    cbn; intros ? ? eq1 ? ? eq2 H.
    apply (ft_t equ_clos_sst0); econstructor; [symmetry; eauto | | eauto]; assumption.
  Qed.

  #[global] Instance equ_ss0_closed_goal {r} :
    Proper (equ eq ==> equ eq ==> flip impl) (ss0 L r).
  Proof.
    intros t t' tt' u u' uu'; cbn; intros.
    rewrite tt' in H0. apply H in H0 as (l' & ? & ? & ? & ?).
    do 2 eexists; eauto. rewrite uu'. eauto.
  Qed.

  #[global] Instance equ_ss0_closed_ctx {r} :
    Proper (equ eq ==> equ eq ==> impl) (ss0 L r).
  Proof.
    intros t t' tt' u u' uu'; cbn; intros.
    rewrite <- tt' in H0. apply H in H0 as (l' & ? & ? & ? & ?).
    do 2 eexists; eauto. rewrite <- uu'. eauto.
  Qed.

  (*|
    stuck ctrees can be simulated by anything.
    |*)
  Lemma is_stuck_ss0 (R : rel _ _) (t : ctree E C X) (t': ctree F D Y):
    is_stuck t -> ss0 L R t t'.
  Proof.
    repeat intro. now apply H in H0.
  Qed.

  Lemma is_stuck_ssim0 (t: ctree E C X) (t': ctree F D Y):
    is_stuck t -> ssim0 L t t'.
  Proof.
    intros. step. now apply is_stuck_ss0.
  Qed.

  Lemma stuckD_ss0 (R : rel _ _) (t : ctree F D Y) : ss0 L R stuckD t.
  Proof.
    repeat intro. now apply stuckD_is_stuck in H.
  Qed.

  Lemma stuckD_ssim0 (t : ctree F D Y) : ssim0 L stuckD t.
  Proof.
    intros. step. apply stuckD_ss0.
  Qed.
  
  Lemma spinD_ss0 (R : rel _ _) (t : ctree F D Y) `{HasTau: B1 -< C}: ss0 L R spinD t.
  Proof.
    repeat intro. now apply spinD_is_stuck in H.
  Qed.

  Lemma spinD_ssim0 : forall (t' : ctree F D Y) `{HasTau: B1 -< C},
      ssim0 L spinD t'.
  Proof.
    intros. step. apply spinD_ss0.
  Qed.

End ssim0_heterogenous_theory.

(*|
Up-to [bind] context simulations
----------------------------------
We have proved in the module [Equ] that up-to bind context is
a valid enhancement to prove [equ].
We now prove the same result, but for strong simulation.
|*)

Section bind.
  Arguments label: clear implicits.
  Obligation Tactic := idtac.

  Context {E F C D: Type -> Type} {X X' Y Y': Type}
          `{HasStuck : B0 -< C} `{HasStuck' : B0 -< D}
          (L : hrel (@label E) (@label F)).
  (*|
    Specialization of [bind_ctx] to a function acting with [ssim] on the bound value,
    and with the argument (pointwise) on the continuation.
    |*)
  Program Definition bind_ctx_ssim0: mon (rel (ctree E C X') (ctree F D Y')) :=
    {|body := fun R => @bind_ctx E F C D X Y X' Y' (ssim0 L) (pointwise (fun x y => L (val x) (val y)) R) |}.
  Next Obligation.
    intros ?? H. apply leq_bind_ctx. intros ?? H' ?? H''.
    apply in_bind_ctx. apply H'. intros t t' HS. apply H, H'', HS.
  Qed.

  (*|
    The resulting enhancing function gives a valid up-to technique
  |*)
  Lemma bind_ctx_ssim0_t {RV: Respects_val L}: 
    bind_ctx_ssim0 <= (sst0 L).
  Proof.
    apply Coinduction.
    intros R. apply (leq_bind_ctx _).
    intros t1 t2 tt k1 k2 kk.
    step in tt.
    simpl; intros l u STEP; 
      apply trans_bind_inv in STEP as [(H & t' & STEP & EQ) | (v & STEPres & STEP)];
      cbn in *.
    apply tt in STEP as (u' & l' & STEP & EQ' & ?).
    do 2 eexists. split.
    apply trans_bind_l; eauto.
    + intro Hl. destruct Hl. apply RV in H0 as [_ ?]. specialize (H0 (Is_val _)). auto.
    + split; auto.
        apply (fT_T equ_clos_sst0).
        econstructor; [exact EQ | | reflexivity].
        apply (fTf_Tf (ss0 L)).
        apply in_bind_ctx; auto.
        intros ? ? ?.
        apply (b_T (ss0 L)).
        red in kk; cbn; now apply kk.
    + apply tt in STEPres as (u' & ? & STEPres & EQ' & ?).
      destruct RV.
      destruct (respects_val _ _ H) as [? _]. specialize (H0 (Is_val _)). destruct H0.
      pose proof (trans_val_invT STEPres); subst.
      pose proof (trans_val_inv STEPres) as EQ.
      rewrite EQ in STEPres.      
      specialize (kk v x0 H).      
      apply kk in STEP as (u'' & ? & STEP & EQ'' & ?); cbn in *.
      do 2 eexists; split.
      eapply trans_bind_r; eauto.
      split; auto.
      eapply (id_T (ss0 L)); auto.      
  Qed.

End bind.

(*|
Expliciting the reasoning rule provided by the up-to principles.
|*)
Lemma sst0_clo_bind {E F C D: Type -> Type} {X Y X' Y': Type} {L: rel (@label E) (@label F)}
      `{HasStuck: B0 -< C} `{HasStuck': B0 -< D} {RV: Respects_val L}
      (t1 : ctree E C X) (t2: ctree F D Y)
      (k1 : X -> ctree E C X') (k2 : Y -> ctree F D Y') RR:
  ssim0 L t1 t2 ->
  (forall x y, (sst0 L RR) (k1 x) (k2 y)) ->
  sst0 L RR (t1 >>= k1) (t2 >>= k2).
Proof.
  intros ? ?.
  apply (ft_t (@bind_ctx_ssim0_t E F C D X X' Y Y' _ _ L RV)).
  apply in_bind_ctx; eauto.
  intros ? ? ?; auto.
Qed.

(*|
Specializing the congruence principle for [≲]
|*)
Lemma ssim0_clo_bind {E F C D: Type -> Type} {X Y X' Y': Type}  {L: rel (@label E) (@label F)}
      `{HasStuck: B0 -< C} `{HasStuck': B0 -< D} {RV: Respects_val L}
      (t1 : ctree E C X) (t2: ctree F D Y)
      (k1 : X -> ctree E C X') (k2 : Y -> ctree F D Y'):
  ssim0 L t1 t2 ->
  (forall x y, ssim0 L (k1 x) (k2 y)) ->
  ssim0 L (t1 >>= k1) (t2 >>= k2).
Proof.
  intros * EQ EQs.
  apply (ft_t (@bind_ctx_ssim0_t E F C D X X' Y Y' _ _ L RV)).
  apply in_bind_ctx; auto.
  intros ? ? ?; auto.
  apply EQs.
Qed.

(*|
And in particular, we can justify rewriting [≲] to the left of a [bind].
|*)
Lemma bind_ssim0_cong_gen {E C X X'} RR {HasStuck: B0 -< C}
      {L: relation (@label E)} {RV: Respects_val L}:
  Proper (ssim0 L ==> (fun f g => forall x y, sst0 L RR (f x) (g y)) ==> sst0 L RR) (@bind E C X X').
Proof.
  do 4 red; intros.
  eapply sst0_clo_bind; auto.
Qed.

Ltac __upto_bind_ssim0 :=
  match goal with
    |- @ssim0 ?E ?F ?C ?D ?X ?Y _ _ ?L (CTree.bind (T := ?T) _ _) (CTree.bind (T := ?T') _ _) =>
      apply ssim0_clo_bind
  | |- body (t (@ss0 ?E ?F ?C ?D ?X ?Y _ _ ?L)) ?R (CTree.bind (T := ?T) _ _) (CTree.bind (T := ?T') _ _) =>
      apply (ft_t (@bind_ctx_ssim0_t E F C D X T Y T' _ L)), in_bind_ctx
  | |- body (bt (@ss0 ?E ?F ?C ?D ?X ?Y _ _ ?L)) ?R (CTree.bind (T := ?T) _ _) (CTree.bind (T := ?T') _ _) =>
      apply (fbt_bt (@bind_ctx_ssim0_t E F C D X T Y T' _ L)), in_bind_ctx
  end.

Ltac __upto_bind_eq_ssim0 :=
  match goal with
  | |- @ssim0 ?E ?F ?C ?D ?X ?Y _ _ ?L (CTree.bind (T := ?T) _ _) (CTree.bind (T := ?T') _ _) =>
      __upto_bind_ssim0; [reflexivity | intros ?]
  | _ => __upto_bind_ssim0; [reflexivity | intros ? ? <-]
  end.

Ltac __play_ssim0 := step; cbn; intros ? ? ?TR.

Ltac __play_ssim0_in H :=
  step in H;
  cbn in H; edestruct H as [? ?TR ?EQ];
  clear H; [etrans |].

Ltac __eplay_ssim0 :=
  match goal with
  | h : @ssim0 ?E ?F ?C ?D ?X ?Y _ _ ?L _ _ |- _ =>
      __play_ssim0_in h
  end.

#[local] Tactic Notation "play" := __play_ssim0.
#[local] Tactic Notation "play" "in" ident(H) := __play_ssim0_in H.
#[local] Tactic Notation "eplay" := __eplay_ssim0.

Section Proof_Rules.

  Arguments label: clear implicits.
  Context {E C: Type -> Type}
          {X : Type}
          {HasStuck: B0 -< C}.

  Lemma step_ss0_ret_gen {Y F D} `{HasStuck': B0 -< D}(x : X) (y : Y) (R L : rel _ _) :
    R stuckD stuckD ->
    (Proper (equ eq ==> equ eq ==> impl) R) ->
    L (val x) (val y) ->
    ss0 L R (Ret x : ctree E C X) (Ret y : ctree F D Y).
  Proof.
    intros Rstuck PROP Lval.
    cbn; intros ? ? TR; inv_trans; subst;
      cbn; eexists; eexists; intuition; etrans;
      now rewrite EQ.
  Qed.

  Lemma step_ss0_ret {Y F D} `{HasStuck': B0 -< D} (x : X) (y : Y) (R L : rel _ _) :
    L (val x) (val y) ->
    ssbt0 L R (Ret x : ctree E C X) (Ret y : ctree F D Y).
  Proof.
    intros.
    apply step_ss0_ret_gen.
    - step. intros.
      apply is_stuck_ss0; apply stuckD_is_stuck.
    - typeclasses eauto.
    - apply H.
  Qed.

  (*|
    The vis nodes are deterministic from the perspective of the labeled
    transition system, stepping is hence symmetric and we can just recover
    the itree-style rule.
  |*)
  Lemma step_ss0_vis_gen {Y Z Z' F D} `{HasStuck': B0 -< D} (e : E Z) (f: F Z')
        (k : Z -> ctree E C X) (k' : Z' -> ctree F D Y) (R L: rel _ _) :
    (Proper (equ eq ==> equ eq ==> impl) R) ->
    (forall x, exists y, R (k x) (k' y) /\ L (obs e x) (obs f y)) ->
    ss0 L R (Vis e k) (Vis f k').
  Proof.
    intros.
    cbn; intros ? ? TR; inv_trans; subst;
      destruct (H0 x) as (x' & RR & LL);
      cbn; eexists; eexists; intuition.
    - rewrite EQ; eauto. 
    - assumption.      
  Qed.     

  Lemma step_ss0_vis {Y Z F D} `{HasStuck': B0 -< D} (e : E Z) (f: F Z)
        (k : Z -> ctree E C X) (k' : Z -> ctree F D Y) (R L : rel _ _) :
    (forall x, exists y, sst0 L R (k x) (k' y) /\ L (obs e x) (obs f y)) ->
    ssbt0 L R (Vis e k) (Vis f k').
  Proof.
    intros * EQ.
    apply step_ss0_vis_gen; auto.
    typeclasses eauto.
  Qed.

  (*|
    Same goes for visible tau nodes.
    |*)
  Lemma step_ss0_step_gen {Y F D} `{HasTau: B1 -< C} `{HasStuck': B0 -< D} `{HasTau': B1 -< D}
        (t : ctree E C X) (t': ctree F D Y) (R L: rel _ _):
    (Proper (equ eq ==> equ eq ==> impl) R) ->
    L tau tau ->
    (R t t') ->
    ss0 L R (Step t) (Step t').
  Proof.
    intros PR ? EQs.
    intros ? ? TR; inv_trans; subst.
    cbn; do 2 eexists; split; [etrans | split; [rewrite EQ; eauto|assumption]].
  Qed.

  Lemma step_ss0_step {Y F D} `{HasStuck': B0 -< D} `{HasTau: B1 -< C} `{HasTau': B1 -< D}
        (t: ctree E C X) (t': ctree F D Y) (R L : rel _ _) :
    (sst0 L R t t') ->
    L tau tau ->
    ssbt0 L R (Step t) (Step t').
  Proof.
    intros. apply step_ss0_step_gen; auto.
    typeclasses eauto.
  Qed.

  (*|
    When matching visible brs one against another, in general we need to explain how
    we map the branches from the left to the branches to the right.
    A useful special case is the one where the arity coincide and we simply use the identity
    in both directions. We can in this case have [n] rather than [2n] obligations.
    |*)
  Lemma step_ss0_brS_gen {Z Z' Y F D} `{HasStuck': B0 -< D} (c : C Z) (d : D Z')
        (k : Z -> ctree E C X) (k' : Z' -> ctree F D Y) (R L: rel _ _) :
    (Proper (equ eq ==> equ eq ==> impl) R) ->
    (forall x, exists y, R (k x) (k' y)) ->
    L tau tau ->
    ss0 L R (BrS c k) (BrS d k').
  Proof.
    intros PROP EQs ? ? ? TR; inv_trans; subst.
    destruct (EQs x) as [y HR].
    cbn; do 2 eexists; split; [etrans | split; [rewrite EQ; eauto|assumption]].
  Qed.

  Lemma step_ss0_brS {Z Z' Y F} (c : C Z) (c' : C Z')
        (k : Z -> ctree E C X) (k' : Z' -> ctree F C Y) (R L: rel _ _) :
    (forall x, exists y, sst0 L R (k x) (k' y)) ->
    L tau tau ->
    ssbt0 L R (BrS c k) (BrS c' k').
  Proof.
    intros.    
    apply step_ss0_brS_gen; auto.
    typeclasses eauto.
  Qed.

  Lemma step_ss0_brS_id_gen {Z Y D F} `{HasStuck': B0 -< D} (c : C Z) (d: D Z)
        (k: Z -> ctree E C X) (k': Z -> ctree F D Y)(R L : rel _ _) :
    (Proper (equ eq ==> equ eq ==> impl) R) ->
    (forall x, exists y, R (k x) (k' y)) ->
    L tau tau ->
    ss0 L R (BrS c k) (BrS d k').
  Proof.
    intros; apply step_ss0_brS_gen; eauto.
  Qed.
  
  Lemma step_ss0_brS_id {Z Y F} (c : C Z)
        (k: Z -> ctree E C X) (k': Z -> ctree F C Y)(R L : rel _ _) :
    (forall x, exists y, sst0 L R (k x) (k' y)) ->
    L tau tau ->
    ssbt0 L R (BrS c k) (BrS c k').
  Proof.
    intros.
    apply step_ss0_brS_id_gen; eauto. 
    typeclasses eauto.
  Qed.

  (*|
    For invisible nodes, the situation is different: we may kill them, but that execution
    cannot act as going under the guard.
    |*)
  Lemma step_ss0_guard_gen {Y F D} `{HasStuck': B0 -< D} `{HasTau: B1 -< C} `{HasTau': B1 -< D}
        (t: ctree E C X) (t': ctree F D Y) (R L: rel _ _):
    ss0 L R t t' ->
    ss0 L R (Guard t) (Guard t').
  Proof.
    intros EQ.
    intros ? ? TR; inv_trans; subst.
    apply EQ in TR as (? & ? & ? & ? & ?); subst.
    do 2 eexists; split; [etrans | split; trivial].
  Qed.

  Lemma step_ss0_guard {Y F D} `{HasStuck': B0 -< D} `{HasTau: B1 -< C} `{HasTau': B1 -< D}
        (t: ctree E C X) (t': ctree F D Y) (R L: rel _ _):
    ssbt0 L R t t' ->
    ssbt0 L R (Guard t) (Guard t').
  Proof.
    apply step_ss0_guard_gen.
  Qed.

  Lemma step_ss0_brD_l_gen {Y F D Z} `{HasStuck': B0 -< D} (c : C Z)
        (k : Z -> ctree E C X) (t': ctree F D Y) (R L: rel _ _):
    (forall x, ss0 L R (k x) t') ->
    ss0 L R (BrD c k) t'.
  Proof.
    intros EQs.
    intros ? ? TR; inv_trans; subst.
    apply EQs in TR; destruct TR as [u' TR' EQ'].
    eauto.
  Qed.

  Lemma step_ss0_brD_l {Y F D Z} `{HasStuck': B0 -< D} (c : C Z)
        (k : Z -> ctree E C X) (t: ctree F D Y) (R L: rel _ _):
    (forall x, ssbt0 L R (k x) t) ->
    ssbt0 L R (BrD c k) t.
  Proof.
    apply step_ss0_brD_l_gen.
  Qed.

  Lemma step_ss0_brD_r_gen {Y F D Z} `{HasStuck': B0 -< D} (c : D Z) x
        (k : Z -> ctree F D Y) (t: ctree E C X) (R L: rel _ _):
    ss0 L R t (k x) ->
    ss0 L R t (BrD c k).
  Proof.
    cbn. intros.
    apply H in H0 as (? & ? & ? & ? & ?).
    exists x0; etrans.
  Qed.

  Lemma step_ss0_brD_r{Y F D Z} `{HasStuck': B0 -< D} (c : D Z) x
        (k : Z -> ctree F D Y) (t: ctree E C X) (R L: rel _ _):
    ssbt0 L R t (k x) ->
    ssbt0 L R t (BrD c k).
  Proof.
    intros. eapply step_ss0_brD_r_gen. apply H.
  Qed.

  Lemma step_ss0_brD_gen {Y F D n m} `{HasStuck': B0 -< D} (a: C n) (b: D m)
    (k : n -> ctree E C X) (k' : m -> ctree F D Y) (R L : rel _ _) :
    (forall x, exists y, ss0 L R (k x) (k' y)) ->
    ss0 L R (BrD a k) (BrD b k').
  Proof.
    intros EQs.
    apply step_ss0_brD_l_gen.
    intros. destruct (EQs x) as [x' ?].
    now apply step_ss0_brD_r_gen with (x:=x').
  Qed.

  Lemma step_ss0_brD {Y F D n m} `{HasStuck': B0 -< D} (cn: C n) (cm: D m)
    (k : n -> ctree E C X) (k' : m -> ctree F D Y) (L R : rel _ _) :
    (forall x, exists y, ssbt0 L R (k x) (k' y)) ->
    ssbt0 L R (BrD cn k) (BrD cm k').
  Proof.
    apply step_ss0_brD_gen.
  Qed.

  Lemma step_ss0_brD_id_gen {Y F D n m} `{HasStuck': B0 -< D} (c: C n) (d: D m)
        (k : n -> ctree E C X) (k' : m -> ctree F D Y)
        (R L : rel _ _) :
    (forall x, exists y, ss0 L R (k x) (k' y)) ->
    ss0 L R (BrD c k) (BrD d k').
  Proof.
   intros; apply step_ss0_brD_gen.
    intros x; destruct (H x) as [y ?]; exists y; apply H0.
  Qed.

  Lemma step_ss0_brD_id {Y F D n m} `{HasStuck': B0 -< D} (c: C n) (d: D m)
    (k : n -> ctree E C X) (k': m -> ctree F D Y) (R L: rel _ _) :
    (forall x, exists y, ssbt0 L R (k x) (k' y)) ->
    ssbt0 L R (BrD c k) (BrD d k').
  Proof.
    apply step_ss0_brD_id_gen.
  Qed.

  (*|
    Note that with visible schedules, nary-spins are equivalent only
    if neither are empty, or if both are empty: they match each other's
    tau challenge infinitely often.
    With invisible schedules, they are always equivalent: neither of them
    produce any challenge for the other.
  |*)
  Lemma spinS_gen_nonempty : forall {Z Y D F} {L: rel (label E) (label F)} `{HasStuck': B0 -< D}
                               (c: C X) (c': C Y) (x: X) (y: Y),
      L tau tau ->
      ssim0 L (@spinS_gen E C Z X c) (@spinS_gen F C Z Y c').
  Proof.
    intros until L.
    coinduction S CIH; simpl; intros ? ? ? ? ? ? ? ? TR;
      rewrite ctree_eta in TR; cbn in TR;
      apply trans_brS_inv in TR as (_ & EQ & ->);
      eexists; eexists;
      rewrite ctree_eta; cbn.
      split; [econstructor|].
      + exact y.
      + reflexivity.
      + rewrite EQ; eauto.
  Qed.

  (*|
    Inversion principles
    --------------------
    |*)
  Lemma ssim0_ret_inv {F D} {L: rel (label E) (label F)} `{HasStuck': B0 -< D} (r1 r2 : X) :
    ssim0 L (Ret r1 : ctree E C X) (Ret r2 : ctree F D X) ->
    L (val r1) (val r2).
  Proof.
    intro.
    eplay.
    destruct TR as (? & ? & ? & ?).    
    inv_trans; subst; assumption.
  Qed.
  
  Lemma ssim0_vis_inv_type {D Y X1 X2} {L: relation (label E)} `{HasStuck': B0 -< D}
        (e1 : E X1) (e2 : E X2) (k1 : X1 -> ctree E C X) (k2 : X2 -> ctree E D Y) (x : X1):
    ssim0 L (Vis e1 k1) (Vis e2 k2) ->
    X1 = X2.
  Proof.
    intros.
    eplay.
    destruct TR as (? & ? & ? & ?).
    inv_trans; subst; auto.
    instantiate (1:=x) in H0.
  Admitted.

  Lemma ssbt0_vis_inv {F D Y X1 X2} {L: rel (label E) (label F)} `{HasStuck': B0 -< D}
        (e1 : E X1) (e2 : F X2) (k1 : X1 -> ctree E C X) (k2 : X2 -> ctree F D Y) (x : X1) R:
    ssbt0 L R (Vis e1 k1) (Vis e2 k2) ->
    (exists y, L (obs e1 x) (obs e2 y))  /\ (forall x, exists y, sst0 L R (k1 x) (k2 y)).
  Proof.
    intros.
    split; intros; edestruct H as [? ? ?];
      etrans; subst; destruct H0 as (? & ? & ? & ? );
      inv_trans; subst; eexists; auto.
    - now eapply H2.
    - now apply H1. 
  Qed.

  Lemma ssim0_vis_inv {F D Y X1 X2} {L: rel (label E) (label F)} `{HasStuck': B0 -< D}
        (e1 : E X1) (e2 : F X2) (k1 : X1 -> ctree E C X) (k2 : X2 -> ctree F D Y) (x : X1):
    ssim0 L (Vis e1 k1) (Vis e2 k2) ->
    (exists y, L (obs e1 x) (obs e2 y)) /\ (forall x, exists y, ssim0 L (k1 x) (k2 y)).
  Proof.
    intros.
    split. 
      - eplay; destruct TR as (? & ? & ? & ?).
        inv_trans; subst; exists x2; eapply H1.
      - epose proof (proj1 (enhanced_gfp (@ss0 E F C D X Y _ _ L) _ _)). apply H0 in H. clear H0.
        step in H. eapply ssbt0_vis_inv in H.
        destruct H as [[y Hy] ?].
        intros.
        destruct (H x0) as [y' Hy'].
        eexists.
        step.
        econstructor; eexists; eauto; esplit.
        + (* LEF: Because the left transitions doesn't mean the right will as well -- right could be stuck? *)
   Admitted.        
  
  Lemma ssim0_brS_inv {F D Y} {L: rel (label E) (label F)} `{HasStuck': B0 -< D}
        n m (cn: C n) (cm: D m) (k1 : n -> ctree E C X) (k2 : m -> ctree F D Y) :
    ssim0 L (BrS cn k1) (BrS cm k2) ->
    (forall i1, exists i2, ssim0 L (k1 i1) (k2 i2)).
  Proof.
    intros EQ i1.
    eplay.
    destruct TR as (? & ? & ? & ?); subst.
    inv_trans.
    eexists; eauto.
  Qed.

  Lemma ss0_brD_l_inv {F D Y} {L: rel (label E) (label F)} `{HasStuck': B0 -< D}
        n (c: C n) (t : ctree F D Y) (k : n -> ctree E C X) R:
    ss0 L R (BrD c k) t ->
    forall x, ss0 L R (k x) t.
  Proof.
    cbn. intros.
    eapply trans_brD in H0; [| reflexivity].
    apply H in H0 as (? & ? & ? & ? & ?); subst.
    eauto.
  Qed.

  Lemma ssim0_brD_l_inv {F D Y} {L: rel (label E) (label F)} `{HasStuck': B0 -< D}
        n (c: C n) (t : ctree F D Y) (k : n -> ctree E C X):
    ssim0 L (BrD c k) t ->
    forall x, ssim0 L (k x) t.
  Proof.
    intros. step. step in H. eapply ss0_brD_l_inv. apply H.
  Qed.

  (* This one isn't very convenient... *)
  Lemma ssim0_brD_r_inv {F D Y} {L: rel (label E) (label F)} `{HasStuck': B0 -< D}
        n (c: D n) (t : ctree E C X) (k : n -> ctree F D Y):
    ssim0 L t (BrD c k) ->
    forall l t', trans l t t' ->
    exists l' x t'' , trans l' (k x) t'' /\ L l l' /\ (ssim0 L t' t'').
  Proof.
    cbn. intros. step in H. apply H in H0 as (? & ? & ? & ? & ?); subst. inv_trans.
    do 3 eexists; eauto.
  Qed.

End Proof_Rules.

(*|
A strong bisimulation gives two strong simulations,
but two strong simulations do not always give a strong bisimulation.
This property is true if we only allow brs with 0 or 1 branch,
but we prove a counter-example for a ctree with a binary br.
|*)

Lemma ss0_sb : forall {E C X} RR {HasStuck: B0 -< C}
  (t t' : ctree E C X),
  ss0 eq RR t t' ->
  ss0 eq (flip RR) t' t ->
  sb eq RR t t'.
Proof.
  intros.
  split; eauto.
  simpl in *; intros.
  destruct (H0 _ _ H1) as (? & ? & ? & ? & ?).
  destruct (H _ _ H2) as (? & ? & ? & ? & ?).
  subst; eauto.
Qed.

#[local] Definition t1 : ctree void1 (B0 +' B1 +' B2) unit :=
  Step (Ret tt).

#[local] Definition t2 : ctree void1 (B0 +' B1 +' B2) unit :=
  brS2 (Ret tt) (stuckD).

Lemma ssim0_sbisim_nequiv :
  ssim0 eq t1 t2 /\ ssim0 eq t2 t1 /\ ~ sbisim eq t1 t2.
Proof.
  unfold t1, t2. intuition.
  - step.
    apply step_ss0_brS; auto.
    intros _. exists true. reflexivity.
  - step. apply step_ss0_brS; auto.
    intros [|]; exists tt. 
    + reflexivity.
    + step. apply stuckD_ss0.
  - step in H. cbn in H. destruct H as [_ ?].
    specialize (H tau stuckD). lapply H; [| etrans].
    intros. destruct H0 as (? & ? & ? & ? & ?).
    inv_trans. step in H1. cbn in H1. destruct H1 as [? _].
    specialize (H0 (val tt) stuckD). lapply H0.
    2: subst; etrans.
    intro; destruct H1 as (? & ? & ? & ? & ?).
    now apply stuckD_is_stuck in H1.
Qed.

