From Coq Require Import Lia Basics Fin.

From Coinduction Require Import
     coinduction rel tactics.

From ITree Require Import Core.Subevent.

From CTree Require Import
     CTree
     Utils
     Eq.Equ
     Eq.SBisim
     Eq.SSim0Theory
     Eq.Shallow
     Eq.Trans.

From RelationAlgebra Require Export
     rel srel.

Set Implicit Arguments.

Import EquNotations.
Import SBisimNotations.

(* TODO: Decide where to set this *)
Arguments trans : simpl never.

#[local] Tactic Notation "step" := __step_sbisim || step.
#[local] Tactic Notation "coinduction" simple_intropattern(R) simple_intropattern(H) :=
  __coinduction_sbisim R H || coinduction R H.
#[local] Tactic Notation "step" "in" ident(H) := __step_in_sbisim H || step in H.


Section ssim_heterogenous_theory.
  
  Arguments label: clear implicits.
  Context {E F C D: Type -> Type} {X Y: Type}
          {L: rel (@label E) (@label F)}
          {HasStuck1: B0 -< C} {HasStuck2: B0 -< D}.
  
  Notation ss0 := (@ss0 E F C D X Y _ _).
  Notation ss := (@ss E F C D X Y _ _).
  Notation ssim  := (@ssim E F C D X Y _ _).
  Notation sst L := (coinduction.t (ss L)).
  Notation ssbt L := (coinduction.bt (ss L)).
  Notation ssT L := (coinduction.T (ss L)).

  (*|
    Various results on reflexivity and transitivity.
    |*)

  (*|
    Aggressively providing instances for rewriting hopefully faster
    [sbisim] under relevant [ss]-related contexts (consequence of the transitivity
    of the companion).
    |*)
  Lemma sbisim_clos_ss : @sbisim_clos E F C D X Y _ _ eq eq <= (sst L).
  Proof.
    intro R1. apply Coinduction.
    cbn; intros Rs x y [z x' y' z' SBzx' [x'y' y'x'] SBy'z']; split. 
    - intros l t zt.      
      step in SBzx'.
      apply SBzx' in zt as (l' & t' & x't' & ? & ?); subst.
      destruct (x'y' _ _ x't') as (l'' & t'' & y't'' & ? & ?).
      
      step in SBy'z'.
      apply SBy'z' in y't'' as (ll & tt & z'tt & ? & ?); subst.
      exists ll, tt; split; trivial.
      + split; trivial.
        apply (f_Tf (ss L)).
        econstructor; eauto.
    - intros l t z't.
      step in SBy'z'.
      symmetry in SBy'z'.      
      apply SBy'z' in z't as (l' & t' & y't' & ? & ?); subst.
      destruct (y'x' _ _ y't') as (l'' & t'' & y't'' & ?).
      step in SBzx'.
      apply SBzx' in H0 as (ll & tt & ztt & ? & ?); subst.
      exists ll, tt; split; trivial.
      simpl in H0, H1; subst; assumption.
  Qed.

  (*|
    Aggressively providing instances for rewriting hopefully faster
    [sbisim] under all [ss1]-related contexts (consequence of the transitivity
    of the companion).
  |*)    
  #[global] Instance sbisim_clos_ssim_goal:
    Proper (sbisim eq ==> sbisim eq ==> flip impl) (ssim L).
  Proof.
    cbn.
    coinduction R CH. intros.
    do 2 red; cbn; split; intros.
    - symmetry in H0.
      step in H; apply H in H2 as (? & ? & ? & ? & ?).
      step in H1; apply H1 in H2 as (? & ? & ? & ? & ?).
      step in H0; apply H0 in H2 as (? & ? & ? & ? & ?); subst.
      exists x5, x6.
      split; [assumption |].
      split; [| assumption].
      symmetry in H7. eapply CH; eassumption.
    - step in H0; apply H0 in H2 as (? & ? & ? & ? & ?).
      step in H1. apply H1 in H2 as (? & ? & ? & ?). 
      step in H. apply H in H5 as (? & ? & ? & ? & ?); simpl in *; subst.
      exists x3, x6.
      split; assumption.
  Qed.

  #[global] Instance sbisim_clos_ssim_ctx :
    Proper (sbisim eq ==> sbisim eq ==> impl) (ssim L).
  Proof.
    repeat intro. symmetry in H, H0. eapply sbisim_clos_ssim_goal; eauto.
  Qed.

  #[global] Instance sbisim_clos_sst_goal RR :
    Proper (sbisim eq ==> sbisim eq ==> flip impl) (sst L RR).
  Proof.
    cbn; intros ? ? eq1 ? ? eq2 H.
    apply (ft_t sbisim_clos_ss). cbn.
    econstructor; eauto.
    now rewrite eq2.
  Qed.

  #[global] Instance sbisim_clos_sst_ctx RR :
    Proper (sbisim eq ==> sbisim eq ==> impl) (sst L RR).
  Proof.
    cbn; intros ? ? eq1 ? ? eq2 ?.
    rewrite <- eq1, <- eq2.
    auto.
  Qed.

  #[global] Instance sbisim_clos_ssT_goal RR f :
    Proper (sbisim eq ==> sbisim eq ==> flip impl) (ssT L f RR).
  Proof.
    cbn; intros ? ? eq1 ? ? eq2 H.
    apply (fT_T sbisim_clos_ss). cbn.
    econstructor; eauto.
    now rewrite eq2.
  Qed.

  #[global] Instance sbisim_clos_ssT_ctx RR f :
    Proper (sbisim eq ==> sbisim eq ==> impl) (ssT L f RR).
  Proof.
    cbn; intros ? ? eq1 ? ? eq2 ?.
    rewrite <- eq1, <- eq2.
    auto.
  Qed.

  (*|
    Strong simulation up-to [equ] is valid
    ----------------------------------------
    |*)
  Lemma equ_clos_ss : equ_clos <= t (ss L).
  Proof.
    apply Coinduction.
    intros R t u EQ; split; intros l ? TR; cbn in EQ; inv EQ;
      cbn in *.
    - rewrite Equt in TR;
        apply HR in TR;
        destruct TR as (? & ? & ? & ? & ?); subst;
        exists x, x0; intuition.
      + rewrite <- Equu; auto.
      + eapply (f_Tf (ss L)).
        econstructor; auto; auto.
    - rewrite <- Equu in TR;
        apply HR in TR as (? & ? & ? & ?); subst;
        exists x, x0; intuition; rewrite Equt; auto.
  Qed.

  #[global] Instance equ_clos_sst_goal RR :
    Proper (equ eq ==> equ eq ==> flip impl) (sst L RR).
  Proof.
    cbn; intros ? ? eq1 ? ? eq2 H.
    apply (ft_t equ_clos_ss); econstructor; [eauto | | symmetry; eauto]; assumption.
  Qed.

  #[global] Instance equ_clos_sst_ctx RR :
    Proper (equ eq ==> equ eq ==> impl) (sst L RR).
  Proof.
    cbn; intros ? ? eq1 ? ? eq2 H.
    apply (ft_t equ_clos_ss); econstructor; [symmetry; eauto | | eauto]; assumption.
  Qed.

  #[global] Instance equ_ssbt_closed_goal {r}:
    Proper (equ eq ==> equ eq ==> flip impl) (ssbt L r).
  Proof.
    cbn; repeat intro.
    symmetry in H.
    apply (fbt_bt equ_clos_ss); econstructor; [symmetry; eauto | | eauto].
    apply (fbt_bt equ_clos_ss); econstructor; [reflexivity| eauto| eauto].
    now symmetry in H0.
  Qed.

  #[global] Instance equ_ssbt_closed_ctx {r} :
    Proper (equ eq ==> equ eq ==> impl) (ssbt L r).
  Proof.
    cbn; repeat intro. 
    setoid_rewrite H in H1. setoid_rewrite H0 in H1.
    auto.
  Qed.

  #[global] Instance equ_clos_ssT_goal RR f :
    Proper (equ eq ==> equ eq ==> flip impl) (ssT L f RR).
  Proof.
    cbn; intros ? ? eq1 ? ? eq2 H.
    apply (fT_T equ_clos_ss); econstructor; [eauto | | symmetry; eauto]; assumption.
  Qed.

  #[global] Instance equ_clos_ssT_ctx RR f :
    Proper (equ eq ==> equ eq ==> impl) (ssT L f RR).
  Proof.
    cbn; intros ? ? eq1 ? ? eq2 H.
    apply (fT_T equ_clos_ss); econstructor; [symmetry; eauto | | eauto]; assumption.
  Qed.

  #[global] Instance equ_clos_ssim_goal :
    Proper (equ eq ==> equ eq ==> flip impl) (ssim L).
  Proof.
    cbn; intros ? ? eq1 ? ? eq2 H.
    apply (ft_t equ_clos_ss); econstructor; [eauto | | symmetry; eauto]; assumption.
  Qed.

  #[global] Instance equ_clos_ssim_ctx :
    Proper (equ eq ==> equ eq ==> impl) (ssim L).
  Proof.
    cbn; intros ? ? eq1 ? ? eq2 H.
    apply (ft_t equ_clos_ss); econstructor; [symmetry; eauto | | eauto]; assumption.
  Qed.

  #[global] Instance equ_ss_closed_goal {r} : Proper (equ eq ==> equ eq ==> flip impl) (ss L r).
  Proof.
    intros t t' tt' u u' uu'; cbn; intros [H H0]; split; intros l t0 TR.
    - rewrite tt' in TR. destruct (H _ _ TR) as (? & ? & ? & ? & ?).     
      exists x, x0; auto; rewrite uu'; auto.
    - rewrite uu' in TR. destruct (H0 _ _ TR) as (? & ? & ? & ?).
      exists x, x0; eauto; rewrite tt'; auto.
  Qed.

  #[global] Instance equ_ss_closed_ctx {r} : Proper (equ eq ==> equ eq ==> impl) (ss L r).
  Proof.
    intros t t' tt' u u' uu'; cbn; intros [H H0]; split; intros l t0 TR.
    - rewrite <- tt' in TR. destruct (H _ _ TR) as (? & ? & ? & ? & ?).
      exists x, x0; auto; rewrite <- uu'; auto.
    - rewrite <- uu' in TR. destruct (H0 _ _ TR) as (? & ? & ? & ?). 
      exists x, x0; auto; rewrite <- tt'; auto.
  Qed.

  Lemma is_stuck_ss : forall (t: ctree E C X) (u: ctree F D Y) R,
      ss L R t u -> is_stuck t <-> is_stuck u.
  Proof.
    split; intros; intros ? ? ?.
    - apply H in H1 as (? & ? & ? & ?). now apply H0 in H2.
    - apply H in H1 as (? & ? & ? & ? & ?). now apply H0 in H1.
  Qed.

  Lemma is_stuck_ssim :  forall (t: ctree E C X) (u: ctree F D Y),
      t (≲ L) u -> is_stuck t <-> is_stuck u.
  Proof.
    intros. step in H. eapply is_stuck_ss; eauto.
  Qed.

  Lemma ss_is_stuck : forall (t : ctree E C X) (u: ctree F D Y) R,
      is_stuck t -> is_stuck u -> ss L R t u.
  Proof.
    split; intros.
    - cbn. intros. now apply H in H1.
    - now apply H0 in H1.
  Qed.

  Lemma ssim_is_stuck : forall (t : ctree E C X) (u: ctree F D Y),
      is_stuck t -> is_stuck u -> t (≲ L) u.
  Proof.
    intros. step. now apply ss_is_stuck.
  Qed.

End ssim_heterogenous_theory.

Section ssim_homogenous_theory.

  Context {E C : Type -> Type} {X : Type}
          {L: relation (@label E)}
          {HasStuck: B0 -< C}.

  Notation ss0 := (@ss0 E E C C X X _ _).
  Notation ss := (@ss E E C C X X _ _).
  Notation ssim  := (@ssim E E C C X X _ _).
  Notation sst L := (coinduction.t (ss L)).
  Notation ssbt L := (coinduction.bt (ss L)).
  Notation ssT L := (coinduction.T (ss L)).

  Lemma ssim_subrelation : forall (t t' : ctree E C X) L',
      subrelation L L' -> ssim L t t' -> ssim L' t t'.
  Proof.
    intros. revert t t' H0. coinduction R CH.
    intros. step in H0. simpl; split; intros; cbn in H0; destruct H0 as [H0' H0''].  
    - cbn in H0'; apply H0' in H1 as (? & ? & ? & ? & ?);
        apply H in H2. exists x, x0. auto.
    - cbn in H0''; apply H0'' in H1 as (? & ? & ? & ?).
      apply H in H0. exists x, x0. auto.
  Qed.

  (*|
    Various results on reflexivity and transitivity.
    |*)
  Lemma refl_sst `{Reflexive _ L}: const seq <= (sst L).
  Proof.
    intros. apply leq_t.
    cbn. intros. unfold seq in H0. subst. split; eauto.
  Qed.

  #[global] Instance Reflexive_ss R `{Reflexive _ L} `{Reflexive _ R}: Reflexive (ss L R).
  Proof.
    intros t.
    split; simpl; intros l t' TR; exists l, t'; auto.
  Qed.

  #[global] Instance Reflexive_ssim `{Reflexive _ L}: Reflexive (ssim L).
  Proof.
    cbn.  coinduction R CH.
    intros t.
    split; simpl; intros l t' TR; exists l, t'; split; auto.
  Qed.

  Lemma square_sst `{Transitive _ L}: square <= (sst L).
  Proof.
    apply Coinduction; cbn.
    intros R x z [y [xy yx] [yz zy]].
    split.
    - intros l x' xx'.
      destruct (xy _ _ xx') as (l' & y' & yy' & ? & ?).
      destruct (yz _ _ yy') as (l'' & z' & zz' & ? & ?).
      exists l'', z'.
      split; [assumption |split].
      + apply (f_Tf (ss L)).
        exists y'; eauto.
      + transitivity l'; auto.
    - intros l z' zz'.
      destruct (zy _ _ zz') as (l' & y' & ? & yy'). 
      destruct (yx _ _ yy') as (l'' & x' & ? & xx').
      exists l'', x'.
      split; eauto with trans.
  Qed.

  Lemma Transitive_ss R `{Transitive _ L} `{Transitive _ R}: Transitive (ss L R).
  Proof.
    cbn.
    intros x y z [xy yx] [yz zy].
    split.
    - intros l x' xx'.
      destruct (xy _ _ xx') as (l' & y' & yy' & ? & ?).
      destruct (yz _ _ yy') as (l'' & z' & zz' & ? & ?).
      exists l'', z'.
      split; [assumption | split].
      + now transitivity y'.
      + now transitivity l'.
    - intros l z' zz'.
      destruct (zy _ _ zz') as (l' & y' & ? & yy'). 
      destruct (yx _ _ yy') as (l'' & x' & ? & xx').
      exists l'', z'.
      split.
      + now transitivity l'.
      + admit. (* LEF: not sure why this doesn't work *)
  Admitted.

  #[global] Instance PreOrder_sst R `{PreOrder _ L}: PreOrder (sst L R).
  Proof. apply PreOrder_t. apply refl_sst. apply square_sst. Qed.

  Corollary PreOrder_ssim `{PreOrder _ L}:  PreOrder (ssim L).
  Proof. now apply PreOrder_sst. Qed.

  #[global] Instance PreOrder_ssbt R `{PreOrder _ L}: PreOrder (ssbt L R).
  Proof. apply rel.PreOrder_bt. now apply refl_sst. apply square_sst. Qed.

  #[global] Instance PreOrder_ssT f R `{PreOrder _ L}: PreOrder ((T (ss L)) f R).
  Proof. apply rel.PreOrder_T. now apply refl_sst. apply square_sst. Qed.

End ssim_homogenous_theory.

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
  Program Definition bind_ctx_ssim : mon (rel (ctree E C X') (ctree F D Y')) :=
    {|body := fun R => @bind_ctx E F C D X Y X' Y' (ssim L) (pointwise (fun x y => L (val x) (val y)) R) |}.
  Next Obligation.
    intros ?? H. apply leq_bind_ctx. intros ?? H' ?? H''.
    apply in_bind_ctx. apply H'. intros t t' HS. apply H, H'', HS.
  Qed.

(*|
The resulting enhancing function gives a valid up-to technique
|*)
  Lemma bind_ctx_ssim_t :
    respects_val L ->
    bind_ctx_ssim <= sst L.
  Proof.
    intro HL.
    apply Coinduction.
    intros R. apply (leq_bind_ctx _).
    intros t1 t2 tt k1 k2 kk.
    step in tt.
    split; simpl; intros l u STEP; 
      apply trans_bind_inv in STEP as [(H & t' & STEP & EQ) | (v & STEPres & STEP)];
      cbn in *.
    - apply tt in STEP as (u' & l' & STEP & EQ' & ?).
      do 2 eexists. split.
      apply trans_bind_l; eauto.
      + intro Hl. destruct Hl. apply HL in H0 as [_ ?]. specialize (H0 (Is_val _)). auto.
      + split; auto.
        apply (fT_T equ_clos_ss).
        econstructor; [exact EQ | | reflexivity].
        apply (fTf_Tf (ss L)).
        apply in_bind_ctx; auto.
        intros ? ? ?.
        apply (b_T (ss L)).
        red in kk; now apply kk. 
    - apply tt in STEPres as (u' & ? & STEPres & EQ' & ?).
      specialize (HL _ _ H) as [? _]. specialize (H0 (Is_val _)). destruct H0.
      pose proof (trans_val_invT STEPres). subst.
      pose proof (trans_val_inv STEPres) as EQ.
      rewrite EQ in STEPres.
      specialize (kk v x0 H). 
      apply kk in STEP as (u'' & ? & STEP & EQ'' & ?); cbn in *.
      do 2 eexists; split.
      eapply trans_bind_r; eauto.
      split; auto.
      eapply (id_T (ss L)); auto.
    - apply tt in STEP as (u' & l' & ? & STEP). 
      do 2 eexists; split; eauto.
      apply trans_bind_l.
      + intro Hl. destruct Hl. apply HL in H0 as [? _]. specialize (H0 (Is_val _)). auto.
      + eauto.
    - destruct tt as [tt tt'].
      apply tt' in STEPres as (u' & ? & ? & STEPres).
      specialize (HL _ _ H) as [_ ?]. specialize (H0 (Is_val _)). destruct H0.
      pose proof (trans_val_invT STEPres). subst.
      pose proof (trans_val_inv STEPres) as EQ.
      rewrite EQ in STEPres.
      specialize (kk x0 v H). 
      apply kk in STEP as (u'' & ? & ? & STEP); cbn in *.
      do 2 eexists; split; eauto.      
      eapply trans_bind_r; eauto.
  Qed.

End bind.

Lemma bind_ctx_ssim_eq_t {E C T X} `{B0 -< C} :
    (bind_ctx_ssim (X := T) (Y := T) eq : mon (relation (ctree E C X))) <= sst eq.
Proof.
  apply bind_ctx_ssim_t. red. intros. now subst.
Qed.

Import CTree.
Import CTreeNotations.

(*|
Expliciting the reasoning rule provided by the up-to principles.
|*)
Lemma sst_clo_bind (E F C D: Type -> Type) `{B0 -< C} `{B0 -< D} (X X' Y Y' : Type) L :
  forall (t1 : ctree E C X) (t2 : ctree F D X') (k1 : X -> ctree E C Y) (k2 : X' -> ctree F D Y') RR,
		t1 (≲L) t2 ->
    respects_val L ->
    (forall x y, L (val x) (val y) -> (sst L RR) (k1 x) (k2 y)) ->
    sst L RR (t1 >>= k1) (t2 >>= k2)
.
Proof.
  intros.
  apply (ft_t (@bind_ctx_ssim_t E F C D X Y X' Y' _ _ L H2)).
  apply in_bind_ctx; auto.
Qed.

(*|
Specializing the congruence principle for [~]
|*)
Lemma ssim_clo_bind (E F C D: Type -> Type) `{B0 -< C} `{B0 -< D} (X X' Y Y' : Type) L :
  forall (t1 : ctree E C X) (t2 : ctree F D X') (k1 : X -> ctree E C Y) (k2 : X' -> ctree F D Y'),
		t1 (≲L) t2 ->
    respects_val L ->
    (forall x x', L (val x) (val x') -> k1 x (≲L) k2 x') ->
    t1 >>= k1 (≲L) t2 >>= k2
.
Proof.
  intros.
  apply (ft_t (@bind_ctx_ssim_t E F C D X Y X' Y' _ _ L H2)).
  apply in_bind_ctx; auto.
Qed.

(*|
And in particular, we can justify rewriting [≲] to the left of a [bind].
|*)
Lemma bind_ssim_cong_gen {E F C D X X' Y Y'} `{B0 -< C} `{B0 -< D} RR (L : rel _ _) :
  forall (t : ctree E C X) (t' : ctree F D X')
      (k : X -> ctree E C Y) (k' : X' -> ctree F D Y'),
    respects_val L ->
    ssim L t t' ->
    (forall x x', L (val x) (val x') -> sst L RR (k x) (k' x')) ->
    sst L RR (CTree.bind t k) (CTree.bind t' k').
Proof.
  intros; eapply sst_clo_bind; red in H2; eauto.
Qed.

Ltac __upto_bind_ssim :=
  match goal with
    |- @ssim _ _ _ _ ?X ?X' _ _ _ (CTree.bind (T := ?T) _ _) (CTree.bind (T := ?T') _ _) =>
      apply ssim_clo_bind
  | |- body (t (@ss ?E ?E ?C ?C ?X ?X _ _ eq)) ?R (CTree.bind (T := ?T) _ _) (CTree.bind (T := ?T) _ _) =>
      apply (ft_t (@bind_ctx_ssim_eq_t E C T X _)), in_bind_ctx
  | |- body (bt (@ss ?E ?E ?C ?C ?X ?X _ _ eq)) ?R (CTree.bind (T := ?T) _ _) (CTree.bind (T := ?T) _ _) =>
      apply (fbt_bt (@bind_ctx_ssim_eq_t E C T X _)), in_bind_ctx
  end.
Ltac __upto_bind_eq_ssim :=
  __upto_bind_ssim; [reflexivity | intros ? _ _].

Ltac __play_ssim := step; cbn; intros ? ? ?TR.

Ltac __play_ssim_in H :=
  step in H;
  cbn in H; edestruct H as (? & ? & ?TR & ?EQ & ?);
  clear H; subst; [etrans |].

Ltac __eplay_ssim :=
  match goal with
  | h : @ssim ?E ?F ?C ?D ?X ?Y _ _ ?L _ _ |- _ =>
      __play_ssim_in h
  end.

#[local] Tactic Notation "play" := __play_ssim.
#[local] Tactic Notation "play" "in" ident(H) := __play_ssim_in H.
#[local] Tactic Notation "eplay" := __eplay_ssim.

Section Proof_Rules.

  Context {E F C D : Type -> Type}.
  Context {HasStuck : B0 -< C} {HasStuck' : B0 -< D}.
  Context {HasTau : B1 -< C} {HasTau' : B1 -< D}.
  Context {X X' Y Y' : Type}.
  Context {L : rel (@label E) (@label F)}.

  Lemma step_ss_ret_gen (x : X) (y : Y) (R : rel _ _) :
    R stuckD stuckD ->
    (Proper (equ eq ==> equ eq ==> impl) R) ->
    L (val x) (val y) ->
    ss L R (Ret x : ctree E C X) (Ret y : ctree F D Y).
  Proof.
    intros Rstuck PROP Lval.
    cbn; split; intros ? ? TR; inv_trans; subst;
      cbn; eexists; eexists; intuition; etrans;
      now rewrite EQ.
  Qed.
End Proof_Rules.

Section Foo.
   Context {E C : Type -> Type} {X : Type}
          {L: relation (@label E)}
          {HasStuck: B0 -< C}.
   
   Lemma step_ss_ret (x y : X) (R : rel _ _) `{Reflexive _ L}:
     x = y ->
     ssbt L R (Ret x : ctree E C X) (Ret y: ctree E C X).
   Proof.
     intros.
     apply step_ss_ret_gen.
     apply refl_sst; eauto.
     typeclasses eauto.
     subst; reflexivity.
  Qed.
    

(*|
The vis nodes are deterministic from the perspective of the labeled transition system,
stepping is hence symmetric and we can just recover the itree-style rule.
|*)
<<<<<<< HEAD
  Lemma step_ss_vis_gen (l : rel _ _) (e : E X) (k : X -> ctree E C Y) (k' : X -> ctree E D Y') (R : rel _ _) :
    (Proper (equ eq ==> equ eq ==> impl) R) ->
    (forall x, R (k x) (k' x)) ->
    (forall x, l (obs e x) (obs e x)) ->
    ss l R (Vis e k) (Vis e k').
  Proof.
    intros PR EQs.
    intros ? ? ? TR; inv_trans; subst.
    cbn; eexists; eexists; intuition. rewrite EQ; auto.
  Qed.

  Lemma step_ss_vis (l : rel _ _) (e : E X) (k : X -> ctree E C Y) (k' : X -> ctree E D Y') (R : rel _ _) :
    (forall x, sst l R (k x) (k' x)) ->
    (forall x, l (obs e x) (obs e x)) ->
    ssbt l R (Vis e k) (Vis e k').
=======
  Lemma step_ss_vis_gen (e : E X) (k k' : X -> ctree E Y) (R : rel _ _) :
    (Proper (equ eq ==> equ eq ==> impl) R) ->
    (forall x, R (k x) (k' x)) ->
    ss R (Vis e k) (Vis e k').
  Proof.
    split.
    - apply step_ss0_vis_gen; auto.
    - intros. inv_trans. etrans.
    Unshelve. auto.
  Qed.

  Lemma step_ss_vis (e : E X) (k k' : X -> ctree E Y) (R : rel _ _) :
    (forall x, sst R (k x) (k' x)) ->
    ssbt R (Vis e k) (Vis e k').
>>>>>>> master
  Proof.
    intros * EQ.
    apply step_ss_vis_gen; auto.
    typeclasses eauto.
  Qed.

(*|
Same goes for visible tau nodes.
|*)
<<<<<<< HEAD
   Lemma step_ss_tauV_gen (t : ctree E C X) (t' : ctree F D Y) (R : rel _ _) :
    (Proper (equ eq ==> equ eq ==> impl) R) ->
    (R t t') ->
    L tau tau ->
    ss L R (tauV t) (tauV t').
  Proof.
    intros PR EQs.
    intros ? ? ? TR; inv_trans; subst.
    cbn; eexists; eexists; intuition; rewrite EQ; auto.
  Qed.

  Lemma step_ss_tauV (t : ctree E C X) (t' : ctree F D Y) (R : rel _ _) :
    L tau tau ->
    (sst L R t t') ->
    ssbt L R (tauV t) (tauV t').
  Proof.
    intros. apply step_ss_tauV_gen; auto.
=======
   Lemma step_ss_step_gen (t t' : ctree E X) (R : rel _ _) :
    (Proper (equ eq ==> equ eq ==> impl) R) ->
    (R t t') ->
    ss R (Step t) (Step t').
  Proof.
    split.
    - apply step_ss0_step_gen; auto.
    - etrans.
  Qed.

  Lemma step_ss_step (t t' : ctree E X) (R : rel _ _) :
    (sst R t t') ->
    ssbt R (Step t) (Step t').
  Proof.
    intros. apply step_ss_step_gen; auto.
>>>>>>> master
    typeclasses eauto.
  Qed.

(*|
<<<<<<< HEAD
When matching visible choices one against another, in general we need to explain how
=======
When matching visible brs one against another, in general we need to explain how
>>>>>>> master
we map the branches from the left to the branches to the right.
A useful special case is the one where the arity coincide and we simply use the identity
in both directions. We can in this case have [n] rather than [2n] obligations.
|*)
<<<<<<< HEAD

  Lemma step_ss_choiceV_gen C' Z `{C0 -< C'} (c : C Y) (c' : C' Z)
    (k : Y -> ctree E C X) (k' : Z -> ctree F C' X') (R : rel _ _) :
    (Proper (equ eq ==> equ eq ==> impl) R) ->
    L tau tau ->
    (forall x, exists y, R (k x) (k' y)) ->
    ss L R (ChoiceV c k) (ChoiceV c' k').
  Proof.
    intros PROP ? EQs.
    intros ? ? TR; inv_trans; subst.
    destruct (EQs x) as [z HR].
    eexists. eexists. intuition.
    rewrite EQ; eauto.
  Qed.

  Lemma step_ss_choiceV Z (c : C Y) (c' : D Z)
    (k : Y -> ctree E C X) (k' : Z -> ctree F D X') (R : rel _ _) :
    L tau tau ->
    (forall x, exists y, sst L R (k x) (k' y)) ->
    ssbt L R (ChoiceV c k) (ChoiceV c' k').
  Proof.
    intros ? EQs.
    apply step_ss_choiceV_gen; auto.
    typeclasses eauto.
  Qed.

  Lemma step_ss_choiceV_id_gen (c : C Y)
    (k : Y -> ctree E C X) (k' : Y -> ctree F C X') (R : rel _ _) :
    (Proper (equ eq ==> equ eq ==> impl) R) ->
    L tau tau ->
    (forall x, R (k x) (k' x)) ->
    ss L R (ChoiceV c k) (ChoiceV c k').
  Proof.
    intros PROP ? EQs.
    apply step_ss_choiceV_gen; auto.
    intros x; exists x; auto.
  Qed.

  Lemma step_ss_choiceV_id (c : C Y)
    (k : Y -> ctree E C X) (k' : Y -> ctree F C X') (R : rel _ _) :
    L tau tau ->
    (forall x, sst L R (k x) (k' x)) ->
    ssbt L R (ChoiceV c k) (ChoiceV c k').
  Proof.
    apply step_ss_choiceV_id_gen.
=======
  Lemma step_ss_brS_gen n m (k : fin (S n) -> ctree E X) (k' : fin m -> ctree E X) (R : rel _ _) :
    (Proper (equ eq ==> equ eq ==> impl) R) ->
    (forall x, exists y, R (k x) (k' y)) ->
    ss R (BrS (S n) k) (BrS m k').
  Proof.
    split.
    - apply step_ss0_brS_gen; auto.
    - etrans.
    Unshelve. apply Fin.F1.
  Qed.

  Lemma step_ss_brS n m (k : fin (S n) -> ctree E X) (k' : fin m -> ctree E X) (R : rel _ _) :
    (forall x, exists y, sst R (k x) (k' y)) ->
    ssbt R (BrS (S n) k) (BrS m k').
  Proof.
    apply step_ss_brS_gen; auto.
    typeclasses eauto.
  Qed.

  Lemma step_ss_brS_id_gen n
    (k k' : fin n -> ctree E X) (R : rel _ _) :
    (Proper (equ eq ==> equ eq ==> impl) R) ->
    (forall x, R (k x) (k' x)) ->
    ss R (BrS n k) (BrS n k').
  Proof.
    intros; destruct n.
    - apply ss_is_stuck; rewrite br0_always_stuck; apply stuckS_is_stuck.
    - apply step_ss_brS_gen; auto.
      intros x; exists x; auto.
  Qed.

  Lemma step_ss_brS_id n
    (k k' : fin n -> ctree E X) (R : rel _ _) :
    (forall x, sst R (k x) (k' x)) ->
    ssbt R (BrS n k) (BrS n k').
  Proof.
    apply step_ss_brS_id_gen.
>>>>>>> master
    typeclasses eauto.
  Qed.

(*|
For invisible nodes, the situation is different: we may kill them, but that execution
cannot act as going under the guard.
|*)
<<<<<<< HEAD
  Lemma step_ss_tauI_gen (t : ctree E C X) (t' : ctree F D Y) (R : rel _ _) :
    ss L R t t' ->
    ss L R (tauI t) (tauI t').
  Proof.
    intros EQ.
    intros ? ? TR; inv_trans; subst.
    apply EQ in TR as (? & ? & ? & ? & ?).
    eexists; eexists; intuition; subst; [apply trans_tauI; eauto | eauto | eauto].
  Qed.

  Lemma step_ss_tauI (t : ctree E C X) (t' : ctree F D Y) (R : rel _ _) :
    ssbt L R t t' ->
    ssbt L R (tauI t) (tauI t').
  Proof.
    apply step_ss_tauI_gen.
  Qed.

  Lemma step_ss_choiceI_l_gen C' Z `{C0 -< C'} (c : C Z)
    (k : Z -> ctree E C X) (t' : ctree F C' Y) (R : rel _ _) :
    (forall x, ss L R (k x) t') ->
    ss L R (ChoiceI c k) t'.
  Proof.
    intros EQs.
    intros ? ? TR; inv_trans; subst.
    apply EQs in TR; destruct TR as (u' & ? & TR' & EQ' & ?).
    eexists. eexists. subst. intuition; eauto.
  Qed.

  Lemma step_ss_choiceI_l C' Z `{C0 -< C'} (c : C Z)
    (k : Z -> ctree E C X) (t' : ctree F C' Y) (R : rel _ _) :
    (forall x, ssbt L R (k x) t') ->
    ssbt L R (ChoiceI c k) t'.
  Proof.
    apply step_ss_choiceI_l_gen.
  Qed.

  Lemma step_ss_choiceI_r_gen C' Z `{C0 -< C'} :
    forall (t : ctree E C X) (c : C' Z) (k : Z -> ctree F C' Y) x R,
    ss L R t (k x) ->
    ss L R t (ChoiceI c k).
  Proof.
    simpl. intros.
    apply H0 in H1 as (? & ? & ? & ? & ?). subst.
    exists x0, x1. intuition. econstructor. eauto.
  Qed.

  Lemma step_ss_choiceI_r Z : forall (t : ctree E C X) (c : D Z) (k : Z -> ctree F D Y) x R,
    ssbt L R t (k x) ->
    ssbt L R t (ChoiceI c k).
  Proof.
    intros. eapply step_ss_choiceI_r_gen. apply H.
  Qed.

  Lemma step_ss_choiceI_gen C' Z Z' `{C0 -< C'} (c : C Z) (c' : C' Z')
    (k : Z -> ctree E C X) (k' : Z' -> ctree F C' Y) (R : rel _ _) :
    (forall x, exists y, ss L R (k x) (k' y)) ->
    ss L R (ChoiceI c k) (ChoiceI c' k').
  Proof.
    intros EQs.
    apply step_ss_choiceI_l_gen.
    intros. destruct (EQs x) as [x' ?].
    now apply step_ss_choiceI_r_gen with (x := x').
  Qed.

  Lemma step_ss_choiceI C' Z Z' `{C0 -< C'} (c : C Z) (c' : C' Z')
    (k : Z -> ctree E C X) (k' : Z' -> ctree F C' Y) (R : rel _ _) :
    (forall x, exists y, ssbt L R (k x) (k' y)) ->
    ssbt L R (ChoiceI c k) (ChoiceI c' k').
  Proof.
    apply step_ss_choiceI_gen.
  Qed.

  Lemma step_ss_choiceI_id_gen Z (c : C Z)
    (k : Z -> ctree E C X) (k' : Z -> ctree F C Y) (R : rel _ _) :
    (forall x, ss L R (k x) (k' x)) ->
    ss L R (ChoiceI c k) (ChoiceI c k').
  Proof.
    intros; apply step_ss_choiceI_gen.
    intros x; exists x; apply H.
  Qed.

  Lemma step_ss_choiceI_id Z (c : C Z) (k : Z -> ctree E C X) (k' : Z -> ctree F C Y) (R : rel _ _) :
    (forall x, ssbt L R (k x) (k' x)) ->
    ssbt L R (ChoiceI c k) (ChoiceI c k').
  Proof.
    apply step_ss_choiceI_id_gen.
=======
  Lemma step_ss_guard_gen (t t' : ctree E X) (R : rel _ _) :
    ss R t t' ->
    ss R (Guard t) (Guard t').
  Proof.
    split.
    - destruct H. apply step_ss0_tauI_gen. auto.
    - intros. inv_trans.
      apply H in H0 as (? & ? & ?).
      etrans.
  Qed.

  Lemma step_ss_guard (t t' : ctree E X) (R : rel _ _) :
    ssbt R t t' ->
    ssbt R (Guard t) (Guard t').
  Proof.
    apply step_ss_guard_gen.
  Qed.

  Lemma step_ss_brD_l_gen n
    (k : fin (S n) -> ctree E X) (t' : ctree E X) (R : rel _ _) :
    (forall x, ss R (k x) t') ->
    ss R (BrD (S n) k) t'.
  Proof.
    intros EQs. split.
    - apply step_ss0_brD_l_gen. intro. now destruct (EQs x).
    - intros. apply (EQs Fin.F1) in H as (? & ? & ?).
      etrans.
  Qed.

  Lemma step_ss_brD_l n
    (k : fin (S n) -> ctree E X) (t' : ctree E X) (R : rel _ _) :
    (forall x, ssbt R (k x) t') ->
    ssbt R (BrD (S n) k) t'.
  Proof.
    apply step_ss_brD_l_gen.
  Qed.

  Lemma step_ss_brD_r_gen :
    forall (t : ctree E X) n (k : fin n -> ctree E X) x R,
    (exists l t', trans l t t') ->
    ss R t (k x) ->
    ss R t (BrD n k).
  Proof.
    cbn. split; intros.
    - apply H0 in H1 as [? ? ?].
      exists x0; etrans.
    - apply H.
  Qed.

  Lemma step_ss_brD_r :
    forall (t : ctree E X) n (k : fin n -> ctree E X) x R,
    (exists l t', trans l t t') ->
    ssbt R t (k x) ->
    ssbt R t (BrD n k).
  Proof.
    intros. eapply step_ss_brD_r_gen. apply H. apply H0.
  Qed.

  Lemma step_ss_brD_gen n m
    (k : fin n -> ctree E X) (k' : fin m -> ctree E X) x (R : rel _ _) :
    (exists l' t', trans l' (k x) t') ->
    (forall x, exists y, ss R (k x) (k' y)) ->
    ss R (BrD n k) (BrD m k').
  Proof.
    intros ? EQs. split; intros.
    - apply step_ss0_brD_gen. intros.
      destruct (EQs x0). destruct H0. eauto.
    - destruct H as (? & ? & ?). etrans.
  Qed.

  Lemma step_ss_brD n m
    (k : fin n -> ctree E X) (k' : fin m -> ctree E X) x (R : rel _ _) :
    (exists l' t', trans l' (k x) t') ->
    (forall x, exists y, ssbt R (k x) (k' y)) ->
    ssbt R (BrD n k) (BrD m k').
  Proof.
    apply step_ss_brD_gen.
  Qed.

  Lemma step_ss_brD_id_gen n
    (k k' : fin n -> ctree E X) (R : rel _ _) :
    (forall x, ss R (k x) (k' x)) ->
    ss R (BrD n k) (BrD n k').
  Proof.
    destruct n; intros.
    - apply ss_is_stuck; rewrite br0_always_stuck; apply stuckD_is_stuck.
    - split; cbn; intros.
      + inv_trans. apply H in TR as []. etrans.
      + inv_trans. apply H in TR as (? & ? & ?). etrans.
  Qed.

  Lemma step_ss_brD_id n
    (k k' : fin n -> ctree E X) (R : rel _ _) :
    (forall x, ssbt R (k x) (k' x)) ->
    ssbt R (BrD n k) (BrD n k').
  Proof.
    apply step_ss_brD_id_gen.
>>>>>>> master
  Qed.

End Proof_Rules.

Section WithParams.

<<<<<<< HEAD
  Context {E F C D : Type -> Type}.
  Context {HasStuck : C0 -< C}.
  Context {HasTau : C1 -< C}.
  Context {HasStuck' : C0 -< D}.
  Context {HasTau' : C1 -< D}.
  Context (L : rel (@label E) (@label F)).
=======
  Context {E : Type -> Type}.
  Context {X : Type}.
>>>>>>> master

(*|
Note that with visible schedules, nary-spins are equivalent only
if neither are empty, or if both are empty: they match each other's
tau challenge infinitely often.
With invisible schedules, they are always equivalent: neither of them
produce any challenge for the other.
|*)
<<<<<<< HEAD
  Lemma spinV_gen_nonempty : forall {Z Z' X Y} (c: C X) (c': D Y) (x: X) (y: Y) (L : rel _ _),
    L tau tau ->
    ssim L (@CTree.spinV_gen E C Z X c) (@CTree.spinV_gen F D Z' Y c').
  Proof.
    intros.
    red. coinduction R CH.
    intros l t' TR.
    rewrite ctree_eta in TR; cbn in TR.
    apply trans_choiceV_inv in TR as (_ & EQ & ->).
    eexists. eexists.
    rewrite ctree_eta; cbn.
    split; [econstructor |]. exact y.
    reflexivity.
    rewrite EQ; auto.
=======
  Lemma spinS_nary_n_m : forall n m,
    n > 0 -> m > 0 ->
    ssim (@spinS_nary E X n) (spinS_nary m).
  Proof.
    intros.
    red. coinduction R CH.
    setoid_rewrite ctree_eta. cbn.
    destruct n, m; try lia.
    eapply step_ss_brS.
    intros _. exists Fin.F1.
    apply CH.
>>>>>>> master
  Qed.

(*|
Inversion principles
--------------------
|*)
<<<<<<< HEAD
  Lemma ssim_ret_inv X Y (r1 : X) (r2 : Y) :
    (Ret r1 : ctree E C X) (≲L) (Ret r2 : ctree F D Y) ->
    L (val r1) (val r2).
  Proof.
    intro.
    eplay. inv_trans. now subst.
  Qed.

  Lemma ssim_vis_inv_type {X X1 X2}
        (e1 : E X1) (e2 : E X2) (k1 : X1 -> ctree E C X) (k2 : X2 -> ctree E C X) (x : X1):
=======
  Lemma ssim_ret_inv (r1 r2 : X) :
    (Ret r1 : ctree E X) ≲ Ret r2 ->
    r1 = r2.
  Proof.
    intro.
    eplay. etrans. inv_trans. auto.
  Qed.

  Lemma ssim_vis_inv_type {X1 X2}
        (e1 : E X1) (e2 : E X2) (k1 : X1 -> ctree E X) (k2 : X2 -> ctree E X) (x : X1):
>>>>>>> master
    Vis e1 k1 ≲ Vis e2 k2 ->
    X1 = X2.
  Proof.
    intros.
    eplay.
    inv TR; auto.
    Unshelve. auto.
  Qed.

<<<<<<< HEAD
  Lemma ssbt_eq_vis_inv {X Y} (e1 e2 : E Y) (k1 k2 : Y -> ctree E C X) (x : Y) R :
    ss eq (t (ss eq) R) (Vis e1 k1) (Vis e2 k2) ->
    e1 = e2 /\ forall x, sst eq R (k1 x) (k2 x).
  Proof.
    intros.
    split.
    - cbn in H. edestruct H as (? & ? & ? & ? & ?).
      etrans. subst. now inv_trans.
    - cbn. intros. edestruct H as (? & ? & ? & ? & ?).
=======
  Lemma ssbt_eq_vis_inv {Y} (e1 e2 : E Y) (k1 k2 : Y -> ctree E X) (x : Y) R :
    ssbt R (Vis e1 k1) (Vis e2 k2) ->
    e1 = e2 /\ forall x, sst R (k1 x) (k2 x).
  Proof.
    intros. split.
    - cbn in H. edestruct H as [[? ? ?] _].
      etrans. subst. now inv_trans.
    - cbn. intros. edestruct H as [[? ? ?] _].
>>>>>>> master
      etrans. subst. inv_trans. subst. apply H1.
    Unshelve. auto.
  Qed.

<<<<<<< HEAD
  Lemma t_gfp_bt : forall {X} `{CompleteLattice X} (b : mon X),
    weq (t b (gfp (bt b))) (gfp b).
  Proof.
    intros. cbn.
    rewrite <- enhanced_gfp. rewrite t_gfp.
    reflexivity.
  Qed.

  Lemma ssim_eq_vis_inv {X Y} (e1 e2 : E Y) (k1 k2 : Y -> ctree E C X) (x : Y) :
=======
  Lemma ssim_eq_vis_inv {Y} (e1 e2 : E Y) (k1 k2 : Y -> ctree E X) (x : Y) :
>>>>>>> master
    Vis e1 k1 ≲ Vis e2 k2 ->
    e1 = e2 /\ forall x, k1 x ≲ k2 x.
  Proof.
    intros.
    (* Why doesn't apply work directly here? *)
<<<<<<< HEAD
    epose proof (proj1 (enhanced_gfp (@ss E E C C X X _ _ eq) _ _)). apply H0 in H. clear H0.
    step in H. apply ssbt_eq_vis_inv in H; auto.
    destruct H. split; auto.
    intro. subst. specialize (H0 x0).
    apply (proj1 (t_gfp_bt (@ss E E C C X X _ _ eq) _ _)) in H0. apply H0.
  Qed.

  Lemma ssim_choiceV_inv {X Y Z Z'}
        c1 c2 (k1 : X -> ctree E C Z) (k2 : Y -> ctree F D Z') :
    ChoiceV c1 k1 (≲L) ChoiceV c2 k2 ->
    (forall i1, exists i2, k1 i1 (≲L) k2 i2).
=======
    epose proof (proj1 (enhanced_gfp (@ss E X) _ _)). apply H0 in H. clear H0.
    step in H. apply ssbt_eq_vis_inv in H; auto.
    destruct H. split; auto.
    intro. subst. specialize (H0 x0).
    apply (proj1 (t_gfp_bt (@ss E X) _ _)) in H0. apply H0.
  Qed.

  Lemma ssim_brS_inv
        n1 n2 (k1 : fin n1 -> ctree E X) (k2 : fin n2 -> ctree E X) :
    BrS n1 k1 ≲ BrS n2 k2 ->
    (forall i1, exists i2, k1 i1 ≲ k2 i2).
>>>>>>> master
  Proof.
    intros EQ i1.
    eplay.
    inv_trans.
    eexists; eauto.
  Qed.

<<<<<<< HEAD
  Lemma ss_choiceI_l_inv : forall {X Y Z}
    (t : ctree E C X) (c : D Y) (k : Y -> ctree F D Z) L R,
    ss L R (ChoiceI c k) t ->
    forall x, ss L R (k x) t.
  Proof.
    cbn. intros.
    eapply trans_choiceI in H0; [| reflexivity].
    apply H in H0 as (? & ? & ? & ? & ?).
    exists x0, x1. auto.
  Qed.

  Lemma ssim_choiceI_l_inv : forall {X Y Z}
    (t : ctree E C X) (c : D Y) (k : Y -> ctree F D Z) L,
    ChoiceI c k (≲L) t ->
    forall x, k x (≲L) t.
  Proof.
    intros. step. step in H. eapply ss_choiceI_l_inv. apply H.
  Qed.

  (* This one isn't very convenient... *)
  Lemma ssim_choiceI_r_inv : forall {X Y Z}
    (t : ctree E C X) (c : D Y) (k : Y -> ctree F D Z) L,
    ssim L t (ChoiceI c k) ->
    forall l t', trans l t t' ->
    exists x t'' l', trans l' (k x) t'' /\ ssim L t' t'' /\ L l l'.
  Proof.
    cbn. intros. step in H. apply H in H0 as (? & ? & ? & ? & ?). subst. inv_trans.
    exists x1, x, x0. auto.
  Qed.

End WithParams.

(*|
A strong bisimulation gives two strong simulations,
but two strong simulations do not always give a strong bisimulation.
This property is true if we only allow choices with 0 or 1 branch,
but we prove a counter-example for a ctree with a binary choice.
|*)

Lemma ss_hsb : forall {E F C D X Y} `{C0 -< C} `{C0 -< D} L RR
  (t : ctree E C X) (t' : ctree F D Y),
  ss L RR t t' ->
  ss (flip L) (flip RR) t' t ->
  hsb L RR t t'.
Proof.
  split; auto.
Qed.

Lemma ctree_C01_trans_det : forall {E X} l (t t' t'' : ctree E C01 X),
  trans l t t' -> trans l t t'' -> t' ≅ t''.
Proof.
  intros. do 3 red in H.
  rewrite ctree_eta in H0.
  genobs t ot. genobs t' ot'. rewrite ctree_eta, <- Heqot'.
  clear t t' Heqot Heqot'. revert t'' H0.
  dependent induction H; intros; inv_trans.
  - eapply IHtrans_; eauto.
    rewrite <- ctree_eta.
    destruct c, c, x, x0. assumption.
  - rewrite <- ctree_eta. destruct c, c, x, x0. now rewrite <- H, EQ.
  - subst. rewrite <- ctree_eta. now rewrite <- H, EQ.
  - rewrite EQ. apply choice0_always_stuck.
Qed.

Lemma ssim_hsbisim_equiv_gen : forall {E F X Y} (L : rel _ _) (t : ctree E C01 X) (t' : ctree F C01 Y),
  (forall x x' y, L x y -> L x' y -> x = x') ->
  (forall x y y', L x y -> L x y' -> y = y') ->
  ssim L t t' -> ssim (flip L) t' t -> hsbisim L t t'.
Proof.
  intros until 2. revert t t'.
  coinduction R CH. red. red. cbn. split; intros.
  - step in H1. cbn in H1.
    apply H1 in H3 as H3'. destruct H3' as (? & ? & ? & ? & ?).
    exists x, x0. intuition. apply CH.
    + apply H5.
    + step in H2. cbn in H2. apply H2 in H4 as (? & ? & ? & ? & ?).
      replace x2 with l in H4.
      2: { eapply H; eauto. }
      assert (t'0 ≅ x1) by (eapply ctree_C01_trans_det; eauto).
      now rewrite H9.
  - step in H2. cbn in H2.
    apply H2 in H3 as H3'. destruct H3' as (? & ? & ? & ? & ?).
    exists x, x0. intuition. apply CH.
    + step in H1. cbn in H1. apply H1 in H4 as (? & ? & ? & ? & ?).
      replace x2 with l in H4.
      2: { eapply H0; eauto. }
      assert (t'0 ≅ x1) by (eapply ctree_C01_trans_det; eauto).
      now rewrite H9.
    + apply H5.
Qed.

Lemma ssim_hsbisim_equiv : forall {E X} (t t' : ctree E C01 X),
  ssim eq t t' -> ssim eq t' t -> hsbisim eq t t'.
Proof.
  intros. apply ssim_hsbisim_equiv_gen; intros.
  - now subst.
  - now subst.
  - apply H.
  - apply ssim_subrelation with (L := eq); auto.
    red. intros. subst. reflexivity.
Qed.

#[local] Definition t1 : ctree void1 (C01 +' C2) unit :=
  tauV (Ret tt).

#[local] Definition t2 : ctree void1 (C01 +' C2) unit :=
  chooseV2 (Ret tt) (stuckI).

Lemma ssim_hsbisim_nequiv :
  ssim eq t1 t2 /\ ssim (flip eq) t2 t1 /\ ~ hsbisim eq t1 t2.
Proof.
  unfold t1, t2. intuition.
  - step. apply step_ss_choiceV; auto.
    intros _. exists true. reflexivity.
  - step. apply step_ss_choiceV; auto.
    intro. exists tt. destruct x.
    + reflexivity.
    + step. apply stuckI_ss.
  - step in H. cbn in H. destruct H as [_ ?].
    specialize (H tau stuckI). lapply H; [| etrans].
    intros. destruct H0 as (? & ? & ? & ? & ?). subst.
    inv_trans. step in H1. cbn in H1. destruct H1 as [? _].
    specialize (H0 (val tt) stuckI). lapply H0. 2: { rewrite EQ. etrans. }
    intro. destruct H1 as (? & ? & ? & ? & ?). subst.
    now apply stuckI_is_stuck in H1.
Qed.
=======
  Lemma ss_brD_l_inv : forall n
    (t : ctree E X) (k : fin n -> ctree E X) x R,
    ss R (BrD n k) t ->
    (exists l t', trans l (k x) t') ->
    ss R (k x) t.
  Proof.
    split.
    - apply ss0_brD_l_inv. now apply H.
    - intros. apply H0.
  Qed.

  Lemma ssim_brD_l_inv : forall n
    (t : ctree E X) (k : fin n -> ctree E X) x,
    BrD n k ≲ t ->
    (exists l t', trans l (k x) t') ->
    k x ≲ t.
  Proof.
    intros. step. step in H. eapply ss_brD_l_inv; auto.
  Qed.

  (* This one isn't very convenient... *)
  Lemma ssim_brD_r_inv : forall n
    (t : ctree E X) (k : fin n -> ctree E X),
    t ≲ BrD n k ->
    forall l t', trans l t t' ->
    exists x t'', trans l (k x) t'' /\ t' ≲ t''.
  Proof.
    cbn. intros. step in H. apply H in H0 as [? ? ?]. inv_trans.
    eauto.
  Qed.

End WithParams.
>>>>>>> master

        
Section ssim_heterogenous_theory.
  #[local] Arguments label: clear implicits.
  Context {E F C D : Type -> Type} {X Y : Type}
          {L: rel (label E) (label F)}
          {HasStuck1: B0 -< C} {HasStuck2: B0 -< D}.

  Notation hss := (@ss E F C D X Y _ _ L).
  Notation hssim  := (@ssim E F C D X Y _ _ L).
  Notation hsst := (coinduction.t ss).
  Notation hssbt := (coinduction.bt ss).
  Notation hssT := (coinduction.T ss).
  
End ssim_heterogenous_theory.
