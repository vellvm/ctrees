From Coq Require Import
     Classes.RelationClasses
     Basics
     Fin
     Logic.Eqdep.

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

Import CTree.
Import EquNotations.
Import SBisimNotations.
Import CTreeNotations.

(* TODO: Decide where to set this *)
Arguments trans : simpl never.

#[local] Tactic Notation "step" := __step_sbisim || step.
#[local] Tactic Notation "coinduction" simple_intropattern(R) simple_intropattern(H) :=
  __coinduction_sbisim R H || coinduction R H.
#[local] Tactic Notation "step" "in" ident(H) := __step_in_sbisim H || step in H.

(*| Very polymorphic definitions and lemmas
  - Polymorphic on labels, by heterogenous relation [L].
  - Polymorphic on return type.
  - Polymorphic on branch effects. |*)
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
      t (⪅ L) u -> is_stuck t <-> is_stuck u.
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
      is_stuck t -> is_stuck u -> t (⪅ L) u.
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
  Lemma bind_ctx_ssim_t {HL: Respects_val L}:
    bind_ctx_ssim <= sst L.
  Proof.
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
      destruct HL.
      pose proof (respects_val _ _ H) as [? _]. specialize (H0 (Is_val _)). destruct H0.
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
      destruct HL.
      pose proof (respects_val _ _ H) as [_ ?]. specialize (H0 (Is_val _)). destruct H0.
      pose proof (trans_val_invT STEPres). subst.
      pose proof (trans_val_inv STEPres) as EQ.
      rewrite EQ in STEPres.
      specialize (kk x0 v H). 
      apply kk in STEP as (u'' & ? & ? & STEP); cbn in *.
      do 2 eexists; split; eauto.      
      eapply trans_bind_r; eauto.
  Qed.

End bind.

(*| More lemmas about [bind] |*)
Lemma bind_ctx_ssim_eq_t {E C T X} `{B0 -< C} :
  (bind_ctx_ssim (X := T) (Y := T) eq : mon (relation (ctree E C X))) <= sst eq.
Proof.
  apply bind_ctx_ssim_t. split. intros. now subst.
Qed.

(*|
Expliciting the reasoning rule provided by the up-to principles.
|*)
Lemma sst_clo_bind {E F C D: Type -> Type} `{B0 -< C} `{B0 -< D}
      {X X' Y Y' : Type} {L: rel (@label E) (@label F)} {HL: Respects_val L} (t1 : ctree E C X) (t2 : ctree F D X')
      (k1 : X -> ctree E C Y) (k2 : X' -> ctree F D Y') RR:
		t1 (⪅ L) t2 ->
    (forall x y, L (val x) (val y) -> (sst L RR) (k1 x) (k2 y)) ->
    sst L RR (t1 >>= k1) (t2 >>= k2).
Proof.
  intros.
  apply (ft_t (@bind_ctx_ssim_t E F C D X Y X' Y' _ _ L HL)).
  apply in_bind_ctx; auto.
Qed.

(*|
Specializing the congruence principle for [~]
|*)
Lemma ssim_clo_bind {E F C D: Type -> Type} `{B0 -< C} `{B0 -< D}
      {X X' Y Y' : Type} L {HL: Respects_val L} (t1 : ctree E C X) (t2 : ctree F D X')
      (k1 : X -> ctree E C Y) (k2 : X' -> ctree F D Y'):
		t1 (⪅L) t2 ->
    (forall x x', L (val x) (val x') -> k1 x (⪅L) k2 x') ->
    t1 >>= k1 (⪅L) t2 >>= k2
.
Proof.
  intros.
  apply (ft_t (@bind_ctx_ssim_t E F C D X Y X' Y' _ _ L HL)).
  apply in_bind_ctx; auto.
Qed.

(*|
And in particular, we can justify rewriting [⪅] to the left of a [bind].
|*)
Lemma bind_ssim_cong_gen {E F C D X X' Y Y'} `{B0 -< C} `{B0 -< D} RR (L : rel _ _)
      {HL: Respects_val L} (t : ctree E C X) (t' : ctree F D X')
      (k : X -> ctree E C Y) (k' : X' -> ctree F D Y'):
    ssim L t t' ->
    (forall x x', L (val x) (val x') -> sst L RR (k x) (k' x')) ->
    sst L RR (CTree.bind t k) (CTree.bind t' k').
Proof.
  intros; eapply sst_clo_bind; red in H2; eauto.
Qed.

(*| Ltac automation rule for [bind] and [ssim] |*)
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
  cbn in H; edestruct H as (? & ? & ? & ? & ? );
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
  Arguments label: clear implicits.
  Context {E C : Type -> Type} {X: Type} `{HasStuck : B0 -< C}.

  Lemma step_ss_ret_gen {Y F D}(x : X) (y : Y) `{HasStuck': B0 -< D}
        {L: rel (label E) (label F)} {R : rel (ctree E C X) (ctree F D Y)}:
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

  Lemma step_ss_ret  {Y F D}(x : X) (y : Y) `{HasStuck': B0 -< D}
        {L: rel (label E) (label F)} {R : rel (ctree E C X) (ctree F D Y)}:
    L (val x) (val y) ->
    ssbt L R (Ret x : ctree E C X) (Ret y : ctree F D Y).
  Proof.
    intros.
    apply step_ss_ret_gen.
    - step. intros. apply ss_is_stuck; apply stuckD_is_stuck.
    - typeclasses eauto.
    - apply H.
  Qed.

  (*|
    The vis nodes are deterministic from the perspective of the labeled
    transition system, stepping is hence symmetric and we can just recover
    the itree-style rule.
  |*)
  (* LEF: Here, I got lazy -- it would be nice to have [k': Z' -> ctree F D Y]
     see [step_ss0_vis_gen] *)
   Lemma step_ss_vis_gen {Y Z F D} `{HasStuck': B0 -< D} (e : E Z) (f: F Z)
        (k : Z -> ctree E C X) (k' : Z -> ctree F D Y) (R L: rel _ _) :
    (Proper (equ eq ==> equ eq ==> impl) R) ->
    (forall x, R (k x) (k' x)) ->
    (forall x, L (obs e x) (obs f x)) ->
    ss L R (Vis e k) (Vis f k').
  Proof.
    split.
    - apply step_ss0_vis_gen; eauto.
    - intros. inv_trans; subst; etrans.
  Qed.

  Lemma step_ss_vis {Y Z F D} `{HasStuck': B0 -< D} (e : E Z) (f: F Z)
        (k : Z -> ctree E C X) (k' : Z -> ctree F D Y) (R L: rel _ _) :
    (forall x, sst L R (k x) (k' x)) ->
    (forall x, L (obs e x) (obs f x)) ->
    ssbt L R (Vis e k) (Vis f k').
  Proof.
    intros * EQ.
    apply step_ss_vis_gen; auto.
    typeclasses eauto.
  Qed.
  
  (*|
    Same goes for visible tau nodes.
  |*)  
  Lemma step_ss_step_gen{Y F D} `{HasStuck': B0 -< D} `{HasTau: B1 -< C} `{HasTau': B1 -< D}
        (t : ctree E C X) (t' : ctree F D Y) (R L: rel _ _) :
    (Proper (equ eq ==> equ eq ==> impl) R) ->
    (R t t') ->
    L tau tau ->
    ss L R (Step t) (Step t').
  Proof.
    intros PR EQs ?.
    cbn; split; intros ? ? TR; inv_trans; subst;
      eexists; eexists; intuition.
    - now rewrite EQ.
    - assumption.
  Qed.

  Lemma step_ss_step{Y F D} `{HasStuck': B0 -< D} `{HasTau: B1 -< C} `{HasTau': B1 -< D}
        (t : ctree E C X) (t' : ctree F D Y) (R L: rel _ _) :
    L tau tau ->
    (sst L R t t') ->
    ssbt L R (Step t) (Step t').
  Proof.
    intros. eapply step_ss_step_gen; eauto.
    typeclasses eauto.
  Qed.

  (*|
    When matching visible brs one against another, in general we need to explain how
    we map the branches from the left to the branches to the right.
    A useful special case is the one where the arity coincide and we simply use
    the identity in both directions. We can in this case have [n] rather than [2n]
    obligations.
  |*)
  (** LEF: Here I need to show [Z] is inhabited,
      I think the way to go is to axiomatize it. Maybe it's possible
      to extract a [Z] from [HasTau: B1 -< C]? YZ says no,
      so maybe the extra restriction is truly needed. *)
  Lemma step_ss_brS_gen{Y Z Z' F D} `{HasStuck': B0 -< D} (c : C Z) (d: D Z')
        (k : Z -> ctree E C X) (k' : Z' -> ctree F D Y) (R L: rel _ _) :
    (Proper (equ eq ==> equ eq ==> impl) R) ->
    L tau tau ->
    inhabited Z ->
    (forall x, exists y, R (k x) (k' y)) ->
    ss L R (BrS c k) (BrS d k').
  Proof.
    intros PROP ? EX EQs; cbn; split; 
      intros ? ? TR; inv_trans; subst.
    - destruct (EQs x) as [z HR].
      do 2 eexists; intuition.      
      rewrite EQ; eassumption.
    - exists tau; eexists; intuition.
      Unshelve. apply (proj1_sig EX).
  Qed.

  Lemma step_ss_brS {Y Z Z' F D} `{HasStuck': B0 -< D} (c : C Z) (d: D Z')
        (k : Z -> ctree E C X) (k' : Z' -> ctree F D Y) (R L: rel _ _) :
    L tau tau ->
    inhabited Z ->
    (forall x, exists y, sst L R (k x) (k' y)) ->
    ssbt L R (BrS c k) (BrS d k').
  Proof.
    intros.
    apply step_ss_brS_gen; auto.
    typeclasses eauto.
  Qed.

  Lemma step_ss_brS_id_gen {Y Z F } (c : C Z)
        (k : Z -> ctree E C X) (k' : Z -> ctree F C Y) (R L: rel _ _) :
    (Proper (equ eq ==> equ eq ==> impl) R) ->
    L tau tau ->
    inhabited Z ->
    (forall x, R (k x) (k' x)) ->
    ss L R (BrS c k) (BrS c k').
  Proof.
    intros PROP ? ? EQs.
    apply step_ss_brS_gen; auto.
    intros x; exists x; auto.
  Qed.

  Lemma step_ss_brS_id {Y Z F } (c : C Z)
        (k : Z -> ctree E C X) (k' : Z -> ctree F C Y) (R L: rel _ _) :
    L tau tau ->
    inhabited Z ->
    (forall x, sst L R (k x) (k' x)) ->
    ssbt L R (BrS c k) (BrS c k').
  Proof.
    apply step_ss_brS_id_gen.
    typeclasses eauto.
  Qed.

  (*|
    For invisible nodes, the situation is different: we may kill them, but that
    execution cannot act as going under the guard.
  |*)
  Lemma step_ss_guard_gen {Y F D} `{HasStuck': B0 -< D}`{HasTau: B1 -< C} `{HasTau': B1 -< D}
        (t : ctree E C X) (t' : ctree F D Y) (R L: rel _ _) :
    ss L R t t' ->
    ss L R (Guard t) (Guard t').
  Proof.
    intros EQ; cbn; split; intros ? ? TR; inv_trans; subst.
    - apply EQ in TR as (? & ? & ? & ? & ?).
      do 2 eexists; intuition; subst; [apply trans_guard; eauto | eauto | eauto].
    - apply EQ in TR as (? & ? & ? & ?).
      do 2 eexists; subst; intuition.
      + eapply H.
      + apply trans_guard; eauto.
  Qed.

  Lemma step_ss_guard {Y F D} `{HasStuck': B0 -< D}`{HasTau: B1 -< C} `{HasTau': B1 -< D}
        (t : ctree E C X) (t' : ctree F D Y) (R L : rel _ _) :
    ssbt L R t t' ->
    ssbt L R (Guard t) (Guard t').
  Proof.
    apply step_ss_guard_gen.
  Qed.

  Lemma step_ss_brD_l_gen {Y F D Z} `{HasStuck': B0 -< D} (c : C Z)
    (k : Z -> ctree E C X) (t' : ctree F D Y) (R L: rel _ _) :
    (forall x, ss L R (k x) t') ->
    inhabited Z -> 
    ss L R (BrD c k) t'.
  Proof.
    intros EQs ?; cbn; split;
      intros ? ? TR; inv_trans; subst.
    - apply EQs in TR as (u' & ? & TR' & EQ' & ?); eauto.
    - pose proof (proj1_sig X0) as z.
      destruct (EQs z) as (tt & ? & ? & ? & ?); eauto.
      do 2 eexists; intuition.
      apply H.
      eapply trans_brD; eauto.
  Qed.

  Lemma step_ss_brD_l {Y F D Z} `{HasStuck': B0 -< D} (c : C Z)
    (k : Z -> ctree E C X) (t' : ctree F D Y) (R L: rel _ _) :
    (forall x, ssbt L R (k x) t') ->
    inhabited Z ->
    ssbt L R (BrD c k) t'.
  Proof.
    apply step_ss_brD_l_gen.
  Qed.

  Lemma step_ss_brD_r_gen {Y F D Z} `{HasStuck': B0 -< D} (c : D Z)
    (t : ctree E C X) (k : Z -> ctree F D Y) (R L: rel _ _) z :
    ss L R t (k z) ->
    ss L R t (BrD c k).
  Proof.
    simpl. split; intros.
    - apply H in H0 as (? & ? & ? & ? & ?); subst.
      exists x, x0. intuition. econstructor. eauto.
    - apply trans_brD_inv in H0 as (? & ?).
      (** HM maybe this isn't so easy for complete simulation *)
      admit.
  Admitted.

  Lemma step_ss_brD_r {Y F D Z} `{HasStuck': B0 -< D} (c : D Z)
        (t : ctree E C X) (k : Z -> ctree F D Y) (R L: rel _ _) z :
    ssbt L R t (k z) ->
    ssbt L R t (BrD c k).
  Proof.
    intros. eapply step_ss_brD_r_gen. apply H.
  Qed.

  Lemma step_ss_brD_gen {Y F D Z Z'} `{HasStuck': B0 -< D} (c: C Z) (c': D Z')
        (k : Z -> ctree E C X) (k' : Z' -> ctree F D Y) (R L: rel _ _) :
    (forall x, exists y, ss L R (k x) (k' y)) ->
    inhabited Z ->
    ss L R (BrD c k) (BrD c' k').
  Proof.
    intros EQs ?.
    apply step_ss_brD_l_gen; trivial.
    intros. destruct (EQs x) as [x' ?].
    now apply step_ss_brD_r_gen with (z := x').
  Qed.

  Lemma step_ss_brD {Y F D Z Z'} `{HasStuck': B0 -< D} (c: C Z) (c': D Z')
        (k : Z -> ctree E C X) (k' : Z' -> ctree F D Y) (R L: rel _ _) :
    (forall x, exists y, ssbt L R (k x) (k' y)) ->
    inhabited Z -> 
    ssbt L R (BrD c k) (BrD c' k').
  Proof.
    apply step_ss_brD_gen.
  Qed.

  Lemma step_ss_brD_id_gen {Y F Z} (c: C Z)
        (k : Z -> ctree E C X) (k' : Z -> ctree F C Y) (R L: rel _ _) :
    (forall x, ss L R (k x) (k' x)) ->
    inhabited Z ->
    ss L R (BrD c k) (BrD c k').
  Proof.
    intros; apply step_ss_brD_gen; trivial.
    intros x; exists x; apply H.
  Qed.

  Lemma step_ss_brD_id {Y F Z} (c: C Z)
        (k : Z -> ctree E C X) (k' : Z -> ctree F C Y) (R L: rel _ _) :
    (forall x, ssbt L R (k x) (k' x)) ->
    inhabited Z -> 
    ssbt L R (BrD c k) (BrD c k').
  Proof.
    apply step_ss_brD_id_gen.
  Qed.

End Proof_Rules.

Section WithParams.

  Context {E F C D : Type -> Type}.
  Context {HasStuck : B0 -< C}.
  Context {HasTau : B1 -< C}.
  Context {HasStuck' : B0 -< D}.
  Context {HasTau' : B1 -< D}.
  Context (L : rel (@label E) (@label F)).

  (*|
    Note that with visible schedules, nary-spins are equivalent only
    if neither are empty, or if both are empty: they match each other's
    tau challenge infinitely often.
    With invisible schedules, they are always equivalent: neither of them
    produce any challenge for the other.
    |*)
  Lemma spinS_gen_nonempty : forall {Z Z' X Y} (c: C X) (c': D Y) (x: X) (y: Y) (L : rel _ _),
    L tau tau ->
    ssim L (@spinS_gen E C Z X c) (@spinS_gen F D Z' Y c').
  Proof.
    intros.
    red. coinduction R CH.
    simpl; split; intros l t' TR; rewrite ctree_eta in TR; cbn in TR;
    apply trans_brS_inv in TR as (_ & EQ & ->);
      do 2 eexists;
      rewrite ctree_eta; cbn; intuition.
    - econstructor; auto.
    - rewrite EQ; eauto.
    - eapply H.
    - eapply H.
    - econstructor; auto.
  Qed.

  (*|
    Inversion principles
    --------------------
  |*)
  Lemma ssim_ret_inv X Y (r1 : X) (r2 : Y) :
    (Ret r1 : ctree E C X) (⪅L) (Ret r2 : ctree F D Y) ->
    L (val r1) (val r2).
  Proof.
    intro.
    eplay. inv_trans. now subst.
  Qed.

  Lemma ssim_vis_inv_type {X X1 X2}
        (e1 : E X1) (e2 : E X2) (k1 : X1 -> ctree E C X) (k2 : X2 -> ctree E C X) (x : X1):
    Vis e1 k1 ⪅ Vis e2 k2 ->
    X1 = X2.
  Proof.
    intros.
    eplay.
    inv H2.
    apply inj_pair2 in H6, H7; subst.
    step in H1; inv H1; reflexivity.
    Unshelve. admit.
  Admitted.
  
  Lemma ssbt_eq_vis_inv {X Y} (e1 e2 : E Y) (k1 k2 : Y -> ctree E C X) (x : Y) R :
    ss eq (t (ss eq) R) (Vis e1 k1) (Vis e2 k2) ->
    e1 = e2 /\ forall x, sst eq R (k1 x) (k2 x).
  Proof.
    intros.
    split.
    - cbn in H. edestruct H as (? & ? & ? & ? & ?).
      etrans. subst. now inv_trans.
    - cbn. intros. edestruct H as [? ? ?].
  Admitted.

  Lemma t_gfp_bt : forall {X} `{CompleteLattice X} (b : mon X),
    weq (t b (gfp (bt b))) (gfp b).
  Proof.
    intros. cbn.
    rewrite <- enhanced_gfp. rewrite t_gfp.
    reflexivity.
  Qed.

  Lemma ssim_eq_vis_inv {X Y} (e1 e2 : E Y) (k1 k2 : Y -> ctree E C X) (x : Y) :
    Vis e1 k1 ⪅ Vis e2 k2 ->
    e1 = e2 /\ forall x, k1 x ⪅ k2 x.
  Proof.
    intros.
    (* Why doesn't apply work directly here? *)
    epose proof (proj1 (enhanced_gfp (@ss E E C C X X _ _ eq) _ _)). apply H0 in H. clear H0.
    step in H. apply ssbt_eq_vis_inv in H; auto.
    destruct H. split; auto.
    intro. subst. specialize (H0 x0).
    apply (proj1 (t_gfp_bt (@ss E E C C X X _ _ eq) _ _)) in H0. apply H0.
  Qed.

  Lemma ssim_brS_inv {X Y Z Z'}
        c1 c2 (k1 : X -> ctree E C Z) (k2 : Y -> ctree F D Z') :
    BrS c1 k1 (⪅L) BrS c2 k2 ->
    (forall i1, exists i2, k1 i1 (⪅L) k2 i2).
  Proof.
    intros.
    eplay.
    inv_trans;
      eexists; eauto.
  Admitted.    

  Lemma ss_brD_l_inv : forall {X Y Z}
    (t : ctree E C X) (c : D Y) (k : Y -> ctree F D Z) L R,
    ss L R (BrD c k) t ->
    forall x, ss L R (k x) t.
  Proof.
    cbn. intros; split; intros.
    eapply trans_brD in H0; [| reflexivity].
    - apply H in H0 as (? & ? & ? & ? & ?); exists x0, x1; auto.
    - apply H in H0 as (? & ? & ? & ?). apply trans_brD_inv in H1 as (x' & y').
  Admitted.

  Lemma ssim_brD_l_inv : forall {X Y Z}
    (t : ctree E C X) (c : D Y) (k : Y -> ctree F D Z) L,
    BrD c k (⪅L) t ->
    forall x, k x (⪅L) t.
  Proof.
    intros. step. step in H. eapply ss_brD_l_inv. apply H.
  Qed.

  (* This one isn't very convenient... *)
  Lemma ssim_brD_r_inv : forall {X Y Z}
    (t : ctree E C X) (c : D Y) (k : Y -> ctree F D Z) L,
    ssim L t (BrD c k) ->
    forall l t', trans l t t' ->
    exists x t'' l', trans l' (k x) t'' /\ ssim L t' t'' /\ L l l'.
  Proof.
    cbn. intros. step in H. apply H in H0 as (? & ? & ? & ? & ?). subst. inv_trans.
    exists x1, x0, x. auto.
  Qed.

End WithParams.

(*|
A strong bisimulation gives two strong simulations,
but two strong simulations do not always give a strong bisimulation.
This property is true if we only allow choices with 0 or 1 branch,
but we prove a counter-example for a ctree with a binary choice.
|*)

Lemma ss_sb : forall {E F C D X Y} `{B0 -< C} `{B0 -< D} L RR
  (t : ctree E C X) (t' : ctree F D Y),
  ss L RR t t' ->
  ss (flip L) (flip RR) t' t ->
  sb L RR t t'.
Proof.
  split; cbn; intros.
  - apply H1 in H3 as (? & ? & ? & ? & ?); eauto.
  - apply H2 in H3 as (? & ? & ? & ? & ?); eauto.
Qed.

Lemma ctree_B01_trans_det : forall {E X} l (t t' t'' : ctree E B01 X),
  trans l t t' -> trans l t t'' -> t' ≅ t''.
Proof.
  intros. do 3 red in H.
  rewrite ctree_eta in H0.
  genobs t ot. genobs t' ot'. rewrite ctree_eta, <- Heqot'.
  clear t t' Heqot Heqot'. revert t'' H0.
  dependent induction H; intros; inv_trans.
  - eapply IHtrans_; cbn.
    rewrite <- ctree_eta.
    destruct c, b, x0, x; intuition.
  - rewrite <- ctree_eta. destruct c, b, x, x0.
    now rewrite <- H, EQ.
  - subst. rewrite <- ctree_eta. now rewrite <- H, EQ.
  - rewrite EQ. apply br0_always_stuck.
Qed. 


Lemma ssim_sbisim_equiv_gen :
  forall {E F X Y} (L : rel _ _) `{Injective (@label E) (@label F) L}
    `{Deterministic _ _ L}
    (t : ctree E B01 X) (t' : ctree F B01 Y),
  ssim L t t' -> ssim (flip L) t' t -> sbisim L t t'.
Proof.
  intros until 2.
  coinduction R CH. red. red. cbn. split; intros.
  - step in H1. cbn in H1.
    apply H1 in H3 as H3'. destruct H3' as (? & ? & ? & ? & ?).
    exists x, x0. intuition. apply CH.
    + apply H5.
    + step in H2. cbn in H2. apply H2 in H4 as (? & ? & ? & ? & ?).
      do_inj.
      assert (t'0 ≅ x2) by (eapply ctree_B01_trans_det; eauto).
      now rewrite H6.
  - step in H2. cbn in H2.
    apply H2 in H3 as H3'. destruct H3' as (? & ? & ? & ? & ?).
    exists x, x0. intuition. apply CH.
    + step in H1. cbn in H1. apply H1 in H4 as (? & ? & ? & ? & ?).
      do_det.
      assert (t'0 ≅ x2) by (eapply ctree_B01_trans_det; eauto).
      now rewrite H6.
    + apply H5.
  Qed.

Lemma ssim_sbisim_equiv_eq : forall {E X} (t t' : ctree E B01 X),
  ssim eq t t' -> ssim eq t' t -> sbisim eq t t'.
Proof.
  intros. apply ssim_sbisim_equiv_gen; intros.
  - typeclasses eauto. 
  - typeclasses eauto.
  - apply H.
  - apply (@ssim_subrelation _ _ _ eq); auto.
    red. intros. subst. reflexivity.
Qed.

#[local] Definition t1 : ctree void1 (B01 +' B2) unit :=
  Step (Ret tt).

#[local] Definition t2 : ctree void1 (B01 +' B2) unit :=
  brS2 (Ret tt) (stuckD).

Lemma ssim_sbisim_nequiv :
  ssim eq t1 t2 /\ ssim (flip eq) t2 t1 /\ ~ sbisim eq t1 t2.
Proof.
  unfold t1, t2. intuition.
  - step. eapply step_ss_brS; auto.
    exact  (exist _ tt I).
    intros _. exists true. reflexivity.
  - step. eapply step_ss_brS; auto.
    exact  (exist _ true I).
    intro. exists tt. destruct x.
    + reflexivity.
    + step. apply ss_is_stuck.
      * apply stuckD_is_stuck.
      * admit. (* This looks wrong, Ret is not stuck *)
  - step in H. cbn in H. destruct H as [_ ?].
    specialize (H tau stuckD). lapply H; [| etrans].
    intros. destruct H0 as (? & ? & ? & ? & ?). subst.
    inv_trans. step in H1. cbn in H1. destruct H1 as [? _].
    specialize (H0 (val tt) stuckD). lapply H0. 2: { etrans. }
    intro. destruct H1 as (? & ? & ? & ? & ?). subst.
    now apply stuckD_is_stuck in H1.
Admitted.

