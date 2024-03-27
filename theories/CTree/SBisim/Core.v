From Coq Require Import
     Lia
     Basics
     Fin
     RelationClasses
     Program.Equality
     Logic.Eqdep.

From Coinduction Require Import
     coinduction rel tactics.

From CTree Require Import
  CTree.Core
  CTree.Equ
  CTree.Trans
  CTree.SBisim.SSim.

Local Open Scope ctree_scope.
Set Implicit Arguments.
Generalizable All Variables.

Arguments pointwise_relation /.
Arguments Proper /.
Arguments respectful /.
Arguments impl /.
Arguments flip /.

Section StrongBisim.
  Context {E F: Type} {HE: Encode E} {HF: Encode F} {X Y : Type}.
  Notation S := (ctree E X).
  Notation S' := (ctree F Y).

  (*| The symmetric closure of two [ss] |*)
  Program Definition sb L : mon (S -> S' -> Prop) :=
    {| body R t u := ss L R t u /\ ss (flip L) (flip R) u t |}.
  Next Obligation.
    split; intros.
    - destruct (H0 _ _ H2) as (? & ? & ? & ? & ?).
      exists x0, x1; auto.
    - destruct (H1 _ _ H2) as (? & ? & ? & ? & ?); unfold flip in *.
      exists x0, x1; auto.      
  Qed.

  #[global] Instance weq_sb : Proper (weq ==> weq) sb.
  Proof.
    split; intros.
    - split.
      + epose proof (weq_ss H). cbn in H1. setoid_rewrite <- H1. apply H0.
      + cbn in H. assert (flip x == flip y).
        { cbn. split; intro. apply H. apply H1. apply H. apply H1. }
        epose proof (weq_ss H1).
        cbn in H2. setoid_rewrite <- H2. apply H0.
    - split.
      + epose proof (weq_ss H). cbn in H1. setoid_rewrite H1. apply H0.
      + cbn in H. assert (flip x == flip y).
        { cbn. split; intro. apply H. apply H1. apply H. apply H1. }
        epose proof (weq_ss H1).
        cbn in H2. setoid_rewrite H2. apply H0.
  Qed.

  Definition sbisim L := gfp (sb L).

  #[global] Instance weq_sbisim : 
      Proper (weq ==> weq) sbisim.
  Proof.
    intros. split.
    - intro. unfold sbisim.
      epose proof (gfp_weq (sb x) (sb y)). lapply H1.
      + intro. red in H2. cbn in H2. rewrite <- H2. unfold sbisim in H0. apply H0.
      + now rewrite H.
    - intro. unfold sbisim.
      epose proof (gfp_weq (sb x) (sb y)). lapply H1.
      + intro. red in H2. cbn in H2. rewrite H2. unfold sbisim in H0. apply H0.
      + now rewrite H.
  Qed.

End StrongBisim.

(* This instance allows to use the symmetric tactic from coq-coinduction
   for homogeneous bisimulations *)
#[global] Instance sbisim_sym `{HE: Encode E} {X} {L: rel (label E) (label E) }
  {HL: Symmetric L}:
    Sym_from converse (sb (X:=X) L) (ss L).
  Proof.
    split; intro.
    - destruct H. split.
      + apply H.
      + cbn. intros. apply H0 in H1 as (? & ? & ? & ? & ?). apply HL in H3. eauto.
    - destruct H. split.
      + apply H.
      + cbn. intros. apply H0 in H1 as (? & ? & ? & ? & ?). apply HL in H3. eauto.
  Qed.

Local Open Scope ctree_scope.

(*| sb (bisimulation) notation |*)
Local Notation st L := (t (sb L)).
Local Notation sT L := (T (sb L)).
Local Notation sbt L := (bt (sb L)).
Local Notation sbT L := (bT (sb L)).

Notation "t ~ u" := (sbisim eq t u) (at level 70): ctree_scope.
Notation "t (~ L ) u" := (sbisim L t u) (at level 70): ctree_scope.
Notation "t [~ L] u" := (st L _ t u) (at level 78): ctree_scope.
Notation "t [~] u" := (st eq _ t u) (at level 78): ctree_scope.
Notation "t {~ L } u" := (sbt L _ t u) (at level 79): ctree_scope.
Notation "t {~} u" := (sbt eq _ t u) (at level 79): ctree_scope.
Notation "t {{ ~ L }} u" := (sb L _ t u) (at level 79): ctree_scope.
Notation "t {{~}} u" := (sb eq _ t u) (at level 79): ctree_scope.

Ltac fold_sbisim :=
  repeat
    match goal with
    | h: context[gfp (@sb ?E ?F ?C ?D ?X ?Y ?L)] |- _  => fold (@sbisim E F C D X Y L) in h
    | |- context[gfp (@sb ?E ?F ?C ?D ?X ?Y ?L)]       => fold (@sbisim E F C D X Y L)
    end.

Ltac __coinduction_sbisim R H :=
  (try unfold sbisim);
  apply_coinduction; fold_sbisim; intros R H.

#[global] Tactic Notation "__step_sbisim" :=
  match goal with
  | |- context[@sbisim ?E ?F ?C ?D ?X ?Y ?LR] =>
      unfold sbisim;
      step;
      fold (@sbisim E F C D X Y L)
  end.

#[local] Tactic Notation "step" := __step_sbisim || __step_ssim || step.

#[local] Tactic Notation "coinduction" simple_intropattern(R) simple_intropattern(H) :=
  __coinduction_sbisim R H || __coinduction_ssim R H || coinduction R H.

Ltac __step_in_sbisim H :=
  match type of H with
  | context [@sbisim ?E ?F ?C ?D ?X ?Y ?L ] =>
      unfold sbisim in H;
      step in H;
      fold (@sbisim E F C D X Y L) in H
  end.

#[local] Tactic Notation "step" "in" ident(H) := __step_in_sbisim H || __step_in_ssim H || step in H.

(*| Unary up-to-bisimulation enhancing function |*)
Variant sbisim_clos1_body `{HE: Encode E} {X} {LE}
  (R : ctree E X -> Prop) : ctree E X -> Prop :=
    | Sbisim_clos1 : forall t t'
                       (Sbisimt : t (~ LE) t')
                       (HR : R t'),
        @sbisim_clos1_body E HE X LE R t.

Program Definition sbisim_clos1 `{HE: Encode E} {X} {LE}
  : mon (ctree E X -> Prop) :=
  {| body := @sbisim_clos1_body E HE X LE |}.
Next Obligation. destruct H0; econstructor; eauto. Qed.

(*|
  This section should describe lemmas proved for the
  heterogenous version of `ss`, parametric on
  - Return types X, Y
  - Label types E, F
|*)
Section sbisim_heterogenous_theory.
  Context `{HE: Encode E} `{HF: Encode F} {X Y : Type}
          {L: rel (label E) (label F)}.

  Local Notation sb := (@sb E F HE HF X Y).
  Local Notation sbisim := (@sbisim E F HE HF X Y).
  Local Notation st L := (coinduction.t (sb L)).
  Local Notation sbt L := (coinduction.bt (sb L)).
  Local Notation sT  L := (coinduction.T (sb L)).

  (*| Strong bisimulation up-to [equ] is valid |*)
  Lemma equ_clos2_st : @equ_clos2 E F X Y HE HF <= (st L).
  Proof.
    apply Coinduction; cbn.
    intros R x y [x' y' x'' y'' EQ' [Fwd Back] EQ'']; split.
    - intros l z x'z.
      rewrite EQ' in x'z.
      apply Fwd in x'z.
      destruct x'z as (? & ? & ? & ? & ?).
      do 2 eexists; intuition.
      rewrite <- EQ''; eauto.
      eapply (f_Tf (sb L)).
      econstructor; eauto.
      assumption.
    - intros l z y'z.
      rewrite <- EQ'' in y'z.
      apply Back in y'z.
      destruct y'z as (? & ? & ? & ? & ?).
      do 2 eexists; intuition.
      rewrite EQ'; eauto.
      eapply (f_Tf (sb L)).
      econstructor; eauto.
      eauto.
  Qed.

(*|
    Aggressively providing instances for rewriting [equ] under all [sb]-related
    contexts.
|*)
  #[global] Instance equ_clos2_st_goal RR :
    Proper (@equ E HE X X eq ==> @equ F HF Y Y eq ==> flip impl) (st L RR).
  Proof.
    cbn; intros ? ? eq1 ? ? eq2 H.
    apply (ft_t equ_clos2_st); econstructor; [eauto | | symmetry; eauto]; assumption.
  Qed.

  #[global] Instance equ_clos2_st_ctx RR :
    Proper (@equ E HE X X eq ==> @equ F HF Y Y eq ==> impl) (st L RR).
  Proof.
    cbn; intros ? ? eq1 ? ? eq2 H.
    apply (ft_t equ_clos2_st); econstructor; [symmetry; eauto | | eauto]; assumption.
  Qed.

  #[global] Instance equ_clos2_sT_goal RR f :
    Proper (equ eq ==> equ eq ==> flip impl) (sT L f RR).
  Proof.
    cbn; intros ? ? eq1 ? ? eq2 H.
    apply (fT_T equ_clos2_st); econstructor; [eauto | | symmetry; eauto]; assumption.
  Qed.

  #[global] Instance equ_clos2_sT_ctx RR f :
    Proper (equ eq ==> equ eq ==> impl) (sT L f RR).
  Proof.
    cbn; intros ? ? eq1 ? ? eq2 H.
    apply (fT_T equ_clos2_st); econstructor; [symmetry; eauto | | eauto]; assumption.
  Qed.

  #[global] Instance equ_clos2_sbisim_goal :
    Proper (equ eq ==> equ eq ==> flip impl) (sbisim L).
  Proof.
    cbn; intros ? ? eq1 ? ? eq2 H.
    apply (ft_t equ_clos2_st); econstructor; [eauto | | symmetry; eauto]; assumption.
  Qed.

  #[global] Instance equ_clos2_sbisim_ctx :
    Proper (equ eq ==> equ eq ==> impl) (sbisim L).
  Proof.
    cbn; intros ? ? eq1 ? ? eq2 H.
    apply (ft_t equ_clos2_st); econstructor; [symmetry; eauto | | eauto]; assumption.
  Qed.

  #[global] Instance equ_ss_clos2_goal {r} : Proper (@equ E HE X X eq ==> @equ F HF Y Y eq ==> flip impl) (ss L r).
  Proof.
    intros t t' tt' u u' uu'; cbn; intros.
    rewrite tt' in H0. apply H in H0 as (? & ? & ? & ? & ?).
    eexists; eexists; eauto. rewrite uu'. eauto.
  Qed.

  #[global] Instance equ_ss_clos2_ctx {r} : Proper (@equ E HE X X eq ==> @equ F HF Y Y eq ==> impl) (ss L r).
  Proof.
    intros t t' tt' u u' uu'; intros.
    rewrite tt', uu'. reflexivity.
  Qed.
  
  (*| Binary up-to-bisimulation enhancing function |*)
  Variant sbisim_clos2_body {LE LF}
          (R : rel (ctree E X) (ctree F Y)) : (rel (ctree E X) (ctree F Y)) :=
    | Sbisim_clos2 : forall t t' u' u
                      (Sbisimt : t (~ LE) t')
                      (HR : R t' u')
                      (Sbisimu : u' (~ LF) u),
        @sbisim_clos2_body LE LF R t u.

  Program Definition sbisim_clos2 {LE LF} : mon (rel (ctree E X) (ctree F Y)) :=
    {| body := @sbisim_clos2_body LE LF |}.
  Next Obligation. destruct H0; econstructor; eauto. Qed.

  
  (*| stuck ctrees can be simulated by anything. |*)
  Lemma is_stuck_sb (R : rel _ _) (t : ctree E X) (t': ctree F Y):
    is_stuck t -> is_stuck t' -> sb L R t t'.
  Proof.
    split; repeat intro; exfalso. 
    - apply H; now (exists l, t'0).
    - apply H0; now (exists l, t'0).
  Qed.

  Theorem sbisim_clos2_upto R: @sbisim_clos2 eq eq R <= st L R.
  Proof.
    apply leq_t.
    intros S t u HRel.
    split; cbn; intros ? ? TR.
    - inv HRel.
      step in Sbisimt; apply Sbisimt in TR; destruct TR as (? & ? & TR & Sbis & <-).
      apply HR in TR; destruct TR as (? & ? & TR & Sbis' & HL).
      step in Sbisimu; apply Sbisimu in TR; destruct TR as (? & ? & TR & Sbis'' & <-).
      do 2 eexists; repeat split; eauto.
      econstructor.
      apply Sbis.
      eauto.
      apply Sbis''.
    - inv HRel.
      step in Sbisimu; apply Sbisimu in TR; destruct TR as (? & ? & TR & Sbis & <-).
      apply HR in TR; destruct TR as (? & ? & TR & Sbis' & HL).
      step in Sbisimt; apply Sbisimt in TR; destruct TR as (? & ? & TR & Sbis'' & <-).
      do 2 eexists; repeat split; eauto.
      econstructor.
      apply Sbis''.
      eauto.
      apply Sbis.
  Qed.

End sbisim_heterogenous_theory.

Definition respects_val `{Encode E} `{Encode F} (L : rel (label E) (label F)) :=
  forall l l', L l l' -> is_val l <-> is_val l'.

Definition respects_tau `{Encode E} `{Encode F} (L : rel (label E) (label F)) :=
  forall l l', L l l' -> l = tau <-> l' = tau.

Definition eq_obs `{Encode E} (L : relation (label E)) : Prop :=
  forall e e' (x : encode e) (x' : encode e'),
    L (obs e x) (obs e' x') -> obs e x = obs e' x'.

Lemma respects_val_eq `{Encode E}: respects_val (@eq (label E)).
Proof.
  split; intros; subst; auto. 
Defined.

Lemma respects_tau_eq `{Encode E}: respects_tau (@eq (label E)).
Proof.
  split; intros; subst; auto. 
Defined.
Global Hint Resolve respects_val_eq respects_tau_eq: ctree.

Section sbisim_homogenous_theory.
  Context {E: Type} {HE: Encode E} {X: Type} {L: relation (label E)}.

  Local Notation sb  := (@sb E E HE HE X X).
  Local Notation sbisim := (@sbisim E E HE HE X X).
  Local Notation st L := (coinduction.t (sb L)).
  Local Notation sbt L := (coinduction.bt (sb L)).
  Local Notation sT  L := (coinduction.T (sb L)).

  (*|
    This is just a hack suggested by Damien Pous to avoid a
    universe inconsistency when using both the relational algebra
    and coinduction libraries (we fix the type at which we'll use [eq]). |*)

  Lemma refl_st {RL: Reflexive L} : const eq <= (st L).
  Proof.
    apply leq_t.
    split; intros; cbn*; intros; inv H; subst;
      exists l, t'; split; eauto.
  Qed.

(*|
[converse] is compatible
i.e. validity of up-to symmetry
|*)
  Lemma converse_st `{SL: Symmetric _ L}: converse <= (st L).
  Proof.
    apply leq_t; cbn.
    intros R ? ? [H1 H2]; split; intros.
    - destruct (H2 _ _ H) as (? & ? & ? & ? & ?); subst; symmetry in H4; eauto.
    - destruct (H1 _ _ H) as (? & ? & ? & ? & ?); subst; symmetry in H4; eauto.
  Qed.

(*|
[square] is compatible
i.e. validity of up-to transivitiy
|*)
  Lemma square_st `{TR: Transitive _ L}: square <= (st L).
  Proof.
    apply Coinduction; cbn.
    intros R x z [y [xy yx] [yz zy]].
    split.
     - intros ?l x' xx'.
      destruct (xy _ _ xx') as (?l & y' & yy' & ? & EQ).
      destruct (yz _ _ yy') as (?l & z' & zz' & ? & EQ').
      do 2 eexists; repeat split.
      eauto.
      apply (f_Tf (sb L)).
      eexists; eauto.
      transitivity l0; assumption.
    - intros ?l z' zz'.
      destruct (zy _ _ zz') as (?l & y' & yy' & ? & EQ).
      destruct (yx _ _ yy') as (?l & x' & xx' & ? & EQ').
      do 2 eexists; repeat split.
      eauto.
      apply (f_Tf (sb L)).
      eexists; eauto.
      transitivity l0; assumption.
  Qed.

(*|
Reflexivity
|*)
  #[global] Instance Reflexive_st R `{Reflexive _ L}: Reflexive (st L R).
  Proof. apply build_reflexive; apply ft_t; apply refl_st. Qed.

  #[global] Instance Reflexive_sbisim `{Reflexive _ L}: Reflexive (sbisim L).
  Proof. now apply Reflexive_st. Qed.

  #[global] Instance Reflexive_sbt R `{Reflexive _ L}: Reflexive (sbt L R).
  Proof. apply build_reflexive; apply fbt_bt; apply refl_st. Qed.

  #[global] Instance Reflexive_sT f R `{Reflexive _ L}: Reflexive (sT L f R).
  Proof. apply build_reflexive; apply fT_T; apply refl_st. Qed.

(*|
Transitivity
|*)
  #[global] Instance Transitive_st R `{Transitive _ L}: Transitive (st L R).
  Proof. apply build_transitive; apply ft_t; apply (square_st). Qed.

  #[global] Instance Transitive_sbisim `{Transitive _ L}: Transitive (sbisim L).
  Proof. now apply Transitive_st. Qed.

  #[global] Instance Transitive_sbt R `{Transitive _ L}: Transitive (sbt L R).
  Proof. apply build_transitive; apply fbt_bt; apply square_st. Qed.

  #[global] Instance Transitive_sT f R `{Transitive _ L}: Transitive (sT L f R).
  Proof. apply build_transitive; apply fT_T; apply square_st. Qed.

(*|
Symmetry
|*)
  #[global] Instance Symmetric_st R `{Symmetric _ L}: Symmetric (st L R).
  Proof. apply build_symmetric; apply ft_t; apply (converse_st). Qed.

  #[global] Instance Symmetric_sbisim `{Symmetric _ L}: Symmetric (sbisim L).
  Proof. now apply Symmetric_st. Qed.

  #[global] Instance Symmetric_sbt R `{Symmetric _ L}: Symmetric (sbt L R).
  Proof. apply build_symmetric; apply fbt_bt; apply converse_st. Qed.

  #[global] Instance Symmetric_sT f R `{Symmetric _ L}: Symmetric (sT L f R).
  Proof. apply build_symmetric; apply fT_T; apply converse_st. Qed.

(*|
Thus bisimilarity and [t R] are always equivalence relations.
|*)
  #[global] Instance Equivalence_st `{Equivalence _ L} R: Equivalence (st L R).
  Proof. split; typeclasses eauto. Qed.

  #[global] Instance Equivalence_bisim `{Equivalence _ L}: Equivalence (sbisim L).
  Proof. split; typeclasses eauto. Qed.

  #[global] Instance Equivalence_sbt `{Equivalence _ L} R: Equivalence (sbt L R).
  Proof. split; typeclasses eauto. Qed.

  #[global] Instance Equivalence_sT `{Equivalence _ L} f R: Equivalence ((T (sb L)) f R).
  Proof. split; typeclasses eauto. Qed.

(*|
Aggressively providing instances for rewriting hopefully faster
[sbisim] under all [sb]-related contexts (consequence of the transitivity
of the companion).
|*)
  #[global] Instance sbisim_sbisim_clos2_goal `{Transitive _ L} `{Symmetric _ L} :
    Proper (sbisim L ==> sbisim L ==> flip impl) (sbisim L).
  Proof.
    repeat intro.
    etransitivity; [etransitivity; eauto | symmetry; eassumption].
  Qed.

  #[global] Instance sbisim_sbisim_clos2_ctx `{Transitive _ L} `{Symmetric _ L} :
    Proper (sbisim L ==> sbisim L ==> impl) (sbisim L).
  Proof.
    repeat intro.
    etransitivity; [symmetry; eassumption | etransitivity; eauto].
  Qed.

  #[global] Instance sbisim_clos2_st_goal `{Equivalence _ L} R:
    Proper (sbisim L ==> sbisim L ==> flip impl) (st L R).
  Proof.
    cbn; intros ? ? eq1 ? ? eq2 ?.
    rewrite eq1, eq2.
    auto.
  Qed.

  #[global] Instance sbisim_clos2_st_ctx `{Equivalence _ L} R :
    Proper (sbisim L ==> sbisim L ==> impl) (st L R).
  Proof.
    cbn; intros ? ? eq1 ? ? eq2 ?.
    rewrite <- eq1, <- eq2.
    auto.
  Qed.

  #[global] Instance sbisim_clos2_sT_goal `{Equivalence _ L} R f :
    Proper (sbisim L ==> sbisim L ==> flip impl) (sT L f R).
  Proof.
    cbn; intros ? ? eq1 ? ? eq2 ?.
    rewrite eq1, eq2.
    auto.
  Qed.

  #[global] Instance sbisim_clos2_sT_ctx `{Equivalence _ L} R f :
    Proper (sbisim L ==> sbisim L ==> impl) (sT L f R).
  Proof.
    cbn; intros ? ? eq1 ? ? eq2 ?.
    rewrite <- eq1, <- eq2.
    auto.
  Qed.

  #[global] Instance equ_sbt_closed_goal `{EqL: Equivalence _ L} R:
    Proper (equ eq ==> equ eq ==> flip impl) (sbt L R).
  Proof.
    repeat intro. pose proof (gfp_bt (sb L) R).
    etransitivity; [| etransitivity]; [ | apply H1 | ]; apply H2.
    rewrite H; auto. rewrite H0; auto.
  Qed.

  #[global] Instance equ_sbt_closed_ctx `{EqL: Equivalence _ L} {R} :
    Proper (equ eq ==> equ eq ==> impl) (sbt L R).
  Proof.
    repeat intro. pose proof (gfp_bt (sb L) R).
    etransitivity; [| etransitivity]; [ | apply H1 | ]; apply H2.
    rewrite H; auto. rewrite H0; auto.
  Qed.

End sbisim_homogenous_theory.


(*|
Up-to [bind] context bisimulations
----------------------------------
We have proved in the module [Equ] that up-to bind context is
a valid enhancement to prove [equ].
We now prove the same result, but for strong and weak bisimulation.
|*)

Section bind.
  Obligation Tactic := trivial.
  Context {E F: Type} {HE: Encode E} {HF: Encode F} {X X' Y Y': Type}
    {L: rel (label E) (label F)} (R0 : rel X Y).

  Program Definition bind_ctx_sbisim L0 : mon (rel (ctree E X') (ctree F Y')) :=
    {|body := fun R => @bind_ctx E F HE HF X Y X' Y' (sbisim L0)
                              (pointwise R0 R) |}.
  Next Obligation.
    intros ??? H. apply leq_bind_ctx. intros ?? H' ?? H''.
    apply in_bind_ctx. apply H'. intros t t' HS. apply H, H'', HS.
  Qed.

(*|
The resulting enhancing function gives a valid up-to technique
|*)
  Lemma bind_ctx_sbisim_t L0 :
    is_update_val_rel L R0 L0 -> bind_ctx_sbisim L0 <= st L.
  Proof.
    intros HL0. apply Coinduction.
    intros R. apply (leq_bind_ctx _).
    intros t1 t2 tt k1 k2 kk.
    step in tt; split; simpl;  intros l u STEP.
    - apply trans_bind_inv in STEP as [(VAL & t' & STEP & EQ) | (v & STEPres & STEP)]; cbn in *.
      + apply tt in STEP as (l' & u' & STEP & SIM & LBL).
        apply HL0 in LBL; etrans.
        apply update_val_rel_nonval_l in LBL as [VAL' LBL]; auto.
        do 2 eexists. split.
        apply trans_bind_l; eauto.
        split; auto.
        apply (fT_T equ_clos2_st).
        econstructor; [exact EQ | | reflexivity].
        apply (fTf_Tf (sb L)).
        apply in_bind_ctx; auto.
        intros ? ? ?.
        apply (b_T (sb L)).
        red in kk; now apply kk.
      + apply tt in STEPres as (l' & u' & STEPres & SIM & LBL).
        apply HL0 in LBL; etrans.
        apply update_val_rel_val_l in LBL as (v' & -> & ?).
        pose proof (trans_val_inv STEPres) as EQ.
        rewrite <- EQ in STEPres.
        specialize (kk v v' H).
        apply kk in STEP as (l' & u'' & STEP & EQ'' & ?); cbn in *.
        do 2 eexists; split.
        eapply trans_bind_r; eauto.
        split; auto.
        eapply (id_T (sb L)); auto.
    - apply trans_bind_inv in STEP as [(H & t' & STEP & EQ) | (v & STEPres & STEP)]; cbn in *.
      + apply tt in STEP as (l' & u' & STEP & EQ' & LBL).
        apply HL0 in LBL; etrans.
        apply update_val_rel_nonval_r in LBL as [VAL' LBL]; auto.
        do 2 eexists; split.
        apply trans_bind_l; eauto.
        split; auto.
        apply (fT_T equ_clos2_st).
        symmetry in EQ.
        econstructor; [reflexivity | | exact EQ].
        apply (fTf_Tf (sb L)).
        apply in_bind_ctx; auto.
        intros ? ? ?.
        apply (b_T (sb L)).
        red in kk; now apply kk.
      + apply tt in STEPres as (l' & u' & STEPres & EQ' & LBL).
        apply HL0 in LBL; etrans.
        apply update_val_rel_val_r in LBL as (v' & -> & ?).
        pose proof (trans_val_inv STEPres) as EQ.
        rewrite <- EQ in STEPres.
        specialize (kk v' v H).
        apply kk in STEP as (u'' & ? & STEP & EQ'' & ?); cbn in *.
        do 2 eexists; split.
        eapply trans_bind_r; eauto.
        split; auto.
        eapply (id_T (sb L)); auto.
  Qed.

End bind.

Import Ctree.
Import CTreeNotations.

(*|
Expliciting the reasoning rule provided by the up-to principles.
This principle is unusable for most [L], see https://github.com/vellvm/ctrees/issues/21
|*)
Lemma st_clo_bind_gen {E F: Type} {HE: Encode E} {HF: Encode F} {X Y X' Y': Type}
  {L : rel (label E) (label F)}
  (R0 : rel X Y) L0
  (t1 : ctree E X) (t2: ctree F Y)
  (HL0 : is_update_val_rel L R0 L0)
  (k1 : X -> ctree E X') (k2 : Y -> ctree F Y') RR:
  t1 (~L0) t2 ->
  (forall x y, R0 x y -> (st L RR) (k1 x) (k2 y)) ->
  st L RR (t1 >>= k1) (t2 >>= k2).
Proof.
  intros ? ?.
  apply (ft_t (@bind_ctx_sbisim_t E F HE HF X X' Y Y' L R0 L0 HL0)).
  apply in_bind_ctx; eauto.
Qed.

Lemma st_clo_bind {E F: Type} {HE: Encode E} {HF: Encode F} {X Y X' Y': Type}
  {L : rel (label E) (label F)}
  (R0 : rel X Y)
  (t1 : ctree E X) (t2: ctree F Y)
  (k1 : X -> ctree E X') (k2 : Y -> ctree F Y') RR:
  t1 (~update_val_rel L R0) t2 ->
  (forall x y, R0 x y -> (st L RR) (k1 x) (k2 y)) ->
  st L RR (t1 >>= k1) (t2 >>= k2).
Proof.
  intros ? ?.
  eapply st_clo_bind_gen; eauto.
  apply update_val_rel_correct.
Qed.

Lemma st_clo_bind_eq {E: Type} {HE: Encode E} {X X': Type}
      (t1 : ctree E X) (t2: ctree E X)
      (k1 : X -> ctree E X') (k2 : X -> ctree E X') RR:
  t1 ~ t2 ->
  (forall x, st eq RR (k1 x) (k2 x)) ->
  st eq RR (t1 >>= k1) (t2 >>= k2).
Proof.
  intros ? ?.
  eapply st_clo_bind_gen.
  - apply is_update_val_rel_eq.
  - assumption.
  - intros. now subst.
Qed.

Lemma sbt_clo_bind_gen `{HE: Encode E} `{HF: Encode F} {X Y X' Y': Type} {L : rel (label E) (label F)}
      (R0 : rel X Y) L0
      (t1 : ctree E X) (t2: ctree F Y)
      (HL0 : is_update_val_rel L R0 L0)
      (k1 : X -> ctree E X') (k2 : Y -> ctree F Y') RR:
  t1 (~L0) t2 ->
  (forall x y, R0 x y -> (sbt L RR) (k1 x) (k2 y)) ->
  sbt L RR (t1 >>= k1) (t2 >>= k2).
Proof.
  intros ? ?.
  apply (fbt_bt (@bind_ctx_sbisim_t E F HE HF X X' Y Y' L R0 L0 HL0)).
  apply in_bind_ctx; eauto.
Qed.

Lemma sbt_clo_bind {E F: Type} `{HE: Encode E} `{HF: Encode F} {X Y X' Y': Type}
  {L : rel (label E) (label F)}
      (R0 : rel X Y)
      (t1 : ctree E X) (t2: ctree F Y)
      (k1 : X -> ctree E X') (k2 : Y -> ctree F Y') RR:
  t1 (~update_val_rel L R0) t2 ->
  (forall x y, R0 x y -> (sbt L RR) (k1 x) (k2 y)) ->
  sbt L RR (t1 >>= k1) (t2 >>= k2).
Proof.
  intros ? ?.
  eapply sbt_clo_bind_gen; eauto.
  apply update_val_rel_correct.
Qed.

Lemma sbt_clo_bind_eq `{HE: Encode E} {X X': Type}
      (t1 : ctree E X) (t2: ctree E X)
      (k1 : X -> ctree E X') (k2 : X -> ctree E X') RR:
  t1 ~ t2 ->
  (forall x, sbt eq RR (k1 x) (k2 x)) ->
  sbt eq RR (t1 >>= k1) (t2 >>= k2).
Proof.
  intros ? ?.
  eapply sbt_clo_bind_gen.
  - apply is_update_val_rel_eq.
  - assumption.
  - intros. now subst.
Qed.

Lemma sbisim_clo_bind_gen `{HE: Encode E} `{HF: Encode F} {X Y X' Y': Type} {L : rel (label E) (label F)}
      (R0 : rel X Y) L0
      (t1 : ctree E X) (t2: ctree F Y)
      (HL0 : is_update_val_rel L R0 L0)
      (k1 : X -> ctree E X') (k2 : Y -> ctree F Y') :
  t1 (~L0) t2 ->
  (forall x y, R0 x y -> k1 x (~L) k2 y) ->
  t1 >>= k1 (~L) t2 >>= k2.
Proof.
  now apply st_clo_bind_gen.
Qed.

Lemma sbisim_clo_bind `{HE: Encode E} `{HF: Encode F} {X Y X' Y': Type}
  {L : rel (label E) (label F)}
  (R0 : rel X Y)
  (t1 : ctree E X) (t2: ctree F Y)
  (k1 : X -> ctree E X') (k2 : Y -> ctree F Y') :
  t1 (~update_val_rel L R0) t2 ->
  (forall x y, R0 x y -> k1 x (~L) k2 y) ->
  t1 >>= k1 (~L) t2 >>= k2.
Proof. now apply st_clo_bind. Qed.

Lemma sbisim_clo_bind_eq `{HE: Encode E} {X X': Type}
      (t1 : ctree E X) (t2: ctree E X)
      (k1 : X -> ctree E X') (k2 : X -> ctree E X') :
  t1 ~ t2 ->
  (forall x, k1 x ~ k2 x) ->
  t1 >>= k1 ~ t2 >>= k2.
Proof. now apply st_clo_bind_eq. Qed.

(*|
And in particular, we get the proper instance justifying rewriting [~] to the left of a [bind].
|*)
#[global] Instance bind_sbisim_cong_gen `{HE: Encode E} {X X'} (RR: relation (ctree E X')):
  Proper (sbisim eq ==> pointwise_relation X (st eq RR) ==> st eq RR) (@bind E HE X X').
Proof.
  unfold Proper, respectful, pointwise_relation.
  intros.
  now apply st_clo_bind_eq.
Qed.

Ltac __upto_bind_sbisim :=
  match goal with
    |- @sbisim ?E ?F ?C ?D ?X ?Y ?L
              (Ctree.bind (X := ?T) _ _) (Ctree.bind (X := ?T) _ _) => apply sbisim_clo_bind_eq
  | |- body (t (@sb ?E ?F ?C ?D ?X ?Y ?L)) ?R
           (Ctree.bind (X := ?X') _ _) (Ctree.bind (X := ?X') _ _) =>
      apply st_clo_bind_eq
  | |- body (bt (@sb ?E ?F ?C ?D ?X ?Y ?L)) ?R
           (Ctree.bind (X := ?X') _ _) (Ctree.bind (X := ?X') _ _) =>
      apply sbt_clo_bind_eq
  end.

Ltac __upto_bind_eq_sbisim :=
  match goal with
  | |- @sbisim ?E ?F ?C ?D ?X ?Y eq (Ctree.bind (X := ?Z) _ _) (Ctree.bind (X := ?Z) _ _) =>
      __upto_bind_sbisim; [reflexivity | intros ?]
  | _ =>
      __upto_bind_sbisim; [reflexivity | intros ? ? EQl]
  end.

Section Ctx.

  Context {E F: Type} {HE: Encode E} {HF: Encode F} {X X' Y Y': Type}.

  Definition vis_ctx (e : E) (f: F)
             (R: rel (encode e -> ctree E X') (encode f -> ctree F Y')):
    rel (ctree E X') (ctree F Y') :=
    sup_all (fun k => sup (R k) (fun k' => pairH (Vis e k) (Vis f k'))).
  
  Lemma leq_vis_ctx (e: E) (f: F):
    forall (R: rel (encode e -> ctree E X') (encode f -> ctree F Y')) R', vis_ctx R <= R' <->
              (forall k k', R k k' -> R' (Vis e k) (Vis f k')).
  Proof.
    intros.
    unfold vis_ctx.
    setoid_rewrite sup_all_spec.
    setoid_rewrite sup_spec.
    setoid_rewrite <-leq_pairH.
    firstorder.
  Qed.

  Lemma in_vis_ctx e f (R :rel _ _) x x' :
    R x x' -> vis_ctx R (Vis e x) (Vis f x').
  Proof. intros. now apply ->leq_vis_ctx. Qed.
  #[global] Opaque vis_ctx.

End Ctx.

Section sb_vis_ctx.

  Obligation Tactic := idtac.

  Section Gen.
    Context {E F: Type} {HE: Encode E} {HF: Encode F} {X Y X' Y': Type}.

    Program Definition vis_ctx_sbisim_gen (e : E) (f: F)
      (right : encode e -> encode f) (left : encode f -> encode e) :
      mon (rel (ctree E X') (ctree F Y')) :=
      {|body := fun R =>
                  @vis_ctx E F HE HF X' Y' e f
                    (fun ff gg =>
                       (forall x, R (ff x) (gg (right x))) /\
                         (forall y, R (ff (left y)) (gg y)))
      |}.
    Next Obligation.
      intros e f Rf Rg ? ? ? . apply leq_vis_ctx. intros k k' [H1 H2].
      apply in_vis_ctx; split; intros.
      eapply H in H1; eapply H1.
      eapply H in H2; eapply H2.
    Qed.

    (*| The resulting enhancing function gives a valid up-to technique |*)
    Lemma vis_ctx_sbisim_gen_t {L: rel (label E) (label F)} (e : E) (f: F)
      (right: encode e -> encode f) (left: encode f -> encode e) :
      (forall x, L (obs e x) (obs f (right x))) ->
      (forall y, L (obs e (left y)) (obs f y)) ->
      vis_ctx_sbisim_gen right left <= (st L).
    Proof.
      intros HHT HHF.
      apply Coinduction.
      intros R.
      apply leq_vis_ctx.
      intros k k' kk'.
      cbn.
      split; intros ? ? TR; trans in TR; cbn.
      - do 2 eexists; split; etrans; split; auto.
        rewrite Eqt; now eapply (b_T (sb L)).
      - do 2 eexists; split; etrans; split; auto.
        rewrite Eqt; now eapply (b_T (sb L)).
    Qed.

  End Gen.

  Section Specialized.

    Context {E: Type} `{HE: Encode E} {X X': Type}.

    Program Definition vis_ctx_sbisim (e : E) :
      mon (rel (ctree E X') (ctree E X')) :=
      {|body := fun R =>
                  @vis_ctx E E HE HE X' X' e e
                    (fun ff gg => forall x, R (ff x) (gg x))
      |}.
    Next Obligation.
      intros e ? ? ?. apply leq_vis_ctx. intros k k' H0.
      apply in_vis_ctx; intros.
      eapply H in H0; eapply H0.
    Qed.

(*|
The resulting enhancing function gives a valid up-to technique
|*)
    Lemma vis_ctx_sbisim_t (e : E) :
      vis_ctx_sbisim e <= (st eq).
    Proof.
      apply Coinduction.
      intros R.
      apply leq_vis_ctx.
      intros k k' kk'.
      cbn.
      split; intros ? ? TR; trans in TR; subst; cbn.
      - do 2 eexists; split; etrans; split; auto.
        rewrite Eqt; now eapply (b_T (sb eq)).
      - do 2 eexists; split; etrans; split; auto.
        rewrite Eqt; now eapply (b_T (sb eq)).
    Qed.

  End Specialized.

End sb_vis_ctx.

Arguments vis_ctx_sbisim_t {E HE X'} e.

Ltac __upto_vis_sbisim :=
  match goal with
    |- @sbisim ?E ?F ?HE ?HF ?X _ ?RR (Vis ?e _) (Vis ?e _) =>
      apply (ft_t (vis_ctx_sbisim_t e)), in_vis_ctx; intros ?
  | |- body (t (@sb ?E ?F ?HE ?HF ?X _ _ ?R _)) ?RR (Vis ?e _) (Vis ?f _) =>
      apply (ft_t (vis_ctx_sbisim_t e)), in_vis_ctx; intros ?
  | |- body (bt (@sb ?E ?F ?C _ ?X _ _ ?R _)) ?RR (Vis ?e _) (Vis ?f _) =>
      apply (fbt_bt (vis_ctx_sbisim_t e)), in_vis_ctx; intros ?
  end.

#[local] Tactic Notation "upto_vis" := __upto_vis_sbisim.

Ltac __play_sbisim := step; split; cbn; intros ? ? ?TR.

Ltac __playL_sbisim H :=
  step in H;
  let Hf := fresh "Hf" in
  destruct H as [Hf _];
  cbn in Hf; edestruct Hf as (? & ? & ?TR & ?EQ & ?);
  clear Hf; subst; [etrans |].

Ltac __eplayL_sbisim :=
  match goal with
  | h : @sbisim ?E ?F _ _ ?X ?Y ?L _ _ |- _ =>
      __playL_sbisim h
  end.

Ltac __playR_sbisim H :=
  step in H;
  let Hb := fresh "Hb" in
  destruct H as [_ Hb];
  cbn in Hb; edestruct Hb as (? & ? & ?TR & ?EQ & ?);
  clear Hb; subst; [etrans |].

Ltac __eplayR_sbisim :=
  match goal with
  | h : @sbisim ?E ?F ?HE ?HF ?X ?Y ?L _ _ |- _ =>
      __playR_sbisim h
  end.

#[local] Tactic Notation "play" := __play_sbisim.
#[local] Tactic Notation "playL" "in" ident(H) := __playL_sbisim H.
#[local] Tactic Notation "playR" "in" ident(H) := __playR_sbisim H.
#[local] Tactic Notation "eplayL" := __eplayL_sbisim.
#[local] Tactic Notation "eplayR" := __eplayR_sbisim.

(*|
Proof rules for [~]
-------------------
Naive bisimulations proofs naturally degenerate into exponential proofs,
splitting into two goals at each step.
The following proof rules avoid this issue in particular cases.

Be sure to notice that contrary to equations such that [sb_guard] or
up-to principles such that [upto_vis], (most of) these rules consume a [sb].

TODO: need to think more about this --- do we want more proof rules?
Do we actually need them on [sb (st R)], or something else?
|*)
Section Proof_Rules.
  Context {E F: Type} {HE: Encode E} {HF: Encode F} {X Y: Type} {L: rel (label E) (label F)}.

  Lemma step_sb_ret_gen(x: X) (y: Y) (R : rel (ctree E X) (ctree F Y)) :
    R stuck stuck ->
    L (val x) (val y) ->
    (Proper (equ eq ==> equ eq ==> impl) R) ->
    sb L R (Ret x) (Ret y).
  Proof.
    intros Rstuck ValRefl PROP.
    split; apply step_ss_ret_gen; eauto.
    typeclasses eauto.
  Qed.
  
  Lemma step_sb_ret (x: X) (y: Y) (R : rel (ctree E X) (ctree F Y)) :
    L (val x) (val y) ->
    sbt L R (Ret x) (Ret y).
  Proof.
    intros LH; subst.
    apply step_sb_ret_gen; eauto.
    - step; split;
      apply is_stuck_sb; apply stuck_is_stuck.
    - typeclasses eauto.
  Qed.

  (*|
    The vis nodes are deterministic from the perspective of the labeled transition system,
    stepping is hence symmetric and we can just recover the itree-style rule.
  |*)
  Lemma step_sb_vis_gen {X' Y'} (e: E) (f: F)
    (k: encode e -> ctree E X') (k': encode f -> ctree F Y') {R : rel _ _}:
    (Proper (equ eq ==> equ eq ==> impl) R) ->
    (forall x, exists y, R (k x) (k' y) /\ L (obs e x) (obs f y)) ->
    (forall y, exists x, R (k x) (k' y) /\ L (obs e x) (obs f y)) ->
    sb L R (Vis e k) (Vis f k').
  Proof.
    intros PR EQs EQs'.
    split; apply step_ss_vis_gen; eauto.
    typeclasses eauto.
  Qed.

  Lemma step_sb_vis {X' Y'} (e: E) (f: F) (k: encode e -> ctree E X') (k': encode f -> ctree F Y') {R : rel _ _}:
    (forall x, exists y, st L R (k x) (k' y) /\ L (obs e x) (obs f y)) ->
    (forall y, exists x, st L R (k x) (k' y) /\ L (obs e x) (obs f y)) ->
    sbt L R (Vis e k) (Vis f k').
  Proof.
    intros EQs EQs'.
    apply step_sb_vis_gen; eauto.
    typeclasses eauto.
  Qed.

  (*| Same goes for visible tau nodes. |*)
  Lemma step_sb_step_gen (t : ctree E X) (t' : ctree F Y) (R: rel _ _) :
    (Proper (equ eq ==> equ eq ==> impl) R) ->
    L tau tau ->
    (R t t') ->
    sb L R (step t) (step t').
  Proof.
    intros. split; apply step_ss_step_gen; auto.
    typeclasses eauto.
  Qed.

  Lemma step_sb_step (t : ctree E X) (t' : ctree F Y) (R: rel _ _) :
    L tau tau ->
    (st L R t t') ->
    sbt L R (step t) (step t').
  Proof.
    apply step_sb_step_gen.
    typeclasses eauto.
  Qed.

  Lemma step_sb_br_gen {n m}
    (k : fin' n -> ctree E X) (k': fin' m  -> ctree F Y) (R : rel _ _):
    (Proper (equ eq ==> equ eq ==> impl) R) ->
    L tau tau ->
    (forall x, exists y, R (k x) (k' y)) ->
    (forall y, exists x, R (k x) (k' y)) ->
    sb L R (Br n k) (Br m k').
  Proof.
    intros PROP ? EQs1 EQs2.
    split; intros ? ? TR; trans in TR. 
    - destruct (EQs1 n0) as [y HR].
      exists tau, (k' y); split; [etrans|].
      rewrite Eqt; auto.
    - destruct (EQs2 n0) as [y HR].
      exists tau, (k y); split; [etrans|].
      rewrite Eqt; auto.
  Qed.

  Lemma step_sb_br {n m}
    (k : fin' n -> ctree E X) (k': fin' m  -> ctree F Y) (R : rel _ _):
    L tau tau ->
    (forall x, exists y, st L R (k x) (k' y)) ->
    (forall y, exists x, st L R (k x) (k' y)) ->
    sbt L R (Br n k) (Br m k').
  Proof.
    intros EQs1 EQs2.
    apply step_sb_br_gen; auto.
    typeclasses eauto.
  Qed.

  Lemma step_sb_br_id_gen {n} 
        (k : fin' n -> ctree E X) (k': fin' n -> ctree F Y) (R: rel _ _) :
    (Proper (equ eq ==> equ eq ==> impl) R) ->
    L tau tau ->
    (forall x, R (k x) (k' x)) ->
    sb L R (Br n k) (Br n k').
  Proof.
    intros PROP ? EQs.
    apply step_sb_br_gen; trivial; intros x; exists x; auto.
  Qed.

  Lemma step_sb_br_id {n} 
    (k : fin' n -> ctree E X) (k': fin' n -> ctree F Y) (R: rel _ _) :
    L tau tau ->
    (forall x, st L R (k x) (k' x)) ->
    sbt L R (Br n k) (Br n k').
  Proof.
    apply step_sb_br_id_gen.
    typeclasses eauto.
  Qed.

  (*|
    For invisible nodes, the situation is different: we may kill them, but that execution
    cannot act as going under the guard.
  |*)
  Lemma step_sb_guard_gen (t : ctree E X) (t': ctree F Y) (R: rel _ _) :
    sb L R t t' ->
    sb L R (Guard t) (Guard t').
  Proof.
    intros EQ.
    split; apply step_ss_guard_gen; apply EQ.
  Qed.

  Lemma step_sb_guard (t : ctree E X) (t' : ctree F Y) (R: rel _ _) :
    sbt L R t t' ->
    sbt L R (Guard t) (Guard t').
  Proof.
    now apply step_sb_guard_gen.
  Qed.

End Proof_Rules.

(*|
Proof system for homogenous [~]
--------------------

While the proof rules from the previous section are useful for performing full on
coinductive proofs, lifting these at the level of [sbisim] can allow for completely
avoiding any coinduction when combined with a pre-established equational theory.
|*)
Section Sb_Proof_System.
  Context {E: Type} {HE: Encode E} {X: Type}.

  Lemma sb_ret: forall x y,
      x = y ->
      (Ret x: ctree E X) ~ Ret y.
  Proof.
    intros * EQ; step.
    now apply step_sb_ret; subst.
  Qed.

  Lemma sb_vis {Y}: forall (e: E) (k k': encode e -> ctree E Y),
      (forall x, k x ~ k' x) ->
      Vis e k ~ Vis e k'.
  Proof.
    intros.
    upto_vis.
    apply H.
  Qed.

  (*|
    Visible vs. Invisible Taus
    ~~~~~~~~~~~~~~~~~~~~~~~~~~
    Invisible taus can be stripped-out w.r.t. to [sbisim], but not visible ones
  |*)
  Lemma sb_guard: forall (t : ctree E X),
      Guard t ~ t.
  Proof.
    intros t; play.
    - trans in TR; etrans. 
    - eauto 6 with trans.
  Qed.

 Lemma sb_guard_l: forall (t u : ctree E X),
      t ~ u ->
      Guard t ~ u.
  Proof.
    intros * EQ; now rewrite sb_guard.
  Qed.

  Lemma sb_guard_r: forall (t u : ctree E X),
      t ~ u ->
      t ~ Guard u.
  Proof.
    intros * EQ; now rewrite sb_guard.
  Qed.

  Lemma sb_guard_lr: forall (t u : ctree E X),
      t ~ u ->
      Guard t ~ Guard u.
  Proof.
    intros * EQ; now rewrite !sb_guard.
  Qed.
  
  Lemma sb_step: forall (t u : ctree E X),
      t ~ u ->
      step t ~ step u.
  Proof.
    intros * EQ; step.
    apply step_sb_step; auto.
  Qed.

  Lemma sb_br {n m} (k : fin' n -> ctree E X) (k': fin' m -> ctree E X) :
    (forall x, exists y, k x ~ k' y) ->
    (forall y, exists x, k x ~ k' y) ->
    Br n k ~ Br m k'.
  Proof.
    intros * EQs1 EQs2; step.
    apply @step_sb_br; auto.
  Qed.

  Lemma sb_br_id {n} (k k' : fin' n -> ctree E X) :
    (forall x, k x ~ k' x) ->
    Br n k ~ Br n k'.
  Proof.
    intros * EQs; step.
    apply @step_sb_br_id; auto.
  Qed.


  Lemma sb_unfold_iter{I}: forall (step: I -> ctree E (I + X))(i: I),
      iter step i ~
        (lr <- step i;;
         match lr with
         | inl l => iter step l
         | inr r => Ret r
         end).
  Proof.
    intros step i.
    rewrite unfold_iter.
    __upto_bind_eq_sbisim.
    destruct x.
    - apply sb_guard.
    - reflexivity.
  Qed.

  Lemma sb_unfold_forever{Y}: forall (k: Y -> ctree E Y)(i: Y),
      forever X k i ~ r <- k i ;; forever X k r.
  Proof.
    intros k i.
    unfold forever.
    rewrite sb_unfold_iter.
    rewrite bind_map.
    reflexivity.
  Qed.

End Sb_Proof_System.

(* TODO: tactics!
   Should it be the same to step at both levels or two different sets?

Ltac bsret  := apply step_sb_ret.
Ltac bsvis  := apply step_sb_vis.
Ltac bstauv := apply step_sb_tauV.
Ltac bsstep := bsret || bsvis || bstauv.

Ltac sret  := apply sb_ret.
Ltac svis  := apply sb_vis.
Ltac stauv := apply sb_tauV.
Ltac sstep := sret || svis || stauv.
 *)

Section SanityChecks.
  Context {E: Type} {HE: Encode E} {X: Type}.

  Lemma sbisim_ret_inv (r1 r2 : X) :
    (Ret r1 : ctree E X) ~ Ret r2 -> r1 = r2.
  Proof.
    intro.
    eplayL.    
    trans in TR.
    dependent destruction Eql.
    reflexivity.
  Qed.

  (*| Need to know [encode e1] is inhabited to take a step (not [void]) |*)
  Lemma sbisim_vis_invT {e1 e2: E} {k1: encode e1 -> ctree E X} {k2: encode e2 -> ctree E X} (x: encode e1):
    Vis e1 k1 ~ Vis e2 k2 ->
    encode e1 = encode e2 /\ e1 = e2.
  Proof.
    intros Hsim.
    eplayL.
    trans in TR.
    dependent destruction Eql.
    auto.
    Unshelve. exact x.
  Qed.

  Lemma sbisim_vis_invE (e: E) (k1 k2: encode e -> ctree E X) (x: encode e):
    Vis e k1 ~ Vis e k2 ->
    forall x, k1 x ~ k2 x.
  Proof.
    intros.
    eplayL.
    trans in TR.
    dependent destruction Eql.
    rewrite <- Eqt.
    apply EQ.
  Qed.

  Lemma sbisim_br_inv {Y n m} (k1 : fin' n -> ctree E X) (k2: fin' m -> ctree E Y) :
    Br n k1 ~ Br m k2 ->
    (forall i1, exists i2, k1 i1 ~ k2 i2).
  Proof.
    intros EQ i1.
    eplayL.
    trans in TR.
    exists n0; rewrite <- Eqt.
    apply EQ.
  Qed.

  Lemma sbisim_ret_vis_inv (r : X) (e : E) (k : encode e -> ctree E X) :
    Ret r ~ Vis e k -> False.
  Proof.
    intros * abs.
    eplayL.
    unfold trans in TR; cbn in TR.
    inversion TR.
  Qed.

  Lemma sbisim_ret_br_inv {n} (r: X) (k : fin' n -> ctree E X) :
    Ret r ~ Br n k -> False.
  Proof.
    intros * abs.
    eplayL.
    unfold trans in TR; cbn in TR.
    inversion TR.
  Qed.

  Lemma sbisim_vis_br_inv{n} (e: E) (k1 : encode e -> ctree E X) (k2: fin' n -> ctree E X):
    Vis e k1 ~ Br n k2 -> False.
  Proof.
    intros * abs.
    eplayR.
    inversion TR.
    Unshelve. exact Fin.F1. 
  Qed.
  
End SanityChecks.

Section StrongSimulations.

  Context {E F: Type} {HE: Encode E} {HF: Encode F} {X Y: Type}
          {L: rel (label E) (label F)}.

  Notation ss := (@ss E F HE HF X Y).
  Notation sst L := (coinduction.t (ss L)).
  Notation ssim  := (@ssim E F HE HF X Y).
  Notation ssbt L := (coinduction.bt (ss L)).
  Notation ssT L := (coinduction.T (ss L)).

  Lemma sbisim_clos2_ss : @sbisim_clos2 E HE F HF X Y eq eq <= (sst L).
  Proof.
    intro R1. apply Coinduction.
    cbn; intros Rs x y [z x' y' z' SBzx' x'y' SBy'z'].
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
  Qed.

  (*| Instances for rewriting [sbisim] under all [ss]-related contexts |*)
  #[global] Instance sbisim_eq_clos2_ssim_goal:
    Proper (sbisim eq ==> sbisim eq ==> flip impl) (ssim L).
  Proof.
    cbn.
    coinduction R CH. intros * EQ1 * EQ2 SIM.
    do 2 red; cbn; intros * TR.
    symmetry in EQ2.
    step in EQ1; apply EQ1 in TR as (? & ? & ? & ? & ?).
    step in SIM; apply SIM in H as (? & ? & ? & ? & ?).
    step in EQ2; apply EQ2 in H as (? & ? & ? & ? & ?); subst.
    do 2 eexists.
    split; [eassumption |].
    split; [| eassumption].
    symmetry in H4. eapply CH; eassumption.
  Qed.

  #[global] Instance sbisim_eq_clos2_ssim_ctx :
    Proper (sbisim eq ==> sbisim eq ==> impl) (ssim L).
  Proof.
    repeat intro. symmetry in H, H0. eapply sbisim_eq_clos2_ssim_goal; eauto.
  Qed.

  #[global] Instance sbisim_eq_clos2_sst_goal RR :
    Proper (sbisim eq ==> sbisim eq ==> flip impl) (sst L RR).
  Proof.
    cbn; intros ? ? eq1 ? ? eq2 H.
    apply (ft_t sbisim_clos2_ss). cbn.
    econstructor; eauto.
    now rewrite eq2.
  Qed.

  #[global] Instance sbisim_eq_clos2_sst_ctx RR :
    Proper (sbisim eq ==> sbisim eq ==> impl) (sst L RR).
  Proof.
    cbn; intros ? ? eq1 ? ? eq2 ?.
    rewrite <- eq1, <- eq2.
    auto.
  Qed.

  #[global] Instance sbisim_eq_clos2_ssT_goal RR f :
    Proper (sbisim eq ==> sbisim eq ==> flip impl) (ssT L f RR).
  Proof.
    cbn; intros ? ? eq1 ? ? eq2 H.
    apply (fT_T sbisim_clos2_ss). cbn.
    econstructor; eauto.
    now rewrite eq2.
  Qed.

  #[global] Instance sbisim_eq_clos2_ssT_ctx RR f :
    Proper (sbisim eq ==> sbisim eq ==> impl) (ssT L f RR).
  Proof.
    cbn; intros ? ? eq1 ? ? eq2 ?.
    rewrite <- eq1, <- eq2.
    auto.
  Qed.

End StrongSimulations.
