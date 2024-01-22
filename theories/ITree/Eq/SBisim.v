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
  ITree.Core
  ITree.Equ.

Local Open Scope itree_scope.

Generalizable All Variables.

Inductive label (E: Type) `{Encode E} :=
| obs (e: E) (v: encode e)
| val {X: Type} (x: X).
Arguments obs {E} {H} e v.
Arguments val {E} {H} {X} x.

Section StrongBisim.
  Context {E F: Type} {HE: Encode E} {HF: Encode F}
    {X Y: Type}.

  Notation S := (itree E X).
  Notation S' := (itree F Y).

  Inductive sbF (L:  rel (label E) (label F)) R: itree' E X -> itree' F Y -> Prop :=
  | SbTauL: forall t u,
      sbF L R (observe t) u ->
      sbF L R (TauF t) u
  | SbTauR: forall t u,
      sbF L R t (observe u) ->
      sbF L R t (TauF u)
  | SbTau: forall t u,
      R t u ->
      sbF L R (TauF t) (TauF u)
  | SbVis: forall (e: E) (f: F) k k',
      (forall (v: encode e) (v': encode f),
          L (obs e v) (obs f v') ->
          R (k v) (k' v')) ->
      sbF L R (VisF e k) (VisF f k')
  | SbRet: forall (x: X) (y: Y),
      L (val x) (val y) ->
      sbF L R (RetF x) (RetF y).
  
  (*| The symmetric closure of two [ss] |*)
  Program Definition sb L : mon (S -> S' -> Prop) :=
    {| body R t u := sbF L R (observe t) (observe u) |}.
  Next Obligation.
    unfold Proper, respectful, impl.
    intros.
    dependent induction H0; rewrite <- ?x, <- ?x1, <- ?x2.
    - apply SbTauL; auto.
    - apply SbTauR; auto.
    - apply SbTau; auto.
    - apply SbVis; intros; auto.
    - apply SbRet; auto.
  Qed.

  Definition sbisim L := gfp (sb L).

End StrongBisim.

(*| sb (bisimulation) notation |*)
Local Notation st L := (t (sb L)).
Local Notation sT L := (T (sb L)).
Local Notation sbt L := (bt (sb L)).
Local Notation sbT L := (bT (sb L)).

Notation "t ~ u" := (sbisim eq t u) (at level 70): itree_scope.
Notation "t (~ L ) u" := (sbisim L t u) (at level 70): itree_scope.
Notation "t [~ L ] u" := (st L _ t u) (at level 78): itree_scope.
Notation "t [~] u" := (st eq _ t u) (at level 78): itree_scope.
Notation "t {~ L } u" := (sbt L _ t u) (at level 79): itree_scope.
Notation "t {~} u" := (sbt eq _ t u) (at level 79): itree_scope.
Notation "t {{ ~ L }} u" := (sb L _ t u) (at level 79): itree_scope.
Notation "t {{~}} u" := (sb eq _ t u) (at level 79): itree_scope.

Ltac __coinduction_sbisim R H :=
  (try unfold sbisim);
  apply_coinduction; intros R H.

#[global] Tactic Notation "__step_sbisim" :=
  match goal with
  | |- context[@sbisim ?E ?F ?C ?D ?X ?Y ?LR] =>
      unfold sbisim;
      step;
      fold (@sbisim E F C D X Y L)
  end.

#[local] Tactic Notation "step" := __step_sbisim || step.

#[local] Tactic Notation "coinduction" simple_intropattern(R) simple_intropattern(H) :=
  __coinduction_sbisim R H || coinduction R H.

Ltac __step_in_sbisim H :=
  match type of H with
  | context [@sbisim ?E ?F ?C ?D ?X ?Y ?L ] =>
      unfold sbisim in H;
      step in H;
      fold (@sbisim E F C D X Y L) in H
  end.

#[local] Tactic Notation "step" "in" ident(H) := __step_in_sbisim H || step in H.

(*|
  This section should describe lemmas proved for the
  heterogenous version of `ss`, parametric on
  - Return types X, Y
  - Label types E, F
|*)
Section sbisim_upto_equ.
  Context `{HE: Encode E} `{HF: Encode F} {X Y : Type}
          {L:  rel (label E) (label F)}.

  Local Notation sb := (@sb E F HE HF X Y).
  Local Notation sbisim := (@sbisim E F HE HF X Y).
  Local Notation st L := (coinduction.t (sb L)).
  Local Notation sbt L := (coinduction.bt (sb L)).
  Local Notation sT L := (coinduction.T (sb L)).

  (*| Strong bisimulation up-to [equ] is valid |*)
  Lemma equ_clos_st : @equ_clos E F X Y HE HF <= (st L).
  Proof.
    apply Coinduction; cbn.
    intros R x y [x' y' x'' y'' EQ' ? EQ''].
    generalize dependent x'.
    generalize dependent x.
    generalize dependent y''.
    generalize dependent y.
    dependent induction HR; intros. 
    - observe_equ x.
      rewrite Eqt in EQ'.
      step in EQ'; cbn in EQ'.
      dependent destruction EQ'.
      rewrite <- x.
      apply SbTauL.
      eapply IHHR; auto.
    - observe_equ x.
      rewrite Eqt in EQ''.
      step in EQ''; cbn in EQ''.
      dependent destruction EQ''.
      rewrite <- x.
      apply SbTauR.
      eapply IHHR; auto.
    - observe_equ x.
      observe_equ x0.
      rewrite Eqt in EQ''.
      rewrite Eqt0 in EQ'.
      step in EQ'; cbn in EQ'; dependent destruction EQ'.
      step in EQ''; cbn in EQ''; dependent destruction EQ''.
      rewrite <- x3, <- x.
      apply SbTau.
      eapply (f_Tf (sb L)).
      econstructor; eauto.
    - observe_equ x.
      observe_equ x0.
      rewrite Eqt in EQ''.
      rewrite Eqt0 in EQ'.      
      step in EQ'; cbn in EQ'; dependent destruction EQ'.
      step in EQ''; cbn in EQ''; dependent destruction EQ''.
      rewrite <- x3, <- x.
      apply SbVis; intros.      
      eapply (f_Tf (sb L)).
      econstructor.
      + apply H1.
      + apply H, H2.
      + apply H0.
    - observe_equ x.
      observe_equ x1.
      rewrite Eqt in EQ''.
      rewrite Eqt0 in EQ'.
      step in EQ'; cbn in EQ'; dependent destruction EQ'.
      step in EQ''; cbn in EQ''; dependent destruction EQ''.
      rewrite <- x, <- x4.
      now apply SbRet.
  Qed.

  (*| Aggressively providing instances for rewriting [equ]
    under all [sb]-related contexts. |*)
  #[global] Instance proper_equ_st RR :
    Proper (@equ E HE X X eq ==> @equ F HF Y Y eq ==> iff) (st L RR).
  Proof.
    cbn; split; intro Hsim;
      apply (ft_t equ_clos_st); econstructor.
    + symmetry; apply H.
    + eauto. 
    + auto.
    + apply H.
    + eauto.
    + symmetry; apply H0.
  Qed.

  #[global] Instance proper_equ_sT RR f :
    Proper (equ eq ==> equ eq ==> iff) (sT L f RR).
  Proof.
    split; intro Hsim;
      apply (fT_T equ_clos_st); econstructor.
    + symmetry; apply H.
    + eauto. 
    + auto.
    + apply H.
    + eauto.
    + symmetry; apply H0.
  Qed.

  #[global] Instance proper_equ_sbisim :
    Proper (equ eq ==> equ eq ==> iff) (sbisim L).
  Proof.
    split; intro Hsim;
      apply (ft_t equ_clos_st); econstructor.
    + symmetry; apply H.
    + eauto. 
    + auto.
    + apply H.
    + eauto.
    + symmetry; apply H0.
  Qed.
End sbisim_upto_equ.

Section sbisim_homogenous_theory.
  Context {E: Type} {HE: Encode E} {X: Type}.

  Local Notation sb  := (@sb E E HE HE X X).
  Local Notation sbisim := (@sbisim E E HE HE X X (@eq (label E))).
  Local Notation st := (coinduction.t (sb (@eq (label E)))).
  Local Notation sbt := (coinduction.bt (sb (@eq (label E)))).
  Local Notation sT  := (coinduction.T (sb (@eq (label E)))).
  Arguments impl /.
  Arguments pointwise_relation /.

  (*| Up-to-bisimulation enhancing function |*)
  Variant sbisim_clos_body (R : rel (itree E X) (itree E X)) : rel (itree E X) (itree E X) :=
    | Sbisim_clos : forall t t' u' u
                      (Sbisimt : t ~ t')
                      (HR : R t' u')
                      (Sbisimu : u' ~ u),
        @sbisim_clos_body R t u.

  Program Definition sbisim_clos: mon (rel (itree E X) (itree E X)) :=
    {| body := sbisim_clos_body |}.
  Next Obligation.
    unfold Proper, respectful, impl; intros.
    destruct H0; econstructor; eauto.
  Qed.
  
  Theorem sbisim_clos_upto: sbisim_clos <= st.
  Proof.
    apply Coinduction; cbn.
    intros R x y [x' y' x'' y'' EQ' ? EQ''].
    generalize dependent x'.
    generalize dependent x.
    generalize dependent y''.
    generalize dependent y.
    setoid_rewrite (itree_eta y').
    setoid_rewrite (itree_eta x'').
    remember (observe y') as Y'.
    remember (observe x'') as X''.
    clear HeqY' y' HeqX'' x''.
    induction HR; intros. 
  Admitted.

  Lemma refl_st : const eq <= st.
  Proof.
    apply leq_t.
    cbn*; intros; subst.
    desobs a1.
    - now apply SbRet.
    - now apply SbTau.
    - apply SbVis; intros.
      dependent destruction H.
      reflexivity.
  Qed.

  (*| [converse] is compatible i.e. validity of up-to symmetry |*)
  Lemma converse_st: converse <= st.
  Proof.
    apply leq_t; cbn.
    intros.
  Admitted.

(*| [square] is compatible i.e. validity of up-to transivitiy |*)
  Lemma square_st: square <= st.
  Proof.
    apply Coinduction; cbn.
    intros R x z [y ? ?]. 
  Admitted.

  (*| Reflexivity |*)
  #[global] Instance Reflexive_st R: Reflexive (st R).
  Proof. apply build_reflexive; apply ft_t; apply refl_st. Qed.

  #[global] Instance Reflexive_sbisim: Reflexive sbisim.
  Proof. now apply Reflexive_st. Qed.

  #[global] Instance Reflexive_sbt R : Reflexive (sbt R).
  Proof. apply build_reflexive; apply fbt_bt; apply refl_st. Qed.

  #[global] Instance Reflexive_sT f R : Reflexive (sT f R).
  Proof. apply build_reflexive; apply fT_T; apply refl_st. Qed.

  (*| Transitivity |*)
  #[global] Instance Transitive_st R: Transitive (st R).
  Proof. apply build_transitive; apply ft_t; apply (square_st). Qed.

  #[global] Instance Transitive_sbisim: Transitive sbisim.
  Proof. now apply Transitive_st. Qed.

  #[global] Instance Transitive_sbt R : Transitive (sbt R).
  Proof. apply build_transitive; apply fbt_bt; apply square_st. Qed.

  #[global] Instance Transitive_sT f R: Transitive (sT f R).
  Proof. apply build_transitive; apply fT_T; apply square_st. Qed.

  (*| Symmetry |*)
  #[global] Instance Symmetric_st R: Symmetric (st R).
  Proof. apply build_symmetric; apply ft_t; apply (converse_st). Qed.

  #[global] Instance Symmetric_sbisim: Symmetric sbisim.
  Proof. now apply Symmetric_st. Qed.

  #[global] Instance Symmetric_sbt R: Symmetric (sbt R).
  Proof. apply build_symmetric; apply fbt_bt; apply converse_st. Qed.

  #[global] Instance Symmetric_sT f R: Symmetric (sT f R).
  Proof. apply build_symmetric; apply fT_T; apply converse_st. Qed.

  (*| Thus bisimilarity and [t R] are always equivalence relations. |*)
  #[global] Instance Equivalence_st R: Equivalence (st R).
  Proof. split; typeclasses eauto. Qed.

  #[global] Instance Equivalence_bisim : Equivalence sbisim.
  Proof. split; typeclasses eauto. Qed.

  #[global] Instance Equivalence_sbt R: Equivalence (sbt R).
  Proof. split; typeclasses eauto. Qed.

  #[global] Instance Equivalence_sT f R: Equivalence ((T (sb eq) f R)).
  Proof. split; typeclasses eauto. Qed.

(*|
Aggressively providing instances for rewriting hopefully faster
[sbisim] under all [sb]-related contexts (consequence of the transitivity
of the companion).
|*)
  #[global] Instance sbisim_sbisim_closed_goal :
    Proper (sbisim ==> sbisim ==> flip impl) sbisim.
  Proof.
    repeat intro.
    etransitivity; [etransitivity; eauto | symmetry; eassumption].
  Qed.

  #[global] Instance sbisim_sbisim_closed_ctx:
    Proper (sbisim ==> sbisim ==> impl) sbisim.
  Proof.
    repeat intro.
    etransitivity; [symmetry; eassumption | etransitivity; eauto].
  Qed.

  #[global] Instance sbisim_clos_st_goal R:
    Proper (sbisim ==> sbisim ==> flip impl) (st R).
  Proof.
    cbn; intros ? ? eq1 ? ? eq2 ?.
    rewrite eq1, eq2.
    auto.
  Qed.

  #[global] Instance sbisim_clos_st_ctx R :
    Proper (sbisim ==> sbisim ==> impl) (st R).
  Proof.
    cbn; intros ? ? eq1 ? ? eq2 ?.
    rewrite <- eq1, <- eq2.
    auto.
  Qed.

  #[global] Instance sbisim_clos_sT_goal R f :
    Proper (sbisim ==> sbisim ==> flip impl) (sT f R).
  Proof.
    cbn; intros ? ? eq1 ? ? eq2 ?.
    rewrite eq1, eq2.
    auto.
  Qed.

  #[global] Instance sbisim_clos_sT_ctx R f :
    Proper (sbisim ==> sbisim ==> impl) (sT f R).
  Proof.
    cbn; intros ? ? eq1 ? ? eq2 ?.
    rewrite <- eq1, <- eq2.
    auto.
  Qed.

  #[global] Instance equ_sbt_closed_goal R:
    Proper (equ eq ==> equ eq ==> flip impl) (sbt R).
  Proof.
    repeat intro. pose proof (gfp_bt (sb eq) R).
    etransitivity; [| etransitivity]; [ | apply H1 | ]; apply H2.
    rewrite H; auto. rewrite H0; auto.
  Qed.

  #[global] Instance equ_sbt_closed_ctx R :
    Proper (equ eq ==> equ eq ==> impl) (sbt R).
  Proof.
    repeat intro. pose proof (gfp_bt (sb eq) R).
    etransitivity; [| etransitivity]; [ | apply H1 | ]; apply H2.
    rewrite H; auto. rewrite H0; auto.
  Qed.

  (*| Hence [equ eq] is a included in [sbisim] |*)
  #[global] Instance equ_sbisim_subrelation : subrelation (equ eq) sbisim.
  Proof.
    red; intros.
    rewrite H; reflexivity.
  Qed.

End sbisim_homogenous_theory.


(*|
Up-to [bind] context bisimulations
----------------------------------
We have proved in the module [Equ] that up-to bind context is
a valid enhancement to prove [equ].
We now prove the same result, but for strong and weak bisimulation.
|*)

(* TODO *)
