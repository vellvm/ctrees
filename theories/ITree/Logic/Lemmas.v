From Coq Require Import
  Basics
  Classes.RelationPairs.

From Coinduction Require Import
  coinduction lattice.

From ExtLib Require Import
  Structures.Monad
  Data.Monads.StateMonad.

From CTree Require Import
  ITree.Core
  ITree.Equ
  ITree.Logic.Trans
  Events.Writer
  Logic.Ctl
  Logic.Kripke.

Set Implicit Arguments.
Generalizable All Variables.

Import ITreeNotations CtlNotations.
Local Open Scope ctl_scope.
Local Open Scope itree_scope.

(*| CTL logic lemmas on c/itrees |*)
Section CtlITrees.
  Context {W X: Type}.
  Notation itreeW X := (itree (writerE W) X).

  Lemma ctl_af_star: forall (t: itreeW X * W) φ,
      <( t |= AF φ )> <-> ( exists t', t ↦* t' /\ <( t' |= φ )>).
  Proof.
    cbn; split; intros.
    dependent induction H.
    + exists m; split.
      * exists 0%nat; reflexivity.
      * assumption.
    + destruct H1 as [(? & ?) ?].
      destruct (H2 _ H1) as [[? ?] (? & ?)].
      destruct H3 as (n & ?).
      exists (k, w); split; auto.
      exists (S n).
      cbn; unfold hrel_dot.
      exists x; auto.
    + destruct H as (t' & [n ?] & Hφ).
      generalize dependent t.
      revert t' Hφ.
      induction n; intros; cbn in H.
      * apply ctl_af_ax.
        left.
        now rewrite H.
      * apply ctl_af_ax.
        right.
        apply ctl_ax.
        destruct H as [t0 TR0 TRn].
        split; [now exists t0|].
        intros.
        pose proof (trans_det (W:=W) (X:=X) _ _ _ TR0 H).
        eapply IHn with t'; auto.
        now rewrite <- H0.
  Qed.

  Lemma ctl_star_ef: forall (t:  itreeW X * W) φ,
      (exists t', t ↦* t' /\ <( t' |= φ )>) <-> <( t |= EF φ )>.
  Proof.
    split.
    - intros (t' & [n Iter] & Hφ).
      revert Hφ.
      revert t t' φ Iter.
      induction n; intros; cbn in Iter.
      + rewrite Iter.
        now rewrite ctl_ef_ex; left.
      + red in Iter.
        destruct (Iter) as [t0 Htr Htt]; clear Iter.
        specialize (IHn _ _ _ Htt Hφ).
        rewrite ctl_ef_ex; right; cbn.
        exists t0; split; auto.
    - intro H.
      induction H.
      + exists m; split; auto.
        exists 0; cbn; reflexivity.
      + destruct H1 as (m' & TR & m'' & TRn & ?).
        exists m''; split; [|auto].
        destruct TRn as (n & ?).
        exists (S n); cbn; unfold hrel_dot.
        exists m'; auto.
  Qed.

  Lemma iter_ctl_af: forall (t: X -> itreeW X) (σ: W) (i : X) (φ: W -> Prop),
      <( {(t i, σ)} |= AF done φ )> ->
      <( {(forever t i, σ)} |= AG AF now φ )>.
  Proof.
    intros.
    coinduction R CIH.
    remember (t i, σ).
    generalize dependent i.
    induction H; intros; subst; apply RStepA.
    - apply MatchA.
      now destruct H.
  Admitted.

End CtlITrees.
