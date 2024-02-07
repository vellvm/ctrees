From Coq Require Import
  Basics
  Classes.Morphisms.

From Coinduction Require Import
  coinduction lattice.

From CTree Require Import
  Events.Core
  CTree.Core
  CTree.SBisim
  CTree.Equ
  CTree.Trans
  CTree.Logic.Trans
  CTree.Logic.CanStep
  Logic.Ctl
  Logic.Kripke.

Set Implicit Arguments.
Generalizable All Variables.

Import CTreeNotations CtlNotations.
Local Open Scope ctl_scope.
Local Open Scope ctree_scope.
  
(*| CTL logic lemmas on c/itrees |*)
Section BasicLemmas.
  Context {E: Type} {HE: Encode E} {X: Type}.

  Lemma done_af: forall (t: ctree E X) φ w,
      is_done w ->
      <( t, w |= AF now φ )> ->
      φ w.
  Proof.
    intros * Hret Hcontra.
    inv Hcontra.
    - now rewrite ctl_now in H.
    - destruct H0 as ((? & ? & ?) & ?).
      exfalso.
      eapply done_not_ktrans with (t:=t); eauto.
  Qed.

  (* This lemma forces us to have finite branches.
     Alternatively, a classical φ would also allow
     us to work without induction on branch arity. *)
  Lemma af_brD_aux: forall n (k: fin' n -> ctree E X) w φ,
      (forall (i: fin' n), <( {k i}, w |= AF now φ )>) -> 
      φ w \/ (forall i, can_step (k i) w /\
                    (forall (t': ctree E X) w', [k i, w] ↦ [t', w'] ->
                                           <( t', w' |= AF now φ )>)).
  Proof.
    induction n; intros.
    - specialize (H Fin.F1).
      next in H; destruct H.
      + now left.
      + right.
        intro i.
        dependent destruction i; try solve [inv i].
        next in H.
        destruct H; intuition.
    - (* Need to construct [k, i] *)
      pose proof (H Fin.F1).
      edestruct IHn with (k:=fun (i: fin (S n)) =>
                               k (Fin.FS i)) (φ:=φ) (w:=w).
      + intro i.
        apply H.
      + now left.
      + next in H0; destruct H0.
        * now left.
        * right.
          intros.
          dependent destruction i.
          -- now next in H0; destruct H0.
          -- now apply H1.
  Qed.
  
  Lemma af_brD: forall n (k: fin' n -> ctree E X) w φ,
      (forall (i: fin' n), <( {k i}, w |= AF now φ )>) ->
      <( {BrD n k}, w |= AF now φ )>.
  Proof.
    intros.
    apply af_brD_aux in H.
    destruct H.
    + next; now left.
    + next; right.
      next; split. 
      * apply can_step_brD.
        exists (Fin.F1).
        now destruct (H Fin.F1).
      * intros.
        apply ktrans_brD in H0 as (i & TR).
        destruct (H i); eauto.
  Qed.
  
  Lemma af_brS: forall n (k: fin' n -> ctree E X) w φ,
      <( {BrS n k}, w |= AF now φ )> <->
        (forall (i: fin' n), <( {k i}, w |= AF now φ )>).
  Proof.
    split; intros.
    - next in H; destruct H.
      + next; left.
        now rewrite ctl_now in *.
      + destruct H.
        apply H0.
        apply ktrans_brS.
        apply can_step_not_done in H.
        exists i; eauto.
    - destruct (not_done_dec w).
      + next; right.
        next; split; auto.
        * now apply can_step_brS.
        * intros t' w' TR'.
          apply ktrans_brS in TR' as (? & -> & -> & ?).
          apply H.
      + apply done_af with (φ:=φ) (t:= k Fin.F1) in i; auto.
        next; left.
        now apply ctl_now.
  Qed.
  
  Lemma af_vis: forall (e: E) (k: encode e -> ctree E X) (_: encode e) w φ,
      (φ w \/ (not_done w /\ forall (x: encode e),
                 <( {k x}, {Obs e x} |= AF now φ )>)) ->
      <( {Vis e k}, w |= AF now φ )>.        
  Proof.
    intros.
    destruct H as [H | [Hd H]].
    - now next; left.
    - next; right; next; split.
      + now apply can_step_vis.
      + intros t' w' TR'.
        apply ktrans_vis in TR' as (? & -> & ? & ?).
        now rewrite <- H0.
  Qed.

End BasicLemmas.

Section AfIndLemma.
  Context {E: Type} {HE: Encode E} {X: Type}.

  (* t, w |= WF now φ *)
  Inductive AFNowInd(φ: World E -> Prop): ctree E X -> World E -> Prop :=
  | AFNowIndBase: forall (t: ctree E X) (w: World E),
      φ w ->
      AFNowInd φ t w
  | AFNowIndDone: forall t (x: X),
      observe t = RetF x ->
      φ (Done x) ->
      AFNowInd φ t Pure
  | AFNowIndFinish: forall t (e: E) (v: encode e) (x: X),
      observe t = RetF x ->
      φ (Finish e v x) ->
      AFNowInd φ t (Obs e v)
  | AFNowIndBr: forall t w b n (k: fin' n -> ctree E X),
      observe t = BrF b n k ->
      not_done w ->
      (forall (i: fin' n), can_step (k i) w -> AFNowInd φ (k i) w) ->
      AFNowInd φ t w
  | AFNowIndVis: forall (t: ctree E X) w e k,
      observe t = VisF e k ->
      not_done w ->
      (forall (v: encode e), AFNowInd φ (k v) (Obs e v)) ->
      AFNowInd φ t w.

  Global Instance proper_equ_afind φ:
    Proper (equ eq ==> eq ==> iff) (AFNowInd φ).
  Proof.
    unfold Proper, respectful.
    intros; subst; split; intros Hind.
    - generalize dependent y.
      induction Hind; intros.
      + apply AFNowIndBase; auto.
      + apply AFNowIndDone with x; auto.
        unfold equ in H1; step in H1; cbn in H1;
          dependent destruction H1; congruence.
      + apply AFNowIndFinish with x; auto.
        unfold equ in H1; step in H1; cbn in H1;
          dependent destruction H1; congruence.
      + step in H3; cbn in H3; rewrite H in H3.
        dependent destruction H3.
        eapply AFNowIndBr with b n k2; auto.
        intros i (t' & w' & TR').
        eapply H2 with i; [|apply H3].
        assert (Heqi: k i ≅ k2 i) by apply H3; auto.
        rewrite Heqi. 
        now (exists t', w').
      + step in H3; cbn in H3; rewrite H in H3.
        dependent destruction H3.
        eapply AFNowIndVis with e k2; auto.
        intros.
        apply H2, H3.
    - generalize dependent x.
      induction Hind; intros.
      + apply AFNowIndBase; auto.        
      + apply AFNowIndDone with x; auto.
        unfold equ in H1; step in H1; cbn in H1;
          dependent destruction H1; congruence.
      + apply AFNowIndFinish with x; auto.
        unfold equ in H1; step in H1; cbn in H1;
          dependent destruction H1; congruence.
      + step in H3; cbn in H3; rewrite H in H3.
        dependent destruction H3.
        eapply AFNowIndBr with b n k1; auto.
        intros i (t' & w' & TR').
        assert (Heqi: k1 i ≅ k i) by apply H3; auto.
        eapply H2 with i; auto.
        rewrite <- Heqi.
        now (exists t', w').
      + step in H3; cbn in H3; rewrite H in H3.
        dependent destruction H3.
        eapply AFNowIndVis with e k1; auto.
        intros.
        apply H2, H3.
  Qed.

  Lemma afind_brD_aux: forall n (k: fin' n -> ctree E X) w φ,
      (forall i, AFNowInd φ (k i) w) ->
      φ w \/ (forall i, can_step (k i) w /\
                    (forall t' w', [k i, w] ↦ [t', w'] ->
                              AFNowInd φ t' w')).
  Proof.
    induction n; intros.
    - specialize (H Fin.F1).
      dependent induction H.
      + (* AFIndNow *) now left.
      + (* AFIndDone *)
        right; intros.
        dependent destruction i; try solve [inv i].
        split; unfold can_step; cbn; rewrite H.
        * exists Ctree.stuck, (Done x).
          now econstructor.
        * intros * TR.
          dependent destruction TR.
          now apply AFNowIndBase.
      + (* AFIndFinish *)
        right; intros.
        dependent destruction i; try solve [inv i].
        split; unfold can_step; cbn; rewrite H.
        * exists Ctree.stuck, (Finish e v x).
          now econstructor.
        * intros * TR.
          dependent destruction TR.
          now apply AFNowIndBase.
      + (* AFIndBr *) destruct b.
        * (* BrS *) right.
          intro i.
          dependent destruction i; try solve [inv i].
          unfold can_step; cbn; setoid_rewrite H.
          split; intros.
          -- exists (k0 Fin.F1), w; try econstructor; auto.
          -- admit. 
        * (* BrD *)
          induction n.
          -- edestruct H2.
  Admitted.

  Lemma pull1_iff: forall {A B} (P : A -> Prop) (R : A -> B -> Prop),
      (forall a, (exists b, R a b)-> P a) <-> (forall a b, R a b -> P a).
    split; intros; eauto.
    destruct H0.
    now apply H with x.
  Qed.

  Lemma pull2_iff: forall {A B C} (P : A -> B -> Prop) (R : A -> B -> C -> Prop),
      (forall a b, (exists c, R a b c)-> P a b) <-> (forall a b c, R a b c -> P a b).
    split; intros; eauto.
    destruct H0.
    now apply H with x.
  Qed.
    
  (* This is a super useful lemma, it allows us to do
     induction on [AFInd] instead of two inductions on
     [cau] and [trans] *)
  Opaque Ctree.stuck.
  Lemma af_afind : forall (t: ctree E X) (w: World E) φ,
       <( t, w |= AF now φ )> -> AFNowInd φ t w.
  Proof.    
    intros; cbn in H.
    induction H.
    - now apply AFNowIndBase.
    - destruct H0, H1; clear H H1.
      destruct H0 as (t' & w' & TR).      
      cbn in TR; desobs t. 
      + (* RetF *)
        destruct w; cbn in H2, H3; setoid_rewrite Heqt in H2;
          setoid_rewrite Heqt in H3.
        * (* RetF, Pure *)
          destruct (H2 _ _ TR); dependent destruction TR.
          -- apply AFNowIndDone with x0; auto.
          -- destruct H1.
             apply can_step_not_done in H1.
             inv H1.
        * (* RetF, Obs e v *)
          destruct (H2 _ _ TR); dependent destruction TR.
          -- apply AFNowIndFinish with x0; auto.
          -- destruct H1.
             apply can_step_not_done in H1.
             inv H1.
        * (* RetF, Done *) dependent destruction TR.
        * (* RetF, Finish *) dependent destruction TR.
      + (* Br b n k *)
        apply AFNowIndBr with b n k; auto.
        * apply ktrans_not_done with (Br b n k) t' w'; auto.
        * destruct b.
          -- (* BrS *)
            intros i Hs.
            apply ktrans_brS in TR as (? & ? & -> & ?).
            apply H3; cbn.
            rewrite Heqt.
            apply ktrans_brS.
            exists i; auto.
          -- (* BrD *)
            intros i (t_ & w_ & TR_).
            assert(TR': [t, w] ↦ [t_, w_]).
            { cbn; rewrite Heqt; apply ktrans_brD; exists i; auto. }
            cbn in TR_, TR', H2, H3.
            rewrite Heqt in *.
            clear TR TR_ t' w'.
            specialize (H2 t_ w_ TR').
            specialize (H3 t_ w_ TR').            
            clear t Heqt.
            rewrite ctree_eta.
            rewrite ctree_eta in H2, H3.
            remember (BrF false n k) as T.
            remember (observe t_) as T_.            
            clear HeqT_ t_.
            revert i.
            generalize dependent n.
            generalize dependent φ.
            dependent induction TR'; intros; dependent destruction HeqT.
            apply AFNowIndBr with false n0 k0;  eauto.            
            (* BrD *)            
            ++ cbn. admit.
            ++ now apply ktrans_not_done with (k0 i) t' w'.
            ++ intros j Hs.
               rewrite ctree_eta.
               apply IHTR'; auto.
               admit.
      + (* Vis e k *)
        apply AFNowIndVis with e k; auto.
        * apply ktrans_not_done with (Vis e k) t' w'; auto.
        * intros v. 
          apply ktrans_vis in TR as (? & -> & ? & ?).
          apply H3; cbn.
          rewrite Heqt.
          apply ktrans_vis.
          exists v; auto.
  Admitted.
  
End AfIndLemma.
