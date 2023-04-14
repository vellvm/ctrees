(* begin hide *)

From ExtLib Require Import
     Structures.Functor
     Structures.Monad.

From ITree Require Import
     Basics.Basics
     Core.Subevent.

From CTree Require Import
  CTree
  Eq
  Eq.Epsilon
  Eq.IterFacts
  Fold.

Import CTreeNotations.
Open Scope ctree_scope.

(* end hide *)

(** Establishing generic results on [fold] is tricky: because it goes into
    a very generic monad [M], it requires some heavy axiomatization of this
    monad. Yoon et al.'s ICFP'22 develop the necessary tools to this end.
    For now, we simply specialize results to specific [M]s.
 *)

(* FIXME universe inconsistency *)
Unset Universe Checking.
Theorem ssim_interp_h {E F1 F2 C D1 D2 X Y}
  `{HasB0 : B0 -< D1} `{HasB1 : B1 -< D1} `{HasB0' : B0 -< D2} `{HasB1' : B1 -< D2}
  `{HC1 : C -< D1} `{HC2 : C -< D2}
  (Ldest : rel (@label F1) (@label F2)) :
  forall (h : E ~> ctree F1 D1) (h' : E ~> ctree F2 D2),
  (Ldest tau tau /\ forall (x : X), Ldest (val x) (val x)) ->
  (forall {Z} (e : E Z), h _ e (≲update_val_rel Ldest (@eq Z)) h' _ e) ->
  forall (x : Y) (k : Y -> ctree E C X), interp h (k x) (≲Ldest) interp h' (k x).
Proof.
  intros.
  eapply ssim_iter with (Ra := equ eq) (Rb := fun b b' => Ldest (val b) (val b')).
  2, 4: auto. 1: red; reflexivity.
  cbn. intros.
  setoid_rewrite ctree_eta in H1.
  destruct (observe a) eqn:?, (observe a') eqn:?; try now (step in H1; inv H1).
  - step. apply step_ss_ret. constructor. cbn. step in H1. inv H1. apply H.
  - unfold CTree.map.
    apply equ_vis_invT in H1 as ?. subst.
    eapply ssim_clo_bind_gen with (R0 := eq).
    + red. reflexivity.
    + eapply weq_ssim. apply update_val_rel_update_val_rel.
      apply equ_vis_invE in H1 as [<- ?]. apply H0.
    + intros. step. apply step_ss_ret. constructor.
      apply equ_vis_invE in H1 as [<- ?]. subst. apply H1.
  - unfold CTree.map. setoid_rewrite bind_branch.
    apply equ_br_invT in H1 as ?. destruct H2 as [<- <-].
    apply equ_br_invE in H1 as [<- ?].
    destruct vis.
    + step. apply step_ss_brS. intros. exists x0. step. apply step_ss_ret. constructor. apply H1. right; auto. 3: apply H. all: intros H2; inversion H2.
    + step. apply step_ss_brD. intros. exists x0. apply step_ss_ret. constructor. apply H1.
Qed.
Set Universe Checking.

