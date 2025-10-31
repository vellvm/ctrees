From Stdlib Require Import
     Lia
     Basics
     Fin
     RelationClasses
     Program.Equality
     Logic.Eqdep.

From Coinduction Require Import all.

From ITree Require Import Core.Subevent.

From CTree Require Import
     CTree
     Utils
     Eq.Equ
     Eq.Shallow
     Eq.Trans.

From RelationAlgebra Require Export
     rel srel.

Import CoindNotations.
Import CTree.
Set Implicit Arguments.

Section StrongSim.
(*|
The function defining strong simulations: [trans] plays must be answered
using [trans].
The [ss] definition stands for [strong simulation]. The bisimulation [sb]
is obtained by expliciting the symmetric aspect of the definition following
Pous'16 in order to be able to exploit symmetry arguments in proofs
(see [square_st] for an illustration).
|*)
  Program Definition ss {E F C D : Type -> Type} {X Y : Type}
    (L : lrel E F X Y) :
    mon (@S E C X -> @S F D Y -> Prop) :=
    {| body R t u :=
      forall l t', trans l t t' ->
              exists l' u', trans l' u u' /\
                       R t' u' /\
                       L l l'
    |}.
  Next Obligation.
    edestruct3 H0; eauto.
    ex2; intuition; eauto.
  Qed.

  #[global] Instance lequiv_ss : forall {E F C D X Y}, Proper (lequiv ==> weq) (@ss E F C D X Y).
  Proof.
    cbn. intros * EQ *. split.
    - intros. apply H in H0 as (? & ? & ? & ? & ?).
      ex2; split3; eauto.
      now rewrite <- EQ.
     - intros. apply H in H0 as (? & ? & ? & ? & ?).
      ex2; split3; eauto.
      now rewrite EQ.
  Qed.

End StrongSim.

Definition ssim {E F C D X Y} L :=
  (gfp (@ss E F C D X Y L): hrel _ _).

Module SSimNotations.

  Infix "≲" := (ssim Leq) (at level 70).
  Notation "t (≲ [ Q ] ) u" := (ssim (Lvrel Q) t u) (at level 79).
  Notation "t (≲ Q ) u" := (ssim Q t u) (at level 79).

  Notation "t '[≲]' u" := (ss Leq (` _) t u) (at level 90, only printing).
  Notation "t '[≲' [ R ] ']' u" := (ss (Lvrel R) (` _) t u) (at level 90, only printing).
  Notation "t '[≲' R ']' u" := (ss R (` _) t u) (at level 90, only printing).
End SSimNotations.

Import SSimNotations.

Ltac fold_ssim :=
  repeat
    match goal with
    | h: context[gfp (@ss ?E ?F ?C ?D ?X ?Y ?L)] |- _ => fold (@ssim E F C D X Y L) in h
    | |- context[gfp (@ss ?E ?F ?C ?D ?X ?Y ?L)]      => fold (@ssim E F C D X Y L)
    end.

Import CTreeNotations.
Import EquNotations.

Tactic Notation "__step_ssim" :=
  match goal with
  | |- context[@ssim ?E ?F ?C ?D ?X ?Y ?LR] =>
      unfold ssim;
      step;
      fold (@ssim E F C D X Y L)
  end.

#[local] Tactic Notation "step" := __step_ssim || step.

Ltac __step_in_ssim H :=
  match type of H with
  | context[@ssim ?E ?F ?C ?D ?X ?Y ?LR] =>
      unfold ssim in H;
      step in H;
      fold (@ssim E F C D X Y L) in H
  end.

#[local] Tactic Notation "step" "in" ident(H) := __step_in_ssim H || step in H.

Tactic Notation "__coinduction_ssim" simple_intropattern(r) simple_intropattern(cih) :=
  first [unfold ssim at 4 | unfold ssim at 3 | unfold ssim at 2 | unfold ssim at 1]; coinduction r cih.
#[local] Tactic Notation "coinduction" simple_intropattern(r) simple_intropattern(cih) := __coinduction_ssim r cih || coinduction r cih.

Ltac __play_ssim := step; cbn; intros ? ? ?TR.

Ltac __play_ssim_in H :=
  step in H;
  cbn in H; edestruct H as (? & ? & ?TR & ?SS & ?HL);
  clear H; [etrans |]; fold_ssim.

Ltac __eplay_ssim :=
  match goal with
  | h : @ssim ?E ?F ?C ?D ?X ?Y _ _ ?L |- _ =>
      __play_ssim_in h
  end.

#[local] Tactic Notation "play" := __play_ssim.
#[local] Tactic Notation "play" "in" ident(H) := __play_ssim_in H.
#[local] Tactic Notation "eplay" := __eplay_ssim.

Section ssim_homogenous_theory.
  Context {E B: Type -> Type} {X: Type}
          {L: lrel E E X X}.

  Notation ss := (@ss E E B B X X).

  #[global] Instance refl_sst {LR: Reflexive L} {C: Chain (ss L)}: Reflexive `C.
  Proof.
    apply Reflexive_chain.
    cbn; eauto.
  Qed.

  #[global] Instance square_sst {LT: Transitive L} {C: Chain (ss L)}: Transitive `C.
  Proof.
    apply Transitive_chain.
    cbn. intros ????? xy yz.
    intros ?? xx'.
    destruct (xy _ _ xx') as (l' & y' & yy' & ? & ?).
    destruct (yz _ _ yy') as (l'' & z' & zz' & ? & ?).
    eauto 8.
  Qed.

  (*| PreOrder |*)
  #[global] Instance PreOrder_sst {LPO: PreOrder L} {C: Chain (ss L)}: PreOrder `C.
  Proof. split; typeclasses eauto. Qed.

End ssim_homogenous_theory.
 
(*|
Parametric theory of [ss] with heterogenous [L]
|*)
Section ssim_heterogenous_theory.
  Arguments label: clear implicits.
  Context {E F C D: Type -> Type} {X Y: Type}.

  Notation ss := (@ss E F C D X Y).
  Notation ssim  := (@ssim E F C D X Y).

  Lemma ssim_subrelation :
    Proper (sub_lrel ==> leq) ssim.
  Proof.
    cbn; intros * SUB.
    coinduction R cih.
    intros u v HSS l u' TR.
    eplay.
    ex2; split3; etrans.
    eapply sub_lrel_subrel; eauto.
  Qed.

  Context {L: lrel E F X Y}.

(*|
   Strong simulation up-to [equ] is valid
   ----------------------------------------
|*)

  Lemma equ_clos_chain {c: Chain (ss L)}:
    forall x y, equ_clos `c x y -> `c x y.
  Proof.
    apply tower.
    - intros ? INC x y [x' y' x'' y'' EQ' EQ''] ??. red.
      apply INC; auto.
      econstructor; eauto.
      apply leq_infx in H.
      now apply H.
    - intros a b ?? [x' y' x'' y'' EQ' EQ''] ? ? tr.
      rewrite EQ' in tr.
      edestruct EQ'' as (l' & ? & ? & ? & ?); [eauto |].
      exists l',x0; intuition.
      rewrite <- Equu; auto.
  Qed.

  #[global] Instance seq_chain_goal {c: Chain (ss L)} :
    Proper (Seq ==> Seq ==> flip impl) (`c).
  Proof.
    apply tower.
    - intros ? INC t t' HP' ? ? HP'' ?? HP'''. 
      red.
      eapply INC; eauto.
      apply leq_infx in HP'''.
      now apply HP'''.
    - intros ? INC  t t' EQt u u' EQu HS l v TR.
      rewrite EQt in TR.
      apply HS in TR as (l' & v' & ? & ? & ?).
      exists l',v'; split; auto.
      now rewrite EQu.
  Qed.

  #[global] Instance equ_chain_goal {c: Chain (ss L)} :
    Proper (equ eq ==> equ eq ==> flip impl) `c.
  Proof.
    cbn; intros ? ? eq1 ? ? eq2 H.
    apply equ_clos_chain; econstructor; [eauto | | symmetry; eauto]; assumption.
  Qed.

  #[global] Instance seq_ss_closed_goal {r} :
    Proper (Seq ==> Seq ==> flip impl) (ss L r).
  Proof.
    intros t t' tt' u u' uu'; cbn; intros.
    rewrite tt' in H0. apply H in H0 as (l' & ? & ? & ? & ?).
    ex2; eauto. rewrite uu'. eauto.
  Qed.

  #[global] Instance equ_ss_closed_goal {r} :
    Proper (equ eq ==> equ eq ==> flip impl) (ss L r).
  Proof.
    intros t t' tt' u u' uu'; cbn; intros.
    rewrite tt' in H0. apply H in H0 as (l' & ? & ? & ? & ?).
    ex2; eauto. rewrite uu'. eauto.
  Qed.

  #[global] Instance seq_chain_ctx  {c: Chain (ss L)} :
    Proper (Seq ==> Seq ==> impl) `c.
  Proof.
    apply tower.
    - intros ? INC t t' HP' ? ? HP'' ?? HP'''. 
      red.
      eapply INC; eauto.
      apply leq_infx in HP'''.
      now apply HP'''.
    - intros ? INC  t t' EQt u u' EQu HS l v TR.
      rewrite <- EQt in TR.
      apply HS in TR as (l' & v' & ? & ? & ?).
      exists l',v'; split; auto.
      now rewrite <- EQu.
  Qed.

  #[global] Instance equ_chain_ctx  {c: Chain (ss L)} :
    Proper (equ eq ==> equ eq ==> impl) `c.
  Proof.
    cbn; intros ? ? eq1 ? ? eq2 H.
    apply equ_clos_chain; econstructor; [symmetry; eauto | | eauto]; assumption.
  Qed.

  #[global] Instance seq_ss_closed_ctx {r} :
    Proper (Seq ==> Seq ==> impl) (ss L r).
  Proof.
    intros t t' tt' u u' uu'; cbn; intros.
    rewrite <- tt' in H0. apply H in H0 as (l' & ? & ? & ? & ?).
    ex2; eauto. rewrite <- uu'. eauto.
  Qed.

  #[global] Instance equ_ss_closed_ctx {r} :
    Proper (equ eq ==> equ eq ==> impl) (ss L r).
  Proof.
    intros t t' tt' u u' uu'; cbn; intros.
    rewrite <- tt' in H0. apply H in H0 as (l' & ? & ? & ? & ?).
    ex2; eauto. rewrite <- uu'. eauto.
  Qed.

End ssim_heterogenous_theory.

#[global] Instance weq_ssim : forall {E F C D X Y},
  Proper (lequiv ==> weq) (@ssim E F C D X Y).
Proof.
  cbn -[ss weq]. intros. apply gfp_weq. now apply lequiv_ss.
Qed.

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

(*|
Specialization of [bind_ctx] to a function acting with [ssim] on the bound value,
and with the argument (pointwise) on the continuation.
|*)
  Lemma bind_chain_gen
    {E F C D: Type -> Type} {X X' Y Y': Type}
    (L : lrel E F X' Y')
    (SS: rel X Y)
    {R : Chain (@ss E F C D X' Y' L)} :
    forall (t : ctree E C X) (t' : ctree F D Y)
      (k : X -> ctree E C X') (k' : Y -> ctree F D Y'),
      ssim (upd_rel L SS) t t' ->
      (forall x y, SS x y -> ` R (k x) (k' y)) ->
      ` R (bind t k) (bind t' k').
  Proof.
    apply tower.
    - intros ? INC ? ? ? ? tt' kk' ? ?.
      apply INC. apply H. apply tt'.
      intros x x' xx'. apply leq_infx in H. apply H. now apply kk'.
    - clear R.
      intros R ? ? ? ? ? tt' kk'.
      step in tt'.
      cbn; intros * STEP.
      apply trans_bind_inv in STEP as [(?H & ?t' & STEP & EQ) | [(Z & e & EQl & g & STEP & SEQ) | (v & STEPres & STEP)]].
      + subst l.
        apply tt' in STEP as (? & ? & STEP' & HSIM & HRL).
        inv HRL.
        refine_trans.
        ex2; split3.
        apply trans_bind_l_τ; eauto.
        * rewrite EQ.
          apply H; auto.
          intros.
          now step; apply kk'.
        * etrans.
      + subst l.
        apply tt' in STEP as (? & ? & STEP' & HSIM & HRL).
        invL.
        refine_trans.
        exists (ask f); ex; split3.
        eapply trans_bind_l_ask; eauto.
        * rewrite SEQ.
          step.
          intros ? ? STEP''.
          pose proof trans_passive_inv' STEP'' as (a & EQ & ->).
          rewrite EQ in STEP''.
          assert (TR: trans (rcv e a) (β e g) (g a)) by etrans.
          step in HSIM; apply HSIM in TR as (l' & u' & TR' & HSIM' & HRL').
          pose proof trans_passive_inv' TR' as (b & EQ' & ->).
          exists (rcv f b); ex; split; eauto; split; cycle 1.
          { invL; etrans. }
          rewrite EQ.
          apply H.
          rewrite EQ' in HSIM'; auto.
          intros.
          now step; apply kk'.
        * etrans.
      + apply tt' in STEPres as (? & ? & STEP' & HSIM & HRL).
        invL.
        apply (kk' v y) in STEP as (l' & u' & STEP'' & HSIM'' & HRL').
        exists l'; eexists; split; eauto.
        2:etrans.
        eapply trans_bind_r; eauto.
        erewrite <- trans_val_inv'; eauto.
  Qed.

(*|
Specialization: equality on external calls, equality everywhere
|*)
  Lemma bind_chain E C D X Y X' Y'
    (RR : rel X' Y') (SS : rel X Y)
    {R : Chain (@ss E E C D X' Y' (Lvrel RR))} :
    forall (t1 : ctree E C X) (t2: ctree E D Y)
      (k1 : X -> ctree E C X') (k2 : Y -> ctree E D Y'),
      t1 (≲[SS]) t2 ->
      (forall x y, SS x y -> `R (k1 x) (k2 y)) ->
      `R (t1 >>= k1) (t2 >>= k2).
  Proof.
    intros.
    eapply bind_chain_gen; eauto.
  Qed.

  Lemma bind_chain_eq E C X X'
    {R : Chain (@ss E E C C X' X' Leq)} :
    forall (t1 t2 : ctree E C X)
      (k1 k2 : X -> ctree E C X'),
      t1 ≲ t2 ->
      (forall x, `R (k1 x) (k2 x)) ->
      `R (t1 >>= k1) (t2 >>= k2).
  Proof.
    intros.
    eapply bind_chain_gen; eauto.
    intros ??<-; auto.
  Qed.

(*|
Specializations to the gfp
|*)
  Lemma ssim_bind_gen E F C D X Y X' Y'
    L (SS : rel X Y) 
    (t1 : ctree E C X) (t2: ctree F D Y)
    (k1 : X -> ctree E C X') (k2 : Y -> ctree F D Y'):
    t1 (≲ upd_rel L SS) t2 ->
    (forall x y, SS x y -> k1 x (≲ L) k2 y) ->
    t1 >>= k1 (≲ L) t2 >>= k2.
  Proof.
    intros.
    eapply bind_chain_gen; eauto.
  Qed.

  Lemma ssim_bind E C D X Y X' Y'
    (RR : rel X' Y') (SS : rel X Y) 
    (t1 : ctree E C X) (t2: ctree E D Y)
    (k1 : X -> ctree E C X') (k2 : Y -> ctree E D Y'):
    t1 (≲ [SS]) t2 ->
    (forall x y, SS x y -> k1 x (≲ [RR]) k2 y) ->
    t1 >>= k1 (≲ [RR]) t2 >>= k2.
  Proof.
    intros.
    eapply bind_chain_gen; eauto.
  Qed.

  Lemma ssim_bind_eq {E C D: Type -> Type} {X X': Type}
    (t1 : ctree E C X) (t2: ctree E D X)
    (k1 : X -> ctree E C X') (k2 : X -> ctree E D X'):
    t1 ≲ t2 ->
    (forall x, k1 x ≲ k2 x) ->
    t1 >>= k1 ≲ t2 >>= k2.
  Proof.
    intros.
    eapply ssim_bind; eauto.
    intros ?? ->; auto.
  Qed.

End bind.

(*|
And in particular, we can justify rewriting [≲] to the left of a [bind].

NOTE: we shouldn't have to impose [eq] to the right.
|*)
#[global] Instance ssim_bind_chain {E C X Y}
  {R : Chain (@ss E E C C Y Y Leq)} :
  Proper ((fun t u => ssim Leq (α t) (α u)) ==>
          (pointwise_relation _ (fun t u => ` R (α t) (α u))) ==> ` R) (@bind E C X Y).
Proof.
  repeat intro; eapply bind_chain_gen; eauto.
  intros ?? <-; auto.
Qed.

(* #[global] Instance bind_ssim_cong_gen {E C X X'} : *)
(*   Proper (ssim eq ==> pointwise_relation X (ssim eq) ==> ssim eq) (@CTree.bind E C X X'). *)
(* Proof. *)
(*   cbn. intros. now apply ssim_clo_bind_eq. *)
(* Qed. *)

(* Notation ssim_ L t u := (ssim L (α t) (α u)). *)
(* Notation ss_ L t u := (ss L _ (α t) (α u)). *)

Section Proof_Rules.

  Context {E F C D: Type -> Type} {X Y : Type}.

(*|
Stuck ctrees can be simulated by anything.
|*)
  Lemma ss_is_stuck L R (t : ctree E C X) (t': ctree F D Y):
    is_stuck t ->
    ss L R t t'.
  Proof.
    repeat intro. now apply H in H0.
  Qed.

  Lemma ssim_is_stuck L (t: ctree E C X) (t': ctree F D Y):
    is_stuck t ->
    ssim L t t'.
  Proof.
    intros. step. now apply ss_is_stuck.
  Qed.

  Lemma ss_stuck L R (t : ctree F D Y) :
    @ss E F C D X Y L R Stuck t.
  Proof.
    repeat intro. now apply Stuck_is_stuck in H.
  Qed.

  Lemma ssim_stuck L (t : ctree F D Y) :
    @ssim E F C D X Y L Stuck t.
  Proof.
    intros. step. apply ss_stuck.
  Qed.

  Lemma ss_spin L R (t : ctree F D Y) :
    @ss E F C D X Y L R spin t.
  Proof.
    repeat intro. now apply spin_is_stuck in H.
  Qed.

  Lemma ssim_spin L (t' : ctree F D Y) :
      @ssim E F C D X Y  L spin t'.
  Proof.
    intros. step. apply ss_spin.
  Qed.

(*|
Ret nodes
|*)
  Lemma ss_ret (x : X) (y : Y) L
    {R : Chain (@ss E F C D X Y L)} :
    RR L x y ->
    ss L `R (Ret x : ctree E C X) (Ret y : ctree F D Y).
  Proof.
    intros HR l u TR.
    inv_trans. subst.
    ex2; intuition.
    rewrite EQ.
    step; apply ss_stuck.
  Qed.
  
  Lemma ssim_ret (x : X) (y : Y) L :
    RR L x y ->
    ssim L (Ret x : ctree E C X) (Ret y : ctree F D Y).
  Proof.
    intros.
    step. now apply ss_ret.
  Qed.
  
(*|
 The vis nodes are deterministic from the perspective of the labeled
 transition system, stepping is hence symmetric and we can just recover
 the itree-style rule.
|*)
  Lemma ss_vis {Z Z'} (e : E Z) (f: F Z')
    (k : Z -> ctree E C X) (k' : Z' -> ctree F D Y) L
    {R : Chain (@ss E F C D X Y L)}
    (HRask : Rask L e f)
    (HRrcv : forall x, exists y, `R (k x) (k' y) /\ Rrcv L e f x y) :
    ss L ` R (Vis e k) (Vis f k').
  Proof.
    intros ?? TR; inv_trans.
    subst.
    ex2; intuition.
    rewrite EQ.
    step.
    intros l u TR.
    inv_trans; subst.
    destruct (HRrcv x) as (y & ? & ?).
    ex2; intuition.
    rewrite EQ0; eauto.
    etrans.
  Qed.

  Lemma ssim_vis {Z Z'} (e : E Z) (f: F Z')
    (k : Z -> ctree E C X) (k' : Z' -> ctree F D Y) L
    (HRask : Rask L e f)
    (HRrcv : forall x, exists y, ssim L (k x) (k' y) /\ Rrcv L e f x y) :
    ssim L (Vis e k) (Vis f k').
  Proof.
    intros. step. apply ss_vis; auto.
  Qed.

  (* Useful special case: over the same type return type,
     we usually pick the identity *)
  Lemma ss_vis_id {Z} (e : E Z) (f: F Z)
    (k : Z -> ctree E C X) (k' : Z -> ctree F D Y) L
    {R : Chain (@ss E F C D X Y L)} 
    (HRask : Rask L e f)
    (HRrcv : forall z, ` R (k z) (k' z) /\ Rrcv L e f z z) :
    ss L ` R (Vis e k) (Vis f k').
  Proof.
    eapply ss_vis; eauto.
  Qed.
  
  Lemma ssim_vis_id {Z} (e : E Z) (f : F Z)
    (k : Z -> ctree E C X) (k' : Z -> ctree F D Y) L
    (HRask : Rask L e f)
    (HRrcv : forall x, ssim L (k x) (k' x) /\ Rrcv L e f x x) :
    ssim L (Vis e k) (Vis f k').
  Proof.
    intros. step. now apply ss_vis_id.
  Qed.

(*|
Invisible nodes
|*)
  (* Here we need a stronger lemma quantifying over arbitrary relations [R] and not just elements of the Chain in order to lift things to ssim as we don't unlock ssim in the structural subterm *)
  Lemma ss_br_l_gen {Z} (c : C Z)
    (k : Z -> ctree E C X) (t': ctree F D Y) R L:
    (forall x, ss L R (k x) t') ->
    ss L R (Br c k) t'.
  Proof.
    intros EQs.
    intros ? ? TR; inv_trans; subst.
    edestruct3 EQs; eauto.
  Qed.

  Lemma ss_br_l {Z} (c : C Z)
    (k : Z -> ctree E C X) (t: ctree F D Y) L 
    {R : Chain (@ss E F C D X Y L)} :
    (forall x,  ss L `R (k x) t) ->
    ss L `R (Br c k) t.
  Proof.
    intros.
    intros ? ? TR.
    inv_trans; subst.
    edestruct3 H; eauto.
  Qed.

  Lemma ssim_br_l {Z} (c : C Z)
    (k : Z -> ctree E C X) (t: ctree F D Y) L :
    (forall x, ssim L (k x) t) ->
    ssim L (Br c k) t.
  Proof.
    intros. step. apply ss_br_l_gen. intros.
    specialize (H x). step in H. apply H.
  Qed.

  Lemma ss_br_r_gen {Z} (c : D Z) x
    (k : Z -> ctree F D Y) (t: ctree E C X) R L:
    ss L R t (k x) ->
    ss L R t (Br c k).
  Proof.
    cbn. intros.
    apply H in H0 as (? & ? & ? & ? & ?).
    exists x0; etrans.
  Qed.

  Lemma ss_br_r {Z} (c : D Z) x
        (k : Z -> ctree F D Y) (t: ctree E C X) L
        {R : Chain (@ss E F C D X Y L)} :
    ss L `R t (k x) ->
    ss L `R t (Br c k).
  Proof.
    apply ss_br_r_gen.
  Qed.

  Lemma ssim_br_r {Z} (c : D Z) x
        (k : Z -> ctree F D Y) (t: ctree E C X) L :
    ssim L t (k x) ->
    ssim L t (Br c k).
  Proof.
    intros. step. apply ss_br_r_gen with (x := x). now step in H.
  Qed.

  Lemma ss_br_gen {A B} (c: C A) (d: D B)
    (k : A -> ctree E C X) (k' : B -> ctree F D Y) R L :
    (forall x, exists y, ss L R (k x) (k' y)) ->
    ss L R (Br c k) (Br d k').
  Proof.
    intros EQs.
    apply ss_br_l_gen.
    intros. destruct (EQs x) as [x' ?].
    now apply ss_br_r_gen with (x:=x').
  Qed.

  Lemma ss_br {A B} (c: C A) (d: D B)
    (k : A -> ctree E C X) (k' : B -> ctree F D Y) L 
    {R : Chain (@ss E F C D X Y L)} :
    (forall x, exists y, ss L `R (k x) (k' y)) ->
    ss L `R (Br c k) (Br d k').
  Proof.
    apply ss_br_gen.
  Qed.

  Lemma ssim_br {A B} (c: C A) (d: D B)
    (k : A -> ctree E C X) (k' : B -> ctree F D Y) L :
    (forall x, exists y, ssim L (k x) (k' y)) ->
    ssim L (Br c k) (Br d k').
  Proof.
    intros. step. apply ss_br_gen.
    intros. destruct (H x). step in H0. exists x0. apply H0.
  Qed.

  Lemma ss_br_id {A} (c: C A) (d: D A)
    (k : A -> ctree E C X) (k': A -> ctree F D Y) L
    {R : Chain (@ss E F C D X Y L)} :
    (forall x, ss L `R (k x) (k' x)) ->
    ss L `R (Br c k) (Br d k').
  Proof.
    intros; apply ss_br; eauto.
  Qed.

  Lemma ssim_br_id {A} (c: C A) (d: D A)
    (k : A -> ctree E C X) (k': A -> ctree F D Y) L :
    (forall x, ssim L (k x) (k' x)) ->
    ssim L (Br c k) (Br d k').
  Proof.
    intros. apply ssim_br. eauto.
  Qed.

  Lemma ss_guard_l_gen 
    (t: ctree E C X) (t': ctree F D Y) R L:
    ss L R t t' ->
    ss L R (Guard t) t'.
  Proof.
    intros EQ.
    intros ? ? TR; inv_trans; subst.
    apply EQ in TR; edestruct5 TR; eauto.
  Qed.

  Lemma ss_guard_l
    (t: ctree E C X) (t': ctree F D Y) L
    {R : Chain (@ss E F C D X Y L)} :
    ss L `R t t' ->
    ss L `R (Guard t) t'.
  Proof.
    intros; now apply ss_guard_l_gen.
  Qed.

  Lemma ssim_guard_l 
    (t: ctree E C X) (t': ctree F D Y) L:
    ssim L t t' ->
    ssim L (Guard t) t'.
  Proof.
    intros; step; apply ss_guard_l; step in H; auto.
  Qed.

  Lemma ss_guard_r_gen 
    (t: ctree E C X) (t': ctree F D Y) R L :
    ss L R t t' ->
    ss L R t (Guard t').
  Proof.
    intros EQ.
    intros ? ? TR; inv_trans; subst.
    apply EQ in TR; edestruct5 TR; eauto 7.
  Qed.

  Lemma ss_guard_r
    (t: ctree E C X) (t': ctree F D Y) L
    {R : Chain (@ss E F C D X Y L)} :
    ss L `R t t' ->
    ss L `R t (Guard t').
  Proof.
    now apply ss_guard_r_gen.
  Qed.

  Lemma ssim_guard_r 
    (t: ctree E C X) (t': ctree F D Y) L :
    ssim L t t' ->
    ssim L t (Guard t').
  Proof.
    intros; step; apply ss_guard_r; step in H; auto.
  Qed.

  Lemma ssim_guard 
    (t: ctree E C X) (t': ctree F D Y) L :
    ssim L t t' ->
    ssim L (Guard t) (Guard t').
  Proof.
    intros.
    now apply ssim_guard_l, ssim_guard_r.
  Qed.

(*|
Internal transitions
|*)
  Lemma ss_step 
    (t: ctree E C X) (t': ctree F D Y) L
    {R : Chain (@ss E F C D X Y L)} :
    ` R t t' ->
    ss L ` R (Step t) (Step t').
  Proof.
    intros HR ???; inv_trans; subst.
    ex2; intuition.
    now rewrite EQ.
  Qed.

  Lemma ssim_step
    (t: ctree E C X) (t': ctree F D Y) L :
    ssim L t t' ->
    ssim L (Step t) (Step t').
  Proof.
    now intros; step; apply ss_step.
  Qed.

  Lemma ss_brS {Z Z'} (c : C Z) (c' : D Z')
    (k : Z -> ctree E C X) (k' : Z' -> ctree F D Y) L 
    {R : Chain (@ss E F C D X Y L)} :
    (forall x, exists y, ` R (k x) (k' y)) ->
    ss L ` R (BrS c k) (BrS c' k').
  Proof.
    intros.
    eapply ss_br.
    intros x; specialize (H x) as [y ?].
    exists y.
    eapply ss_step; auto.
  Qed.

  Lemma ssim_brS {Z Z'} (c : C Z) (c' : D Z')
    (k : Z -> ctree E C X) (k' : Z' -> ctree F D Y) L :
    (forall x, exists y, ssim L (k x) (k' y)) ->
    ssim L (BrS c k) (BrS c' k').
  Proof.
    now intros; step; apply ss_brS.
  Qed.

  Lemma ss_brS_id {Z} (c : C Z) (d : D Z)
    (k: Z -> ctree E C X) (k': Z -> ctree F D Y) L 
    {R : Chain (@ss E F C D X Y L)} :
    (forall x, `R (k x) (k' x)) ->
    ss L ` R (BrS c k) (BrS d k').
  Proof.
    intros; apply ss_brS; eauto.
  Qed.

  Lemma ssim_brS_id {Z} (c : C Z) (d : D Z)
    (k: Z -> ctree E C X) (k': Z -> ctree F D Y) L :
    (forall x, ssim L (k x) (k' x)) ->
    ssim L (BrS c k) (BrS d k').
  Proof.
    intros; apply ssim_brS; eauto.
  Qed.

(*|
    Note that with visible schedules, an nary-spins refines another only
    if it is empty, or if neither are empty.
|*)
  Lemma ssim_spinS_nonempty :
    forall {Z Z'} L (x: Z) (y: Z') (c: C Z) (c': D Z'),
      @ssim E F C D X Y L (spinS_gen c) (spinS_gen c').
  Proof.
    intros until L; intros x y.
    coinduction S CIH.
    intros * ?? TR.
    rewrite ctree_eta in TR; cbn in TR.
    inv_trans.
    ex2; split3; subst; etrans.
    rewrite ctree_eta; cbn; etrans.
    now rewrite EQ.
  Qed.

  Lemma ssim_spinS_empty :
    forall Z L (c: C False) (c': D Z),
      @ssim E F C D X Y L (spinS_gen c) (spinS_gen c').
  Proof.
    intros.
    eapply ssim_is_stuck.
    intros ?? TR.
    rewrite ctree_eta in TR; cbn in TR.
    now inv_trans.
  Qed.

  (* Seems useless, but used in a fold lemma. To double check *)
  (* Lemma step_ss_ret_l_gen {Y F D} (x : X) (y : Y) (u u' : ctree F D Y) (L R : rel _ _) : *)
  (*   R Stuck Stuck -> *)
  (*   (Proper (equ eq ==> equ eq ==> impl) R) -> *)
  (*   L (val x) (val y) -> *)
  (*   trans (val y) u u' -> *)
  (*   ss L R (Ret x : ctree E C X) u. *)
  (* Proof. *)
  (*   intros. cbn. intros. *)
  (*   apply trans_val_inv in H2 as ?. *)
  (*   inv_trans. subst. setoid_rewrite EQ. *)
  (*   etrans. *)
  (* Qed. *)

  (* Lemma step_ss_ret_l {Y F D} (x : X) (y : Y) (u u' : ctree F D Y) (L : rel _ _) *)
  (*   {R : Chain (@ss E F C D X Y L)} : *)
  (*   L (val x) (val y) -> *)
  (*   trans (val y) u u' -> *)
  (*   ss L ` R (Ret x : ctree E C X) u. *)
  (* Proof. *)
  (*   intros. *)
  (*   eapply step_ss_ret_l_gen; eauto. *)
  (*   - apply (b_chain R). *)
  (*     apply is_stuck_ss; apply Stuck_is_stuck. *)
  (*   - typeclasses eauto. *)
  (* Qed. *)

(*|
Inversion principles
--------------------
Question: are the principles useful over [ss] as well?
|*)
  
  Lemma ssim_stuck_inv L (t : ctree E C X) (u : ctree F D Y)
    (IS : is_stuck u)
    (SS :@ssim E F C D X Y  L t u) :
    is_stuck t.
  Proof.
    intros l t' TR.
    step in SS.
    apply SS in TR.
    edestruct5 TR.
    eapply IS; eauto.
  Qed.

  Lemma ssim_ret_l_inv L :
    forall r (u : ctree F D Y)
      (SS : @ssim E F C D X Y L (Ret r) u),
      exists r' u', trans (val r') u u' /\ RR L r r'.
  Proof.
    intros. step in SS.
    edestruct5 SS; etrans.
    invL.
    ex2; split; etrans.
  Qed.
 
  Lemma ssim_ret_inv L (r1 : X) (r2 : Y)
    (SS : @ssim E F C D X Y L (Ret r1) (Ret r2)) :
    L (val r1) (val r2).
  Proof.
    eplay.
    now inv_trans.
  Qed.

  Lemma ssim_vis_inv {X1 X2} L
    (e : E X1) (f : F X2)
    (k1 : X1 -> ctree E C X) (k2 : X2 -> ctree F D Y)
    (SS : ssim L (Vis e k1) (Vis f k2)) :
    Rask L e f /\
      (forall x, exists y, Rrcv L e f x y /\ ssim L (k1 x) (k2 y)).
  Proof.
    eplay; inv_trans; invL.
    split; auto.
    intros x.
    unshelve eplay; [exact x |].
    invL.
    inv_trans.
    dependent destruction EQl.
    ex; split; eauto.
  Qed.

  Lemma ssim_vis_l_inv {Z L} :
    forall (e : E Z) (k : Z -> ctree E C X) u,
    @ssim E F C D X Y L (Vis e k) u ->
    exists Z' (f : F Z') k',
      trans (ask f) u (β f k') /\
      Rask L e f /\
      forall x, exists y, ssim L (k x) (k' y) /\ Rrcv L e f x y.
  Proof.
    intros.
    eplay; invL; refine_trans.
    ex3; split3; etrans.
    intros z.
    unshelve eplay; [eassumption |]; inv_trans; invL.
    ex; split; etrans.
  Qed.

  Lemma ssim_guard_l_inv L (t1 : ctree E C X) (t2 : ctree F D Y) :
    ssim L (Guard t1) t2 ->
    ssim L t1 t2.
  Proof.
    intros SS; play; eplay.
    ex2; split3; etrans.
  Qed.

  Lemma ssim_guard_r_inv L (t1 : ctree E C X) (t2 : ctree F D Y) :
    ssim L t1 (Guard t2) ->
    ssim L t1 t2.
  Proof.
    intros SS; play; eplay; inv_trans.
    ex2; split3; etrans.
  Qed.

  Lemma ssim_guard_inv L (t1 : ctree E C X) (t2 : ctree F D Y) :
    ssim L (Guard t1) (Guard t2) ->
    ssim L t1 t2.
  Proof.
    intros.
    now apply ssim_guard_r_inv, ssim_guard_l_inv.
  Qed.

  Lemma ssim_br_l_inv L Z
    (c: C Z) (t : ctree F D Y) (k : Z -> ctree E C X):
    ssim L (Br c k) t ->
    forall x, ssim L (k x) t.
  Proof.
    intros; play; eplay; eauto.
  Qed.

  Lemma ssim_br_r_inv L Z
    (d: D Z) (t : ctree E C X) (k : Z -> ctree F D Y):
    ssim L t (Br d k) ->
    forall l t', trans l t t' ->
    exists x l' u', trans l' (k x) u' /\
               ssim L t' u' /\
               L l l'.
  Proof.
    intros SS * TR.
    eplay; inv_trans.
    ex3; split3; eauto.
  Qed.

  Lemma ssim_step_inv L (t1 : ctree E C X) (t2 : ctree F D Y) :
    ssim L (Step t1) (Step t2) ->
    ssim L t1 t2.
  Proof.
    intros; eplay; inv_trans; etrans.
  Qed.

  Lemma ssim_step_l_inv L (t1 : ctree E C X) (t2 : ctree F D Y) :
    ssim L (Step t1) t2 ->
    exists t2', trans τ t2 t2' /\ ssim L t1 t2'.
  Proof.
    intros; eplay; invL; refine_trans.
    ex; split; etrans.
  Qed.

  Lemma ssim_brS_inv L
    A B (c: C A) (d: D B) (k1 : A -> ctree E C X) (k2 : B -> ctree F D Y) :
    ssim L (BrS c k1) (BrS d k2) ->
    forall i1, exists i2, ssim L (k1 i1) (k2 i2).
  Proof.
    intros EQ i1.
    eplay; invL; inv_trans; eauto.
  Qed.

  Lemma ssim_brS_l_inv L
    A (c: C A) (k1 : A -> ctree E C X) (t2 : ctree F D Y) :
    ssim L (BrS c k1) t2 ->
    forall i, exists t2', trans τ t2 t2' /\ ssim L (k1 i) t2'.
  Proof.
    intros EQ i1.
    eplay; invL; inv_trans; eauto.
  Qed.

End Proof_Rules.
