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

(* TODO: Decide where to set this *)
Arguments trans : simpl never.
(* check *)
Notation htrans l u v := (hrel_of (trans l) u v) (only parsing).
Ltac refine_transition H :=
  match type of H with
  | htrans τ _ _ =>
      let u  := fresh "u" in
      let EQ := fresh "EQ" in
      pose proof trans_τ_active H as [u EQ];
      rewrite EQ in *;
      match type of EQ with
      | Seq ?a _ => try clear a EQ
      end
  | hrel_of (trans (ask ?e)) _ _ =>
      let u  := fresh "u" in
      let EQ := fresh "EQ" in
      pose proof trans_ask_passive H as [u EQ];
      rewrite EQ in *;
      match type of EQ with
      | Seq ?a _ => try clear a EQ
      end
  end.

(* Truc de ce genre c'est un Proper *)
(* forall X Y (R : X -> Y -> Prop), equiv R (ret x) (ret y) -> R x y. *)

Section build_rel.

  Context {E F : Type -> Type} {X Y : Type}.

  Record lrel :=
    {
      RR: rel X Y ;
      Rask: forall [X Y], E X -> F Y -> Prop ;
      Rrcv: forall [X Y] (e : E X) (f : F Y), X -> Y -> Prop ;
    }.
  
  Variant build_rel {RL : lrel} : hrel (label E) (label F) :=
    | rel_τ   : build_rel τ τ
    | rel_ask {X Y} {e : E X} {f : F Y}
        (HR : Rask RL e f) :
      build_rel (ask e) (ask f)
    | rel_rcv {X Y} {e : E X} {f : F Y} x y
        (HR : Rrcv RL e f x y) :
      build_rel (rcv e x) (rcv f y)
    | rel_ret {x : X} {y : Y}:
      RR RL x y -> build_rel (val x) (val y).
  Arguments build_rel : clear implicits.
  
  Lemma build_rel_val RL x y :
    build_rel RL (val x) (val y) -> RR RL x y.
  Proof.
    now intros H; dependent induction H.
  Qed.
  
  Lemma build_rel_ask RL A B (e : E A) (f : F B) :
    build_rel RL (ask e) (ask f) -> Rask RL e f.
  Proof.
    now intros H; dependent induction H.
  Qed.
  
  Lemma build_rel_rcv RL A B (e : E A) (f : F B) a b : 
    build_rel RL (rcv e a) (rcv f b) -> Rrcv RL e f a b.
  Proof.
    now intros H; dependent induction H.
  Qed.

  Lemma build_rel_τ RL :
    build_rel RL τ τ.
  Proof.
    constructor.
  Qed.
  
End build_rel.

Arguments lrel : clear implicits.
Arguments build_rel {E F X Y} RL.
#[global] Hint Constructors build_rel : trans.
Coercion build_rel : lrel >-> hrel.

Definition upd_Lrel {E F X Y X' Y'}
  (RL : lrel E F X Y)
  (SS : rel X' Y') : lrel E F X' Y' :=
  {|
    RR   := SS ;
    Rask := Rask RL ;
    Rrcv := Rrcv RL
  |}.

Variant eq1 {E} : forall [X Y : Type], rel (E X) (E Y) :=
  | Eq1 X (e : E X) : eq1 e e.
Variant eq2 {E} : forall [X Y : Type], E X -> E Y -> rel X Y :=
  | Eq2 X (e : E X) x : eq2 e e x x.
Hint Resolve Eq1 : trans.
Hint Resolve Eq2 : trans.

Definition Leq {E} {X : Type} : lrel E E X X :=
  {|
    RR   := eq ;
    Rask := eq1 ;
    Rrcv := eq2
  |}.

Definition Lvrel {E X Y} (RR : rel X Y) : lrel E E X Y :=
   {|
    RR   := RR ;
    Rask := eq1 ;
    Rrcv := eq2
  |}.

Ltac ex  :=  eexists.
Ltac ex2 := do 2 eexists.
Ltac ex3 := do 3 eexists.
Ltac split3 := split; [| split].
Ltac edestruct3 H := edestruct H as (? & ? & ?).
Ltac edestruct4 H := edestruct H as (? & ? & ? & ?).
Ltac edestruct5 H := edestruct H as (? & ? & ? & ? & ?).

Definition lequiv {E F X Y} : rel (lrel E F X Y) (lrel E F X Y) :=
  fun L1 L2 => RR L1 == RR L2 /\ Rask L1 == Rask L2 /\ Rrcv L1 == Rrcv L2.

#[global] Instance lequiv_equivalence {E F X Y} : Equivalence (@lequiv E F X Y).
Proof.
  constructor.
  - split3; auto.
  - intros ?? [? []]; split3; symmetry; auto.
  - intros ??? [? []] [? []]; split3; etransitivity; eauto.
Qed.

#[global] Instance lequiv_build_rel {E F X Y} : Proper (lequiv ==> weq) (@build_rel E F X Y).
Proof.
  cbn; intros L1 L2 [EQ1 [EQ2 EQ3]] l1 l2; split; intros H.
  - inv H; etrans.
    constructor; now apply EQ2.
    constructor; now apply EQ3.
    constructor; now apply EQ1.
  - inv H; etrans.
    constructor; now apply EQ2.
    constructor; now apply EQ3.
    constructor; now apply EQ1.
Qed.

#[global] Instance lequiv_build_rel' {E F X Y} : Proper (lequiv ==> eq ==> eq ==> iff) (@build_rel E F X Y).
Proof.
  now cbn; intros; subst; eapply lequiv_build_rel.
Qed.

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
  Context {E F C D: Type -> Type} {X Y: Type}
          {L: lrel E F X Y}.

  Notation ss := (@ss E F C D X Y).
  Notation ssim  := (@ssim E F C D X Y).

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
      ssim (upd_Lrel L SS) t t' ->
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
        refine_transition STEP'.
        ex2; split3.
        apply trans_bind_l_τ; eauto.
        * rewrite EQ.
          apply H; auto.
          intros.
          now step; apply kk'.
        * etrans.
      + subst l.
        apply tt' in STEP as (? & ? & STEP' & HSIM & HRL).
        dependent induction HRL.
        refine_transition STEP'.
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
          {dependent induction HRL'. etrans.}
          rewrite EQ.
          apply H.
          rewrite EQ' in HSIM'; auto.
          intros.
          now step; apply kk'.
        * etrans.
      + apply tt' in STEPres as (? & ? & STEP' & HSIM & HRL).
        dependent induction HRL.
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
    t1 (≲ upd_Lrel L SS) t2 ->
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

Ltac __play_ssim := step; cbn; intros ? ? ?TR.

Ltac __play_ssim_in H :=
  step in H;
  cbn in H; edestruct H as (? & ? & ?TR & ?EQ & ?HL);
  clear H; [etrans |].

Ltac __eplay_ssim :=
  match goal with
  | h : @ssim ?E ?F ?C ?D ?X ?Y _ _ ?L |- _ =>
      __play_ssim_in h
  end.

#[local] Tactic Notation "play" := __play_ssim.
#[local] Tactic Notation "play" "in" ident(H) := __play_ssim_in H.
#[local] Tactic Notation "eplay" := __eplay_ssim.

(* Definition ss_ {E F C D X Y} (L : lrel E F X Y) *)
(*   (R : rel S S) : rel (ctree E C X) (ctree F D Y) := *)
(*   fun t u => ss L R (α t) (α u). *)

(* Definition ssim_ {E F C D X Y} (L : lrel E F X Y): rel (ctree E C X) (ctree F D Y) := *)
(*   fun t u => ssim L (α t) (α u). *)

Lemma ask_invT : forall E X Y e1 e2, @ask E X e1 = @ask E Y e2 -> X = Y.
  intros * EQ.
  now dependent induction EQ.
Qed.

Lemma ask_inv : forall E X e1 e2, @ask E X e1 = @ask E X e2 -> e1 = e2.
  intros * EQ.
  now dependent induction EQ.
Qed.

Lemma rcv_invT : forall E X Y e1 e2 v1 v2, @rcv E X e1 v1 = @rcv E Y e2 v2 -> X = Y.
  intros * EQ.
  now dependent induction EQ.
Qed.

Lemma rcv_inv : forall E X e1 e2 v1 v2, @rcv E X e1 v1 = @rcv E X e2 v2 -> e1 = e2 /\ v1 = v2.
  intros * EQ.
  now dependent induction EQ.
Qed.

Ltac inv_label_eq EQl :=
  match type of EQl with
    | τ        = τ     =>
        clear EQl
    | val _   = val _ =>
        apply val_eq_inv in EQl; try (inversion EQl; fail)
    | ask _   = ask _ =>
        let EQt := fresh "EQt" in
        let EQe := fresh "EQe" in
        apply ask_invT in EQl as EQt;
        symmetry in EQt;
        (* subst_hyp_in EQt h; *)
        apply ask_inv in EQl as EQe;
        try (inversion EQe; fail)
    | rcv _ _ = rcv _ _ =>
        let EQt := fresh "EQt" in
        let EQt := fresh "EQv" in
        let EQe := fresh "EQe" in
        apply rcv_invT in EQl as EQt;
        symmetry in EQt;
        (* subst_hyp_in EQt h; *)
        apply rcv_inv in EQl as [EQe EQv];
        try (inversion EQe; inversion EQv; fail)
    | _ => try now inv EQl
  end.

Ltac inv_trans_one :=
  match goal with
  (* Ret *)
  | h : hrel_of (trans _) (α Ret _) _ |- _ =>
      let EQl := fresh "EQl" in
      (apply trans_ret_inv in h as [?EQ EQl] || apply trans_ret_inv' in h as [?EQ EQl]);
      inv_label_eq EQl

  (* Step *)
  | h : hrel_of (trans _) (α Step _) _ |- _ =>
      let EQl := fresh "EQl" in
      apply trans_step_inv' in h as (?EQ & EQl);
      inv_label_eq EQl
 
  (* Br *)
  | h : hrel_of (trans _) (α Br _ _) _ |- _ =>
      let TR := fresh "TR" in
      apply trans_br_inv in h as (?n & TR)

  (* Guard *)
  | h : hrel_of (trans _) (α Guard _) _ |- _ =>
      apply trans_guard_inv in h
                                 
  (* Vis *)
  | h : hrel_of (trans _) (α (Vis ?e ?k)) _ |- _ =>
      let EQl := fresh "EQl" in
      apply trans_vis_inv' in h as (?EQ & EQl);
      inv_label_eq EQl
                   
  (* Passive *)
  | h : hrel_of (trans _) (β ?e ?k) _ |- _ =>
      let EQl := fresh "EQl" in
      apply trans_passive_inv' in h as (?x & ?EQ & EQl);
      inv_label_eq EQl
      
  end.

Ltac inv_trans := repeat inv_trans_one.
  
Notation ssim_ L t u := (ssim L (α t) (α u)).
Notation ss_ L t u := (ss L _ (α t) (α u)).

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
    inv_trans.
  Qed.


  (* CHECKPOINT  *)


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
    When matching visible brs one against another, in general we need to explain how
    we map the branches from the left to the branches to the right.
    A useful special case is the one where the arity coincide and we simply use the identity
    in both directions. We can in this case have [n] rather than [2n] obligations.
|*)
(*|
Inversion principles
--------------------
|*)

  Lemma ssim_stuck_rev L (t : ctree E C X) (u : ctree F D Y) :
    is_stuck u ->
    @ssim E F C D X Y  L t u ->
    is_stuck t.
  Proof.
    intros IS SS l t' TR.
    step in SS.
    apply SS in TR.
    edestruct5 TR.
    eapply IS; eauto.
  Qed.

  Lemma ssim_ret_inv {F D Y} {L: rel (label E) (label F)} (r1 : X) (r2 : Y) :
    ssim L (Ret r1 : ctree E C X) (Ret r2 : ctree F D Y) ->
    L (val r1) (val r2).
  Proof.
    intro.
    eplay.
    inv_trans; subst; assumption.
  Qed.

  Lemma ss_ret_l_inv {F D Y L R} :
    forall r (u : ctree F D Y),
    ss L R (Ret r : ctree E C X) u ->
    exists l' u', trans l' u u' /\ R Stuck u' /\ L (val r) l'.
  Proof.
    intros. apply H; etrans.
  Qed.

  Lemma ssim_ret_l_inv {F D Y L} :
    forall r (u : ctree F D Y),
    ssim L (Ret r : ctree E C X) u ->
    exists l' u', trans l' u u' /\ L (val r) l'.
  Proof.
    intros. step in H.
    apply ss_ret_l_inv in H as (? & ? & ? & ? & ?). etrans.
  Qed.

  Lemma ssim_vis_inv_type {D Y X1 X2}
    (e1 : E X1) (e2 : E X2) (k1 : X1 -> ctree E C X) (k2 : X2 -> ctree E D Y) (x1 : X1):
    ssim eq (Vis e1 k1) (Vis e2 k2) ->
    X1 = X2.
  Proof.
    intros.
    step in H; cbn in H.
    edestruct H as (? & ? & ? & ? & ?).
    etrans.
    inv_trans; subst; auto.
    eapply obs_eq_invT; eauto.
    Unshelve.
    exact x1.
  Qed.

  Lemma ssbt_vis_inv {F D Y X1 X2} {L: rel (label E) (label F)}
    (e1 : E X1) (e2 : F X2) (k1 : X1 -> ctree E C X) (k2 : X2 -> ctree F D Y) (x : X1)
    {R : Chain (@ss E F C D X Y L)} :
    ss L (elem R) (Vis e1 k1) (Vis e2 k2) ->
    (exists y, L (obs e1 x) (obs e2 y))  /\ (forall x, exists y, ` R (k1 x) (k2 y)).
  Proof.
    intros.
    split; intros; edestruct H as (? & ? & ? & ? & ?);
      etrans; subst;
      inv_trans; subst; eexists; auto.
    - now eapply H2.
    - now apply H1.
  Qed.

  Lemma ssim_vis_inv {F D Y X1 X2} {L: rel (label E) (label F)}
        (e1 : E X1) (e2 : F X2) (k1 : X1 -> ctree E C X) (k2 : X2 -> ctree F D Y) (x : X1):
    ssim L (Vis e1 k1) (Vis e2 k2) ->
    (exists y, L (obs e1 x) (obs e2 y)) /\ (forall x, exists y, ssim L (k1 x) (k2 y)).
  Proof.
    intros.
    split.
      - eplay.
        inv_trans; subst; exists x2; eauto.
      - intros y.
        step in H.
        cbn in H.
        edestruct H as (l' & u' & TR & IN & HL).
        apply trans_vis with (x := y).
        inv_trans.
        eexists.
        apply IN.
  Qed.

  Lemma ss_vis_l_inv {F D Y Z L R} :
    forall (e : E Z) (k : Z -> ctree E C X) (u : ctree F D Y) x,
    ss L R (Vis e k) u ->
    exists l' u', trans l' u u' /\ R (k x) u' /\ L (obs e x) l'.
  Proof.
    intros. apply H; etrans.
  Qed.

  Lemma ssim_vis_l_inv {F D Y Z L} :
    forall (e : E Z) (k : Z -> ctree E C X) (u : ctree F D Y) x,
    ssim L (Vis e k) u ->
    exists l' u', trans l' u u' /\ ssim L (k x) u' /\ L (obs e x) l'.
  Proof.
    intros. step in H.
    now simple apply ss_vis_l_inv with (x := x) in H.
  Qed.

  Lemma ss_step_inv {F D Y} {L: rel (label E) (label F)} {R : Chain (@ss E F C D X Y L)}
        (t1 : ctree E C X) (t2 : ctree F D Y) :
    ss L (elem R) (Step t1) (Step t2) ->
    (elem R t1 t2).
  Proof.
    intros EQ.
    edestruct EQ as (l & t & TR & REL & HL); etrans.
    now inv_trans.
  Qed.

  Lemma ssim_step_inv {F D Y} {L: rel (label E) (label F)}
        (t1 : ctree E C X) (t2 : ctree F D Y) :
    ssim L (Step t1) (Step t2) ->
    ssim L t1 t2.
  Proof.
    intros EQ. step in EQ. now apply ss_step_inv.
  Qed.

  Lemma ss_step_l_inv {F D Y L R} :
    forall (t : ctree E C X) (u : ctree F D Y),
    ss L R (Step t) u ->
    exists l' u', trans l' u u' /\ R t u' /\ L τ l'.
  Proof.
    etrans.
  Qed.

  Lemma ssim_step_l_inv {F D Y L} :
    forall (t : ctree E C X) (u : ctree F D Y),
    Step t (≲L) u ->
    exists l' u', trans l' u u' /\ t (≲L) u' /\ L τ l'.
  Proof.
    intros. step in H. etrans.
  Qed.

  Lemma ssbt_brS_inv {F D Y} {L: rel (label E) (label F)} {R : Chain (@ss E F C D X Y L)}
        n m (cn: C n) (cm: D m) (k1 : n -> ctree E C X) (k2 : m -> ctree F D Y) :
    ss L (elem R) (BrS cn k1) (BrS cm k2) ->
    (forall i1, exists i2, elem R (k1 i1) (k2 i2)).
  Proof.
    intros EQ i1.
    edestruct EQ as (l & t & TR & REL & HL); etrans.
    inv_trans. subst. eauto.
  Qed.

  Lemma ssim_brS_inv {F D Y} {L: rel (label E) (label F)}
        n m (cn: C n) (cm: D m) (k1 : n -> ctree E C X) (k2 : m -> ctree F D Y) :
    ssim L (BrS cn k1) (BrS cm k2) ->
    (forall i1, exists i2, ssim L (k1 i1) (k2 i2)).
  Proof.
    intros EQ i1.
    eplay.
    subst; inv_trans.
    eexists; eauto.
  Qed.

  Lemma ss_brS_l_inv {F D Y Z L R} :
    forall (c : C Z) (k : Z -> ctree E C X) (u : ctree F D Y) x,
    ss L R (BrS c k) u ->
    exists l' u', trans l' u u' /\ R (k x) u' /\ L τ l'.
  Proof.
    intros. apply H; etrans.
  Qed.

  Lemma ssim_brS_l_inv {F D Y Z L} :
    forall (c : C Z) (k : Z -> ctree E C X) (u : ctree F D Y) x,
    ssim L (BrS c k) u ->
    exists l' u', trans l' u u' /\ ssim L (k x) u' /\ L τ l'.
  Proof.
    intros. step in H.
    now simple apply ss_brS_l_inv with (x := x) in H.
  Qed.

  Lemma ss_br_l_inv {F D Y} {L: rel (label E) (label F)}
        n (c: C n) (t : ctree F D Y) (k : n -> ctree E C X) R:
    ss L R (Br c k) t ->
    forall x, ss L R (k x) t.
  Proof.
    cbn. intros.
    eapply trans_br in H0; [| reflexivity].
    apply H in H0 as (? & ? & ? & ? & ?); subst.
    eauto.
  Qed.

  Lemma ssim_br_l_inv {F D Y} {L: rel (label E) (label F)}
        n (c: C n) (t : ctree F D Y) (k : n -> ctree E C X):
    ssim L (Br c k) t ->
    forall x, ssim L (k x) t.
  Proof.
    intros. step. step in H. eapply ss_br_l_inv. apply H.
  Qed.

  Lemma ss_guard_l_inv {F D Y} {L: rel (label E) (label F)}
    (t : ctree E C X) (u : ctree F D Y) R:
    ss L R (Guard t) u ->
    ss L R t u.
  Proof.
    cbn. intros.
    eapply trans_guard in H0.
    apply H in H0 as (? & ? & ? & ? & ?); subst.
    eauto.
  Qed.

  Lemma ssim_guard_l_inv {F D Y} {L: rel (label E) (label F)}
    (t : ctree E C X) (u : ctree F D Y):
    ssim L (Guard t) u ->
    ssim L t u.
  Proof.
    intros. step. step in H. eapply ss_guard_l_inv. apply H.
  Qed.

  (* This one isn't very convenient... *)
  Lemma ssim_br_r_inv {F D Y} {L: rel (label E) (label F)}
        n (c: D n) (t : ctree E C X) (k : n -> ctree F D Y):
    ssim L t (Br c k) ->
    forall l t', trans l t t' ->
    exists l' x t'' , trans l' (k x) t'' /\ L l l' /\ (ssim L t' t'').
  Proof.
    cbn. intros. step in H. apply H in H0 as (? & ? & ? & ? & ?); subst. inv_trans.
    do 3 eexists; eauto.
  Qed.

End Proof_Rules.
