(*|
==============================
Equational Theory for [ctrees]
==============================

.. coq::none
|*)
From Coq Require Import
     Program
     Setoid
     Morphisms
     RelationClasses
     Psatz.

From Coinduction Require Import
	   coinduction rel tactics.

From RelationAlgebra Require Import
     monoid
     kat
     kat_tac
     prop
     rel
     srel
     comparisons
     rewriting
     normalisation.

From CTree Require Import
	   Utils CTrees Shallow Trans Equ Bisim.

Obligation Tactic := idtac.

Import CTree.
Import CTreeNotations.
Open Scope ctree.

Import Fin.

(*|
Automation for bisimulation proofs
----------------------------------
/!\/!\/!\ WIP /!\/!\/!\

- [inv_trans_one] and [inv_trans] : systematic application of inversion rules for the [trans] relation in hypotheses
- [reach] : recursive search to build a simulation for computations whose internal branching is built using [TauI], [choiceI2], or [choiceI3]. Should be used after [inv_trans].
- [steps] : split a bisimulation goal into one play of its simulations
|*)

Ltac steps := step; split; cbn; intros ? ? ?TR.

(* Ltac stepF H := *)
(*   match goal with *)
(*   | h : gfp wb _ _ |- _ => *)
(*       step in h; destruct h as [?F _]; cbn in F; *)
(*       edestruct F as [? ?TR ?BIS]; [now apply H | clear F] *)
(*   end. *)

(* Ltac stepB H := *)
(*   match goal with *)
(*   | h : gfp wb _ _ |- _ => *)
(*       step in h; destruct h as [_ ?B]; cbn in B; *)
(*       edestruct B as [? ?TR ?BIS]; [now apply H | clear B] *)
(*   end. *)

Ltac stepF H :=
  match goal with
  | h : @wbisim ?E ?X _ _ |- _ =>
      step in h; destruct h as [?F _]; cbn in F;
      edestruct F as [? ?TR ?BIS]; [now apply H | clear F; fold (@wbisim E X) in BIS]
  end.

Ltac stepB H :=
  match goal with
  | h : @wbisim ?E ?X _ _ |- _ =>
      step in h; destruct h as [_ ?B]; cbn in B;
      edestruct B as [? ?TR ?BIS]; [now apply H | clear B; fold (@wbisim E X) in BIS]
  end.

Ltac solve_abs :=
  match goal with
  | h : hrel_of (trans _) _ _ |- _ =>
      first [now inversion TR | idtac]
  end.

Ltac subs :=
  match goal with
    [ h : ?x ≅ _, h' : context[?x] |- _ ] =>
      rewrite h in h'; clear h
  end.

Lemma val_eq_inv : forall E R x y, @val E R x = val y -> x = y.
  intros * EQ.
  now dependent induction EQ.
Qed.

Ltac inv_trans_one :=
  match goal with
  (* Reduces trans to transR *)
  | h : hrel_of (trans _) _ _ |- _ => cbn in h; inv_trans_one

  (* Inverting visible choices *)
  (* choiceV2 *)
  | h : transR _ (choiceV2 _ _) _ |- _ =>
      first [now inv h |
      let x := fresh in
      apply trans_ChoiceV_inv in h as [x [?EQ _]];
      dependent destruction x;
      try subs]
  (* choiceV3 *)
  | h : transR tau (choiceV3 _ _ _) _ |- _ =>
      first [now inv h |
      apply trans_ChoiceV_inv in h as [[| ? [|]] [?EQ _]];
      try subs]
  (* other valid choiceV *)
  | h : transR tau (Choice true _ _) _ |- _ => idtac
  (* invalid choiceV *)
  | h : transR _   (Choice true _ _) _ |- _ => now inv h
  | h : transR _   (choiceV2 _ _) _    |- _ => now inv h
  | h : transR _   (choiceV3 _ _) _    |- _ => now inv h

  (* Inverting invisible choices *)
  (* TauI *)
  | h : transR _ (TauI _) _ |- _ =>
      apply trans_TauI_inv in h as h
  (* choiceI2 *)
  | h : transR _ (choiceI2 _ _) _ |- _ =>
      apply trans_ChoiceI_inv in h as [[|] h]
  (* choiceI3 *)
  | h : transR _ (choiceI3 _ _ _) _ |- _ =>
      apply trans_ChoiceI_inv in h as [[| ? [|]] h]

  (* Valid Ret transition *)
  | h : transR (val ?x) (Ret ?x) _ |- _ =>
      apply trans_ret_inv in h as [_ ?EQ]
  (* Invalid Ret transition 1 *)
  | h : transR (val ?x) (Ret ?y) _ |- _ =>
      let abs := fresh in
      apply trans_ret_inv in h as [abs _];
      apply val_eq_inv in abs; congruence
  (* Invalid Ret transition 2 *)
  | h : transR _ (Ret ?x) _ |- _ =>
      now inv h

  | h : transR _ stuckI _               |- _ =>
      exfalso; eapply stuckI_is_stuck; now apply h
  end.

Ltac old_inv_trans_one :=
  match goal with
  | h : transR _ ?t _ |- _ =>
      match t with
      | TauI _            => apply trans_TauI_inv in h as h
      | choiceI2 _ _      => apply trans_ChoiceI_inv in h as [[|] h]
      | choiceI3 _ _ _    => apply trans_ChoiceI_inv in h as [[| ? [|]] h]
      | ChoiceF false _ _ => idtac
      end; cbn in h
  | h : hrel_of (trans _) ?t _ |- _ => idtac
  end.

Ltac inv_trans := repeat inv_trans_one.

(* Ltac inv_trans_one' := *)
(*   match goal with *)
(*   | h : transR _ ?t _ |- _ => *)
(*       match t with *)
(*       | TauI _            => apply trans_TauI_inv in h as h *)
(*       | choiceI2 _ _      => apply trans_ChoiceI_inv in h as [[|] h] *)
(*       | choiceI3 _ _ _    => apply trans_ChoiceI_inv in h as [[| ? [|]] h] *)
(*       | choiceV2 _ _      => apply trans_ChoiceV_inv in h as [[|] h] *)
(*       | choiceV3 _ _ _    => apply trans_ChoiceV_inv in h as [[| ? [|]] h] *)
(*       | stuckI             => exfalso; eapply stuckI_is_stuck; now apply h *)
(*       | ChoiceF false _ _ => idtac *)
(*       end; cbn in h *)
(*   | h : hrel_of (trans _) ?t _ |- _ => idtac *)
(*   end. *)


Ltac reach_core :=
  lazymatch goal with
  | [|- transR _ (choiceI2 _ _) _] =>
      first [eapply (trans_ChoiceI F1); [ | reflexivity]; cbn; first [easy | reach_core] |
              eapply (trans_ChoiceI (FS F1)); [ | reflexivity]; cbn; first [easy | reach_core]]
  | [|- transR _ (choiceI3 _ _ _) _] =>
      first [eapply (trans_ChoiceI F1); [ | reflexivity]; cbn; first [easy | reach_core]      |
              eapply (trans_ChoiceI (FS F1)); [ | reflexivity]; cbn; first [easy | reach_core] |
              eapply (trans_ChoiceI (FS (FS F1))); [ | reflexivity]; cbn; first [easy | reach_core]]
  end.
Ltac reach := eexists; [| reflexivity]; first [eassumption | reach_core].

Ltac break :=
  repeat match goal with
         | h : _ \/ _  |- _ => destruct h
         | h : _ /\ _  |- _ => destruct h
         | h : exists x, _ |- _ => destruct h
         end.

Lemma trans_choiceV21 E R : forall (t u : ctree E R),
    trans tau (choiceV2 t u) t.
Proof.
  intros.
  unfold choiceV2.
  match goal with
    |- _ (trans tau) (ChoiceV 2 ?k) ?t => exact (trans_ChoiceV (k := k) F1)
  end.
Qed.

Lemma trans_choiceV22 {E R} : forall (t u : ctree E R),
    trans tau (choiceV2 t u) u.
Proof.
  intros.
  unfold choiceV2.
  match goal with
    |- _ (trans tau) (ChoiceV 2 ?k) ?t => exact (trans_ChoiceV (k := k) (FS F1))
  end.
Qed.

Lemma trans_choiceI21 :
  forall {E X} (t t' u : ctree E X) l,
    trans l t t' ->
    trans l (choiceI2 t u) t'.
Proof.
  intros * TR.
  eapply trans_ChoiceI with (x := Fin.F1); eauto.
Qed.

Lemma trans_choiceI22 :
  forall {E X} (t u u' : ctree E X) l,
    trans l u u' ->
    trans l (choiceI2 t u) u'.
Proof.
  intros * TR.
  eapply trans_ChoiceI with (x := Fin.FS Fin.F1); eauto.
Qed.

Lemma trans_choiceI31 :
  forall {E X} (t t' u v : ctree E X) l,
    trans l t t' ->
    trans l (choiceI3 t u v) t'.
Proof.
  intros * TR.
  eapply trans_ChoiceI with (x := Fin.F1); eauto.
Qed.

Lemma trans_choiceI32 :
  forall {E X} (t u u' v : ctree E X) l,
    trans l u u' ->
    trans l (choiceI3 t u v) u'.
Proof.
  intros * TR.
  eapply trans_ChoiceI with (x := Fin.FS Fin.F1); eauto.
Qed.

Lemma trans_choiceI33 :
  forall {E X} (t u v v' : ctree E X) l,
    trans l v v' ->
    trans l (choiceI3 t u v) v'.
Proof.
  intros * TR.
  eapply trans_ChoiceI with (x := Fin.FS (Fin.FS Fin.F1)); eauto.
Qed.

Lemma trans_choiceI41 :
  forall {E X} (t t' u v w : ctree E X) l,
    trans l t t' ->
    trans l (choiceI4 t u v w) t'.
Proof.
  intros * TR.
  eapply trans_ChoiceI with (x := Fin.F1); eauto.
Qed.

Lemma trans_choiceI42 :
  forall {E X} (t u u' v w : ctree E X) l,
    trans l u u' ->
    trans l (choiceI4 t u v w) u'.
Proof.
  intros * TR.
  eapply trans_ChoiceI with (x := Fin.FS Fin.F1); eauto.
Qed.

Lemma trans_choiceI43 :
  forall {E X} (t u v v' w : ctree E X) l,
    trans l v v' ->
    trans l (choiceI4 t u v w) v'.
Proof.
  intros * TR.
  eapply trans_ChoiceI with (x := Fin.FS (Fin.FS Fin.F1)); eauto.
Qed.

Lemma trans_choiceI44 :
  forall {E X} (t u v w w' : ctree E X) l,
    trans l w w' ->
    trans l (choiceI4 t u v w) w'.
Proof.
  intros * TR.
  eapply trans_ChoiceI with (x := Fin.FS (Fin.FS (Fin.FS Fin.F1))); eauto.
Qed.

Lemma wtrans_case {E X} (t u : ctree E X) l:
  wtrans l t u ->
    match l with
    | tau => (t ≅ u \/ exists v, trans tau t v /\ wtrans tau v u)
    | _   => (exists v, trans l t v /\ wtrans tau v u) \/
            (exists v, trans tau t v /\ wtrans l v u)
    end.
Proof.
  intros [t2 [t1 [n TR1] TR2] TR3].
  destruct n as [| n].
  - apply wtrans_tau in TR3.
    cbn in TR1; rewrite <- TR1 in TR2.
    destruct l; eauto.
    destruct TR2; eauto.
    cbn in H; rewrite <- H in TR3.
    apply wtrans_tau in TR3.
    destruct TR3 as [[| n] ?]; eauto.
    destruct H0 as [? ? ?]; right; eexists; split; eauto.
    apply wtrans_tau; exists n; auto.
  - destruct TR1 as [? ? ?].
    destruct l; right.
    all:eexists; split; eauto.
    all:exists t2; [exists t1|]; eauto.
    all:exists n; eauto.
Qed.

Ltac wcase :=
  match goal with
    [ h   : hrel_of (wtrans ?l) _ _,
      bis : wbisim _ _
      |- _] =>
      let EQ := fresh "EQ" in
      match l with
      | tau => apply wtrans_case in h as [EQ|(? & ?TR & ?WTR)];
              [rewrite <- EQ in bis; clear EQ |]
      | _   => apply wtrans_case in h as [(? & ?TR & ?WTR)|(? & ?TR & ?WTR)]
      end
  end.

Lemma wtrans_stuckI_inv {E R} :
  forall (t : ctree E R) l,
    wtrans l stuckI t ->
    match l with | tau => t ≅ stuckI | _ => False end.
Proof.
  intros * TR.
  apply wtrans_case in TR.
  destruct l; break; cbn in *; try now inv_trans_one.
  symmetry; auto.
Qed.

(* Ltac wcase := *)
(*   match goal with *)
(*     [ h   : hrel_of (wtrans ?l) _ _, *)
(*       bis : gfp wb _ _ *)
(*       |- _] => *)
(*       let EQ := fresh "EQ" in *)
(*       match l with *)
(*       | tau => apply wtrans_case in h as [EQ|(? & ?TR & ?WTR)]; *)
(*               [rewrite <- EQ in bis; clear EQ |] *)
(*       | _   => apply wtrans_case in h as [(? & ?TR & ?WTR)|(? & ?TR & ?WTR)] *)
(*       end *)
(*   end. *)

(*|
Up-to [equ eq] bisimulations
----------------------------
We have proved in the module [Bisim] that [sbisim] and [wbisim] are closed under [equ eq].
We prove here more generally that strong and weak bisimulation up-to [equ eq] are valid
reasoning principles.

Note: Should probably refactor things to prove this first and derive the particular case as
a consequence.
|*)

(*|
Definition of the enhancing function
|*)
Variant equ_clos_body {E X1 X2} (R : rel (ctree E X1) (ctree E X2)) : (rel (ctree E X1) (ctree E X2)) :=
  | Equ_clos : forall t t' u' u
                 (Equt : t ≅ t')
                 (HR : R t' u')
                 (Equu : u' ≅ u),
      equ_clos_body R t u.

Program Definition equ_clos {E X1 X2} : mon (rel (ctree E X1) (ctree E X2)) :=
  {| body := @equ_clos_body E X1 X2 |}.
Next Obligation.
  intros * ?? LE t u EQ; inv EQ.
  econstructor; eauto.
  apply LE; auto.
Qed.

(*|
Sufficient condition to prove compatibility only over the simulation
|*)
Lemma equ_clos_sym {E X} : compat converse (@equ_clos E X X).
Proof.
  intros R t u EQ; inv EQ.
  apply Equ_clos with u' t'; intuition.
Qed.

(*|
Strong bisimulation up-to [equ] is valid
|*)
Lemma equ_clos_st {E X} : @equ_clos E X X <= st.
Proof.
  apply Coinduction, by_Symmetry; [apply equ_clos_sym |].
  intros R t u EQ l t1 TR; inv EQ.
  destruct HR as [F _]; cbn in *.
  rewrite Equt in TR.
  apply F in TR.
  destruct TR as [? ? ?].
  eexists.
  rewrite <- Equu; eauto.
  apply (f_Tf sb).
  econstructor; intuition.
  auto.
Qed.

#[global] Instance equ_clos_sT_goal {E R} RR f :
  Proper (@equ E R R eq ==> equ eq ==> flip impl) (sT f RR).
Proof.
  cbn; intros ? ? eq1 ? ? eq2 H.
  apply (fT_T equ_clos_st); econstructor; [eauto | | symmetry; eauto]; assumption.
Qed.

#[global] Instance equ_clos_sT_ctx {E R} RR f :
  Proper (@equ E R R eq ==> equ eq ==> impl) (sT f RR).
Proof.
  cbn; intros ? ? eq1 ? ? eq2 H.
  apply (fT_T equ_clos_st); econstructor; [symmetry; eauto | | eauto]; assumption.
Qed.

#[global] Instance sbisim_clos_sT_goal {E R} RR f :
  Proper (@sbisim E R ==> sbisim ==> flip impl) (sT f RR).
Proof.
  cbn; intros ? ? eq1 ? ? eq2 H.
  rewrite eq1, eq2.
  auto.
Qed.

#[global] Instance sbisim_clos_sT_ctx {E R} RR f :
  Proper (@sbisim E R ==> sbisim ==> impl) (sT f RR).
Proof.
  cbn; intros ? ? eq1 ? ? eq2 H.
  rewrite <- eq1, <- eq2.
  auto.
Qed.

#[global] Instance equ_clos_eT_goal {E R} RR f :
  Proper (@equ E R R eq ==> equ eq ==> flip impl) (eT eq f RR).
Proof.
  cbn; intros ? ? eq1 ? ? eq2 H.
  rewrite eq1, eq2.
  auto.
Qed.

#[global] Instance equ_clos_eT_ctx {E R} RR f :
  Proper (@equ E R R eq ==> equ eq ==> impl) (eT eq f RR).
Proof.
  cbn; intros ? ? eq1 ? ? eq2 H.
  rewrite <- eq1, <- eq2.
  auto.
Qed.

(*|
Weak bisimulation up-to [equ] is valid
|*)
Lemma equ_clos_wt {E X} : @equ_clos E X X <= wt.
Proof.
  apply Coinduction, by_Symmetry; [apply equ_clos_sym |].
  intros R t u EQ l t1 TR; inv EQ.
  destruct HR as [F _]; cbn in *.
  rewrite Equt in TR.
  apply F in TR.
  destruct TR as [? ? ?].
  eexists.
  rewrite <- Equu; eauto.
  apply (f_Tf wb).
  econstructor; intuition.
  auto.
Qed.

(*|
We can therefore rewrite [equ] in the middle of bisimulation proofs
|*)
#[global] Instance equ_clos_st_proper_goal {E R} RR :
  Proper (@equ E R R eq ==> equ eq ==> flip impl) (st RR).
Proof.
  cbn; unfold Proper, respectful; intros.
  apply (ft_t equ_clos_st).
  econstructor; [eauto | | symmetry; eauto]; auto.
Qed.

#[global] Instance equ_clos_wt_proper_ctx {E R} RR :
  Proper (@equ E R R eq ==> equ eq ==> impl) (wt RR).
Proof.
  cbn; unfold Proper, respectful; intros.
  apply (ft_t equ_clos_wt).
  econstructor; [symmetry; eauto | | eauto]; auto.
Qed.

(*|
Up-to [bind] context bisimulations
----------------------------------
We have proved in the module [Equ] that up-to bind context is
a valid enhancement to prove [equ].
We now prove the same result, but for strong and weak bisimulation.
|*)

Section bind.

(*|
Specialization of [bind_ctx] to the [sbisim]-based closure we are
looking for, and the proof of validity of the principle.
|*)
   Section Sbisim_Bind_ctx.

    Context {E: Type -> Type} {X Y: Type}.

(*|
Specialization of [bind_ctx] to a function acting with [sbisim] on the bound value,
and with the argument (pointwise) on the continuation.
|*)
    Program Definition bind_ctx_sbisim : mon (rel (ctree E Y) (ctree E Y)) :=
      {|body := fun R => @bind_ctx E X X Y Y sbisim (pointwise eq R) |}.
    Next Obligation.
      intros ?? H. apply leq_bind_ctx. intros ?? H' ?? H''.
      apply in_bind_ctx. apply H'. intros t t' HS. apply H, H'', HS.
    Qed.

(*|
Sufficient condition to exploit symmetry
|*)
    Lemma bind_ctx_sbisim_sym: compat converse bind_ctx_sbisim.
    Proof.
      intro R. simpl. apply leq_bind_ctx. intros. apply in_bind_ctx.
      symmetry; auto.
      intros ? ? ->.
      apply H0; auto.
    Qed.

(*|
The resulting enhancing function gives a valid up-to technique
|*)
    Lemma bind_ctx_sbisim_t : bind_ctx_sbisim <= st.
    Proof.
      apply Coinduction, by_Symmetry.
      apply bind_ctx_sbisim_sym.
      intros R. apply (leq_bind_ctx _).
      intros t1 t2 tt k1 k2 kk.
      step in tt; destruct tt as (F & B); cbn in *.
      cbn in *; intros l u STEP.
      apply trans_bind_inv in STEP as [(H & t' & STEP & EQ) | (v & STEPres & STEP)]; cbn in *.
      - apply F in STEP as [u' STEP EQ'].
        eexists.
        apply trans_bind_l; eauto.
        apply (fT_T equ_clos_st).
        econstructor; [exact EQ | | reflexivity].
        apply (fTf_Tf sb).
        apply in_bind_ctx; auto.
        intros ? ? ->.
        apply (b_T sb).
        apply kk; auto.
      - apply F in STEPres as [u' STEPres EQ'].
        pose proof (trans_val_inv STEPres) as EQ.
        rewrite EQ in STEPres.
        specialize (kk v v eq_refl) as [Fk Bk].
        apply Fk in STEP as [u'' STEP EQ'']; cbn in *.
        eexists.
        eapply trans_bind_r; cbn in *; eauto.
        eapply (id_T sb); cbn; auto.
    Qed.

   End Sbisim_Bind_ctx.

   Section Wbisim_Bind_ctx.

    Context {E: Type -> Type} {X Y: Type}.

(*|
Specialization of [bind_ctx] to a function acting with [sbisim] on the bound value,
and with the argument (pointwise) on the continuation.
|*)
    Program Definition bind_ctx_wbisim :  mon (rel (ctree E Y) (ctree E Y)) :=
      {|body := fun R => @bind_ctx E X X Y Y wbisim (pointwise eq R) |}.
    Next Obligation.
      intros ???? H. apply leq_bind_ctx. intros ?? H' ?? H''.
      apply in_bind_ctx. apply H'. intros t t' HS. apply H0, H'', HS.
    Qed.

(*|
Sufficient condition to exploit symmetry
|*)
    Lemma bind_ctx_wbisim_sym: compat converse bind_ctx_wbisim.
    Proof.
      intro R. simpl. apply leq_bind_ctx. intros. apply in_bind_ctx.
      symmetry; auto.
      intros ? ? ->.
      apply H0; auto.
    Qed.

(*|
The resulting enhancing function gives a valid up-to technique
|*)
    Lemma bind_ctx_wbisim_t : bind_ctx_wbisim <= wt.
    Proof.
      apply Coinduction, by_Symmetry.
      apply bind_ctx_wbisim_sym.
      intros R. apply (leq_bind_ctx _).
      intros t1 t2 tt k1 k2 kk.
      step in tt; destruct tt as (F & B); cbn in *.
      cbn in *; intros l u STEP.
      apply trans_bind_inv in STEP as [(H & t' & STEP & EQ) | (v & STEPres & STEP)]; cbn in *.
      - apply F in STEP as [u' STEP EQ'].
        eexists.
        apply wtrans_bind_l; eauto.
        apply (fT_T equ_clos_wt).
        econstructor; [exact EQ | | reflexivity].
        apply (fTf_Tf wb).
        apply in_bind_ctx; auto.
        intros ? ? ->.
        apply (b_T wb).
        apply kk; auto.
      - clear B.
        (* Things are tricky, the bind inversion rule is messy *)
        specialize (kk v v eq_refl).
        destruct kk as [F' _].
        apply F  in STEPres as [x STEPres EQ].
        apply F' in STEP    as [u' STEP HR].
        pose proof (wtrans_val_inv' STEPres) as (? & wtr & ? & EQ').
        rewrite EQ' in STEPres.
        pose proof wtrans_bind_r _ STEPres STEP as [EQ'' | ?].
        + rewrite EQ'' in STEP.
          assert (l = tau) by admit.
          subst.
          exists (k2 v).
          admit.
          admit.
        + admit.

    Admitted.

  End Wbisim_Bind_ctx.

End bind.

(*|
Expliciting the reasoning rule provided by the up-to principles.
|*)
Lemma sbisim_clo_bind (E: Type -> Type) (X Y : Type) :
	forall (t1 t2 : ctree E X) (k1 k2 : X -> ctree E Y) RR,
		t1 ~ t2 ->
    (forall x, (st RR) (k1 x) (k2 x)) ->
    st RR (t1 >>= k1) (t2 >>= k2)
.
Proof.
  intros.
  apply (ft_t (@bind_ctx_sbisim_t E X Y)).
  apply in_bind_ctx; auto.
  intros ? ? <-; auto.
Qed.

Lemma wbisim_clo_bind (E: Type -> Type) (X Y : Type) :
	forall (t1 t2 : ctree E X) (k1 k2 : X -> ctree E Y) RR,
		t1 ≈ t2 ->
    (forall x, (wt RR) (k1 x) (k2 x)) ->
    wt RR (t1 >>= k1) (t2 >>= k2)
.
Proof.
  intros.
  apply (ft_t (@bind_ctx_wbisim_t E X Y)).
  apply in_bind_ctx; auto.
  intros ? ? <-; auto.
Qed.

(*|
And in particular, we get the proper instance justifying rewriting [~]
and [≈] to the left of a [bind].
|*)
#[global] Instance bind_sbisim_cong :
 forall (E : Type -> Type) (X Y : Type) (R : rel Y Y) RR,
   Proper (sbisim ==> pointwise_relation X (st RR) ==> st RR) (@bind E X Y).
Proof.
  repeat red; intros; eapply sbisim_clo_bind; eauto.
Qed.

#[global] Instance bind_wbisim_cong :
 forall (E : Type -> Type) (X Y : Type) (R : rel Y Y) RR,
   Proper (wbisim ==> pointwise_relation X (wt RR) ==> wt RR) (@bind E X Y).
Proof.
  repeat red; intros; eapply wbisim_clo_bind; eauto.
Qed.

(** Inversion principles *)

Lemma sbisim_ret_ret_inv {E R} (r1 r2 : R) :
  (Ret r1 : ctree E R) ~ Ret r2 -> r1 = r2.
Proof.
  intro. step in H. destruct H as [Hf Hb]. cbn in *.
  edestruct Hf; [apply trans_ret |]. inv_trans.
Qed.

Lemma sbisim_ret_vis_inv {E R X} (r : R) (e : E X) k :
  Ret r ~ Vis e k -> False.
Proof.
  intro. step in H. destruct H as [Hf Hb]. cbn in *.
  edestruct Hf as [x Ht Hs]; [apply trans_ret |]. inv Ht.
Qed.

Lemma sbisim_ret_ChoiceV_inv {E R} (r : R) n (k : fin n -> ctree E R) :
  Ret r ~ ChoiceV n k -> False.
Proof.
  intro. step in H. destruct H as [Hf Hb]. cbn in *.
  edestruct Hf as [x Ht Hs]; [apply trans_ret |]. inv_trans.
Qed.

(** For the next few lemmas, we need to know that [X] is inhabited in order to
    take a step *)
Lemma sbisim_vis_vis_inv_type {E R X1 X2}
      (e1 : E X1) (e2 : E X2) (k1 : X1 -> ctree E R) (k2 : X2 -> ctree E R) (x : X1):
  Vis e1 k1 ~ Vis e2 k2 ->
  X1 = X2.
Proof.
  intros. step in H. destruct H as [Hf Hb]. cbn in *.
  edestruct Hf as [t Ht Hs]; [apply (@trans_vis _ _ _ _ x _) |].
  inv Ht. reflexivity.
Qed.

Lemma sbisim_vis_vis_inv {E R X} (e1 e2 : E X) (k1 k2 : X -> ctree E R) (x : X) :
  Vis e1 k1 ~ Vis e2 k2 ->
  e1 = e2 /\ forall x, k1 x ~ k2 x.
Proof.
  intros. step in H. destruct H as [Hf Hb]. cbn in *. split.
  - edestruct Hb as [t Ht Hs]; [apply (@trans_vis _ _ _ _ x _) |].
    inv Ht. apply inj_pair2 in H1, H2, H3, H4. subst. reflexivity.
  - intros x'. edestruct Hb as [t Ht Hs]; [apply (@trans_vis _ _ _ _ x' _) |].
    inv Ht. apply inj_pair2 in H1, H2, H3, H4. subst.
    rewrite H0. rewrite ctree_eta. rewrite H5. rewrite <- ctree_eta. auto.
Qed.

Lemma sbisim_vis_ChoiceV_inv {E R X}
      (e : E X) (k1 : X -> ctree E R) n (k2 : fin n -> ctree E R) (x : X) :
  Vis e k1 ~ ChoiceV n k2 -> False.
Proof.
  intro. step in H. destruct H as [Hf Hb]. cbn in *.
  edestruct Hf as [x' Ht Hs]; [apply (@trans_vis _ _ _ _ x _) |]. inv_trans.
Qed.

Lemma sbisim_ChoiceV_ChoiceV_inv {E R}
      n1 n2 (k1 : fin n1 -> ctree E R) (k2 : fin n2 -> ctree E R) :
  ChoiceV n1 k1 ~ ChoiceV n2 k2 ->
  (forall i1, exists i2, k1 i1 ~ k2 i2).
Proof.
  intros H i1.
  step in H. destruct H as [Hf Hb]. cbn in *.
  edestruct Hf as [x' Ht Hs]; [apply (@trans_ChoiceV _ _ n1 _ i1) |].
  apply trans_ChoiceV_inv in Ht. destruct Ht as [i2 [Heq _]].
  exists i2. rewrite <- Heq. assumption.
Qed.

Lemma sbisim_ret_ChoiceI_inv {E R} (r : R) n (k : fin n -> ctree E R) :
  Ret r ~ ChoiceI n k ->
  exists i, Ret r ~ k i.
Proof.
  intro. step in H. destruct H as [Hf Hb]. cbn in *.
  edestruct Hf as [x Ht Hs]; [apply trans_ret |].
  apply trans_ChoiceI_inv in Ht.
  destruct Ht as [i Ht]. exists i.
  step. split.
  - repeat intro. inv H. exists x; auto. rewrite <- Hs.
    rewrite ctree_eta. rewrite <- H3. rewrite choiceI0_always_stuck. auto.
  - repeat intro. eapply trans_ChoiceI in H; eauto. specialize (Hb _ _ H).
    destruct Hb. inv H0. exists stuckI. constructor.
    cbn. rewrite <- H1. symmetry. rewrite ctree_eta .
    rewrite <- H5. rewrite choiceI0_always_stuck. auto.
Qed.

Lemma sbisim_ChoiceI_1_inv {E R} (k : fin 1 -> ctree E R) t x :
  ChoiceI 1 k ~ t ->
  k x ~ t.
Proof.
  intro. step in H. step. destruct H. cbn in *. split; repeat intro.
  - apply H. econstructor; apply H1.
  - edestruct H0. apply H1. exists x0; auto.
    inv H2. apply inj_pair2 in H7. subst.
    assert (x = x1).
    {
      clear H H0 H1 H3 H8 l t' x0 t k E R.
      remember 1%nat.
      destruct x.
      - dependent destruction x1; auto.
        inv Heqn. inv x1.
      - inv Heqn. inv x.
    }
    subst. auto.
Qed.


(*|
Sanity checks
=============
- invisible n-ary spins are strongly bisimilar
- non-empty visible n-ary spins are strongly bisimilar
- Binary invisible choice is:
  + associative
  + commutative
  + merges into a ternary invisible choice
  + admits any stuckI computation as a unit
|*)

(*|
Note that with visible schedules, nary-spins are equivalent only
if neither are empty, or if both are empty: they match each other's
tau challenge infinitely often.
With invisible schedules, they are always equivalent: neither of them
produce any challenge for the other.
|*)
Lemma spinV_nary_n_m : forall {E R} n m, n>0 -> m>0 -> @spinV_nary E R n ~ spinV_nary m.
Proof.
  intros E R.
  unfold sbisim; coinduction S CIH; symmetric.
  intros * ? ? l p' TR.
  destruct m as [|m]; [lia |].
  rewrite ctree_eta in TR; cbn in TR.
  apply trans_ChoiceV_inv in TR as (_ & EQ & ->).
  eexists.
  rewrite ctree_eta; cbn.
  econstructor. exact Fin.F1.
  reflexivity.
  rewrite EQ; eauto.
Qed.

Lemma spinV_nary_0 : forall {E R}, @spinV_nary E R 0 ≈ spinV_nary 0.
Proof.
  intros E R.
  reflexivity.
Qed.

Lemma spinI_nary_n_m : forall {E R} n m, @spinI_nary E R n ~ spinI_nary m.
Proof.
  intros E R.
  coinduction S _; symmetric.
  cbn; intros * TR.
  exfalso; eapply spinI_nary_is_stuck, TR.
Qed.

(*|
Note: with choiceI2, these relations hold up-to strong bisimulation.
With choiceV2 however they don't even hold up-to weak bisimulation.
|*)
Lemma choiceI2_assoc {E X} : forall (t u v : ctree E X),
	  choiceI2 (choiceI2 t u) v ~ choiceI2 t (choiceI2 u v).
Proof.
  intros.
  steps; inv_trans; reach.
Qed.

Lemma choiceI2_commut {E X} : forall (t u : ctree E X),
	  choiceI2 t u ~ choiceI2 u t.
Proof.
(*|
Note: could use a symmetry argument here as follows to only play one direction of the game.
[coinduction ? _; symmetric.]
but automation just handles it...
|*)
  intros.
  steps; inv_trans; reach.
Qed.

(*|
ChoiceI is idempotent
|*)
Lemma choiceI2_idem {E X} : forall (t : ctree E X),
	  choiceI2 t t ~ t.
Proof.
  intros.
  steps; inv_trans; reach.
Qed.

Lemma choiceI2_merge {E X} : forall (t u v : ctree E X),
	  choiceI2 (choiceI2 t u) v ~ choiceI3 t u v.
Proof.
  intros.
  steps; inv_trans; reach.
Qed.

Lemma choiceI2_is_stuck {E X} : forall (u v : ctree E X),
    is_stuck u ->
	  choiceI2 u v ~ v.
Proof.
  intros * ST.
  steps.
  - inv_trans.
    exfalso; eapply ST, TR. (* automate stuck transition trying to step? *)
    exists t'; auto.             (* automate trivial case *)
  - reach.
Qed.

Lemma choiceI2_stuckV_l {E X} : forall (t : ctree E X),
	  choiceI2 stuckV t ~ t.
Proof.
  intros; apply choiceI2_is_stuck, stuckV_is_stuck.
Qed.

Lemma choiceI2_stuckI_l {E X} : forall (t : ctree E X),
	  choiceI2 stuckI t ~ t.
Proof.
  intros; apply choiceI2_is_stuck, stuckI_is_stuck.
Qed.

Lemma choiceI2_stuckV_r {E X} : forall (t : ctree E X),
	  choiceI2 t stuckV ~ t.
Proof.
  intros; rewrite choiceI2_commut; apply choiceI2_stuckV_l.
Qed.

Lemma choiceI2_stuckI_r {E X} : forall (t : ctree E X),
	  choiceI2 t stuckI ~ t.
Proof.
  intros; rewrite choiceI2_commut; apply choiceI2_stuckI_l.
Qed.

Lemma choiceI2_spinI_l {E X} : forall (t : ctree E X),
	  choiceI2 spinI t ~ t.
Proof.
  intros; apply choiceI2_is_stuck, spinI_is_stuck.
Qed.

Lemma choiceI2_spinI_r {E X} : forall (t : ctree E X),
	  choiceI2 t spinI ~ t.
Proof.
  intros; rewrite choiceI2_commut; apply choiceI2_is_stuck, spinI_is_stuck.
Qed.

Lemma wbisim_ret_inv {E R} : forall (x y : R),
    Ret x ≈ (Ret y : ctree E R) ->
    x = y.
Proof.
  intros * EQ.
  step in EQ; destruct EQ as [F B].
  cbn in *.
  edestruct (F (val x)); [apply trans_ret |].
  apply wtrans_case in H as [(?v & TR & WTR)|(?v & TR & WTR)].
  apply trans_ret_inv in TR; break.
  apply val_eq_inv in H; congruence.
  apply trans_ret_inv in TR; break; inv H.
Qed.

(* TODO: maximally inserted arguments are bad to pass by arguments to tactics *)
Arguments trans_choiceV21 [_ _].
Arguments trans_choiceV22 [_ _].
Arguments trans_ret [_ _] _.



(*|
With choiceV2 however they don't even hold up-to weak bisimulation.
The proof is not interesting, but it would be good to have a
light way to automate it, so it's a decent case study.
|*)
Lemma choiceV2_not_assoc :
	~ (choiceV2 (choiceV2 (Ret 0 : ctree Sum.void1 nat) (Ret 1)) (Ret 2) ≈ choiceV2 (Ret 0) (choiceV2 (Ret 1) (Ret 2)))%nat.
Proof.
  intros abs.

  (* init: 012 || 012 *)
  stepF trans_choiceV21.

  (* PL  : 01  || 012 *)
  wcase.
  - (* AR:  01  || 012 *)
    stepB trans_choiceV22.
    (* PR:  01  ||  12 *)
    wcase.
    + (* AL:  01  ||  12 *)
      stepB trans_choiceV22.
      (* PR:  01  ||   2 *)
      wcase.
      * (* AL: 01  ||   2 *)
        stepB trans_ret.
        (* PR: 01  |2?|   ∅ *)
        wcase.
        (* AL: steps with 2, abs *)
        inv_trans_one.
        inv_trans_one.
        (* PR: 0   ||   ∅ *)
        wcase; inv_trans_one.
        (* PR: 1   ||   ∅ *)
        wcase; inv_trans_one.
      * inv_trans_one.
        (* AL: 0  ||   2 *)
        wcase.
        apply wbisim_ret_inv in BIS; inv BIS.
        inv_trans_one.
        (* AL: 1  ||   2 *)
        wcase.
        apply wbisim_ret_inv in BIS; inv BIS.
        inv_trans_one.
    + inv_trans_one.
      * (* AL:  0  ||  12 *)
        wcase.
        stepF trans_ret.
        wcase; inv_trans_one.
        wcase; inv_trans_one.
        wcase; inv_trans_one.
        inv_trans_one.
      * (* AL:  1  ||  12 *)
        wcase.
        stepB trans_choiceV22.
        wcase.
        apply wbisim_ret_inv in BIS; inv BIS.
        inv_trans_one.
        inv_trans_one.
  - inv_trans_one.
    + wcase.
      * stepF trans_choiceV22.
        wcase.
        apply wbisim_ret_inv in BIS; inv BIS.
        inv_trans_one.
      * inv_trans_one.
    + wcase.
      stepF trans_choiceV21.
      wcase.
      stepF trans_ret.
      wcase.
      inv_trans_one.
      inv_trans_one.
      wcase; inv_trans_one.
      wcase; inv_trans_one.
      inv_trans_one.
      wcase.
      apply wbisim_ret_inv in BIS; inv BIS.
      inv_trans_one.
      wcase.
      apply wbisim_ret_inv in BIS; inv BIS.
      inv_trans_one.
      inv_trans_one.
      wcase.
      stepF trans_choiceV21.
      wcase.
      apply wbisim_ret_inv in BIS; inv BIS.
      inv_trans_one.
      inv_trans_one.
      wcase.
      stepF trans_choiceV21.
      wcase.
      apply wbisim_ret_inv in BIS; inv BIS.
      inv_trans_one.
      inv_trans_one.
Qed.

Lemma map_map {E R S T}: forall (f : R -> S) (g : S -> T) (t : ctree E R),
    map g (map f t) ≅ map (fun x => g (f x)) t.
Proof.
  unfold map. intros. rewrite bind_bind. setoid_rewrite bind_ret_l. reflexivity.
Qed.

Lemma bind_map {E R S T}: forall (f : R -> S) (k: S -> ctree E T) (t : ctree E R),
    bind (map f t) k ≅ bind t (fun x => k (f x)).
Proof.
  unfold map. intros. rewrite bind_bind. setoid_rewrite bind_ret_l. reflexivity.
Qed.

Lemma map_bind {E X Y Z} (t: ctree E X) (k: X -> ctree E Y) (f: Y -> Z) :
  (map f (bind t k)) ≅ bind t (fun x => map f (k x)).
Proof.
  intros. unfold map. apply bind_bind.
Qed.

Lemma map_ret {E A B} (f : A -> B) (a : A) :
    @map E _ _ f (Ret a) ≅ Ret (f a).
Proof.
  intros. unfold map.
  rewrite bind_ret_l; reflexivity.
Qed.
