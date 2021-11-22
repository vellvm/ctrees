(* begin hide *)

From CTree Require Import
	Utils CTrees Equ Shallow. 

From RelationAlgebra Require Import
 monoid
 kat      (* kat == Kleene Algebra with Test, we don't use the tests part *)
 kat_tac  
 prop
 rel
 comparisons
 rewriting
 normalisation. 

 From Coinduction Require Import
	coinduction rel tactics.

Section Trans.

  Context {E : Type -> Type} {R : Type}.
	Notation S' := (ctree' E R).
	Notation S  := (ctree  E R).

	Variant label : Type := 
	| tau
	| obs {X : Type} (e : E X) (v : X).

	(* Transition relation over [ctree]s. It can either:
		- stop at a successor of a visible [choice] node, labelled [tau]
		- or stop at a successor of a [Vis] node, labelled by the event and branch taken
	*)
	Inductive trans_ : label -> hrel S' S' :=

  | StepChoice {n} (x : Fin.t n) k l t :
    		trans_ l (observe (k x)) t ->
    		trans_ l (ChoiceF false n k) t

  | Steptau {n} (x : Fin.t n) k t :
				k x ≅ t ->
    		trans_ tau (ChoiceF true n k) (observe t) 

  | Stepobs {X} (e : E X) k x t :
				k x ≅ t ->
    		trans_ (obs e x) (VisF e k) (observe t)
	.
	Hint Constructors trans_ : core.

	Definition trans l : hrel S S := 
		fun u v => trans_ l (observe u) (observe v).

	#[local] Instance trans_equ_aux1 l t : 
		Proper (going (equ eq) ==> flip impl) (trans_ l t).
	Proof.
		intros u u' equ; intros TR. 
		inv equ; rename H into equ.
		step in equ.
		revert u equ. 
		dependent induction TR; intros; subst; eauto.
		+ inv equ. 
			* rewrite H2; eapply (Steptau x); auto.
			* replace (VisF e k1) with (observe (Vis e k1)) by reflexivity.
			  eapply (Steptau x).
				rewrite H.
				rewrite (ctree_eta t), <- H2.
				step; constructor; intros; symmetry; auto.
			* replace (ChoiceF b n0 k1) with (observe (Choice b n0 k1)) by reflexivity.
			  eapply (Steptau x).
				rewrite H.
				rewrite (ctree_eta t), <- H2.
				step; constructor; intros; symmetry; auto.
		+ replace u with (observe (go u)) by reflexivity. 
			econstructor. 
			rewrite H; symmetry; step; auto.
	Qed.

	#[local] Instance trans_equ_aux2 l : 
		Proper (going (equ eq) ==> going (equ eq) ==> impl) (trans_ l).
	Proof.
		intros t t' eqt u u' equ TR.
		rewrite <- equ; clear u' equ.
		inv eqt; rename H into eqt.
		revert t' eqt.
		dependent induction TR; intros; auto.
		+ step in eqt; dependent induction eqt.
			apply (StepChoice x).
			apply IHTR.	
			rewrite REL; reflexivity.
	 	+ step in eqt; dependent induction eqt. 
			econstructor. 
			rewrite <- REL; eauto.	
	 	+ step in eqt; dependent induction eqt. 
			econstructor. 
			rewrite <- REL; eauto.	
	Qed.	

	#[global] Instance trans_equ_ l : 
		Proper (going (equ eq) ==> going (equ eq) ==> iff) (trans_ l).
	Proof.
		intros ? ? eqt ? ? equ; split; intros TR.
		- eapply trans_equ_aux2; eauto.
		- symmetry in equ; symmetry in eqt; eapply trans_equ_aux2; eauto.
	Qed.	

	#[global] Instance trans_equ l : 
		Proper (equ eq ==> equ eq ==> iff) (trans l).
	Proof.
		intros ? ? eqt ? ? equ; unfold trans. 
		rewrite eqt, equ; reflexivity.	
	Qed.	
		
	(* Extending [trans] with its reflexive closure, labelled [tau] *)
  Definition etrans l : hrel S S := 
		match l with 
		| tau => cup (trans tau) 1
		| _ => trans l 
		end.

	(* The transition over which the weak game is built: a sequence of 
	 	internal steps, a labelled step, and a new sequence of internal ones
	*)
	Definition wtrans l : hrel S S :=
		 (trans tau)^* ⋅ etrans l ⋅ (trans tau)^*.

	Lemma trans_etrans l: trans l ≦ etrans l.
	Proof. unfold etrans; case l; ka. Qed.
	Lemma etrans_wtrans l: etrans l ≦ wtrans l.
	Proof. unfold wtrans; ka. Qed.
	Lemma trans_wtrans l: trans l ≦ wtrans l.
	Proof. rewrite trans_etrans. apply etrans_wtrans. Qed.
 
	Lemma trans_etrans_ l: forall p p', trans l p p' -> etrans l p p'.
	Proof. apply trans_etrans. Qed.
	Lemma trans_wtrans_ l: forall p p', trans l p p' -> wtrans l p p'.
	Proof. apply trans_wtrans. Qed.
	Lemma etrans_wtrans_ l: forall p p', etrans l p p' -> wtrans l p p'.
	Proof. apply etrans_wtrans. Qed.

	(* Global Hint Resolve trans_etrans_ trans_wtrans_: ccs. *)
 
	Lemma enil p: etrans tau p p.
	Proof. now right. Qed.
	Lemma wnil p: wtrans tau p p.
	Proof. apply etrans_wtrans, enil. Qed.
	(* Global Hint Resolve enil wnil: ccs. *)
	
	Lemma wcons l: forall p p' p'', trans tau p p' -> wtrans l p' p'' -> wtrans l p p''.
	Proof.
		assert ((trans tau: hrel S S) ⋅ wtrans l ≦ wtrans l) as H
				by (unfold wtrans; ka).
		intros. apply H. eexists; eassumption.
	Qed.
	Lemma wsnoc l: forall p p' p'', wtrans l p p' -> trans tau p' p'' -> wtrans l p p''.
	Proof.
		assert (wtrans l ⋅ trans tau ≦ wtrans l) as H
				by (unfold wtrans; ka).
		intros. apply H. eexists; eassumption.
	Qed.
 
  Lemma wtrans_tau: wtrans tau ≡ (trans tau)^*.
  Proof. unfold wtrans, etrans. ka. Qed.
 
 	Global Instance PreOrder_wtrans_tau: PreOrder (wtrans tau).
 	Proof.
    split.
    intro. apply wtrans_tau. now apply (str_refl (trans tau)).
    intros ?????. apply wtrans_tau. apply (str_trans (trans tau)).
    eexists; apply wtrans_tau; eassumption.
  Qed.

	Lemma trans_Tau : forall l t t',
		trans l (Tau t) t' ->
		trans l t t'.
	Proof.
		intros * TR.
		red in TR |- *.
		cbn in TR.
		match goal with 
		| h: trans_ _ ?x ?y |- _ =>
			remember x as ox; remember y as oy
		end.
		revert t t' Heqox Heqoy.
		induction TR; intros; dependent induction Heqox; auto.
	Qed.	

	Lemma Tau_trans : forall l t t',
		trans l t t' ->
		trans l (Tau t) t'.
	Proof.
		intros * TR.
		constructor. 
		constructor.
		apply TR.
	Qed.	

	Lemma trans_ChoiceV : forall l t t',
		trans l (TauV t) t' ->
		t' ≅ t.
	Proof.
		intros * TR.
		red in TR; cbn in TR.
		dependent induction TR.
		rewrite H.
		rewrite (ctree_eta t'), (ctree_eta t0), x; reflexivity.
	Qed.
			
End Trans.

Section Bisim.

	Context {E : Type -> Type} {X : Type}.
	Notation S := (ctree E X).

	Section Strong.

  (** The function defining strong simulations *)
  Program Definition ss : mon (S -> S -> Prop) :=
    {| body R t u :=
        forall l t', trans l t t' -> exists2 u', trans l u u' & R t' u' 
    |}.
  Next Obligation. 
		edestruct H0; eauto.					
  Qed.

	(* Symmetrized version: the other direction of the simulation is obtained as
   	 fun R t u => ss (fun x y => R y x) u t
		i.e. fun R t u => ss (converse R) u t		
		i.e. fun R => converse (ss (converse R))
		i.e. comp converse (comp ss converse)
	*)
  Notation sb := (cap ss (comp converse (comp ss converse))).

  Definition sbisim := (gfp sb : hrel _ _).
  Notation "t ~ u" := (gfp sb t u) (at level 70).
  Notation st := (t sb).
  Notation sbt := (bt sb).
  (** notations  for easing readability in proofs by enhanced coinduction *)
  Notation "t [~] u" := (st  _ t u) (at level 79). 
  Notation "t {~} u" := (sbt _ t u) (at level 79).

  (** [eq] is a post-fixpoint, thus [const eq] is below [t] *)
  Lemma refl_st: const eq <= st.
  Proof.
 	 apply leq_t.
 	 split; intros; cbn in *; subst; eauto.
  Qed.

  (** converse is compatible *)
  Lemma converse_st: converse <= st.
  Proof.
		apply invol_t.
	Qed.

	(** so is squaring *)
  Lemma square_st: square <= st.
  Proof.
   apply Coinduction, by_Symmetry.        
	  (* We can use a symmetry argument:
		   - we have defined [sb] as [sb = ss /\ i ss i]
			 - so if f (square here) is symmetric in the sense that 
				 f i <= i f
			 - then it suffices to prove that [square sb <= ss square]
				 instead of [square sb <= sb square]  	
		*)
   - intros R x z [y xy yz]. now exists y. 
	 - rewrite cap_l at 1. 
   	 intros R x z [y xy yz] l x' xx'.
   	 destruct (xy _ _ xx') as [y' yy' x'y']. 
   	 destruct (yz _ _ yy') as [z' zz' y'z'].
   	 exists z'. assumption. 
		 apply (f_Tf sb).  (* TODO: set of tactics for the companion *)
		 eexists; eauto.
 Qed.

  (** thus bisimilarity and [t R] are always equivalence relations. *)
  Global Instance Equivalence_st R: Equivalence (st R).
  Proof. apply Equivalence_t. apply refl_st. apply square_st. apply converse_st. Qed.

  Corollary Equivalence_bisim: Equivalence sbisim.
  Proof. apply Equivalence_st. Qed.

	End Strong.

	Section Weak.

  (** the function defining weak simulations and similarity *)
  Program Definition ws: mon (rel S S) :=
    {| body R p q :=
        forall l p', trans l p p' -> exists2 q', wtrans l q q' & R p' q' |}.
  Next Obligation. destruct (H0 _ _ H1). eauto. Qed.

  (** the function defining one-sided expansion (only used later) *)
  Program Definition es: mon (rel S S) :=
    {| body R p q :=
         forall l p', trans l p p' -> exists2 q', etrans l q q' & R p' q' |}.
  Next Obligation. destruct (H0 _ _ H1). eauto. Qed.
 
  (** the symmetrised version, defining weak bisimulations and bisimilarity *)
  Notation wb := (cap ws (comp converse (comp ws converse))).

  Definition wbisim := (gfp wb: hrel _ _).
  Notation "p ≈ q" := (gfp wb p q) (at level 70).
  Notation wt := (coinduction.t wb).
  Notation wT := (coinduction.T wb).
  Notation wbt := (coinduction.bt wb).
  Notation wbT := (coinduction.bT wb).
  (** notations  for easing readability in proofs by enhanced coinduction *)
  Notation "x [≈] y" := (wt _ x y) (at level 80). 
  Notation "x {≈} y" := (wbt _ x y) (at level 80).

  Lemma s_e: ss <= es.
  Proof. intros R p q H l p' pp'. destruct (H _ _ pp'). eauto using trans_etrans_. Qed.
  Lemma e_w: es <= ws.
  Proof. intros R p q H l p' pp'. destruct (H _ _ pp'). eauto using etrans_wtrans_. Qed.
  Lemma s_w: ss <= ws.
  Proof. rewrite s_e. apply e_w. Qed.

  Corollary bisim_wbisim: sbisim <= wbisim.
  Proof.
		apply gfp_leq.
		apply cap_leq. apply s_w.
    intros R p q. apply (@s_w (R°) q p).
  Qed.

  (** [wt R] is always reflexive: it contains ~ *)
 	#[global] Instance Reflexive_wt R: Reflexive (wt R).
  Proof. intro. apply (gfp_t wb). now apply bisim_wbisim. Qed.

  (** converse is compatible *)
  Lemma converse_wt: converse <= wt.
  Proof. apply invol_t. Qed.

  (** thus [wt R] is always symmetric *)
  #[global] Instance Symmetric_wt R: Symmetric (wt R).
  Proof. intros ??. apply (ft_t converse_wt). Qed.
	 
	Lemma tau_wb : forall t,
		Tau t ≈ t.
	Proof.
		intros t; step; split.	
    - intros l t' H.
			apply trans_Tau in H.	
			exists t'.
			apply trans_wtrans; auto.	
			reflexivity.
    - intros l t' H. exists t'. 
			apply trans_wtrans. 
			apply Tau_trans; auto.	
			cbn; reflexivity.
	Qed.

	(*
 (** but squaring is not compatible and [t R] is not always transitive, 
     as soon as there is at least one channel name *)
 Lemma not_Transitive_wt Z: X -> E Z -> ~ forall R, Transitive (wt R).
 Proof.
   intros x e H.
   cut (Vis e (fun _ => Ret x) ≈ Ret x).
	 2:{

	 }
    intro E. apply (gfp_pfp wb) in E as [E _].
    destruct (E (out a) nil) as [?[?[n [k N] N']_]_]. auto with ccs.
    replace n with 0 in N'. inversion N'.
    clear N'. destruct k. assumption.
    destruct N as [? N' ?]. inversion N'.
   rewrite weak_tau. coinduction R CIH. split.
    intros l p' pp'. inverse_trans. exists 0; auto with ccs.
    rewrite (subrelation_gfp_t _ (weak_tau _)). assumption. 
    intros l q' qq'. inverse_trans. 
 Qed.
 
 Lemma not_square_wt: N -> ~ square <= wt.
 Proof.
   intros a H. elim (not_Transitive_wt a). intro R.
   intros ? y ???. apply (ft_t H). now exists y.
 Qed.


  (** so is squaring *)
  Lemma square_wt: square <= wt.
  Proof.
    apply leq_t.
    intros R x z [y [F B] [F' B']]. 
    split.  
    - cbn; intros. 
      edestruct F; eauto.
      edestruct F'; eauto. 
    - cbn; intros. 
      edestruct B'; eauto.
      edestruct B; eauto.
  Qed. 
*)

(* Strong bisimulation played over the weak game, to fix 

  (** The function defining weak bisimulations *)
  Program Definition wb' : mon (rel S S) :=
    {| body R t u :=
        (forall l t', wtrans l t t' -> exists2 u', wtrans l u u' & R t' u') /\
        (forall l u', wtrans l u u' -> exists2 t', wtrans l t t' & R t' u')
    |}.
  Next Obligation. 
		intros R1 R2 INCL t u [F B]; split; [intros l t' STEP | intros l u' STEP].
		- edestruct F; eauto.
			eexists; eauto; apply INCL; auto.
		- edestruct B; eauto.
			eexists; eauto; apply INCL; auto.
	Qed.

  Notation wbisim' := (gfp wb').
  Notation "t ≈' u" := (gfp wb' t u) (at level 70).
  Notation wt' := (t wb').
  Notation wbt' := (bt wb').
  (** notations  for easing readability in proofs by enhanced coinduction *)
  Notation "t [≈'] u" := (wt'  _ t u) (at level 79). 
  Notation "t {≈'} u" := (wbt' _ t u) (at level 79).

	Lemma trans_transs : forall l (t u : S),
		trans  l t u ->
		transs l t u.
	Proof.
	Admitted.
	Hint Resolve trans_transs : core.

 (** [eq] is a post-fixpoint, thus [const eq] is below [t] *)
  Lemma refl_wt': const eq <= wt'.
  Proof.
 	 apply leq_t.
 	 split; intros; cbn in *; subst; eauto.
	Qed.

  (** converse is compatible *)
  Lemma converse_wt': converse <= wt'.
  Proof.
	  apply leq_t.
	  intros R p q [F B]; split; intros * STEP.
		edestruct B; eauto.
		edestruct F; eauto.
	Qed.

(* 
 Lemma cnv_wt R: (wt R: hrel _ _)° ≡ wt R.
 Proof. apply RelationAlgebra.lattice.antisym; intros ???; now apply Symmetric_wt. Qed.
 Lemma cnv_wbisim: wbisim° ≡ wbisim.
 Proof. apply cnv_wt. Qed.
 
 (** by symmetry, similar results for left-to-right game *)
 Lemma wbisim_trans_front l: (trans l)° ⋅ wbisim ≦ wbisim ⋅ (wtrans l)°.
 Proof. cnv_switch. rewrite 2cnvdot, cnv_invol, cnv_wbisim. apply wbisim_trans_back. Qed.
 Lemma wbisim_etrans_front l: (etrans l)° ⋅ wbisim ≦ wbisim ⋅ (wtrans l)°.
 Proof. cnv_switch. rewrite 2cnvdot, cnv_invol, cnv_wbisim. apply wbisim_etrans_back. Qed.
 Lemma wbisim_wtrans_front l: (wtrans l)° ⋅ wbisim ≦ wbisim ⋅ (wtrans l)°.
 Proof. cnv_switch. rewrite 2cnvdot, cnv_invol, cnv_wbisim. apply wbisim_wtrans_back. Qed.

 (** explicit, non-algebraic version *)
 Lemma wbisim_wtrans_front_ p q l p': wtrans l p p' -> p ≈ q -> exists2 q', p' ≈ q' & wtrans l q q'.
 Proof. intros pp' pq. apply wbisim_wtrans_front. now exists p. Qed. *)


	Lemma wbisim_wtrans_front_ :
	forall [t u : S] [l : label] [t' : S],
	transs l t t' -> 
	t ≈' u -> 
	exists2 u' : S, t' ≈' u' & transs l u u'.
	Proof.
		intros * STEP eq.
		trans in eq; destruct eq as [F B].
		destruct STEP as (v2 & (v1 & s & s') & s'').	
		


	Lemma wbisim'_trans : forall (u v w : S),
		u ≈' v ->
		v ≈' w ->
		u ≈' w.
	Proof.
		coinduction R CIH; intros * eq1 eq2.
		split.
		- intros l u' STEP. 
			trans in eq1; destruct eq1 as [F1 B1].
			apply F1 in STEP as [v' STEP equv].
			destruct (wbisim_wtrans_front_ STEP eq2); eauto.

  Lemma square_wt': square <= wt'.
  Proof.
    apply leq_t.
    intros R x z [y [F B] [F' B']]. 
    split.  
    - cbn; intros. 
      edestruct F; eauto.
      edestruct F'; eauto. 
    - cbn; intros. 
      edestruct B'; eauto.
      edestruct B; eauto.
  Qed. 
*)

End Weak.
End Bisim.

