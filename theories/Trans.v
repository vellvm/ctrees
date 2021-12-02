(* begin hide *)
 From Coinduction Require Import
	coinduction rel tactics.

From CTree Require Import 
	Utils CTrees Shallow Equ.  

From RelationAlgebra Require Import 
 monoid
 kat      (* kat == Kleene Algebra with Test, we don't use the tests part *)
 kat_tac   
 prop
 rel
 srel
 comparisons
 rewriting
 normalisation. 

(* end hide *)


Section Trans.

  Context {E : Type -> Type} {R : Type}.

	Notation S' := (ctree' E R).
	Notation S  := (ctree  E R).

	Definition SS : EqType := 
		{| type_of := S ; Eq := equ eq |}. 

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

	Definition transR l : hrel S S := 
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
		Proper (equ eq ==> equ eq ==> iff) (transR l).
	Proof.
		intros ? ? eqt ? ? equ; unfold transR. 
		rewrite eqt, equ; reflexivity.	
	Qed.	

	Definition trans l : srel SS SS := {| hrel_of := transR l : hrel SS SS |}.

	(* Extending [trans] with its reflexive closure, labelled [tau] *)
  Definition etrans (l : label) : srel SS SS := 
	match l with 
		| tau => (lattice.cup (trans l) 1)
	  | _ => trans l 
	end.

	(* The transition over which the weak game is built: a sequence of 
	 	internal steps, a labelled step, and a new sequence of internal ones
	*)
	Definition wtrans l : srel SS SS :=
		 (trans tau)^* ⋅ etrans l ⋅ (trans tau)^*.

	Lemma trans_etrans l: trans l ≦ etrans l.
	Proof. 
		unfold etrans; case l; ka. 
	Qed.
	Lemma etrans_wtrans l: etrans l ≦ wtrans l.
	Proof. 
		unfold wtrans; ka. 
	Qed.
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
	Proof. cbn. now right. Qed.
	Lemma wnil p: wtrans tau p p.
	Proof. apply etrans_wtrans, enil. Qed.
	(* Global Hint Resolve enil wnil: ccs. *)
	
	Lemma wcons l: forall p p' p'', trans tau p p' -> wtrans l p' p'' -> wtrans l p p''.
	Proof.
		assert ((trans tau: srel SS SS) ⋅ wtrans l ≦ wtrans l) as H
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
  Proof. 
 	 unfold wtrans, etrans. ka.
	Qed.
		
 	Global Instance PreOrder_wtrans_tau: PreOrder (wtrans tau).
 	Proof.
    split.
    intro. apply wtrans_tau. 
		now (apply (str_refl (trans tau)); cbn).
    intros ?????. apply wtrans_tau. apply (str_trans (trans tau)).
    eexists; apply wtrans_tau; eassumption.
  Qed.

	Lemma trans_TauI : forall l t t',
		trans l (TauI t) t' ->
		trans l t t'.
	Proof.
		intros * TR.
		cbn in *.
		red in TR |- *.
		cbn in TR |- *.
		match goal with 
		| h: trans_ _ ?x ?y |- _ =>
			remember x as ox; remember y as oy
		end.
		revert t t' Heqox Heqoy.
		induction TR; intros; dependent induction Heqox; cbn in *; auto.
	Qed.	

	Lemma TauI_trans : forall l t t',
		trans l t t' ->
		trans l (TauI t) t'.
	Proof.
		intros * TR.
		constructor. 
		constructor.
		apply TR.
	Qed.	

	Lemma TauV_trans : forall l t t',
		trans l (TauV t) t' ->
		t' ≅ t /\ l = tau.
	Proof.
		intros * TR.
		cbn in *; red in TR; cbn in TR.
		dependent induction TR.
		rewrite H.
		split; auto.
		rewrite (ctree_eta t'), (ctree_eta t0), x; reflexivity.
	Qed.

	Ltac ttaun n := apply (@Steptau n). 
	Ltac ttau := ttaun 1%nat; [exact Fin.F1 |].

	Lemma trans_TauV : forall t,
		trans tau (TauV t) t.
	Proof.
		intros.
		ttau.
		reflexivity.
	Qed.
	
	Lemma wtrans_TauV : forall l t t',
		wtrans l t t' ->
		wtrans l (TauV t) t'.
	Proof.
		intros * TR.
		eapply wcons; eauto.
		apply trans_TauV.
	Qed.

	Lemma trans_ret : forall x l t, 
		~ (trans l (Ret x) t).
	Proof.
		intros * abs.
		inv abs.
	Qed.

	Lemma etrans_ret : forall x l t, 
		etrans l (Ret x) t ->
		l = tau /\ t ≅ Ret x.
	Proof.
		intros ? [] ? step; cbn in step; (now inv step || intuition).
	Qed.

	Lemma trans_tau_str_ret : forall x t, 
		(trans tau)^* (Ret x) t ->
		t ≅ Ret x.
	Proof.
		intros * [[|] step].
		- cbn in *; symmetry; eauto.
		- destruct step.
			exfalso; eapply trans_ret; eauto.
	Qed.

	Lemma wtrans_ret : forall x l t, 
		wtrans l (Ret x) t ->
		l = tau /\ t ≅ Ret x.
	Proof.
		intros * step.
		destruct step as [? [? step1 step2] step3]. 
		apply trans_tau_str_ret in step1.
		rewrite step1 in step2; clear step1.
		apply etrans_ret in step2 as [-> EQ].
		rewrite EQ in step3.
		apply trans_tau_str_ret in step3; auto.
	Qed.

End Trans.

