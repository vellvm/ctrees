(*|
Denotation of [ccs] into [ctree]s
|*)

From Coq Require Export
  List
  Strings.String.

From ITree Require Import ITree.

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

From CTreeCCS Require Import
	Syntax.

From Coinduction Require Import
	coinduction rel tactics.

From CTree Require Import
	Utils
	CTrees
  Trans
 	Interp
	Equ
	Bisim
  CTreesTheory.

(* Import CTree. *)

Import CTreeNotations.
Open Scope term_scope.

Set Implicit Arguments.
Set Contextual Implicit.

(*|
Event signature

Processes can perform actions, synchronizations, or be unresponsive
|*)

Variant ActionE : Type -> Type :=
	| Act (a : action) : ActionE unit.
Variant SynchE : Type -> Type :=
  Tau : SynchE unit.
(* Variant DeadE : Type -> Type := *)
(* 	| throw : DeadE void. *)

(* Definition dead {A : Type} {E} `{DeadE -< E} : ctree E A := *)
(* 	x <- trigger throw;; match x: void with end. *)

(* Definition ccsE : Type -> Type := ((* SynchE +' *) ActionE +' DeadE). *)
Definition ccsE : Type -> Type := (SynchE +' ActionE).

Definition ccsT' T := ctree' ccsE T.
Definition ccsT  := ctree ccsE.

Definition ccs' := ccsT' unit.
Definition ccs := ccsT unit.

(*| Process algebra |*)
Section Combinators.

	Definition nil : ccs := CTree.stuckI.

	Definition prefix (a : action) (P: ccs) : ccs := trigger (Act a);; P.

	Definition plus (P Q : ccs) : ccs := choiceI2 P Q.

  Definition h_trigger {E F} `{E -< F} : E ~> ctree F :=
    fun _ e => trigger e.

  Definition h_restrict_ (c : chan) : ActionE ~> ctree ccsE :=
    fun _ e => let '(Act a) := e in
            match a with
            | Send c'
            | Rcv c' =>
              if (c =? c')%string then CTree.stuckI else trigger e
            end.

	Definition case_ctree {E F G} (f : E ~> ctree G) (g : F ~> ctree G)
		: E +' F ~> ctree G :=
		fun T ab => match ab with
		| inl1 a => f _ a
		| inr1 b => g _ b
		end.

  (* TODO: define basically the theory of handlers for ctrees, all the constructions are specialized to ccs right now *)

  Definition h_restrict c : ccsE ~> ctree ccsE :=
    case_ctree h_trigger (h_restrict_ c).
    (* case_ctree h_trigger (case_ctree (h_restrict_ c) h_trigger). *)

  Definition restrict {X} : chan -> ccsT X -> ccsT X :=
    fun c P => interp (h_restrict c) P.

	Variant head :=
	  | Hdone
	  | Hact (a : option action) (P : ccs).

  Notation "'tauP' e" := (inl1 e) (at level 10).
  Notation "'actP' e" := (inr1 e) (at level 10).
(*|
In order to compose in parallel processes, we need to compute for each process
the set of possibly next communication they would perform.
Doing so corresponds to crawling the tree through invisible schedules until a
communication node is reached. We then wrap the whole subtree into a returned
value. We also wrap stuck computations into a returned value in order to
be able to bind the head tree in the parallel composition without creating a
stuck computation.
We have for our purpose some invariants on the trees:
- They do not contain [Ret] nodes, they are concluded by stuck ones
- They do not contain visible choices
- They do not contain invisible choices of arity > 3
We currently return stuck computations in these cases.
|*)

  Definition get_hd : ccs -> ccsT head :=
    cofix get_hd (t : ccs) :=
      match observe t with
      | RetF x            =>
          CTree.stuckI
      | VisF (tauP e) k   =>
          match e,k with
          | Tau,k => Ret (Hact None (k tt))
          end
      | VisF (actP e) k   =>
          match e, k with
          | Act a, k => Ret (Hact (Some a) (k tt))
          end
      | ChoiceF true n k  => CTree.stuckI
      | ChoiceF false n k =>
          if Nat.eqb n 0
          then Ret Hdone
          else Choice false n (fun i => get_hd (k i))
      end.

  Definition can_synch (a b : option action) : bool :=
		match a, b with | Some a, Some b => are_opposite a b | _, _ => false end.
  Definition reemit (a : option action) : ccsE unit :=
		match a with
    | Some a => inr1 (Act a)
    | None => inl1 Tau
    end.

  Definition para : ccs -> ccs -> ccs :=
    cofix F (P : ccs) (Q : ccs) :=

      (* We construct the "heads" of both computations to get all reachable events *)
			rP <- get_hd P;;
			rQ <- get_hd Q;;

      (* We then proceed by case analysis on these events *)
			match rP, rQ with

      (* Things are straightforward if all or part of the computations are over *)
			| Hdone, Hdone => nil   (* Both computations ended *)
			| Hdone, _ => Q         (* Both computations ended *)
			| _, Hdone => P

      (* If two actions happen, we distinguish two cases *)
			| Hact a P', Hact b Q' =>
          if can_synch a b then
            (* A communication could happen, we have hence three non-deterministic possibilities *)
            choiceI3 (trigger Tau    ;; F P' Q')
                     (trigger (reemit a);; F P' Q )
                     (trigger (reemit b);; F P  Q')
					else
            (* Incompatible communications, only two possibilities *)
            choiceI2 (trigger (reemit a);; F P' Q)
                     (trigger (reemit b);; F P Q')
      end.

(*
				-------------------------------------------------
				!(a.P || bara.Q) -τ> (P || Q) || !(a.P || bara.Q)

					Question: is !P ≈ P || !P?
  Definition bang : ccs -> ccs.
*)

End Combinators.

Notation para_ P Q :=
	(rP <- get_hd P;;
	 rQ <- get_hd Q;;
	 match rP, rQ with
	 | Hdone, Hdone => nil
	 | Hdone, _ => Q
	 | _, Hdone => P
	 | Hact a P', Hact b Q' =>
       if can_synch a b then
         choiceI3 (trigger Tau    ;; para P' Q')
                  (trigger (reemit a);; para P' Q )
                  (trigger (reemit b);; para P  Q')
			 else
         (* Incompatible communications, only two possibilities *)
         choiceI2 (trigger (reemit a);; para P' Q)
                  (trigger (reemit b);; para P Q')
   end)%ctree.

Lemma unfold_para : forall P Q, para P Q ≅ para_ P Q.
Proof.
  intros.
	now step.
Qed.

Module CCSNotationsSem.

  Declare Scope ccs_scope.

  Notation "0" := nil: ccs_scope.
  Infix "+" := plus (at level 50, left associativity).
  Infix "∥" := para (at level 29, left associativity).

End CCSNotationsSem.

Import CCSNotationsSem.
Open Scope ccs_scope.

Lemma plsC: forall p q, p+q ~ q+p.
Proof.
  apply choiceI2_commut.
Qed.

Lemma plsA p q r: p+(q+r) ~ (p+q)+r.
Proof.
  symmetry; apply choiceI2_assoc.
Qed.

Lemma pls0p p: 0 + p ~ p.
Proof.
  apply choiceI2_stuckI_l.
Qed.

Lemma plsp0 p: p + 0 ~ p.
Proof. now rewrite plsC, pls0p. Qed.

Lemma plsidem p: p + p ~ p.
Proof.
  apply choiceI2_idem.
Qed.

Ltac eq2equ H :=
  match type of H with
  | ?u = ?t => let eq := fresh "EQ" in assert (eq : u ≅ t) by (subst; reflexivity); clear H
  end.

Notation "'tauP' e" := (inl1 e) (at level 10).
Notation "'actP' e" := (inr1 e) (at level 10).
Notation get_hd_ P :=
  match observe P with
  | RetF x            => CTree.stuckI
  | VisF (tauP e) k   =>
      match e,k with
      | Tau,k => Ret (Hact None (k tt))
      end
  | VisF (actP e) k   =>
      match e, k with
      | Act a, k => Ret (Hact (Some a) (k tt))
      end
  | ChoiceF true n k  => CTree.stuckI
  | ChoiceF false n k =>
      if Nat.eqb n 0
      then Ret Hdone
      else Choice false n (fun i => get_hd (k i))
  end.

Lemma unfold_get_hd : forall P,
    get_hd P ≅ get_hd_ P.
Proof.
  intros.
	now step.
Qed.


Lemma get_hd0 : get_hd 0 ≅ Ret Hdone.
Proof.
  now rewrite unfold_get_hd.
Qed.


Lemma trans_get_hd_inv : forall P l u,
    transR l (get_hd P) u ->
    is_val l.
Proof.
  intros * TR.
  red in TR.
  remember (get_hd P) as HP.
  eq2equ HeqHP.
  rewrite ctree_eta in EQ.
  revert P EQ.
  induction TR; intros; subst.
  - rewrite unfold_get_hd in EQ.
    desobs P.
    + step in EQ; apply equF_choice_invT in EQ as [-> _]; inv x.
    + destruct e as [e|e]; destruct e; step in EQ; inv EQ.
    + destruct vis.
      step in EQ; apply equF_choice_invT in EQ as [-> _]; inv x.
      destruct n0 as [|n0]; cbn in *.
      * step in EQ; inv EQ.
      * step in EQ; destruct (equF_choice_invT _ _ EQ) as [-> _].
        eapply equF_choice_invE in EQ.
        setoid_rewrite <- ctree_eta in IHTR.
        eapply IHTR; eauto.
  - exfalso.
    rewrite unfold_get_hd in EQ.
    desobs P.
    + step in EQ; apply equF_choice_invT in EQ as [-> _]; inv x.
    + destruct e as [e|e]; destruct e; step in EQ; inv EQ.
    + destruct vis.
      step in EQ; apply equF_choice_invT in EQ as [_ abs]; inv abs.
      destruct n0 as [|n0]; cbn in *.
      step in EQ; inv EQ.
      step in EQ; apply equF_choice_invT in EQ as [_ abs]; inv abs.
  - exfalso.
    rewrite unfold_get_hd in EQ.
    desobs P.
    + step in EQ; inv EQ.
    + destruct e0 as [e0|e0]; destruct e0; step in EQ; inv EQ.
    + destruct vis.
      step in EQ; inv EQ.
      destruct n as [|n]; cbn in *.
      step in EQ; inv EQ.
      step in EQ; inv EQ.
  - constructor.
Qed.

Lemma trans_get_hd_bind_inv : forall l P (k : _ -> ccs) u,
    transR l (get_hd P >>= k) u ->
    exists hd, transR (val hd) (get_hd P) CTree.stuckI /\ transR l (k hd) u.
Proof.
  intros * TR.
  edestruct @trans_bind_inv; [apply TR | | assumption].
  destruct H as (? & ? & ? & ?).
  apply trans_get_hd_inv in H0; contradiction.
Qed.


(* The following three facts are currently a bit messed up by
   [get_hd] assuming invariants on the computations.
   We need to either condition the lemmas, or generalize [get_hd]
 *)
Lemma trans_get_hd : forall l P Q,
    transR l P Q ->
    exists a P', transR (val (Hact a P')) (get_hd P) CTree.stuckI /\
              transR l P' Q.
Proof.
  intros * TR.
  unfold transR in *.
  setoid_rewrite unfold_get_hd; cbn.
  (* genobs P oP. *)
  (* revert P HeqoP. *)
  induction TR; intros.
Admitted.

Lemma trans_parL : forall l P P' Q,
    transR l P P' ->
    transR l (P ∥ Q) (P' ∥ Q).
Proof.
  intros * TR.
  red in TR; red.
  rewrite unfold_para.
  rewrite unfold_bind.
Admitted.

Lemma para0p : forall P, 0 ∥ P ~ P.
Proof.
  intros ?.
  steps.
  - rewrite unfold_para, get_hd0, bind_ret_l in TR.
    apply trans_get_hd_bind_inv in TR as (? & ? & ?).
    destruct x.
    exfalso; eapply stuckI_is_stuck; apply H0.
    now exists t'.
  - exists t'; [| reflexivity].
    rewrite unfold_para, get_hd0, bind_ret_l.
    apply trans_get_hd in TR as (? & ? & ? & ?).
    eapply trans_bind_r; [apply H | cbn].

Admitted.

