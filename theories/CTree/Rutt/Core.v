From Coq Require Import
     Basics
     Program.Equality
     Eqdep
     Classes.SetoidClass
     Classes.RelationPairs.

From Coinduction Require Import
     coinduction rel tactics.

From CTree Require Import
  CTree.Core.


(*| Equivalence up to tau on ctrees |*)
Section Eutt.
  Context {E: Type} {HE: Encode E}
    {X : Type} (RE: forall (e1 e2: E), encode e1 -> encode e2 -> Prop).

  Inductive euttF (eq : ctree E X -> ctree E X -> Prop) :
    ctree' E X -> ctree' E X -> Prop :=
    | EuttRet x y:
      x = y ->
      euttF eq (RetF x) (RetF y)
    | EuttVis (e1 e2: E) (k1: encode e1 -> _) (k2: encode e2 -> _):
      (forall x y, eq_dep E encode e1 x e2 y -> eq (k1 x) (k2 y)) ->
      euttF eq (VisF e1 k1) (VisF e2 k2)
    | EuttTau t1 t2:
      eq t1 t2 ->
      euttF eq (TauF t1) (TauF t2)
    | EuttTauL t1 t2:
      euttF eq (observe t1) t2 ->
      euttF eq (TauF t1) t2
    | EuttTauR t1 t2:
      euttF eq t1 (observe t2) ->
      euttF eq t1 (TauF t2)            
    | EuttBr {n} k1 k2:
      (forall (x: fin' n), eq (k1 x) (k2 x)) ->
      euttF eq (BrF n k1) (BrF n k2).
  Hint Constructors euttF: core.

  Program Definition feutt: mon (ctree E X -> ctree E X -> Prop) :=
    {|body eq t1 t2 :=  euttF eq (observe t1) (observe t2) |}.
  Next Obligation.
    unfold pointwise_relation, Basics.impl,
      Proper, respectful.
    cbn; intros; dependent induction H0;
      rewrite <- ?x2, <- ?x1, <- ?x; eauto.
  Qed.
End Eutt.

Definition eutt {E} {HE:Encode E} {X} :=
  (gfp (@feutt E HE X)).

#[global] Hint Constructors euttF: core.

Ltac fold_eutt_in H:=
  multimatch type of H with
  | context[gfp (@feutt ?E ?HE ?X)] =>
      fold (@eutt E HE X) in H
  end.

Ltac fold_eutt :=
  match goal with
  | |- context[gfp (@feutt ?E ?HE ?X)] =>
      fold (@eutt E HE X)
  end.

Ltac __coinduction_eutt R H :=
  unfold eutt; apply_coinduction; intros R H.

Ltac __step_eutt := unfold eutt; step; fold_eutt.

#[global] Tactic Notation "step" := __step_eutt || step.
#[global] Tactic Notation "coinduction" simple_intropattern(R) simple_intropattern(H) := __coinduction_eutt R H.

Ltac __step_eutt_in H := unfold eutt in H; step in H; fold_eutt_in H.

#[global] Tactic Notation "step" "in" ident(H) :=
  __step_eutt_in H || step in H.


Infix "~" := eutt (at level 70): ctree_scope.

(** The associated companions *)
Notation rt := (t feutt).
Notation rT := (T feutt).
Notation rbt := (bt feutt).
Notation rbT := (bT feutt).

Notation "t [~] u" := (rt t u) (at level 79): ctree_scope.
Notation "t {~} u" := (rbt t u) (at level 79): ctree_scope.
Notation "t {~}} u" := (euttF eutt t u)
                         (at level 79): ctree_scope.

Section EuttHomogenousTheory.
  Context {E: Type} {HE: Encode E} {X : Type}.
  Notation rT  := (T (feutt (E := E) (HE:=HE) (X:=X))).
  Notation rt  := (t (feutt (E := E) (HE:=HE) (X:=X))). 
  Notation rbt := (bt (feutt (E := E) (HE:=HE) (X:=X))). 

  (** [const eq] is compatible: up-to reflexivity is valid *)
  Lemma refl_t: const eq <= rt.
  Proof.
    apply leq_t; intro.
    cbn.
    intros p ? <-.
    desobs p; auto.
    econstructor; intros.
    now dependent destruction H.
  Qed.    

  (** [converse] is compatible: up-to symmetry is valid *)
  Lemma converse_t: converse <= rt.
  Proof.
    apply leq_t; intros S x y H; cbn.
    cbn in H.
    dependent induction H; rewrite <- ?x, <- ?x1, <- ?x2; auto.
  Qed.

  (** [squaring] is compatible: up-to transitivity is valid *)
  Lemma square_t: square <= rt.
  Proof.
    pose proof (refl_t); cbn in H; unfold pointwise_relation, impl in H.
    apply leq_t.
    intros S x z [y xy yz]; cbn in *.
    remember (observe x) as x'.
    remember (observe y) as y'.
    remember (observe z) as z'.
    clear Heqx' x Heqy' y Heqz' z.
    generalize dependent z'.    
    induction xy; intros; subst; induction yz; subst; auto.
    - constructor; intros.
      specialize (H _ _ H0).
      dependent destruction H0.
    constructor.
    
    - constructor.
      rewrite <-H0 in H2.
      rewrite H1, <-H4.
      now inversion H2.
    - constructor. 
      dependent destruction H2.
      eauto.
    - rewrite <- H0 in H2.
      dependent destruction H2.
      eauto.
    - rewrite <- H0 in H2.
      dependent destruction H2.
      eauto.
  Qed.

  #[global] Instance Equivalence_et {HR: Equivalence RR} S: Equivalence (et S).
  Proof. apply Equivalence_t. apply refl_t. apply square_t. apply converse_t. Qed.
  #[global] Instance Equivalence_eT  {HR: Equivalence RR} f S: Equivalence (eT f S).
  Proof. apply Equivalence_T. apply refl_t. apply square_t. apply converse_t. Qed.
  #[global] Instance Equivalence_ebt  {HR: Equivalence RR} S: Equivalence (ebt S).
  Proof. apply Equivalence_bt. apply refl_t. apply square_t. apply converse_t. Qed.
  #[global] Instance Equivalence_equ  {HR: Equivalence RR}: Equivalence (@equ E HE X X RR) | 1.
  Proof. apply Equivalence_et. Qed.

  #[global] Instance Reflexive_equb (equ : ctree E X -> ctree E X -> Prop) :
    Reflexive RR -> Reflexive equ -> Reflexive (equF RR equ).
  Proof.
    red. destruct x; auto.
  Qed.

End EquTheory.
Local Open Scope ctree_scope.
#[global] Hint Constructors equF: core.

#[global] Instance equ_eq_equ_impl {E R} {HE: Encode E}:
  Proper (equ eq ==> equ eq ==> flip impl) (@equ E _ R R eq).
Proof.
  unfold Proper, respectful, flip, impl; cbn.
  unfold equ; coinduction RR IH.  
  intros t t' EQt u u' EQu EQ.
  step in EQt.
  step in EQu.
  step in EQ.
  cbn*; cbn in *; inv EQt; rewrite <-H0 in EQ.
  - inv EQ.
    rewrite <-H2 in EQu.
    inv EQu; auto.
  - dependent destruction EQ.
    rewrite <- x in EQu.
    dependent destruction EQu.
    rewrite <- x.
    constructor.
    intro x1; rewrite H1, H0, <- H.
    reflexivity.
  - dependent destruction EQ.
    rewrite <- x in EQu.
    dependent destruction EQu.
    rewrite <- x.
    constructor.
    eapply IH; eauto.
  - dependent destruction EQ.
    cbn.
    rewrite <- x in EQu.
    dependent destruction EQu.
    rewrite <- x.
    constructor.
    intro x1; rewrite H1, H0, <- H.
    reflexivity.
Qed.

#[global] Instance equ_eq_equ_goal {E R} {HE: Encode E}:
  Proper (equ eq ==> equ eq ==> impl) (@equ E _ R R eq).
Proof.
  unfold Proper, respectful, flip, impl; cbn.
  unfold equ; coinduction RR IH.  
  intros t t' EQt u u' EQu EQ.
  step in EQt.
  step in EQu.
  step in EQ.
  cbn*; cbn in *; inv EQt; rewrite <- H in EQ.
  - inv EQ; auto.
    rewrite <- H2 in EQu.
    inv EQu; auto.
  - dependent destruction EQ.
    rewrite <- x in EQu.
    dependent destruction EQu.
    rewrite <- x.
    constructor.
    intro x1. rewrite <- H, <- H1, H0.
    reflexivity.
  - dependent destruction EQ.
    cbn.
    rewrite <- x in EQu.
    dependent destruction EQu.
    rewrite <- x.
    constructor; eauto.
  - dependent destruction EQ.
    cbn.
    rewrite <- x in EQu.
    dependent destruction EQu.
    rewrite <- x.
    constructor.
    intro x1; rewrite <- H, <- H1, <- H0.
    reflexivity.
Qed.

(** Shallow [observing]: Lift relations through [observe]. *)
Record observing {E R} {HE: Encode E}
           (eq_ : ctree' E R -> ctree' E R -> Prop)
           (t1 : ctree E R) (t2 : ctree E R) : Prop :=
  observing_intros
  { observing_observe : eq_ (observe t1) (observe t2) }.
#[global] Hint Constructors observing: core.
Arguments observing_observe {E R HE eq_ t1 t2}.

Section observing_relations.
  Context {E : Type} {HE: Encode E} {R : Type}.
  Variable (eq_ : ctree' E R -> ctree' E R -> Prop).

  #[global] Instance observing_observe_ :
    Proper (observing eq_ ==> eq_) observe.
  Proof. intros ? ? []; cbv; auto. Qed.

  #[global] Instance observing_go : Proper (eq_ ==> observing eq_) go.
  Proof. cbv; auto. Qed.

  #[global] Instance monotonic_observing eq_' :
    subrelation eq_ eq_' ->
    subrelation (observing eq_) (observing eq_').
  Proof. intros ? ? ? []; cbv; eauto. Qed.

  #[global] Instance Equivalence_observing :
    Equivalence eq_ -> Equivalence (observing eq_).
  Proof.
    intros []; split; cbv; auto.
    - intros ? ? []; auto.
    - intros ? ? ? [] []; eauto.
  Qed.

End observing_relations.

(** ** Unfolding lemmas for [bind] *)
#[global] Instance observing_bind {E R S} {HE: Encode E}:
  Proper (observing eq ==> eq ==> observing eq) (@Ctree.bind E HE R S).
Proof.
  repeat intro; subst. constructor.
  unfold observe. cbn.
  rewrite (observing_observe H). reflexivity.
Qed.

Lemma bind_ret_ {E R S} {HE: Encode E} (r : R) (k : R -> ctree E S) :
  observing eq (Ctree.bind (Ret r) k) (k r).
Proof. constructor; reflexivity. Qed.

Lemma bind_guard_ {E R} {HE: Encode E} U t (k: U -> ctree E R) :
  observing eq (Ctree.bind (Tau t) k) (Tau (Ctree.bind t k)).
Proof. constructor; reflexivity. Qed.

Lemma bind_br_ {E R} {HE: Encode E} n U (bk: fin' n -> ctree E U) (k: U -> ctree E R) :
  observing eq (Ctree.bind (Br n bk) k) (Br n (fun i => Ctree.bind (bk i) k)).
Proof. constructor; reflexivity. Qed.

Lemma bind_vis_ {E R U} {HE: Encode E} (e: E) (ek: encode e -> ctree E U) (k: U -> ctree E R) :
  observing eq
    (Ctree.bind (Vis e ek) k)
    (Vis e (fun x => Ctree.bind (ek x) k)).
Proof. constructor; reflexivity. Qed.

(** Unfolding lemma for [iter]. There is also a variant [unfold_iter]
    without [Tau]. *)
Lemma unfold_aloop_ {E X Y} {HE: Encode E} (f : X -> ctree E (X + Y)) (x : X) :
  observing eq
    (Ctree.iter f x)
    (Ctree.bind (f x) (fun lr => on_left lr l (Tau (Ctree.iter f l)))).
Proof. constructor; reflexivity. Qed.

(** ** [going]: Lift relations through [go]. *)

(** Shallow [going] *)
Inductive going {E R1 R2} {HE: Encode E} (r : ctree E R1 -> ctree E R2 -> Prop)
          (ot1 : ctree' E R1) (ot2 : ctree' E R2) : Prop :=
| going_intros : r (go ot1) (go ot2) -> going r ot1 ot2.
#[global] Hint Constructors going: core.

Lemma observing_going {E R} {HE: Encode E} (eq_ : ctree' E R -> ctree' E R -> Prop) ot1 ot2 :
  going (observing eq_) ot1 ot2 <-> eq_ ot1 ot2.
Proof.
  split; auto; intros [[]]; auto.
Qed.

Section going_relations.

  Context {E : Type} {HE: Encode E} {R : Type}.
  Variable (eq_ : ctree E R -> ctree E R -> Prop).

  #[global] Instance going_go : Proper (going eq_ ==> eq_) go.
  Proof. intros ? ? []; auto. Qed.

#[global] Instance monotonic_going eq_' :
  subrelation eq_ eq_' ->
  subrelation (going eq_) (going eq_').
Proof. intros ? ? ? []; eauto. Qed.

#[global] Instance Equivalence_going :
  Equivalence eq_ -> Equivalence (going eq_).
Proof.
  intros []; constructor; cbv; eauto.
  - intros ? ? []; auto.
  - intros ? ? ? [] []; eauto.
Qed.

End going_relations.

Local Open Scope ctree_scope.

(* Resum lemmas *)
Lemma resumCtree_Ret {E1 E2 : Type} `{ReSumRet E1 E2}
           {R} (r : R) :
  resumCtree (Ret r) ≅ Ret r.
Proof. step. cbn. constructor. reflexivity. Qed.

Lemma resumCtree_Br  {E1 E2 : Type} `{ReSumRet E1 E2}
           {R} (t : ctree E1 R) (n: nat) (k: fin' n -> ctree E1 R):
  resumCtree (Br n k) ≅ Br n (fun x => resumCtree (k x)).
Proof.
  step.
  cbn.
  constructor.
  intros.
  reflexivity.
Qed.

Lemma resumCtree_Vis {E1 E2 : Type} `{ReSumRet E1 E2}
           {R} (e : E1) (k : encode e -> ctree E1 R) :
  resumCtree (Vis e k) ≅ Vis (resum e) (fun x => resumCtree (k (resum_ret e x))).
Proof.
  step.
  cbn.
  constructor.
  intros.
  reflexivity.
Qed.

(*| Dependent inversion of [equ] and [equb] equations |*)
Lemma equ_ret_inv {E R} {HE: Encode E} {r1 r2 : R} :
  (Ret r1) ≅ (Ret r2 : ctree E R) ->
  r1 = r2.
Proof.
  intros EQ. step in EQ.
  inv EQ; auto.
Qed.

Lemma equ_vis_invT {E S} {HE: Encode E} {e1 e2: E} {k1: encode e1 -> ctree E S} {k2: encode e2 -> ctree E S}:
  Vis e1 k1 ≅ Vis e2 k2 ->
  encode e1 = encode e2 /\ e1 = e2.
Proof.
  intros EQ. step in EQ.
  inv EQ; auto.
Qed.

Lemma equ_vis_invE {E S} {HE: Encode E} {e: E} {k1 k2: encode e -> ctree E S}:
  Vis e k1 ≅ Vis e k2 ->
  forall x, k1 x ≅ k2 x.
Proof.
  intros EQ. step in EQ.
  inv EQ.
  dependent destruction H2.
  auto.
Qed.

Lemma equ_br_invT {E S n1 n2} {HE: Encode E}
  {k1 : fin' n1 -> ctree E S} {k2: fin' n2 -> ctree E S}:
  Br n1 k1 ≅ Br n2 k2 ->
  n1 = n2.
Proof.
  intros EQ; step in EQ.
  inv EQ; auto.
Qed.

Lemma equ_br_invE {E S n} {HE: Encode E} {k1 k2: fin' n -> ctree E S}:
  Br n k1 ≅ Br n k2 ->
  forall x,k1 x ≅ k2 x.
Proof.
  intros EQ; step in EQ; cbn in EQ.
  dependent destruction EQ.
  auto.
Qed.

Lemma equ_tau_invE {E S} {HE: Encode E} {t1 t2: ctree E S}:
  Tau t1 ≅ Tau t2 ->
  t1 ≅ t2.
Proof.
  intros EQ; step in EQ; cbn in EQ.
  now dependent destruction EQ.
Qed.

Lemma equF_vis_invT {E S} {HE: Encode E} {e1 e2: E} {R} {k1 k2: _ -> ctree E S}:
  equF R (equ R) (VisF e1 k1) (VisF e2 k2) ->
  encode e1 = encode e2 /\ e1 = e2.
Proof.
  intros EQ.
  dependent induction EQ; auto.
Qed.

Lemma equF_vis_invE {E S} {HE: Encode E} {e: E} {R} {k1 k2 : _ -> ctree E S}:
  equF R (equ R) (VisF e k1) (VisF e k2) ->
  forall x, equ R (k1 x) (k2 x).
Proof.
  intros EQ.
  inv EQ.
  dependent destruction H1; dependent destruction H2; eauto.
Qed.

Lemma equF_br_invT {E S n1 n2} {HE: Encode E} {R}
  (k1 : fin' n1 -> ctree E S) (k2: fin' n2 -> ctree E S) :
  equF R (equ R) (BrF n1 k1) (BrF n2 k2) ->
  n1 = n2.
Proof.
  intros EQ; dependent induction EQ; auto.
Qed.

Lemma equb_br_invE {E S n} {HE: Encode E} {R} {k1 k2: fin' n -> ctree E S}:
  equF R (equ R) (BrF n k1) (BrF n k2) ->
  forall x, equ R (k1 x) (k2 x).
Proof.
  intros EQ.
  now dependent destruction EQ.
Qed.

(*|
Proper Instances
----------------
TODO: step back and think a bit better about those

equ eq       ==> going (equ eq)  observe
∀(equ eq)    ==> going (equ eq)  BrF
∀(equ eq)    ==> going (equ eq)  VisF
observing eq --> equ eq
going(equ)   ==> eq ==> fimpl    equb eq (t_equ eq r)
eq ==> going(equ)   ==> fimpl    equb eq (t_equ eq r)
equ ==> equ ==> flip impl)       bt_equ eq r
|*)

#[global] Instance equ_observe {E X} {HE: Encode E} {R: rel X X}: (* Why not X Y *)
  Proper (equ R ==> going (equ R)) observe.
Proof. constructor; step in H; now step. Qed.

#[global] Instance equ_BrF {E X} {HE: Encode E} {n R}:
  Proper (pointwise_relation _ (equ R) ==> going (equ R)) (@BrF E _ X _ n).
Proof. constructor; red in H; step; econstructor; eauto. Qed.

#[global] Instance equ_VisF {E X} {HE: Encode E} {R} (e : E) :
  Proper (pointwise_relation _ (equ R) ==> going (equ R)) (@VisF E _ X _ e).
Proof. constructor; step; constructor; eauto. Qed.

(*| TODO: Here only [eq] is polymorphic enough to take both [ctree' E X] and [X] arguments |*)
#[global] Instance observing_sub_equ_eq {E X} {HE: Encode E}:
  subrelation (@observing E X _ eq) (equ eq).
Proof.
  repeat intro.
  step; cbn; rewrite (observing_observe H); eauto.
Qed.

#[global] Instance equ_eq_equt {E X} {HE: Encode E} {r R} {HR: Equivalence R}:
  Proper (going (equ R) ==> eq ==> flip impl)
	     (@equF E _ X X R (et R r)).
Proof.
  unfold Proper, respectful, flip, impl; intros; subst.
  inv H; step in H0; inv H0; inv H1; cbn in *; subst;
  match goal with
    | [H: ?a = ?b |- _] =>
        match type of a with
        | ctree' ?E ?X => inv H
        end
  end.
  - econstructor; transitivity x1; eauto.
  - dependent induction H4; econstructor.
    now setoid_rewrite <- H in H0.
  - econstructor.
    transitivity t0; eauto.
    now setoid_rewrite <- H.
  - dependent induction H4; econstructor.
    now setoid_rewrite <- H in H0.
Qed.

#[global] Instance equ_clos_eT_goal {E X} {HE: Encode E} R RR f {HR: Equivalence R}:
  Proper (@equ E HE X X R ==> equ R ==> iff) (eT R f RR).
Proof.
  split; intros.
  - rewrite <- H, <- H0; auto.
  - rewrite H, H0; auto.
Qed.

#[global] Instance gfp_bt_equ {E X} {HE: Encode E} {r R} {HR: Equivalence R}:
  Proper (@equ E HE X X R ==> equ R ==> iff) (ebt R r).
Proof.
  unfold Proper, respectful, flip, impl.
  split; intros.
  - etransitivity; [|etransitivity]; [|apply H1 |]; step.
    + symmetry; assumption.
    + assumption.
  - etransitivity; [|etransitivity]; [|apply H1 |]; step.
    + assumption.
    + symmetry; assumption.
Qed.

#[global] Instance Equivalence_bt_equb_gen {E X} {HE: Encode E} {r R} {HR: Equivalence R}:
  Proper ((gfp (@fequ E HE X X R)) ==> (gfp (@fequ E HE X X R)) ==> flip impl) (ebt R r).
Proof.
  unfold Proper, respectful, flip, impl.
  intros.
  etransitivity; [|etransitivity]; [| eassumption |];
    step; [rewrite H|rewrite H0]; reflexivity.
Qed.
