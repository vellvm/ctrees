From Coq Require Import
     Basics
     Program.Equality
     Classes.SetoidClass
     Classes.RelationPairs
     Vectors.Fin.

From Coinduction Require Import
     coinduction rel tactics.

From CTree Require Import
  CTree.Core
  CTree.Eq.Core
  Utils.Utils.

Import Ctree CTreeNotations.
Local Open Scope ctree_scope.

Generalizable All Variables.

(*|
Up-to bind principle
~~~~~~~~~~~~~~~~~~~~
Consider two computations explicitely built as sequences
[t >>= k] and [u >>= l]. When trying to prove that they are
bisimilar via a coinductive proof, one is faced with a goal
of the shape:
[t_equ RR r (t >>= k) (u >>= l)]
One can of course case analysis on the structure of [t] and [u]
to make progress in the proof.
But if we know from another source that [t ≅ u], we would like
to be able to simply "match" these prefixes, and continue the
coinductive proof over the continuations.
Such a reasoning is dubbed "up-to bind" reasoning, which we
prove sound in the following.

More formally, this corresponds as always to establishing that
the appropriate function is a valid enhancement. The function
in question here is:
f R = {(bind t k, bind u l) | equ SS t u /\ forall x y, SS x y -> R (k x) (l x)}

|*)

Section Bind_ctx.
  Context {E F :Type} `{HE: Encode E} `{HF: Encode F} {X X' Y Y': Type}.

  (*|
Most general contextualisation function associated to bind].
Can be read more digestly as, where R is a relation on ctrees
(the prefixes of the binds) and S on the continuations:
bind_ctx R S = {(bind t k, bind t' k') | R t t' /\ S k k'}

Note that at this point, this is more general that what we are
interested in: we will specialize [R] and [S] for our purpose,
first here w.r.t. to [equ], later w.r.t. to other relations over
[ctree]s.

Remark: the Coinduction library provides generic binary contexts
[binary_ctx], but whose both arguments are at the same types.
We could provide an heterogeneous version of [binary_ctx] and have
[bind_ctx] be an instance of it to avoid having to rethink in terms
of [sup_all] locally.
|*)

  Definition bind_ctx
    (R: rel (ctree E X) (ctree F X'))
    (S: rel (X -> ctree E Y) (X' -> ctree F Y')):
    rel (ctree E Y) (ctree F Y') :=
    sup_all (fun x => sup (R x)
                     (fun x' => sup_all
                               (fun k => sup (S k)
                                        (fun k' =>
                                           pairH (bind x k) (bind x' k'))))).

  (*|
Two lemmas to interact with [bind_ctx] before making it opaque:
- [leq_bind_ctx] specifies relations above the context
- [in_bind_ctx] specifies how to populate it
|*)
  Lemma leq_bind_ctx:
    forall R S S', bind_ctx R S <= S' <->
                (forall x x', R x x' -> forall k k', S k k' -> S' (bind x k) (bind x' k')).
  Proof.
    intros.
    unfold bind_ctx.
    setoid_rewrite sup_all_spec.
    setoid_rewrite sup_spec.
    setoid_rewrite sup_all_spec.
    setoid_rewrite sup_spec.
    setoid_rewrite <-leq_pairH.
    firstorder.
  Qed.

  Lemma in_bind_ctx (R S :rel _ _) x x' y y':
    R x x' -> S y y' -> bind_ctx R S (bind x y) (bind x' y').
  Proof. intros. now apply ->leq_bind_ctx. Qed.
  #[global] Opaque bind_ctx.

End Bind_ctx.

(*|
Specialization of [bind_ctx] to the [equ]-based closure we are
looking for, and the proof of validity of the principle. As
always with the companion, we prove that it is valid by proving
that it si below the companion.
|*)


(*|
Specialization of [bind_ctx] to the [equ]-based closure we are
looking for, and the proof of validity of the principle. As
always with the companion, we prove that it is valid by proving
that it si below the companion.
|*)
Section Equ_Bind_ctx.

  Context `{HE: Encode E} {X1 X2 Y1 Y2: Type}.

  (*|
Specialization of [bind_ctx] to a function acting with [equ] on the bound value,
and with the argument (pointwise) on the continuation.
|*)
  Program Definition bind_ctx_equ r: mon (rel (ctree E Y1) (ctree E Y2)) :=
    {|body := fun R => @bind_ctx E E HE HE X1 X2 Y1 Y2 (equ r) (pointwise r R) |}.
  Next Obligation.
    repeat red; intros.
    apply (@leq_bind_ctx E E HE HE X1 X2 Y1 Y2 (equ r) (pointwise r x)).
    intros ?? H' ?? H''.
    apply in_bind_ctx. apply H'. intros t t' HS. apply H, H'', HS.
    apply H0.
  Qed.

  (*| The resulting enhancing function gives a valid up-to technique |*)
  Lemma bind_ctx_equ_t (SS : rel X1 X2) (RR : rel Y1 Y2): bind_ctx_equ SS <= et RR.
  Proof.
    apply Coinduction. intros R. apply (leq_bind_ctx _).
    intros x x' xx' k k' kk'.
    step in xx'.
    cbn; unfold observe; cbn.
    destruct xx'.
    - cbn in *.
      generalize (kk' _ _ H).
      apply (fequ RR).
      apply id_T.
    - constructor; intros ?. apply (fTf_Tf (fequ _)).
      apply in_bind_ctx. apply H.
      red; intros. apply (b_T (fequ _)), kk'; auto.
    - constructor. apply (fTf_Tf (fequ _)).
      apply in_bind_ctx. apply H.
      red; intros. apply (b_T (fequ _)), kk'; auto.
    - constructor. intro a. apply (fTf_Tf (fequ _)).
      apply in_bind_ctx. apply H.
      red; intros. apply (b_T (fequ _)), kk'; auto.
  Qed.

End Equ_Bind_ctx.


(*|
Expliciting the reasoning rule provided by the up-to principle.
|*)

Lemma et_clo_bind `{HE: Encode E} (X1 X2 Y1 Y2 : Type) :
	forall (t1 : ctree E X1) (t2 : ctree E X2) (k1 : X1 -> ctree E Y1) (k2 : X2 -> ctree E Y2)
    (S : rel X1 X2) (R : rel Y1 Y2) RR,
		equ S t1 t2 ->
    (forall x1 x2, S x1 x2 -> et R RR (k1 x1) (k2 x2)) ->
    et R RR (bind t1 k1) (bind t2 k2)
.
Proof.
  intros.
  apply (ft_t (bind_ctx_equ_t S R)).
  now apply in_bind_ctx.
Qed.

Lemma et_clo_bind_eq `{HE: Encode E} (X Y1 Y2 : Type) :
	forall (t : ctree E X) (k1 : X -> ctree E Y1) (k2 : X -> ctree E Y2)
    (R : rel Y1 Y2) RR,
    (forall x, et R RR (k1 x) (k2 x)) ->
    et R RR (bind t k1) (bind t k2)
.
Proof.
  intros * EQ.
  apply (ft_t (bind_ctx_equ_t (X2 := X) eq R)).
  apply in_bind_ctx.
  reflexivity.
  intros ? ? <-.
  apply EQ.
Qed.

(*|
And in particular, we get the proper instance justifying rewriting [equ]
to the left of a [bind].
|*)
#[global] Instance bind_equ_cong :
 forall `{HE: Encode E} (X Y : Type) (R : rel Y Y) RR,
   Proper (equ (@eq X) ==> pointwise_relation X (et R RR) ==> et R RR) (@bind E HE X Y).
Proof.
  repeat red. intros.
  eapply et_clo_bind; eauto.
  intros ? ? <-; auto.
Qed.

(*|
Specializing these congruence lemmas at the [sbisim] level for equational proofs
|*)
Lemma equ_clo_bind `{HE: Encode E} (X1 X2 Y1 Y2 : Type) :
	forall (t1 : ctree E X1) (t2 : ctree E X2) (k1 : X1 -> ctree E Y1) (k2 : X2 -> ctree E Y2)
    (S : rel X1 X2) (R : rel Y1 Y2),
		equ S t1 t2 ->
    (forall x1 x2, S x1 x2 -> equ R (k1 x1) (k2 x2)) ->
    equ R (bind t1 k1) (bind t2 k2)
.
Proof.
  intros.
  apply (ft_t (bind_ctx_equ_t S R)).
  now apply in_bind_ctx.
Qed.

Lemma equ_clo_bind_eq `{HE: Encode E} (X Y1 Y2 : Type) :
	forall (t : ctree E X) (k1 : X -> ctree E Y1) (k2 : X -> ctree E Y2)
    (R : rel Y1 Y2),
    (forall x, equ R (k1 x) (k2 x)) ->
    equ R (bind t k1) (bind t k2)
.
Proof.
  intros * EQ.
  apply (ft_t (bind_ctx_equ_t (X2 := X) eq R)).
  apply in_bind_ctx.
  reflexivity.
  intros ? ? <-.
  apply EQ.
Qed.

Ltac __upto_bind_equ' SS :=
  match goal with
    (* Out of a coinductive proof --- terminology abuse, this is simply using the congruence of the relation, not a upto *)
    |- @equ ?E ?HE ?R1 ?R2 ?RR (Ctree.bind (X := ?T1) _ _) (Ctree.bind (X := ?T2) _ _) =>
      apply (@equ_clo_bind E HE T1 T2 R1 R2 _ _ _ _ SS RR)

    (* Upto when unguarded *)
  | |- body (t (@fequ ?E ?HE ?R1 ?R2 ?RR)) ?R (Ctree.bind (X := ?T1) _ _) (Ctree.bind (X := ?T2) _ _) =>
        apply (ft_t (@bind_ctx_equ_t E HE T1 T2 R1 R2 SS RR)), in_bind_ctx

    (* Upto when guarded *)
  | |- body (bt (@fequ ?E ?HE ?R1 ?R2 ?RR)) ?R (Ctree.bind (X := ?T1) _ _) (Ctree.bind (X := ?T2) _ _) =>
      apply (fbt_bt (@bind_ctx_equ_t E HE T1 T2 R1 R2 SS RR)), in_bind_ctx
  end.
Tactic Notation "__upto_bind_equ" uconstr(eq) := __upto_bind_equ' eq.

Ltac __eupto_bind_equ :=
  match goal with
    (* Out of a coinductive proof --- terminology abuse, this is simply using the congruence of the relation, not a upto *)
    |- @equ ?E ?HE ?R1 ?R2 ?RR (Ctree.bind (X := ?T1) _ _) (Ctree.bind (X := ?T2) _ _) =>
      eapply (@equ_clo_bind E HE T1 T2 R1 R2 _ _ _ _ _ RR)

    (* Upto when unguarded *)
  | |- body (t (@fequ ?E ?HE ?R1 ?R2 ?RR)) ?R (Ctree.bind (X := ?T1) _ _) (Ctree.bind (X := ?T2) _ _) =>
        eapply (ft_t (@bind_ctx_equ_t E HE T1 T2 R1 R2 _ RR)), in_bind_ctx

    (* Upto when guarded *)
  | |- body (bt (@fequ ?E ?HE ?R1 ?R2 ?RR)) ?R (Ctree.bind (X := ?T1) _ _) (Ctree.bind (X := ?T2) _ _) =>
      eapply (fbt_bt (@bind_ctx_equ_t E HE T1 T2 R1 R2 _ RR)), in_bind_ctx
  end.

Ltac upto_bind_equ :=
  __upto_bind_equ eq; [reflexivity | intros ? ? <-].


(*|
Up-to [equ eq] bisimulations
----------------------------
The transitivity of the [et R] gives us "equ bisimulation up-to equ". Looking forward,
in order to establish "up-to equ" principles for other bisimulations, we define here the
associated enhancing function.
|*)

(*| Unary enchancing function up-to-equ |*)
Variant equ_clos1_body {E X} {HE: Encode E} R : (ctree E X -> Prop) :=
  | Equ_clos1 : forall t t'
                  (Equt : t ≅ t')
                  (HR : R t'),
      equ_clos1_body R t.

Program Definition equ_clos1 {E X} {HE: Encode E} : mon (ctree E X -> Prop) :=
  {| body := @equ_clos1_body E X HE |}.
Next Obligation.
  intros * ?? LE t EQ; inv EQ.
  econstructor; eauto.
  apply LE; auto.
Qed.

(*| Binary enchancing function up-to-equ |*)
Variant equ_clos2_body {E F X1 X2} {HE: Encode E} {HF: Encode F}
  (R : rel (ctree E X1) (ctree F X2)) : (rel (ctree E X1) (ctree F X2)) :=
  | Equ_clos2 : forall t t' u' u
                 (Equt : t ≅ t')
                 (HR : R t' u')
                 (Equu : u' ≅ u),
      equ_clos2_body R t u.

Program Definition equ_clos2 {E F X1 X2} {HE: Encode E} {HF: Encode F}: mon (rel (ctree E X1) (ctree F X2)) :=
  {| body := @equ_clos2_body E F X1 X2 HE HF |}.
Next Obligation.
  unfold impl; repeat red; intros.
  inv H0; econstructor; eauto.
Qed.

(*|
Sufficient condition to prove compatibility only over the simulation
|*)
Lemma equ_clos2_sym {E C X} : compat converse (@equ_clos2 E E C C X X).
Proof.
  intros R t u EQ; inv EQ.
  apply Equ_clos2 with u' t'; intuition.
Qed.

(*| Even eta-laws for coinductive data-structures are not valid w.r.t. to [eq]
  in Coq. We however do recover them w.r.t. [equ]. |*)
Lemma ctree_eta {E R} {HE: Encode E} (t : ctree E R) : t ≅ go (observe t).
Proof. step; now cbn. Qed.

Lemma unfold_stuck {E R} {HE: Encode E}: @stuck E _ R ≅ Guard stuck.
Proof. exact (ctree_eta stuck). Qed.

Lemma unfold_spin {E R} {HE: Encode E}: @spin E _ R ≅ step spin.
Proof. exact (ctree_eta spin). Qed.

Notation bind_ t k :=
  match observe t with
  | RetF r => k%function r
  | VisF e ke => Vis e (fun x => bind (ke x) k)
  | GuardF t => Guard (bind t k)
  | BrF n ke => Br n (fun x => bind (ke x) k)
  end (only parsing).

Lemma unfold_bind {E R S} {HE: Encode E} (t : ctree E R) (k : R -> ctree E S): bind t k ≅ bind_ t k.
Proof. step; now cbn. Qed.

Notation iter_ step i :=
  (lr <- step%function i;;
   match lr with
   | inl l => Guard (iter step l)
   | inr r => Ret r
   end)%ctree (only parsing).

Lemma unfold_iter {E R I} {HE: Encode E} (step : I -> ctree E (I + R)) i:
  iter step i ≅ iter_ step i.
Proof. step; now cbn. Qed.

(*| Monadic laws |*)
Lemma bind_ret_l {E X Y} {HE: Encode E}: forall (x : X) (k : X -> ctree E Y),
    Ret x >>= k ≅ k x.
Proof.
  intros; now rewrite unfold_bind.
Qed.

(* Giving in to [subst'] anger and defining the monad lemmas again *)
Lemma subst_ret_l {E X Y} {HE: Encode E}: forall (x : X) (k : X -> ctree E Y),
    subst' k (RetF x) ≅ k x.
Proof.
  intros; step; cbn.
  replace (observe (subst' k (RetF x))) with (observe (k x)); reflexivity.
Qed.

Lemma bind_ret_r {E X} {HE: Encode E}: forall (t : ctree E X),
    x <- t;; Ret x ≅ t.
Proof.
  coinduction R CIH.
  intros t;
  rewrite unfold_bind.
  cbn*; desobs t; constructor; auto.
Qed.

Lemma subst_ret_r {E X} {HE: Encode E}: forall (t : ctree E X),
    subst' (fun x => Ret x) (observe t) ≅ t.
Proof.
  intros.
  replace (subst' (fun x: X => Ret x) (observe t)) with (x <- t ;; Ret x) by reflexivity.
  apply bind_ret_r.
Qed.

Lemma bind_bind {E X Y Z} {HE: Encode E}: forall (t : ctree E X) (k : X -> ctree E Y) (l : Y -> ctree E Z),
    (t >>= k) >>= l ≅ t >>= (fun x => k x >>= l).
Proof.
  coinduction R CIH; intros.
  pose proof (ctree_eta t).
  rewrite H.
  rewrite (ctree_eta t). cbn*.
  desobs t; cbn.
  - reflexivity.
  - constructor; intros; apply CIH.
  - constructor; intros; apply CIH.
  - constructor; intros; apply CIH.
Qed.

(*| Structural rules |*)
Lemma bind_vis {E Y Z} (e : E) {HE: Encode E} (k : encode e -> ctree E Y) (g : Y -> ctree E Z):
  Vis e k >>= g ≅ Vis e (fun x => k x >>= g).
Proof.
  now rewrite unfold_bind.
Qed.

Lemma bind_trigger {Y: Type} `{ReSumRet E1 E2} (e : E1) (k : encode e -> ctree E2 Y) :
  trigger e >>= k ≅ Vis (resum e) (fun x: encode (resum e) => k (resum_ret e x)) .
Proof.
  unfold trigger.
  rewrite bind_vis.
  setoid_rewrite bind_ret_l.
  reflexivity.
Qed.

Lemma bind_br {E n Y Z} {HE: Encode E} (k : fin' n -> ctree E Y) (g : Y -> ctree E Z):
  Br n k >>= g ≅ Br n (fun x => k x >>= g).
Proof. now rewrite unfold_bind. Qed.

Lemma bind_branch : forall {E n X} {HE: Encode E} (k : fin' n -> ctree E X),
    branch n >>= k ≅ Br n k.
Proof.
  intros. rewrite unfold_bind. cbn. setoid_rewrite bind_ret_l. reflexivity.
Qed.

Lemma bind_guard {E X Y} {HE: Encode E} (t : ctree E X) (g : X -> ctree E Y):
  Guard t >>= g ≅ Guard (t >>= g).
Proof. now rewrite unfold_bind. Qed.

Lemma vis_equ_bind {E X Y} {HE: Encode E}:
  forall (t : ctree E X) (e : E) k (k' : encode e -> ctree E Y),
    x <- t;; k' x ≅ Vis e k ->
    (exists r, t ≅ Ret r) \/
  exists k0, t ≅ Vis e k0 /\ forall x, k x ≅ x <- k0 x;; k' x.
Proof.
  intros.
  destruct (observe t) eqn:?.
  - left. exists x. rewrite ctree_eta, Heqc. reflexivity.
  - rewrite (ctree_eta t), Heqc, bind_br in H;step in H; inv H.
  - rewrite (ctree_eta t), Heqc, bind_guard in H;step in H; inv H.
  - rewrite (ctree_eta t), Heqc, bind_vis in H.
    apply equ_vis_invT in H as ?; subst.
    destruct H0; subst.
    pose proof (equ_vis_invE H).
    right. exists k0. split.
    + rewrite (ctree_eta t), Heqc. reflexivity.
    + cbn in H1. symmetry in H1. apply H1.
Qed.

Lemma br_equ_bind {E n X Y} {HE: Encode E}:
  forall (t : ctree E X) k (k' : X -> ctree E Y),
  x <- t;; k' x ≅ Br n k ->
  (exists r, t ≅ Ret r) \/
  exists k0, t ≅ Br n k0 /\ forall x, k x ≅ x <- k0 x;; k' x.
Proof.
  intros.
  destruct (observe t) eqn:?.
  - left; exists x; rewrite ctree_eta, Heqc; reflexivity.
  - rewrite (ctree_eta t), Heqc, bind_br in H.
    pose proof (equ_br_invT H) as ->.
    pose proof (equ_br_invE H).
    right. exists k0.
    split; cbn in H0. 
    + rewrite (ctree_eta t), Heqc.
      reflexivity.
    + cbn in H0. symmetry in H0. apply H0.
  - rewrite (ctree_eta t), Heqc, bind_guard in H.
    step in H; cbn in H; dependent destruction H.
  - rewrite (ctree_eta t), Heqc, bind_vis in H. step in H. inv H.
Qed.

Lemma tau_equ_bind {E X Y} {HE: Encode E}:
  forall (t: ctree E Y) (k: Y -> ctree E X) t',
    x <- t;; k x ≅ Guard t' ->
    (exists r, t ≅ Ret r) \/
      exists t0, t ≅ Guard t0 /\ t' ≅ x <- t0 ;; k x.
Proof.
  intros.
  destruct (observe t) eqn:?.
  - left; exists x; rewrite ctree_eta, Heqc; reflexivity.
  - rewrite (ctree_eta t), Heqc, bind_br in H.
    step in H; cbn in H; dependent destruction H.
  - rewrite (ctree_eta t), Heqc, bind_guard in H.
    pose proof (equ_guard_invE H).
    right. exists t0.
    split. 
    + rewrite (ctree_eta t), Heqc.
      reflexivity.
    + now symmetry in H0. 
  - rewrite (ctree_eta t), Heqc, bind_vis in H.
    step in H; cbn in H; dependent destruction H.
Qed.

Lemma ret_equ_bind {E X Y} {HE: Encode E}:
  forall (t : ctree E Y) (k : Y -> ctree E X) r,
  x <- t;; k x ≅ Ret r ->
  exists r1, t ≅ Ret r1 /\ k r1 ≅ Ret r.
Proof.
  intros. setoid_rewrite (ctree_eta t) in H. setoid_rewrite (ctree_eta t).
  destruct (observe t) eqn:?.
  - rewrite bind_ret_l in H. eauto.
  - rewrite bind_br in H. step in H. inv H.
  - rewrite bind_guard in H. step in H. inv H.
  - rewrite bind_vis in H. step in H. inv H.
Qed.

(*| Map |*)
Lemma map_map {E R S T} {HE: Encode E}: forall (f : R -> S) (g : S -> T) (t : ctree E R),
    map g (map f t) ≅ map (fun x => g (f x)) t.
Proof.
  unfold map. intros. rewrite bind_bind. setoid_rewrite bind_ret_l. reflexivity.
Qed.

Lemma bind_map {E R S T} {HE: Encode E}: forall (f : R -> S) (k: S -> ctree E T) (t : ctree E R),
    bind (map f t) k ≅ bind t (fun x => k (f x)).
Proof.
  unfold map. intros. rewrite bind_bind. setoid_rewrite bind_ret_l. reflexivity.
Qed.

Lemma map_bind {E X Y Z} {HE: Encode E} (t: ctree E X) (k: X -> ctree E Y) (f: Y -> Z) :
  (map f (bind t k)) ≅ bind t (fun x => map f (k x)).
Proof.
  intros. unfold map. apply bind_bind.
Qed.

Lemma map_ret {E X Y} {HE: Encode E} (f : X -> Y) (x : X) :
    map f (Ret x: ctree E X) ≅ Ret (f x).
Proof.
  intros. unfold map.
  rewrite bind_ret_l; reflexivity.
Qed.

(*| Forever |*)
Lemma unfold_forever {E X Y} {HE: Encode E}: forall (k: X -> ctree E X)(i: X),
    forever Y k i ≅ r <- k i ;; Guard (forever Y k r).
Proof.
  intros k i.
  unfold forever. 
  rewrite unfold_iter.
  rewrite bind_map.
  reflexivity.
Qed.

(*| When |*)
Lemma unfold_when {n E P} {HE: Encode E}: forall (p: fin' n -> {P} + {~P}),
    when p ≅ i <- branch n;; if p i then Ret i else Guard (when p).
Proof.
  intros.
  unfold when. 
  rewrite unfold_iter.
  rewrite bind_bind.
  upto_bind_equ.
  destruct (p x1); now rewrite bind_ret_l.
Qed.

(*| Unless |*)
Lemma unfold_unless {n E P} {HE: Encode E}: forall (p: fin' n -> {P} + {~P}),
    unless p ≅ i <- branch n;; if p i then Guard (unless p) else Ret i.
Proof.
  intros.
  unfold unless.
  rewrite unfold_iter.
  rewrite bind_bind.
  upto_bind_equ.
  destruct (p x1); now rewrite bind_ret_l.
Qed.

Lemma br_equ': forall n (E: Type) {HE: Encode E} R (k k': fin' n -> ctree E R) Q,
    (forall t, k t (≅ Q) (k' t)) ->
    Br n k (≅ Q) Br n k'.
Proof.
  intros * EQ.
  step; econstructor; auto.
Qed.

Lemma br_equ: forall n (E: Type) {HE: Encode E} R (k k': fin' n -> ctree E R),
    (forall t, k t ≅ k' t) ->
    Br n k ≅ Br n k'.
Proof.
  intros n E HE R k k'.
  exact (@br_equ' n E HE R k k' eq).
Qed.

#[global] Instance proper_equ_forever{E X Y} {HE: Encode E}:
  Proper (pointwise_relation X (@equ E HE X X eq) ==> eq ==> @equ E HE Y Y eq) (forever Y).
Proof.
  unfold Proper, respectful; intros; subst.
  revert y0; coinduction R CIH; intros.
  rewrite (unfold_forever x), (unfold_forever y).
  rewrite H.
  upto_bind_equ.
  econstructor; apply CIH.
Qed.

(*| Inversion of [≅] hypotheses |*)
Ltac subst_hyp_in EQ h :=
  match type of EQ with
  | ?x = ?x => clear EQ
  | ?x = ?y => subst x || subst y || rewrite EQ in h
  end.

Ltac ctree_head_in t h :=
  match t with
  | step ?t =>
      change (step t) with (Br 1 (fun _ => t)) in h
  | @Ctree.trigger ?E ?B ?R ?e =>
      change t with (Vis e (fun x => Ret x) : ctree E R) in h
  | @Ctree.branch ?E ?B ?vis ?X ?b =>
      change t with (Br vis b (fun x => Ret x) : ctree E X) in h
  | _ => idtac
  end.

Ltac inv_equ h :=
  match type of h with
  | ?t ≅ ?u => ctree_head_in t h; ctree_head_in u h;
      try solve [ step in h; inv h; (idtac || invert) ]
  end;
  match type of h with
  | Ret _ ≅ Ret _ =>
      apply equ_ret_inv in h;
      subst
  | Vis _ _ ≅ Vis _ _ =>
      let EQt := fresh "EQt" in
      let EQe := fresh "EQe" in
      let EQ := fresh "EQ" in
      apply equ_vis_invT in h as EQt;
      subst_hyp_in EQt h;
      apply equ_vis_invE in h as [EQe EQ];
      subst
  | Guard _ ≅ Guard _ =>
      let EQt := fresh "EQt" in
      let EQ := fresh "EQ" in
      apply equ_br_invE in h as [EQt EQ];
      subst
  | Br _ _ _ ≅ Br _ _ _ =>
      let EQt := fresh "EQt" in
      let EQb := fresh "EQb" in
      let EQe := fresh "EQe" in
      let EQ := fresh "EQ" in
      apply equ_br_invT in h as EQt;
      destruct EQt as [EQt EQb];
      subst_hyp_in EQt h;
      subst_hyp_in EQb h;
      apply equ_br_invE in h as [EQe EQ];
      subst
  end.

Ltac inv_equ_one :=
  multimatch goal with
  | [ h : _ ≅ _ |- _ ] =>
      inv_equ h
  end.

Ltac inv_equ_all := repeat inv_equ_one.

Tactic Notation "inv_equ" hyp(h) := inv_equ h.
Tactic Notation "inv_equ" := inv_equ_all.
