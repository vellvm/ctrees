(*|
Free iterative non-deterministic structures?
=============================================
Exploring itree and ctree variants for fun and profit.
This file argues about variations on the structure in a minimalistic setting.
The latter representations (modules fam[i]) are based on direct suggestions
by Tom Hirschowitz and Peio Borthelle.

.. coq:: none
|*)

From Coq Require Import Fin.
Set Implicit Arguments.
Open Scope type.
Notation fin := Fin.t.
Notation rel X := (X -> X -> Prop).
Inductive void :=.

(*|
Vanilla variant
---------------
The encoding used in `this paper <https://perso.ens-lyon.fr/yannick.zakowski/papers/ctrees_draft_non_anon.pdf>`_, in positive style for simplicity.

.. coq::
|*)

Module vanilla.

(*|
.. coq:: none
|*)

  Section withParam.

    Variable (E : Type -> Type) (R : Type).

(*|
The structure deeply embeds three kind of branching:

- itree-style external interaction (Vis). We branch on all possible answers, but interpret this semantically as a lack of knowledge, not as non-determinism.
- delayed non-deterministic internal branching (brD).
- immediately observable non-deterministic internal branching (brS).

|*)
    CoInductive ctree :=
    | ret (r : R)                               (* a pure computation *)
    | vis {X : Type} (e : E X) (k : X -> ctree) (* an external event *)
    | brD (n : nat) (k : fin n -> ctree)        (* delayed branching *)
    | brS (n : nat) (k : fin n -> ctree)        (* stepping branching *)
    .

(*|
We associate to this concrete representation of the computation an LTS over three kind of labels:

- [tau] internal decisions
- [obs] observations of pairs of question/answer during interactions with the environment
- [val] returned values

|*)
    Variant label : Type :=
      | tau
      | obs {Y : Type} (e : E Y) (v : Y)
      | val {Y : Type} (v : Y).

    Definition sink : ctree :=
      brD (fun (x : fin 0) => match x with end).

(*|
The construction of the LTS is inductive: we bypass the delayed nodes.
|*)
    Inductive trans : label -> rel ctree :=

    | retS r :
      trans (val r) (ret r) sink

    | visS {X} (e : E X) k x :
      trans (obs e x) (vis e k) (k x)

    | brDS {n} (x : fin n) k l t :
      trans l (k x) t ->
      trans l (brD k) t

    | brSS {n} (x : fin n) k :
      trans tau (brS k) (k x)

   .

(*|
For the best or worse, this leads to very different concrete representations of the same LTS.
For instance, the following are all the same one-state stuck LTS as [sink] defined above.
|*)

    Definition sink_vis (e : E void) : ctree :=
      vis e (fun (x : void) => match x with end).
    Definition sink_S                : ctree :=
      brS   (fun (x : fin 0) => match x with end).
    CoFixpoint sink_infty1           : ctree :=
      brS   (fun (_ : fin 1) => sink_infty1).
    CoFixpoint sink_infty2           : ctree :=
      brS   (fun (_ : fin 2) => sink_infty2).

(*|
An internal choice operator in the style of [ccs] is simply encoded with a binary delayed choice.
|*)
    Definition brD2 (t u : ctree) : ctree :=
      (brD (fun b:fin 2 => match b with | F1 => t | _ => u end)).

    Definition plus := brD2.

(*|
.. coq:: none
|*)

  End withParam.

  Arguments ret [E R].

(*|
The bind is straightforward
|*)

  Definition bind {E X Y} (k : Y -> ctree E X)
    : ctree E Y -> ctree E X :=
    cofix bind m :=
      match m with
      | ret y   => k y
      | vis e g => vis e (fun z => bind (g z))
      | brD g   => brD   (fun z => bind (g z))
      | brS g   => brS   (fun z => bind (g z))
      end.

(*|
A funky question is the following: the strong bisimulation arising from this LTS equates the following two computations. Should it?
|*)

  Variant E : Type -> Type := | toss : E bool.
  Definition odd : ctree E nat :=
    brD2
      (vis toss (fun b: bool => if b then ret 0 else ret 1))
      (vis toss (fun b: bool => if b then ret 2 else ret 3))
  .

  Definition ball : ctree E nat :=
    brD2
      (vis toss (fun b: bool => if b then ret 2 else ret 1))
      (vis toss (fun b: bool => if b then ret 0 else ret 3))
  .

(*|
In particular, because they are bisimilar, interpretation does not respect it.
|*)

End vanilla.

(*|
Two stepped external interaction
--------------------------------
The vanilla strong bisimulation is not proper for interpretation. The following is a currently suggested fix that restricts strictly the notion of bisimulation, distinguishing [odd] and [ball].

.. coq::
|*)

Module two_stepped.

(*|
.. coq:: none
|*)

  Section withParam.

    Variable (E : Type -> Type) (R : Type).

(*|
The structure now adds a passive state awaiting for answer.
|*)
    CoInductive ctree :=
    | ret (r : R)                               (* a pure computation *)
    | vis {X : Type} (e : E X) (k : X -> ctree) (* an external event *)
    | waiting {X : Type} (k : X -> ctree)     (* waiting for answer *)
    | brD (n : nat) (k : fin n -> ctree)        (* delayed branching *)
    | brS (n : nat) (k : fin n -> ctree)        (* stepping branching *)
    .

(*|
We now split the [obs e v] label into two [ask e] and [rcv v].
|*)
    Variant label : Type :=
      | tau
      | ask {Y : Type} (e : E Y)
      | rcv {Y : Type} (v : Y)
      | val {Y : Type} (v : Y).

    Definition sink : ctree :=
      brD (fun (x : fin 0) => match x with end).

(*|
The LTS is the same as before, except the [vis] rule is broken into two
|*)
    Inductive trans : label -> rel ctree :=

    | retS r :
      trans (val r) (ret r) sink

    | visS {X} (e : E X) k :
      trans (ask e) (vis e k) (waiting k)

    | waitS {X} k (x : X) :
      trans (rcv x) (waiting k) (k x)

    | brDS {n} (x : fin n) k l t :
      trans l (k x) t ->
      trans l (brD k) t

    | brSS {n} (x : fin n) k :
      trans tau (brS k) (k x)
   .

(*|
.. coq:: none
|*)

  End withParam.

  Arguments ret [E R].

(*|
The bind is still straightforward
|*)
  Definition bind {E X Y} (k : Y -> ctree E X)
    : ctree E Y -> ctree E X :=
    cofix bind m :=
      match m with
      | ret y   => k y
      | vis e g => vis e (fun z => bind (g z))
      | waiting g => waiting (fun z => bind (g z))
      | brD g   => brD   (fun z => bind (g z))
      | brS g   => brS   (fun z => bind (g z))
      end.


(*|
We still have most of the previous representation of the stuck LTS, except for one that is now differentiated: [sink_vis] is no longer bisimilar to [sink] as it asks the crashing question before
getting stuck.
.. coq::
|*)

End two_stepped.

(*|
We use in the following families of types, that is indexed subsets of a type.
|*)
Record fam X := { dom : Type ; forest : dom -> X }.
Arguments dom {X}.
Arguments forest {X}.

Module fam.

(*|
.. coq:: none
|*)

  Section withParam.

    Variable (E : Type -> Type) (R : Type).

(*|
We stick this time to the itrees constructor, but they quantify over families of descendants
|*)
    (* fam <- F arbitrary functor *)
    CoInductive ctree : Type :=
    | ret : fam R -> ctree
    | delay : fam ctree -> ctree
    | vis : forall Y, E Y -> (Y -> fam ctree) -> ctree.

    Variant label : Type :=
      | tau
      | obs {Y : Type} (e : E Y) (v : Y)
      | val {Y : Type} (v : Y).

    Definition sink : ctree :=
      ret {| dom := void; forest := fun x : void => match x with end |}.

(*|
Structurally, the LTS is now much closer to the tree: it is not recursive anymore
|*)
    Variant trans : label -> rel ctree :=

    | retS r :
      trans (val r) (ret r) sink

    | delayS f (x : dom f) :
      trans tau (delay f) (forest f x)

    | visS {X} (e : E X) k (x : X) (y : dom (k x)) :
      trans (obs e x) (vis e k) (forest (k x) y)
    .

(*|
The sink now has essentially two alternate representations
|*)

    Definition sink_delay : ctree :=
      delay {| dom := void;
              forest := fun x : void => match x with end |}.
    Definition sink_vis Y (e : E Y) : ctree :=
      vis e (fun _ => {| dom := void;
                     forest := fun x : void => match x with end |}).

(*|
An internal choice operator in the style of [ccs] requires us to use family of ctrees as domain.
|*)
    Definition ftree := fam ctree.
    Definition plus (t u : ftree) : ftree :=
      {|
        dom    := dom t + dom u;
        forest := fun idx => match idx with
                          | inl i => forest t i
                          | inr j => forest u j
                          end
      |}.

(*|
Hence we need to look at defining the LTS on [ftree] rather than [ctree] as done above.
|*)

(*|
.. coq:: none
|*)

  End withParam.

  Arguments ret [E R].

(*|
Things get messy to deal with [bind]: it makes no sense on a [ctree].
We are hence tempted to move onto [ftree] directly, but the [fam] is above the [ν],
making it impossible to write the cofixpoint.
|*)

  Definition bind {E X Y} (k : Y -> ctree E X)
    : ctree E Y -> ctree E X.
    refine (cofix bind m :=
              match m with
              | ret y   => _
              | delay f => _
              | vis e f => _
              end).
    - admit.
    (* Can't actually bind, the structure is really
       [ftree] and not [ctree] *)
  Abort.

  Definition bind {E X Y} (k : Y -> ftree E X) : ftree E Y -> ftree E X.
    (* Can't bind, [fam] is not coinductive *)
    Fail refine (cofix bind m := _).
  Abort.

End fam.

Module fam2.

(*|
.. coq:: none
|*)

  Section withParam.

    Variable (E : Type -> Type) (R : Type).

(*|
We hence tweak the previous representation to push the [fam] below the [ν].
We move back to open recursion to express this more naturally.
|*)

    Variant ctreeF (REC : Type) : Type :=
      | RetF : R -> ctreeF REC
      | TauF : REC -> ctreeF REC
      | VisF : forall {Y} (e : E Y), (Y -> REC) -> ctreeF REC
    .

    CoInductive ctree := {
        observe : fam (ctreeF ctree)
      }.
    Arguments RetF {REC}.
    Arguments TauF {REC}.
    Arguments VisF {REC Y}.

    Definition sink : ctree :=
      {| observe :=
        {| dom := void;
           forest := fun x : void => match x with end
           |}
      |}.

(*|
Structurally, the LTS is now much closer to the tree: it is not recursive anymore
|*)

    Variant label : Type :=
      | tau
      | obs {Y : Type} (e : E Y) (v : Y)
      | val {Y : Type} (v : Y).

    Variant trans : label -> rel ctree :=

      | retS r f d :
        forest f d = RetF r ->
        trans (val r) {| observe := f |} sink

      | delayS f d c :
        forest f d = TauF c ->
        trans tau {| observe := f |} c

      | visS {X} (e : E X) k x f d :
        forest f d = VisF e k ->
        trans (obs e x) {| observe := f |} (k x)
    .

  End withParam.

  Arguments RetF {E R REC}.
  Arguments TauF {E R REC}.
  Arguments VisF {E R REC Y}.

(*|
Amusingly it seems hard to avoid introducing a guard in the [ret] case, leading the monadic laws to only hold up to weak bisim.
|*)

  Definition bind {E X Y} (k : Y -> ctree E X)
    : ctree E Y -> ctree E X :=
    cofix bind m :=
      {| observe :=
          {|
            dom := m.(observe).(dom);
            forest :=
              fun f =>
                match m.(observe).(forest) f with
                | RetF y   => TauF (k y)
                | TauF c   => TauF (bind c)
                | VisF e k => VisF e (fun z => bind (k z))
                end
          |}
      |}.

End fam2.

Module fam3.

(*|
.. coq:: none
|*)

  Section withParam.

    Variable (E : Type -> Type) (R : Type).

(*|
Wild version from Tom
|*)

    CoInductive ftree :=
      obs: (forall {X} (e : E X) , fam (X -> ftree))
           -> fam ftree (* tau *)
           -> fam R      (* ret *)
           -> ftree.

    Definition Tau (m : ftree) : fam ftree :=
      let '(obs _ tau _) := m in
      tau.

    Definition Vis (m : ftree) :=
      let '(obs vis _ _) := m in
      vis.

    Definition Ret (m : ftree) :=
      let '(obs _ _ ret) := m in
      ret.

    Variant label : Type :=
      | tau
      | ext {Y : Type} (e : E Y) (v : Y)
      | val {Y : Type} (v : Y).

    Definition empty_fam {X} : fam X :=
      {| dom := void;
        forest := fun x: void => match x with end
      |}.
    Definition sink : ftree :=
      obs (fun _ _ => empty_fam) empty_fam empty_fam.

    Inductive trans : label -> rel ftree :=

    | retS vis tau ret d :
      trans (val (forest ret d)) (obs vis tau ret) sink

    | tauS vis ftau ret d :
      trans tau (obs vis ftau ret) (forest ftau d)

    | visS vis tau ret X (e : E X) d x :
      trans (ext e x) (obs vis tau ret) (forest (vis _ e) d x).

    Definition cup {T} (t u : fam T) : fam T :=
      {|
        dom    := dom t + dom u;
        forest := fun idx => match idx with
                          | inl i => forest t i
                          | inr j => forest u j
                          end
      |}.
    Infix "∪" := cup (at level 60).

    Definition plus (P Q : ftree) : ftree :=
      let '(obs visP tauP retP) := P in
      let '(obs visQ tauQ retQ) := Q in
     obs
        (fun _ e => visP _ e ∪ visQ _ e)
        (tauP ∪ tauQ)
        (retP ∪ retQ).

(*|
.. coq:: none
|*)

    Definition distr (f: fam ftree) : ftree.
      destruct f as [D map].
      refine (obs _ _ _).
      - refine (fun X e => _).
        unshelve (refine (Build_fam _)).
        refine ({ d : D & dom (Vis (map d) e)}).
        refine (fun d => _).
        destruct d as [d i].
        refine (forest (Vis (map d) e) i).
      - unshelve refine (Build_fam _).
        refine { d : D & dom (Tau (map d))}.
        refine (fun d => _).
        destruct d as [d i].
        refine (forest (Tau (map d)) i).
      - unshelve refine (Build_fam _).
        refine { d : D & dom (Ret (map d))}.
        refine (fun d => _).
        destruct d as [d i].
        refine (forest (Ret (map d)) i).
Defined.

    Definition distr' (f : fam ftree) : ftree :=
      match f with
      | {| dom := dom0; forest := forest0 |} =>
          (fun (D : Type) (map : D -> ftree) =>
             obs (fun (X : Type) (e : E X) => {| dom := {d : D & dom (Vis (map d) e)}; forest := fun d : {d : D & dom (Vis (map d) e)} => let (x, p) := d in (fun (d0 : D) (i : dom (Vis (map d0) e)) => forest (Vis (map d0) e) i) x p |})
                 {| dom := {d : D & dom (Tau (map d))}; forest := fun d : {d : D & dom (Tau (map d))} => let (x, p) := d in (fun (d0 : D) (i : dom (Tau (map d0))) => forest (Tau (map d0)) i) x p |}
                 {| dom := {d : D & dom (Ret (map d))}; forest := fun d : {d : D & dom (Ret (map d))} => let (x, p) := d in (fun (d0 : D) (i : dom (Ret (map d0))) => forest (Ret (map d0)) i) x p |}) dom0 forest0
      end.


  End withParam.

(*|
Confused about what I should do in the [ret] case.
|*)

  Definition fam_map {X Y}
    (f : X ->  Y) (m : fam X) : fam Y.
    destruct m as [d1 f1].
    unshelve refine (@Build_fam _ d1 _).
    refine (fun i => (f (f1 i))).
  Defined.

  Definition bind {E X Y}
    (k : Y -> ftree E X) : ftree E Y -> ftree E X.
    refine (
        cofix bind m :=
          let '(obs vis ftau ret) := m
          in
          let '(obs visk tauk retk) := distr (fam_map k ret)
          in obs (fun T e => _) _ _).
    - exact
      {|
        dom    := dom (vis _ e) + dom (visk _ e);
        forest := fun idx =>
                    match idx with
                    | inl i =>
                        fun t => bind (forest (vis _ e) i t)
                    | inr j => forest (visk _ e) j
                    end
      |}.
    - exact
        {|
          dom    := dom ftau + dom tauk;
          forest := fun idx =>
                      match idx with
                      | inl i =>
                          bind (forest ftau i)
                      | inr j => forest tauk j
                      end
        |}.
    - exact retk.
  Defined.

  Definition bundle {D Y Z}
    (ret : D -> Y) (k : Y -> Z) : fam Z :=
    @Build_fam _ D (fun d => k (ret d)).

  (* Conjecture, obviously not for [eq] in practice *)
  (* Lemma foo {E X Y} (m : ftree E X) (k : X -> ftree E Y): *)
  (*   bind k m = *)
  (*     cup (bind k (obs (Vis m) (Tau m) empty_fam)) *)
  (*         (bundle (Ret m) k). *)

(*|
.. coq::
|*)

End fam3.

(*|

-
-
-
-
-
-
-
-
-
-
-
-

|*)
