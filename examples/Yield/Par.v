From Coq Require Import
     Program
     List
     Logic.FunctionalExtensionality.

From CTree Require Import
	Utils
	CTrees
 	Interp
	Equ
	Bisim.

From Coinduction Require Import
	coinduction rel tactics.

Import ListNotations.
Import CTreeNotations.

Variant yieldE S : Type -> Type :=
| Yield : S -> yieldE S S.

(** return one of the elements in [x :: xs], as well as the complete list of unchosen elements *)
Fixpoint choose' {E} {X} (x : X) (xs : list X) (rest : list X) :
  ctree E (X * list X)
  := match xs with
     | [] => Ret (x, rest)
     | x' :: xs =>
       Sanity.choice2
         (Ret (x, (x' :: xs) ++ rest)) (* [x] *)
         (choose' x' xs (x :: rest)) (* not [x] *)
     end.
Definition choose {E} {X} x xs : ctree E (X * list X) :=
  choose' x xs [].

Section parallel.
  Context {config : Type}.

  Definition thread := config -> ctree (yieldE config) (config * unit).

  Definition par_match par (curr : thread) (rest : list thread)
    : thread :=
    fun (s : config) =>
      match (observe (curr s)) with
      | RetF (s', _) => match rest with
                       | [] => Ret (s', tt)
                       | h :: t => Tau (par h t s')
                       end
      | ChoiceF n k => Choice n (fun c => (par (fun _ => k c) rest s))
      | VisF (Yield _ s') k =>
        '(curr', rest') <- choose k rest;;
        Vis (Yield _ s') (fun s' => (par curr' rest' s'))
      end.
  CoFixpoint par := par_match par.
  Lemma rewrite_par curr rest s : par curr rest s ≅ par_match par curr rest s.
  Proof.
    coinduction r CIH.
    unfold par. cbn. reflexivity.
  Qed.

  Lemma par_empty :
    forall t c, par t [] c ≅ t c.
  Proof.
    coinduction r CIH. intros. cbn.
    destruct (observe (t c)) eqn:?.
    (* TODO: get proper instance to work *)
    - eapply equ_equF. apply rewrite_par. eauto.
      unfold par_match. rewrite Heqc0. destruct r0, u. constructor; auto.
    - eapply equ_equF. apply rewrite_par. eauto.
      unfold par_match. rewrite Heqc0. destruct e.
      unfold choose, choose'. cbn. constructor; apply CIH.
    - eapply equ_equF. apply rewrite_par. eauto.
      unfold par_match. rewrite Heqc0.
      cbn. constructor; intros; eapply CIH.
  Qed.
