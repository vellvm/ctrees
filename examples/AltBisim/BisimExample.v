From CTree Require Import CTree Eq Eq.SBisimAlt Eq.IterFacts.

Import CoindNotations.
Import CTreeNotations.

(*Variant B2 : Type -> Type := branch2 : B2 bool.*)
Variant PrintE : Type -> Type := print : bool -> PrintE unit.

CoFixpoint t : ctree PrintE B2 void :=
  br2 t (trigger (print true);; t).

CoFixpoint u : ctree PrintE B2 void :=
  br2 (trigger (print true);; u) u.

Lemma unfold_t : t ≅ br2 t (trigger (print true);; t).
Proof. step. cbn. reflexivity. Qed.

Lemma unfold_u : u ≅ br2 (trigger (print true);; u) u.
Proof. step. cbn. reflexivity. Qed.

Theorem bisim_t_u : t ~ u.
Proof.
  coinduction R CH.
  rewrite unfold_t, unfold_u.
  apply step_sb_br; intros [].
  2: {
    exists true.
    rewrite !bind_trigger.
    apply step_sb_vis_id. intros [].
    split; [| auto].
    apply CH.
  }
  {
    exists false.
    Fail apply CH.
Abort.

Theorem bisim_t_u : t ~ u.
Proof.
  (* We switch to the alternative characterization of bisimulation. *)
  rewrite sbisim_sbisim'.
  (* The rest of the proof proceeds as before, but this time it succeeds. *)
  coinduction R CH. intros.
  rewrite unfold_t, unfold_u.
  apply step_sb'_br; intros [].
  (* Notice that unlike step_sb_br, step_sb'_br has unlocked the coinduction hypothesis. *)
  2: {
    exists true.
    rewrite !bind_trigger.
    step. apply step_sb'_vis_id. intros [].
    split; [| auto].
    apply CH.
  }
  {
    exists false.
    apply CH.
  }
  (* The two other cases are the same. *)
  {
    exists false.
    rewrite !bind_trigger.
    step. apply step_sb'_vis_id. intros [].
    split; [| auto].
    apply CH.
  }
  {
    exists true.
    apply CH.
  }
Qed.

(* Using the iter combinator in the definitions of t and u
   leads to a much simpler proof, without coinduction. *)

Definition t' : ctree PrintE B2 void :=
  CTree.iter (fun _ => br2 (Ret (inl tt)) (trigger (print true);; Ret (inl tt))) tt.

Definition u' : ctree PrintE B2 void :=
  CTree.iter (fun _ => br2 (trigger (print true);; Ret (inl tt)) (Ret (inl tt))) tt.

Theorem bisim_t'_u'_simple : t' ~ u'.
Proof.
  unfold t', u'.
  apply sbisim_eq_iter. intros _.
  apply br2_commut.
Qed.
