From CTree Require Import CTree Eq.

Import CoindNotations.
Import CTreeNotations.
Import SSimNotations.

(*Variant B2 : Type -> Type := branch2 : B2 bool.*)
Variant PrintE : Type -> Type := print : bool -> PrintE unit.

CoFixpoint t : ctree PrintE B2 void :=
  Vis (print true) (fun _ =>
    Vis (print false) (fun _ => t)).

Lemma unfold_t : t ≅ Vis (print true) (fun _ =>
    Vis (print false) (fun _ => t)).
Proof. step. cbn. reflexivity. Qed.

CoFixpoint u : ctree PrintE B2 void :=
  br branch2 (fun b => Vis (print b) (fun _ => u)).

Lemma unfold_u : u ≅
  br branch2 (fun b => Vis (print b) (fun _ => u)).
Proof. step. cbn. reflexivity. Qed.

CoFixpoint u' : ctree PrintE B2 void :=
  br2
    (trigger (print true))
    (trigger (print false))
  ;;
  Guard u'.

Lemma unfold_u' : u' ≅
  br2
    (trigger (print true))
    (trigger (print false))
  ;;
  Guard u'.
Proof. step. cbn. reflexivity. Qed.

Notation "t '[≲' R ']' u" := (ss _ (` R) t u) (at level 90, only printing).

Theorem sim_t_u : t ≲ u.
Proof.
  coinduction R CH.
  rewrite unfold_t, unfold_u.
  apply step_ss_br_r with (x := true).
  apply step_ss_vis_id. intros []. split; auto.
  rewrite unfold_u.
  step. apply step_ss_br_r with (x := false).
  apply step_ss_vis_id. intros []. split; [| auto].
  apply CH.
Qed.

Theorem bisim_u_u' : u ~ u'.
Proof.
  coinduction R CH.
  rewrite unfold_u, unfold_u'.
  unfold br2. rewrite bind_br.
  apply step_sb_br_id. intros.
  destruct x.
  - rewrite bind_trigger.
    apply step_sb_vis_id. intros []. split; [| auto].
    rewrite sb_guard.
    apply CH.
  - rewrite bind_trigger.
    apply step_sb_vis_id. intros []. split; [| auto].
    rewrite sb_guard.
    apply CH.
Qed.
