From Coinduction Require Import
  coinduction tactics.

From CTree Require Import
  Utils.Utils
  Logic.Semantics.

Import CtlNotations.
Local Open Scope ctl_scope.

Generalizable All Variables.

Ltac csplit :=
  match goal with
  | |- <( ?m |= ?φ /\ ?ψ )> => cut (<( m |= φ )> /\ <( m |= ψ )>); [auto | split]
  end.

Ltac cright :=
  match goal with
  | |- <( ?m |= ?φ \/ ?ψ )> => cut (<( m |= ψ )> ); [intros; right; auto|]
  end.
Ltac cleft :=
  match goal with
  | |- <( ?m |= ?φ \/ ?ψ )> => cut (<( m |= φ )> ); [intros; left; auto|]
  end.

Ltac cdestruct H0 :=
  match type of H0 with
  | @entailsF ?M ?S ?equ ?KMS ?X (CAnd ?φ ?ψ) ?m =>
      replace (@entailsF M S KMS (CAnd φ ψ) m)
      with (<( m |= φ)> /\ <( m |= ψ )>) in H0 by reflexivity;
      destruct H0
  | @entailsF ?M ?S ?equ ?KMS ?X (COr ?φ ?ψ) ?m =>
      replace (@entailsF M S KMS (COr φ ψ) m)
      with (<( m |= φ)> \/ <( m |= ψ )>) in H0 by reflexivity;
      destruct H0              
  end.

#[global] Tactic Notation "split" := (csplit || split).
#[global] Tactic Notation "right" := (cright || right).
#[global] Tactic Notation "left" := (cleft || left).
#[local] Tactic Notation "destruct" ident(H) := (cdestruct H || destruct H).

Ltac cinduction H :=
  match type of H with
  | @entailsF ?M ?S ?equ ?KMS ?X (CAU ?ψ ?φ) ?ms =>
      let m' := fresh "m" in
      let Heqt := fresh "Heqm" in
      remember ms as m' eqn: Heqm;
      unfold entailsF in H;
      induction H as [m' H' | m' Hbase IH HH];
      rewrite !Heqm in *;
      clear Heqm;
      fold (@entailsF M S KMS) in *
  | @entailsF ?M ?S ?equ ?KMS ?X (CEU ?ψ ?φ) ?ms =>
      let m' := fresh "m" in
      let Heqt := fresh "Heqm" in
      remember ms as m' eqn: Heqm;
      unfold entailsF in H;
      induction H as [m' H' | m' Hbase IH HH];
      rewrite !Heqm in *;
      clear Heqm;
      fold (@entailsF M S KMS) in *
  end.

#[local] Tactic Notation "induction" ident(H) := (cinduction H || induction H).

#[local] Ltac __coinduction_g R H :=  
  unfold entailsF; coinduction R H;
  try match goal with
  | [KMS: Kripke ?M ?W ?equ |- context[?M ?X * ?W] ] =>
      fold (@entailsF M W equ KMS X) in *
  end.

#[global] Tactic Notation "coinduction" simple_intropattern(R) simple_intropattern(H) :=
  __coinduction_g R H || coinduction R H.

(* TODO: Does not work... 
   From [TS -> Prop] to [CtlFormula] *)
Ltac reify' typ :=
  try match typ with
    | car ?p ?q => constr:(CAR ltac:(reify' p) ltac:(reify' q))
    | cer ?p ?q => constr:(CER ltac:(reify' p) ltac:(reify' q))
    | cau ?p ?q => constr:(CAU ltac:(reify' p) ltac:(reify' q))
    | ceu ?p ?q => constr:(CEU ltac:(reify' p) ltac:(reify' q))
    | (fun _ => False) => constr:(CNow (fun _ => False))
    | (fun _ => True) => constr:(CNow (fun _ => True))
    | (fun m => ?p m) => constr:(ltac:(reify' p))
    | ?p /\ ?q => constr:(CAnd ltac:(reify' p) ltac:(reify' q))
    | ?p \/ ?q => constr:(COr ltac:(reify' p) ltac:(reify' q))
    | ?p -> ?q => constr:(CImpl ltac:(reify' p) ltac:(reify' q))
    | entailsF ?p => idtac "ENTAILSF failed"; p
    end.
