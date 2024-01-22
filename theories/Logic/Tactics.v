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
  | |- <( ?t, ?w |= ?φ /\ ?ψ )> => cut (<( t, w |= φ )> /\ <( t, w |= ψ )>); [auto | split]
  end.

Ltac cright :=
  match goal with
  | |- <( ?t, ?w |= ?φ \/ ?ψ )> => cut (<( t, w |= ψ )> ); [intros; right; auto|]
  end.

Ltac cleft :=
  match goal with
  | |- <( ?t, ?w |= ?φ \/ ?ψ )> => cut (<( t, w |= φ )> ); [intros; left; auto|]
  end.

Ltac cdestruct H0 :=
  match type of H0 with
  | @entailsF ?W ?M ?MM ?meq ?EqM ?KMS ?X (CAnd ?φ ?ψ) ?t ?w =>
      replace (@entailsF W M MM meq EqM KMS X (CAnd φ ψ) t w)
      with (<( t, w |= φ)> /\ <( t, w |= ψ )>) in H0 by reflexivity;
      destruct H0
  | @entailsF ?W ?M ?MM ?meq ?EqM ?KMS ?X (COr ?φ ?ψ) ?t ?w =>
      replace (@entailsF W M MM meq EqM KMS X (COr φ ψ) t w)
      with (<( t, w |= φ)> \/ <( t, w |= ψ )>) in H0 by reflexivity;
      destruct H0              
  end.

#[global] Tactic Notation "split" := (csplit || split).
#[global] Tactic Notation "right" := (cright || right).
#[global] Tactic Notation "left" := (cleft || left).
#[local] Tactic Notation "destruct" ident(H) := (cdestruct H || destruct H).

#[local] Ltac __coinduction_g R H :=  
  unfold entailsF; coinduction R H;
  try match goal with
  | [KMS: Kripke ?M ?W ?equ |- context[?M ?X] ] =>
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
    | (fun _ => False) => constr:(CBase (fun _ => False))
    | (fun _ => True) => constr:(CBase (fun _ => True))
    | (fun m => ?p m) => constr:(ltac:(reify' p))
    | ?p /\ ?q => constr:(CAnd ltac:(reify' p) ltac:(reify' q))
    | ?p \/ ?q => constr:(COr ltac:(reify' p) ltac:(reify' q))
    | ?p -> ?q => constr:(CImpl ltac:(reify' p) ltac:(reify' q))
    | entailsF ?p => idtac "ENTAILSF failed"; p
    end.
