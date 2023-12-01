From CTree Require Import
  CTree.Equ
  CTree.Core
  Logic.Ctl
  CTree.Interp.Core
  CTree.Interp.Kripke
  CTree.Events.IO.

Import Ctree CTreeNotations CtlNotations.
Local Open Scope ctree_scope.
Local Open Scope ctl_scope.
Local Open Scope bool_scope.

Notation fd := nat (only parsing).

Definition io_ex1{S}(str: S): ctree (ioE S) unit :=
  f <- fresh ;;
  b <- open f ;;
  forever (fun _: unit =>
             ignore (choose
               (if b then 
                  write f str ;;
                  close f
                else
                  close f)
               (if negb b then                  
                  close f
                else
                  write f str ;;
                  close f))) tt.

Section Ex1Proof.

  Context {S: Type} {s: S} {stF stS : Type}
    {M : Maps.Map fd bool stF} {M0 : Maps.Map fd S stS}.

  Notation Σ := (nat * stF * stS).
  Record ObsFd: Type := Obs { is_open: bool; is_written: bool }.

  (* Observe state in a simpler way than the concrete state *)
  Definition obs(e: ioE S)(w: ObsFd): ObsFd :=
    match e with
    | Fresh => Obs false false
    | Open _ => Obs true (is_written w)
    | Close _ => Obs false (is_written w)
    | Write _ _ => if is_open w then
                    Obs true true
                  else
                    Obs false (is_written w)
    | Read _ => w
    end.

  Definition init : nat * stF * stS * ObsFd :=
    (0, Maps.empty, Maps.empty, Obs false false).
  
  Definition t_w := (interp_kripke obs (io_ex1 s) init).

  Lemma ctl_lemma_ex1:
    <( {(t_w, Obs false false)}
         |= AG (AF now {fun obs => is_open obs = false /\ is_written obs = true }) )>.
  Proof.
  Admitted.
End Ex1Proof.
          
          
          
          
  
