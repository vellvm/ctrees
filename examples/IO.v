From CTree Require Import
  CTree.Equ
  CTree.Core
  Logic.Ctl
  CTree.SBisim
  CTree.Logic.Trans
  CTree.Interp.Core
  CTree.Interp.State
  CTree.Events.State
  CTree.Events.IO
  CTree.Events.Writer.

From ExtLib Require Import
  Structures.Maps.

Generalizable All Variables.

Import Ctree CTreeNotations CtlNotations.
Local Open Scope ctree_scope.
Local Open Scope ctl_scope.
Local Open Scope bool_scope.

Notation fd := nat (only parsing).


#[refine] Local Instance ctree_kripke_option`{Encode E}: Kripke (ctree E) (Bar E) :=
  {|
    ktrans X '(t, w) '(t', w') :=
      ctree_kripke.(ktrans) (X:=X) (t, Some w) (t', Some w');
    mequ X := @sbisim E E _ _ X X eq
  |}.
Proof.
  intros; now apply ctree_kripke.(ktrans_semiproper) with (t:=t) (s:=s).
Defined.

Section Ex1Proof.
  Context {S: Type}.

  (*| Always closes fds |*)
  Definition io_ex1(str: S): ctree (ioE S) unit :=
    f <- fresh ;;
    b <- open f ;;
    forever (fun _: unit =>
               ignore (brD2
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

  Theorem ctl_lemma_ex1: forall (s: S) f,
    <( {(io_ex1 s, None)}
         |== AG ((now {fun '(Obs io x) => io = Open f}) ->
                 AF now {fun '(Obs io x) => io = Close f}) )>.
  Proof.
    intros s f.
    simpl fst; simpl snd; simpl ctl_contramap.
    next; right. (* 1 step *)
    split; next; eauto.
    split.
    - admit. (*can_step should be automated *)
    - intros (t_w' & x) TR.
      next; right. (* 2 step *)
      destruct (ktrans_some_inv _ _ _ TR) as (? & ?); cbn in H; subst.
      split; [exists x0|]; auto.
      next; split. (* 3 step *)
      + cbn; admit.
      + intros (t_w'' & x') TR'.
        next; right.
        split; eauto;
          destruct (ktrans_some_inv _ _ _ TR') as (? & ?); cbn in H; subst.
        * next.
          exists x; auto.
        * next.
          split.
          -- cbn; admit.
          -- intros (t_w''' & x'') TR''.
  Admitted.
End Ex1Proof.
          
          
          
          
  
