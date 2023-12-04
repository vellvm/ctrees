From Coq Require Import Arith.PeanoNat.

From CTree Require Import
  CTree.Equ
  CTree.Core
  Events.Writer
  Logic.Ctl
  CTree.SBisim
  CTree.Logic.Trans
  Logic.Kripke
  CTree.Interp.Core
  CTree.Interp.State
  CTree.Events.State.

From ExtLib Require Import
  Structures.MonadState
  Data.Monads.StateMonad
  Structures.Maps.

Generalizable All Variables.

Import Ctree CTreeNotations CtlNotations.
Local Open Scope ctree_scope.
Local Open Scope ctl_scope.

(*| Security labels |*)
Variant Sec: Set := H | L.

(*| Preorder of [sec] labels |*)
Reserved Notation "a ≤ b" (at level 52, left associativity).
Variant sec_preord: rel Sec Sec :=
| SecRefl: forall a, a ≤ a
| SecHL: L ≤ H
where "a ≤ b" := (sec_preord a b).
Local Hint Constructors sec_preord: core.

Local Instance sec_preord_refl: Reflexive sec_preord := SecRefl.
Local Instance sec_preord_trans: Transitive sec_preord.
Proof. red; intros [] [] [] *; auto. Qed.

Lemma sec_preord_dec(l r: Sec): { l ≤ r } + { r ≤ l }.
Proof.
  revert r; induction l; destruct r.
  - left; reflexivity. 
  - right; auto. 
  - left; auto.
  - left; reflexivity.
Qed.

(*| Both values and addresses are nat |*)
Notation Addr := nat.

Variant secE: Type :=
  | Read (l: Sec) (addr: Addr)
  | Write (l: Sec) (addr: Addr) (val: nat).

Section SecurityEx.  

  Context `{MF: Map Addr (Sec * nat) St} `{OF: MapOk Addr (Sec * nat) St eq}.
  
  Global Instance encode_secE: Encode secE :=
    fun e => match e with
          | Read l addr => nat
          | Write l addr v => unit
          end.

  Global Instance handler_secE: secE ~> stateT St (ctree void) := {
      handler e :=
        mkStateT
          (fun (st: St) =>                                     
             match e return ctree void (encode e * St) with
             | Read l_r addr =>                                 
                 match lookup addr st with
                 | Some (l_a, v) =>
                     if sec_preord_dec l_r l_a then
                       Ctree.stuck
                     else
                       Ret (v, st)
                 | None => Ret (0%nat, st)
                 end
             | Write l_w addr v =>
                 match lookup addr st with
                 | Some (l_a, _) =>
                     if sec_preord_dec l_w l_a then
                       Ctree.stuck
                     else
                       Ret (tt, add addr (l_w, v) st)
                 | None =>
                     Ret (tt, add addr (l_w, v) st)
                 end
             end)
    }.

  Definition read: Sec -> Addr -> ctree secE nat :=
    fun (l: Sec) (addr: Addr) => @Ctree.trigger secE secE _ _ (ReSum_refl) (ReSumRet_refl) (Read l addr).
  
  Definition write: Sec -> Addr -> nat -> ctree secE unit :=
    fun (l: Sec) (addr: Addr) (s: nat) => Ctree.trigger (Write l addr s).

  (* Alice (H) writes [secret] to odd addresses *)
  Definition sec_alice1(secret: nat): ctree secE unit :=
    i <- read L 0 ;; 
    if Nat.Even_Odd_dec i then
      write H (i+1) secret
    else
      write H i secret ;;
    write L 0 (S i).
 
  (* Bob (L) reads from even addresses *)
  Definition sec_bob1: ctree secE unit :=
    i <- read L 0 ;; 
    (if Nat.Even_Odd_dec i then
      read L i 
    else
      read L (i+1)) ;;
    write L 0 (S i).

  Definition sec_system(secret: nat) :=
    (* start [i:=1] to avoid conflict with counter at address [0] *)
    write L 0 1 ;;
    forever (fun _ => brS2 (sec_alice1 secret) sec_bob1) tt.

  (* Interpret system with handler (handler_stateT_trace handler_secE) *)
  Definition t_w (secret: nat): ctreeEW secE (unit * St) :=
    interp_state (h_stateT_writerE handler_secE) (sec_system secret) empty.

  Definition reads_secret(e: Bar secE)(secret: nat) :=
    match e with
    | Obs e x =>
        match e return encode e -> Prop with
        | Read L addr => fun x: nat => x = secret
        | _ => fun _ => False
        end x
    end.
  
  Theorem ctl_safety_sec1: forall (secret: nat) (addr: Addr),
      secret <> 0 ->
      <( {(t_w secret, None)}
           |== AG ¬ now {fun '(Obs (Log e) _) => reads_secret e secret })>.
  Proof.
    intros.
    Unset Printing Notations.
    
    unfold t_w, sec_system.
  Admitted.
                
End SecurityEx.
          
          
          
          
  
