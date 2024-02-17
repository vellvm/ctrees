(*| Useful instructions: IO (files) |*)
From CTree Require Import
  Classes
  CTree.Core.

From CTree Require Import
  Events.Core.

From ExtLib Require Import
  Structures.MonadState
  Data.Monads.StateMonad
  Structures.Maps.

Generalizable All Variables.

(*| Read, write, open, close |*)
Section IO.
  Notation fd := nat.
  Context `{MF: Map fd bool stF} `{MB: Map fd str stS}
    `{OF: MapOk fd bool stF eq} `{OS: MapOk fd str stS eq}.
  
  Variant ioE : Type :=
    | Fresh: ioE
    | Read: fd -> ioE
    | Write: fd -> str -> ioE
    | Open: fd -> ioE
    | Close : fd -> ioE.

  #[global] Instance encode_ioE: Encode ioE :=
    fun e => match e with
          | Fresh => fd
          | Read f => option str
          | Write f s => bool
          | Open f => bool
          | Close f => bool
          end.

  Definition h_ioE: ioE ~> state (fd * stF * stS) :=
      fun e =>
        mkState
          (fun '(i, σf, σs) =>                                      (* A fd counter [i] and state [σ] *)
             match e return (encode e * (fd * stF * stS)) with
             | Fresh =>                                           (* Create a new [fd] *)
                 (i, (S i, add i false σf, σs))                  (* Increase counter [i], add [i] to state *)
             | Read f =>                                          (* Handle [Read] from fd [f] *)
                 match lookup f σf, lookup f σs with             (* If fd [f] is open *)
                 | Some true, Some s => (Some s, (i, σf, σs))     (* Return contents [s] of [f] *)
                 | _ , _ => (None, (i, σf, σs))                   (* [f] closed, return [None] *)
                 end
             | Write f s =>                                       (* Write [s] to fd [f] *)
                 match lookup f σf with                          (* If [f] is open *)
                 | Some true =>
                     (true, (i, σf, add i s σs))                 (* Write [s] to [f] *)
                 | _ => (false, (i, σf, σs))                      (* [f] closed, return [false] *)
                 end
             | Open f =>                               
                 match lookup f σf with                          (* If [f] is open *)
                 | Some false =>
                     (true, (i, add f true σf, σs))              (* [f] closed, set open flag to [true] *)
                 | _ => (false, (i, σf, σs))                      (* Fail on double-open *)
                 end                                        
             | Close f =>                                         (* Close an open fd [f] *)
                 match lookup f σf  with                         (* If [f] is open *)
                 | Some true =>
                     (true, (i, add f false σf, σs))             (* Close it, return [true] *)
                 | _ => (false, (i, σf, σs))                      (* Fail on double-close *)
                 end
             end).
  
End IO.

Arguments ioE str: clear implicits.
