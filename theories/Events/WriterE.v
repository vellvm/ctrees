From CTree Require Import
  Events.Core.

Set Implicit Arguments.
Generalizable All Variables.

(*| Writer events |*)
Section Writer.
  Variable (S : Type).
  Variant writerE : Type :=
    | Log : S -> writerE.
  
  #[global] Instance encode_writerE: Encode writerE :=
    fun e => unit.

End Writer.

Arguments Log {S}.

