From Coq Require Import Bool String.
From ITree Require Import Core.Subevent.
From CTree Require Import CTree Eq Logic.CTLwip Logic.CTLtree.

(* Definition of FreeSpec interface contracts, from their paper *)
Record contract (E : Type -> Type) (S : Type) :=
{ witness_update (s : S)
: forall X, E X -> X -> S
; caller_obligation (s : S)
: forall X, E X -> Prop
; callee_obligation (s : S)
: forall (X : Type), E X -> X -> Prop
}.

Definition makeCK {E C X S} `{B0 -< C} (c: contract E S) :=
  makeKV E (B := C) X (obs := (Prop -> Prop) * S)
    (fun '(existT2 _ _ X e x) '(P, s) =>
      (fun P' : Prop => P (c.(caller_obligation _ _) s X e /\ (c.(callee_obligation _ _) s X e x -> P')), c.(witness_update _ _) s X e x)).

Definition respectful_impure {E C X S} `{B0 -< C} (c : contract E S)
  (s : S) (t : ctree E C X) :=
  @satF (makeCK (C := C) (X := X) c) (FAwG (FNow (K := makeCK (C := C) (X := X) c) (fun '(P, _) => P True))) (t, (fun P => P, s)).

(* Store example *)
Section Store.

  Inductive STORE (s : Type) : Type -> Type :=
  | Get : STORE s s
  | Put (x : s) : STORE s unit.

  Arguments Get {s}.
  Arguments Put {s}.

  Definition is_some {A} (o : option A) := match o with | Some _ => True | _ => False end.

  Definition store_contract (s : Type)
  : contract (STORE s) (option s) :=
  {| witness_update :=
    fun ms _ e _ =>
      match e with
      Get => ms | Put x => Some x
      end
  ; caller_obligation :=
    fun ms X (e : STORE s X) =>
      match e with
      Get => is_some ms | Put x => True
      end
  ; callee_obligation :=
    fun ms _ e x =>
      match e, x with
      | Get, x => match ms with
        | Some s => s = x
        | _ => True
        end
      | Put _, _ => True
      end
  |}.

End Store.

(* HTTP server/filesystem access example *)
Section HTTP.

  Parameter socket_descriptor : Type.

  Inductive TCP : Type -> Type :=
  | NewTCPSocket
  : string -> TCP socket_descriptor
  | ListenIncomingConnection
  : socket_descriptor -> TCP unit
  | AcceptConnection
  : socket_descriptor -> TCP socket_descriptor
  | ReadSocket
  : socket_descriptor -> TCP string
  | WriteSocket
  : socket_descriptor -> string -> TCP unit
  | CloseTCPSocket
  : socket_descriptor -> TCP unit.

  Parameter file_descriptor : Type.
  Parameter fd_eqb : file_descriptor -> file_descriptor -> bool.
  Parameter fd_eqb_correct : forall fd fd', fd_eqb fd fd' = true <-> fd = fd'.

  Inductive FILESYSTEM : Type -> Type :=
  | Open (path : string) : FILESYSTEM file_descriptor
  | FileExists (file : string) : FILESYSTEM bool
  | Read (file : file_descriptor) : FILESYSTEM string
  | Close (file : file_descriptor) : FILESYSTEM unit.

  Definition fd_set : Type := file_descriptor -> bool.

  Definition add_fd S fd := fun fd' => (fd_eqb fd fd' || S fd').
  Definition del_fd S fd := fun fd' => negb (fd_eqb fd fd') && S fd'.
  Definition member (S : fd_set) fd := S fd = true.
  Definition absent (S : fd_set) fd := S fd = false.

  Definition fd_set_update (S : fd_set) (a : Type) (e : FILESYSTEM a) (x : a) : fd_set :=
    match e, x with
    | Open _, fd => add_fd S fd
    | Close fd, _ => del_fd S fd
    | Read _, _ => S
    | FileExists _, _ => S
    end.

  Inductive fd_set_caller_obligation (S : fd_set) : forall (a : Type), FILESYSTEM a -> Prop :=
  | fd_set_open_caller (p : string)
  : fd_set_caller_obligation S file_descriptor (Open p)
  | fd_set_read_caller (fd : file_descriptor) (is_member : member S fd)
  : fd_set_caller_obligation S string (Read fd)
  | fd_set_close_caller (fd : file_descriptor) (is_member : member S fd)
  : fd_set_caller_obligation S unit (Close fd)
  | fd_set_is_file_caller (p : string)
  : fd_set_caller_obligation S bool (FileExists p).

  Inductive fd_set_callee_obligation (S : fd_set) : forall (a : Type), FILESYSTEM a -> a -> Prop :=
  | fd_set_open_callee (p : string) (fd : file_descriptor) (is_absent : absent S fd)
  : fd_set_callee_obligation S file_descriptor (Open p) fd
  | fd_set_read_callee (fd : file_descriptor) (s : string)
  : fd_set_callee_obligation S string (Read fd) s
  | fd_set_close_callee (fd : file_descriptor) (t : unit)
  : fd_set_callee_obligation S unit (Close fd) t
  | fd_set_is_file_callee (p : string) (b : bool)
  : fd_set_callee_obligation S bool (FileExists p) b.

  Definition fd_set_contract : contract FILESYSTEM fd_set :=
  {| witness_update := fd_set_update
   ; caller_obligation := fd_set_caller_obligation
   ; callee_obligation := fd_set_callee_obligation
  |}.

  Import CTreeNotations.
  Open Scope ctree_scope.

  Notation file_exists p := (trigger (FileExists p)).
  Notation open p := (trigger (Open p)).
  Notation read fd := (trigger (Read fd)).
  Notation close fd := (trigger (Close fd)).

  Definition read_file (path: string) : ctree FILESYSTEM B0 (option string) :=
    (isf <- file_exists path;;
    if (isf : bool)
    then
      fd <- open path;;
      content <- read fd;;
      close fd;;
      Ret (Some content)
    else Ret None
    ).

  Lemma member_add_fd : forall s x, member (add_fd s x) x.
  Proof.
    intros. compute. destruct (fd_eqb x x) eqn:?.
    reflexivity.
    rewrite (proj2 (fd_eqb_correct x x) eq_refl) in Heqb. discriminate.
  Qed.

  Goal forall (s : fd_set) (path : string),
    respectful_impure fd_set_contract s (read_file path).
  Proof.
    intros. unfold read_file. unfold respectful_impure.
    setoid_rewrite bind_trigger. apply vis_AwG. 1: { cbn. exact I. }
    intros [].
    - rewrite bind_trigger. apply vis_AwG. 1: { cbn. repeat constructor. }
      intros. rewrite bind_trigger. apply vis_AwG. 1: { cbn. repeat constructor. }
      intros. rewrite bind_trigger. apply vis_AwG.
      1: { cbn. repeat constructor. apply member_add_fd. }
      intros []. apply ret_AwG_now.
      cbn. repeat constructor; apply member_add_fd.
    - apply ret_AwG_now. cbn. repeat constructor.
  Qed.

End HTTP.
