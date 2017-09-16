Require Import Arith.
Require Import RelationClasses.
Require Import Eqdep.

Set Implicit Arguments.

(** Free monad over a set of primitive operations. *)
Section Prog.
  (** The type constructor for primitive operations. An [OpT T] represents a
      primitive operation that ultimately returns a T. *)
  Variable OpT : Type -> Type.

  (** A free monad over OpT that sequences primitive [OpT T] values with [Ret]
      and [Bind]. A [prog T] is a computation that returns a T-typed result. It may
      have effects, as described in an relational operational semantics below. *)
  Inductive prog T :=
  | Primitive : OpT T -> prog T
  | Ret : T -> prog T
  | Bind : forall T', prog T' -> (T' -> prog T) -> prog T.

  Variable State : Type.

  (** Parameter providing semantics for every operation. *)
  Variable step : forall T, State -> OpT T -> State -> T -> Prop.

  (** Simple execution semantics: models executing programs to return values.
      Operations can be non-deterministic, but there is no model of failure
      (instead the program just "gets stuck"). *)
  Inductive exec : forall T, State -> prog T -> State -> T -> Prop :=
  | exec_Ret : forall T (v:T)
                 s, exec s (Ret v) s v
  | exec_Bind : forall T (p: prog T) T' (p': T -> prog T')
                  s s' v s'' v',
      exec s p s' v ->
      exec s' (p' v) s'' v' ->
      exec s (Bind p p') s'' v'
  | exec_Primitive : forall T (op: OpT T)
                       s s' v,
      step s op s' v ->
      exec s (Primitive op) s' v.

  (** We prove that the semantics respect the monad laws (the obvious property
      they should satisfy). *)

  Definition exec_equiv T (p p': prog T) :=
    (forall s s' v, exec s p s' v -> exec s p' s' v) /\
    (forall s s' v, exec s p' s' v -> exec s p s' v).

  Instance exec_equiv_Equivalence T : Equivalence (exec_equiv (T:=T)).
  Proof.
    unfold exec_equiv; constructor; hnf;
      intuition auto.
  Defined.

  Hint Constructors exec.

  Ltac inv_existT :=
    match goal with
    | [ H: existT ?P ?p _ = existT ?P ?p _ |- _ ] =>
      apply inj_pair2 in H; subst
    end.

  Ltac inv_exec :=
    repeat match goal with
           | [ H: exec _ (Ret _) _ _ |- _ ] =>
             inversion H; subst; clear H;
             repeat inv_existT
           | [ H: exec _ (Bind _ _) _ _ |- _ ] =>
             inversion H; subst; clear H;
             repeat inv_existT
           end; eauto.

  Theorem monad_left_id : forall T (v:T) T' (p': T -> prog T'),
      exec_equiv (Bind (Ret v) p') (p' v).
  Proof.
    unfold exec_equiv; (intuition idtac);
      inv_exec.
  Qed.

  Theorem monad_right_id : forall T (p: prog T),
      exec_equiv (Bind p (Ret (T:=T))) p.
  Proof.
    unfold exec_equiv; (intuition idtac);
      inv_exec.
  Qed.

  Theorem monad_bind_assoc : forall T1 (p1: prog T1)
                               T2 (p2: T1 -> prog T2)
                               T3 (p3: T2 -> prog T3),
      exec_equiv (Bind (Bind p1 p2) p3)
                 (Bind p1 (fun x => Bind (p2 x) p3)).
  Proof.
    unfold exec_equiv; (intuition idtac);
      inv_exec.
  Qed.

End Prog.

(** Example of programs that can read and write an input file, with a simple
byte interface. *)

(** We just uses natural numbers as offsets into the file. *)
Definition offset := nat.
Axiom byte : Type.

Inductive FileOp : Type -> Type :=
| Read : offset -> FileOp byte
| Write : offset -> byte -> FileOp unit
| FileSize : FileOp nat.

Definition File := list byte.

Open Scope list.

Fixpoint fileGet (d:File) (a:nat) : option byte :=
  match d, a with
  | nil, _ => None
  | b::_, 0 => Some b
  | _::tl, S a => fileGet tl a
  end.

Fixpoint fileUpd (d:File) (a:nat) (v:byte) : File :=
  match d, a with
  | nil, _ => d
  | _::tl, 0 => v::tl
  | b::tl, S a => b :: fileUpd tl a v
  end.

Inductive file_step : forall T, File -> FileOp T -> File -> T -> Prop :=
(** out-of-bounds reads get stuck *)
| step_read : forall d a v,
    fileGet d a = Some v ->
    file_step d (Read a) d v
(** out-of-bounds writes also get stuck, though we could choose to model them as
    growing the file *)
| step_write : forall d a v0 v',
    fileGet d a = Some v0 ->
    file_step d (Write a v') (fileUpd d a v') tt
(** programs can also ask for the size of the file *)
| step_size : forall d,
    file_step d (FileSize) d (length d).

Definition fileProg T := prog FileOp T.

Definition fileExec := exec file_step.

Arguments Primitive {OpT} {T} op.

Notation "x <- p1 ; p2" := (Bind p1 (fun x => p2))
                            (at level 60, right associativity).

(** Simple example of a program that copies a byte from one location to another.
 *)
Definition copy (a a': offset) : fileProg unit :=
  v <- Primitive (Read a);
    Primitive (Write a' v).

Require Extraction.

Require Import ExtrHaskellBasic.
Require Import ExtrHaskellNatInteger.

Extraction Language Haskell.

Extract Constant byte => "GHC.Base.Char".

(** Extract the syntax for file programs and our simple example program.

Due to a limitation of Coq's extraction, the prog type cannot be properly
extracted to Haskell; the OpT index to the type is higher-kinded ([* -> *]),
which is unsupported in OCaml and also in the intermediate language Coq
extraction uses.
 *)
Extraction "Prog.hs" fileProg copy.

(* Local Variables: *)
(* company-coq-local-symbols: (("State" . ?Σ)) *)
(* End: *)
