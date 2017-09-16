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

(** Example of programs that can read and write a disk, with a simple byte
interface. *)

(** We just uses natural numbers as addresses to the disk. *)
Definition addr := nat.
Axiom byte : Type.

Inductive DiskOp : Type -> Type :=
| Read : addr -> DiskOp byte
| Write : addr -> byte -> DiskOp unit.

(** A disk maps addresses to bytes. Not all addresses map to values (since the
disk is finite). *)
Definition Disk := addr -> option byte.

Definition upd (d:Disk) (a:nat) (v:byte) : Disk :=
  fun a' => if Nat.eq_dec a a' then Some v else d a.

Inductive disk_step : forall T, Disk -> DiskOp T -> Disk -> T -> Prop :=
  (** out-of-bounds reads get stuck *)
| step_read : forall d a v,
    d a = Some v ->
    disk_step d (Read a) d v
(** out-of-bounds writes also get stuck  *)
| step_write : forall d a v0 v',
    d a = Some v0 ->
    disk_step d (Write a v') (upd d a v') tt.

Definition diskProg T := prog DiskOp T.

Definition diskExec := exec disk_step.

Arguments Primitive {OpT} {T} op.

Notation "x <- p1 ; p2" := (Bind p1 (fun x => p2))
                            (at level 60, right associativity).

Definition copy a a' :=
  v <- Primitive (Read a);
    Primitive (Write a' v).

Require Extraction.

Require Import ExtrHaskellBasic.
Require Import ExtrHaskellNatInteger.

Extraction Language Haskell.

Extract Constant byte => "GHC.Base.Char".

(** Extract the syntax for disk programs and our simple example program.

Due to a limitation of Coq's extraction, the prog type cannot be properly
extracted to Haskell; the OpT index to the type is higher-kinded ([* -> *]),
which is unsupported in OCaml and also in the intermediate language Coq
extraction uses.
 *)
Extraction "Prog.hs" diskProg copy.

(* Local Variables: *)
(* company-coq-local-symbols: (("State" . ?Σ)) *)
(* End: *)
