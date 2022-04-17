From bpf.dxcomm Require Import DxIntegers.

From bpf.comm Require Import Monad.
From bpf.verifier.comm Require Import state monad.

Definition M (A: Type) := M state.state A.

Definition returnM {A: Type} (a: A) : M A := returnM a.
Definition bindM {A B: Type} (x: M A) (f: A -> M B) : M B := bindM x f.

Definition eval_ins_len : M nat := monad.eval_ins_len.

Definition eval_ins (idx: uint32_t) : M int64_t := monad.eval_ins idx.

Declare Scope monad_scope.
Notation "'do' x <-- a ; b" :=
  (bindM a (fun x => b))
    (at level 200, x name, a at level 100, b at level 200)
  : monad_scope.