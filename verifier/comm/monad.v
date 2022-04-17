From compcert Require Import AST Integers Values Memory.

From bpf.comm Require Import BinrBPF Monad.
From bpf.verifier.comm Require Import state.
From Coq Require Import ZArith.

Definition eval_ins_len : M state.state nat := fun st => Some (eval_ins_len st, st).

Definition eval_ins (idx: int) : M state.state int64 := fun st =>
  if (Int.cmpu Clt idx (Int.repr (Z.of_nat (ins_len st)))) then
    Some (eval_ins idx st, st)
  else
    None.