From bpf.comm Require Import rBPFAST List64 MemRegion Regs Flag.

From Coq Require Import List Lia ZArith.
From compcert Require Import Integers Values Clight Memory AST.
Import ListNotations.

From bpf.verifier.comm Require Import state monad.
From bpf.clightlogic Require Import CommonLib.
From bpf.verifier.simulation Require Import VerifierSimulation.

Open Scope Z_scope.
(*
Definition ins_int32_correct (x: int) (v: val) (st: state.state) (m:Mem.mem) :=
  Vint x = v /\ Int.cmpu Clt x (Int.repr (Z.of_nat (ins_len st))) = true.
*)

Definition val_ptr_correct {S:special_blocks} (x:val) (v: val) (st: state.state) (m:Mem.mem) :=
  x = v /\
  match_state  st m.


Open Scope nat_scope.

Definition is_state_handle {S: special_blocks} (v: val) := v = Vptr st_blk Ptrofs.zero.

Close Scope nat_scope.