From dx.tests Require Import DxIntegers DxValues DxMemRegion DxRegs DxState DxMonad DxInstructions.
From Coq Require Import List Lia.
From compcert Require Import Integers Values Clight Memory AST.
Import ListNotations.
Require Import ZArith.

From bpf.proof Require Import Clightlogic MatchState.

Definition int64_correct (x:int64_t) (v: val) (stm:stateM) (m: Memory.Mem.mem) :=
  Vlong x = v.

Definition val64_correct (x:val64_t) (v: val) :=
  x = v /\ exists vl, x = Vlong vl.


Definition reg_correct (r: reg) (v: val) (stm:stateM) (m: Memory.Mem.mem) :=
  (*complu_lt_32 v (Vint (Int.repr 11)) = true /\ (**r ensured by verifier *) *)
    v = Vint (Int.repr (id_of_reg r)).


Definition match_chunk (x : memory_chunk) (b: val) :=
  b = Vint (
          match x with
          | Mint8unsigned => Integers.Int.one
          | Mint16unsigned => Integers.Int.repr 2
          | Mint32 => Integers.Int.repr 4
          | Mint64 => Integers.Int.repr 8
          | _ => Integers.Int.repr 0
          end).
