From Coq Require Import ZArith.
From Coq Require Import List.
Import ListNotations.

From compcert.cfrontend Require Csyntax Ctypes Cop.
From compcert.common Require Values.
From compcert.lib Require Integers.

From dx Require Import ResultMonad IR.

Inductive reg: Type :=
  | R0:reg | R1:reg | R2:reg
  | R3:reg | R4:reg | R5:reg
  | R6:reg | R7:reg | R8:reg
  | R9:reg | R10:reg.

(*
Coq src:
Inductive reg: Type :=
  | R0:reg | R1:reg | R2:reg
  | R3:reg | R4:reg | R5:reg
  | R6:reg | R7:reg | R8:reg
  | R9:reg | R10:reg

C dst (as index):
0 | 1 | 2 | ... | 10
 *)

(*
Coq src:
Record regmap: Type := make_regmap{
  r0_val  : val;
  r1_val  : val;
  r2_val  : val;
  r3_val  : val;
  r4_val  : val;
  r5_val  : val;
  r6_val  : val;
  r7_val  : val;
  r8_val  : val;
  r9_val  : val;
  r10_val : val;
}.

C dst:

uint64_t regmap[11];

  or
struct regmap {
  uint64_t r0_val;
  ...
  uint64_t r10_val;
};
 *)

(*
Coq src:
Definition eval_regmap (r:reg) (regs:regmap): val := 
  match r with
  | R0  => r0_val regs
  | R1  => r1_val regs
  | R2  => r2_val regs
  | R3  => r3_val regs
  | R4  => r4_val regs
  | R5  => r5_val regs
  | R6  => r6_val regs
  | R7  => r7_val regs
  | R8  => r8_val regs
  | R9  => r9_val regs
  | R10 => r10_val regs
  end.

C dst:

uint64_t eval_regmap (int r){
  return regs[r];
}

or

uint64_t eval_regmap (int r, uint64_t regs[]){
  switch (r){
  case 0: return regs[0]; break;
  ...
  case 10: return regs[10]; break;
  default: exit;//
  }
}

 *)

