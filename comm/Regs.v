From compcert.cfrontend Require Csyntax Ctypes Cop.
From compcert.common Require Import Values Memory.
From compcert.lib Require Import Integers.

From bpf.comm Require Import rBPFValues.
From Coq Require Import List ZArith.
Import ListNotations.


Inductive reg: Type :=
  | R0:reg | R1:reg | R2:reg
  | R3:reg | R4:reg | R5:reg
  | R6:reg | R7:reg | R8:reg
  | R9:reg | R10:reg
.

Lemma reg_eq: forall (x y: reg), {x=y} + {x<>y}.
Proof.
decide equality. Defined.

Record regmap: Type := make_regmap{
  r0_val  : Values.val;
  r1_val  : Values.val;
  r2_val  : Values.val;
  r3_val  : Values.val;
  r4_val  : Values.val;
  r5_val  : Values.val;
  r6_val  : Values.val;
  r7_val  : Values.val;
  r8_val  : Values.val;
  r9_val  : Values.val;
  r10_val : Values.val;
}.

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

Definition upd_regmap (r:reg) (v:val) (regs:regmap): regmap :=
  match r with
  | R0  => 
    {|
      r0_val  := v;
      r1_val  := r1_val regs;
      r2_val  := r2_val regs;
      r3_val  := r3_val regs;
      r4_val  := r4_val regs;
      r5_val  := r5_val regs;
      r6_val  := r6_val regs;
      r7_val  := r7_val regs;
      r8_val  := r8_val regs;
      r9_val  := r9_val regs;
      r10_val := r10_val regs;
    |} 
  | R1  => 
    {|
      r0_val  := r0_val regs;
      r1_val  := v;
      r2_val  := r2_val regs;
      r3_val  := r3_val regs;
      r4_val  := r4_val regs;
      r5_val  := r5_val regs;
      r6_val  := r6_val regs;
      r7_val  := r7_val regs;
      r8_val  := r8_val regs;
      r9_val  := r9_val regs;
      r10_val := r10_val regs;
    |}
  | R2  => 
    {|
      r0_val  := r0_val regs;
      r1_val  := r1_val regs;
      r2_val  := v;
      r3_val  := r3_val regs;
      r4_val  := r4_val regs;
      r5_val  := r5_val regs;
      r6_val  := r6_val regs;
      r7_val  := r7_val regs;
      r8_val  := r8_val regs;
      r9_val  := r9_val regs;
      r10_val := r10_val regs;
    |} 
  | R3  => 
    {|
      r0_val  := r0_val regs;
      r1_val  := r1_val regs;
      r2_val  := r2_val regs;
      r3_val  := v;
      r4_val  := r4_val regs;
      r5_val  := r5_val regs;
      r6_val  := r6_val regs;
      r7_val  := r7_val regs;
      r8_val  := r8_val regs;
      r9_val  := r9_val regs;
      r10_val := r10_val regs;
    |} 
  | R4  => 
    {|
      r0_val  := r0_val regs;
      r1_val  := r1_val regs;
      r2_val  := r2_val regs;
      r3_val  := r3_val regs;
      r4_val  := v;
      r5_val  := r5_val regs;
      r6_val  := r6_val regs;
      r7_val  := r7_val regs;
      r8_val  := r8_val regs;
      r9_val  := r9_val regs;
      r10_val := r10_val regs;
    |} 
  | R5  => 
    {|
      r0_val  := r0_val regs;
      r1_val  := r1_val regs;
      r2_val  := r2_val regs;
      r3_val  := r3_val regs;
      r4_val  := r4_val regs;
      r5_val  := v;
      r6_val  := r6_val regs;
      r7_val  := r7_val regs;
      r8_val  := r8_val regs;
      r9_val  := r9_val regs;
      r10_val := r10_val regs;
    |} 
  | R6  => 
    {|
      r0_val  := r0_val regs;
      r1_val  := r1_val regs;
      r2_val  := r2_val regs;
      r3_val  := r3_val regs;
      r4_val  := r4_val regs;
      r5_val  := r5_val regs;
      r6_val  := v;
      r7_val  := r7_val regs;
      r8_val  := r8_val regs;
      r9_val  := r9_val regs;
      r10_val := r10_val regs;
    |} 
  | R7  => 
    {|
      r0_val  := r0_val regs;
      r1_val  := r1_val regs;
      r2_val  := r2_val regs;
      r3_val  := r3_val regs;
      r4_val  := r4_val regs;
      r5_val  := r5_val regs;
      r6_val  := r6_val regs;
      r7_val  := v;
      r8_val  := r8_val regs;
      r9_val  := r9_val regs;
      r10_val := r10_val regs;
    |} 
  | R8  => 
    {|
      r0_val  := r0_val regs;
      r1_val  := r1_val regs;
      r2_val  := r2_val regs;
      r3_val  := r3_val regs;
      r4_val  := r4_val regs;
      r5_val  := r5_val regs;
      r6_val  := r6_val regs;
      r7_val  := r7_val regs;
      r8_val  := v;
      r9_val  := r9_val regs;
      r10_val := r10_val regs;
    |} 
  | R9  => 
    {|
      r0_val  := r0_val regs;
      r1_val  := r1_val regs;
      r2_val  := r2_val regs;
      r3_val  := r3_val regs;
      r4_val  := r4_val regs;
      r5_val  := r5_val regs;
      r6_val  := r6_val regs;
      r7_val  := r7_val regs;
      r8_val  := r8_val regs;
      r9_val  := v;
      r10_val := r10_val regs;
    |} 
  | R10 => 
    {|
      r0_val  := r0_val regs;
      r1_val  := r1_val regs;
      r2_val  := r2_val regs;
      r3_val  := r3_val regs;
      r4_val  := r4_val regs;
      r5_val  := r5_val regs;
      r6_val  := r6_val regs;
      r7_val  := r7_val regs;
      r8_val  := r8_val regs;
      r9_val  := r9_val regs;
      r10_val := v;
    |} 
  end.

Definition val64_zero := Vlong Int64.zero.

Definition init_regmap: regmap := {|
  r0_val  := val64_zero;
  r1_val  := val64_zero;
  r2_val  := val64_zero;
  r3_val  := val64_zero;
  r4_val  := val64_zero;
  r5_val  := val64_zero;
  r6_val  := val64_zero;
  r7_val  := val64_zero;
  r8_val  := val64_zero;
  r9_val  := val64_zero;
  r10_val := val64_zero;
|}.

Open Scope Z_scope.

Definition z_to_reg (z:Z): reg :=
  if (Z.eqb z 0) then
    R0
  else if (Z.eqb z 1) then
    R1
  else if (Z.eqb z 2) then
    R2
  else if (Z.eqb z 3) then
    R3
  else if (Z.eqb z 4) then
    R4
  else if (Z.eqb z 5) then
    R5
  else if (Z.eqb z 6) then
    R6
  else if (Z.eqb z 7) then
    R7
  else if (Z.eqb z 8) then
    R8
  else if (Z.eqb z 9) then
    R9
  else
    R10.

Definition get_dst (i:int64):Z := Int64.unsigned (Int64.shru (Int64.and i (Int64.repr 0xfff)) (Int64.repr 8)).
Definition get_src (i:int64):Z := Int64.unsigned (Int64.shru (Int64.and i (Int64.repr 0xffff)) (Int64.repr 12)).

Definition int64_to_dst_reg (ins: int64): reg :=
  z_to_reg (get_dst ins).

Definition int64_to_src_reg (ins: int64): reg :=
  z_to_reg (get_src ins).

Definition get_opcode (ins:int64): nat := Z.to_nat (Int64.unsigned (Int64.and ins (Int64.repr 0xff))).

Definition get_offset (i:int64) := sint16_to_sint32 (int64_to_sint16 (Int64.shru (Int64.shl i (Int64.repr 32)) (Int64.repr 48))).

Definition get_immediate (i1:int64) := int64_to_sint32 (Int64.shru i1 (Int64.repr 32)).