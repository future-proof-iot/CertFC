From Coq Require Import Arith ZArith Bool.
From compcert Require Import Coqlib Integers AST Ctypes Values Maps.
From dx.tests Require Import Int16.

Inductive reg: Type :=
  | R0:reg | R1:reg | R2:reg
  | R3:reg | R4:reg | R5:reg
  | R6:reg | R7:reg | R8:reg
  | R9:reg | R10:reg
.
Lemma reg_eq: forall (x y: reg), {x=y} + {x<>y}.
Proof.
decide equality. Defined.

Definition imm := int.
Definition off := int16.

Inductive instruction: Type :=
  (**r ALU64/32*)
  | BPF_NEG32    : reg -> instruction
  | BPF_NEG64    : reg -> instruction
  | BPF_ADD32r   : reg -> reg -> instruction
  | BPF_ADD32i   : reg -> imm -> instruction
  | BPF_ADD64r   : reg -> reg -> instruction
  | BPF_ADD64i   : reg -> imm -> instruction
  | BPF_RET      : instruction.

Inductive bpf_flag: Type := 
  | BPF_OK                  (**r =  0, *)
  | BPF_ILLEGAL_INSTRUCTION (**r = -1, *)
  | BPF_ILLEGAL_MEM         (**r = -2, *)
  | BPF_ILLEGAL_JUMP        (**r = -3, *)
  | BPF_ILLEGAL_CALL        (**r = -4, *)
  | BPF_ILLEGAL_LEN         (**r = -5, *)
  | BPF_ILLEGAL_REGISTER    (**r = -6  *)
  | BPF_NO_RETURN           (**r = -7, *)
  | BPF_OUT_OF_BRANCHES     (**r = -8, *)
  | BPF_ILLEGAL_DIV         (**r = -9, *)
  | BPF_ILLEGAL_SHIFT       (**r = -10,*)
  | BPF_ILLEGAL_ALU         (**r = -11,*)
.
Lemma bpf_flag_eq: forall (x y: bpf_flag), {x=y} + {x<>y}.
Proof.
decide equality. Defined.

Definition get_opcode (i:int64):Z := (Int64.unsigned (Int64.and i (Int64.repr 0xff))).
Definition get_dst (i:int64):nat := Z.to_nat (Int64.unsigned (Int64.shru (Int64.and i (Int64.repr 0xfff)) (Int64.repr 8))).
Definition get_src (i:int64):nat := Z.to_nat (Int64.unsigned (Int64.shru (Int64.and i (Int64.repr 0xffff)) (Int64.repr 12))).
Definition get_offset (i:int64):int16 := Int16.repr (Int64.unsigned (Int64.shru (Int64.shl i (Int64.repr 32)) (Int64.repr 48))).
Definition get_immediate (i:int64):int := Int.repr (Int64.unsigned (Int64.shru i (Int64.repr 32))).

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

Definition VLzero: val := Vlong Int64.zero.

Definition init_regmap: regmap := {|
  r0_val  := VLzero;
  r1_val  := VLzero;
  r2_val  := VLzero;
  r3_val  := VLzero;
  r4_val  := VLzero;
  r5_val  := VLzero;
  r6_val  := VLzero;
  r7_val  := VLzero;
  r8_val  := VLzero;
  r9_val  := VLzero;
  r10_val := VLzero;
|}.