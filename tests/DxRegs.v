From compcert.cfrontend Require Csyntax Ctypes Cop.
From compcert.common Require Values Memory.
From compcert.lib Require Integers.

From dx Require Import ResultMonad IR.
From dx.Type Require Bool Nat.

Require Import IdentDef CoqIntegers DxIntegers DxValues.

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

Definition eval_regmap (r:reg) (regs:regmap): Values.val := 
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

Definition upd_regmap (r:reg) (v:Values.val) (regs:regmap): regmap :=
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

Definition VLzero: Values.val := Values.Vlong Integers.Int64.zero.

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

Record regs_state: Type := make_rst{
  pc    : nat;
  regs  : regmap;
}.

Definition state: Type := Memory.mem * regs_state.

(******************** Dx Related *******************)

(** Coq2C: reg -> unsigned int;
           matchableType: R_i -> i,  i.e. R0 -> 0
  *)

Definition regCompilableType :=
  MkCompilableType reg C_U32.

Definition regSymbolType :=
  MkCompilableSymbolType nil (Some regCompilableType).

Definition Const_R0 := constant regSymbolType R0 C_U32_zero.

Definition Const_R1 := constant regSymbolType R1 C_U32_one.

Definition Const_R2 := constant regSymbolType R2 C_U32_two.

Definition Const_R3 := constant regSymbolType R3 C_U32_three.

Definition Const_R4 := constant regSymbolType R4 C_U32_four.

Definition Const_R5 := constant regSymbolType R5 C_U32_five.

Definition Const_R6 := constant regSymbolType R6 C_U32_six.

Definition Const_R7 := constant regSymbolType R7 C_U32_seven.

Definition Const_R8 := constant regSymbolType R8 C_U32_eight.

Definition Const_R9 := constant regSymbolType R9 C_U32_nine.

Definition Const_R10 := constant regSymbolType R10 C_U32_ten.

(** Coq2C: regmap -> unsigned long long int regmap[11];
  *)
Definition C_regmap: Ctypes.type := Ctypes.Tarray C_U64 11%Z Ctypes.noattr.

Definition regmapCompilableType := MkCompilableType regmap C_regmap.

(** Type signature: reg -> regmap -> val64
  *)
Definition regToregmapToVal64SymbolType :=
  MkCompilableSymbolType [regCompilableType; regmapCompilableType] (Some val64CompilableType).

Definition Const_eval_regmap :=
  MkPrimitive regToregmapToVal64SymbolType
                eval_regmap
                (fun es => match es with
                           | [e1; e2] => Ok (Csyntax.Eindex e2 e1 C_U64)
                           | _       => Err PrimitiveEncodingFailed
                           end).

(** Type signature: reg -> val64 -> regmap -> regmap
  *)
Definition regToval64ToregmapToregmapSymbolType :=
  MkCompilableSymbolType [regCompilableType; val64CompilableType; regmapCompilableType] (Some regmapCompilableType).

Definition Const_upd_regmap :=
  MkPrimitive regToval64ToregmapToregmapSymbolType
                upd_regmap
                (fun es => match es with
                           | [r; v; regmap] => Ok (
                              Csyntax.Eassign
                              (Csyntax.Eindex regmap r C_U64)
                              (Csyntax.Evalof v C_U64)
                              C_U64)
                           | _       => Err PrimitiveEncodingFailed
                           end).

(** Coq2C: state -> 
            struct state {
              unsigned int pc;
              unsigned long long regmap[11];
            };
  *)

Definition state_struct_type: Ctypes.type := Ctypes.Tstruct state_id Ctypes.noattr.

Definition state_struct_def: Ctypes.composite_definition := 
  Ctypes.Composite state_id Ctypes.Struct [(pc_id, C_U32); (regmaps_id, C_regmap)] Ctypes.noattr.

Module Exports.
  Definition regCompilableType := regCompilableType.
  Definition Const_R0  := Const_R0.
  Definition Const_R1  := Const_R1.
  Definition Const_R2  := Const_R2.
  Definition Const_R3  := Const_R3.
  Definition Const_R4  := Const_R4.
  Definition Const_R5  := Const_R5.
  Definition Const_R6  := Const_R6.
  Definition Const_R7  := Const_R7.
  Definition Const_R8  := Const_R8.
  Definition Const_R9  := Const_R9.
  Definition Const_R10 := Const_R10.
  Definition regmapCompilableType := regmapCompilableType.
  Definition Const_eval_regmap := Const_eval_regmap.
  Definition Const_upd_regmap  := Const_upd_regmap.
End Exports.