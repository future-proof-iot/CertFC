From compcert.cfrontend Require Csyntax Ctypes Cop.
From compcert.common Require Values Memory.
From compcert.lib Require Import Integers.

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

Definition eval_regmap (r:reg) (regs:regmap): val64_t := 
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

Definition upd_regmap (r:reg) (v:val64_t) (regs:regmap): regmap :=
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


Definition z_to_reg (z:Z): reg :=
  if (Z.eqb z 0%Z) then
    R0
  else if (Z.eqb z 1%Z) then
    R1
  else if (Z.eqb z 2%Z) then
    R2
  else if (Z.eqb z 3%Z) then
    R3
  else if (Z.eqb z 4%Z) then
    R4
  else if (Z.eqb z 5%Z) then
    R5
  else if (Z.eqb z 6%Z) then
    R6
  else if (Z.eqb z 7%Z) then
    R7
  else if (Z.eqb z 8%Z) then
    R8
  else if (Z.eqb z 9%Z) then
    R9
  else
    R10.

Definition get_dst (i:int64_t):Z := Int64.unsigned (Int64.shru (Int64.and i int64_0xfff) int64_8).
Definition get_src (i:int64_t):Z := Int64.unsigned (Int64.shru (Int64.and i int64_0xffff) int64_12).

Definition int64_to_dst_reg (ins: int64_t): reg :=
  z_to_reg (get_dst ins).

Definition int64_to_src_reg (ins: int64_t): reg :=
  z_to_reg (get_src ins).


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

Definition Const_R2 := constant regSymbolType R2 C_U32_2.

Definition Const_R3 := constant regSymbolType R3 C_U32_3.

Definition Const_R4 := constant regSymbolType R4 C_U32_4.

Definition Const_R5 := constant regSymbolType R5 C_U32_5.

Definition Const_R6 := constant regSymbolType R6 C_U32_6.

Definition Const_R7 := constant regSymbolType R7 C_U32_7.

Definition Const_R8 := constant regSymbolType R8 C_U32_8.

Definition Const_R9 := constant regSymbolType R9 C_U32_9.

Definition Const_R10 := constant regSymbolType R10 C_U32_10.

(** So, the compcert switch_case only supports case based on Some Z? and None corresponds to default!!!

(Csyntax.Sswitch x
              (Csyntax.LScons (Some 0%Z) r0
                (Csyntax.LScons None r1
                  Csyntax.LSnil))
            )
where x:Csyntax.expr, (Some 0%Z) <=> expr1, ... None <=> default, r0:Csyntax.statement <=> statement1
===>

switch (expression) {
  case expr1: statement1
  case expr2: statement2
  ...
  default: ...
}

  *)
Definition regMatchableType :=
  MkMatchableType regCompilableType
    (fun x cases =>
      match cases with
      | [r0; r1; r2; r3; r4; r5; r6; r7; r8; r9; r10] =>
        Ok (Csyntax.Sswitch x
              (Csyntax.LScons (Some 0%Z) r0
                (Csyntax.LScons (Some 1%Z) r1
                  (Csyntax.LScons (Some 2%Z) r2
                    (Csyntax.LScons (Some 3%Z) r3
                      (Csyntax.LScons (Some 4%Z) r4
                          Csyntax.LSnil)))))
            )
      | _ => Err MatchEncodingFailed
      end)
    [[]; []; []; []; []; []; []; []; []; []; []]
    [[]; []; []; []; []; []; []; []; []; []; []]
    (fun m A r whenR0 whenR1 whenR2 whenR3 whenR4 whenR5 whenR6 whenR7 whenR8 whenR9 whenR10 =>
      match r with
      | R0 => whenR0
      | R1 => whenR1
      | R2 => whenR2
      | R3 => whenR3
      | R4 => whenR4
      | R5 => whenR5
      | R6 => whenR6
      | R7 => whenR7
      | R8 => whenR8
      | R9 => whenR9
      | R10 => whenR10
      end).

Definition int64ToregSymbolType :=
  MkCompilableSymbolType [int64CompilableType] (Some regCompilableType).

Definition Const_int64_to_dst_reg :=
  MkPrimitive int64ToregSymbolType
                int64_to_dst_reg
                (fun es => match es with
                           | [e1] => Ok (Csyntax.Ecast (Csyntax.Ebinop Cop.Oshr
                                          (Csyntax.Ebinop Cop.Oand e1 C_U64_0xfff C_U64)
                                          C_U64_8 C_U64) C_U32)
                           | _       => Err PrimitiveEncodingFailed
                           end).

Definition Const_int64_to_src_reg :=
  MkPrimitive int64ToregSymbolType
                int64_to_src_reg
                (fun es => match es with
                           | [e1] => Ok (Csyntax.Ecast (Csyntax.Ebinop Cop.Oshr
                                          (Csyntax.Ebinop Cop.Oand e1 C_U64_0xffff C_U64)
                                          C_U64_12 C_U64) C_U32)
                           | _       => Err PrimitiveEncodingFailed
                           end).


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

Module Exports.
  Definition regMatchableType := regMatchableType.
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
  Definition Const_int64_to_dst_reg := Const_int64_to_dst_reg.
  Definition Const_int64_to_src_reg := Const_int64_to_src_reg.
  Definition regmapCompilableType := regmapCompilableType.
  Definition Const_eval_regmap := Const_eval_regmap.
  Definition Const_upd_regmap  := Const_upd_regmap.
End Exports.