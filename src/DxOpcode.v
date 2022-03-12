From Coq Require Import List ZArith.
Import ListNotations.

From compcert Require Import Integers.

From dx Require Import ResultMonad IR.

From bpf.src Require Import CoqIntegers DxIntegers DxNat InfComp GenMatchable.

From bpf.monadicmodel Require Import Opcode.


(******************** Dx related *******************)

Definition opcode_alu64_eqb  (o o' : opcode_alu64): bool :=
  match o , o' with
  | op_BPF_ADD64, op_BPF_ADD64
  | op_BPF_SUB64, op_BPF_SUB64
  | op_BPF_MUL64, op_BPF_MUL64
  | op_BPF_DIV64, op_BPF_DIV64
  | op_BPF_OR64,  op_BPF_OR64
  | op_BPF_AND64, op_BPF_AND64
  | op_BPF_LSH64, op_BPF_LSH64
  | op_BPF_RSH64, op_BPF_RSH64
  | op_BPF_NEG64,  op_BPF_NEG64
  | op_BPF_MOD64, op_BPF_MOD64
  | op_BPF_XOR64, op_BPF_XOR64
  | op_BPF_MOV64, op_BPF_MOV64
  | op_BPF_ARSH64,op_BPF_ARSH64
  | op_BPF_ALU64_ILLEGAL_INS, op_BPF_ALU64_ILLEGAL_INS => true
  | _, _ => false
  end.

Definition opcode_alu32_eqb  (o o' : opcode_alu32) : bool :=
  match o , o' with
  | op_BPF_ADD32, op_BPF_ADD32
  | op_BPF_SUB32, op_BPF_SUB32
  | op_BPF_MUL32, op_BPF_MUL32
  | op_BPF_DIV32, op_BPF_DIV32
  | op_BPF_OR32,  op_BPF_OR32
  | op_BPF_AND32, op_BPF_AND32
  | op_BPF_LSH32, op_BPF_LSH32
  | op_BPF_RSH32, op_BPF_RSH32
  | op_BPF_NEG32,  op_BPF_NEG32
  | op_BPF_MOD32, op_BPF_MOD32
  | op_BPF_XOR32, op_BPF_XOR32
  | op_BPF_MOV32, op_BPF_MOV32
  | op_BPF_ALU32_ILLEGAL_INS, op_BPF_ALU32_ILLEGAL_INS => true
  | _, _ => false
  end.

Definition opcode_branch_eqb (o o' : opcode_branch): bool :=
  match o , o' with
  | op_BPF_JA,    op_BPF_JA
  | op_BPF_JEQ,   op_BPF_JEQ
  | op_BPF_JGT,   op_BPF_JGT
  | op_BPF_JGE,   op_BPF_JGE
  | op_BPF_JLT,   op_BPF_JLT
  | op_BPF_JLE,   op_BPF_JLE
  | op_BPF_JSET,  op_BPF_JSET
  | op_BPF_JNE,   op_BPF_JNE
  | op_BPF_JSGT,  op_BPF_JSGT
  | op_BPF_JSGE,  op_BPF_JSGE
  | op_BPF_JSLT,  op_BPF_JSLT
  | op_BPF_JSLE,  op_BPF_JSLE
  | op_BPF_RET,   op_BPF_RET
  | op_BPF_JMP_ILLEGAL_INS, op_BPF_JMP_ILLEGAL_INS => true
  | _, _ => false
  end.

Definition opcode_mem_ld_imm_eqb (o o' : opcode_mem_ld_imm): bool :=
  match o , o' with
  | op_BPF_LDDW,   op_BPF_LDDW
  | op_BPF_LDX_IMM_ILLEGAL_INS, op_BPF_LDX_IMM_ILLEGAL_INS => true
  | _, _ => false
  end.

Definition opcode_mem_ld_reg_eqb (o o' : opcode_mem_ld_reg): bool :=
  match o , o' with
  | op_BPF_LDXW,   op_BPF_LDXW
  | op_BPF_LDXH,   op_BPF_LDXH
  | op_BPF_LDXB,   op_BPF_LDXB
  | op_BPF_LDXDW,  op_BPF_LDXDW
  | op_BPF_LDX_REG_ILLEGAL_INS, op_BPF_LDX_REG_ILLEGAL_INS => true
  | _, _ => false
  end.

Definition opcode_mem_st_imm_eqb (o o' : opcode_mem_st_imm): bool :=
  match o , o' with
  | op_BPF_STW,    op_BPF_STW
  | op_BPF_STH,    op_BPF_STH
  | op_BPF_STB,    op_BPF_STB
  | op_BPF_STDW,   op_BPF_STDW
  | op_BPF_ST_ILLEGAL_INS, op_BPF_ST_ILLEGAL_INS => true
  | _, _ => false
  end.

Definition opcode_mem_st_reg_eqb (o o' : opcode_mem_st_reg): bool :=
  match o , o' with
  | op_BPF_STXW,   op_BPF_STXW
  | op_BPF_STXH,   op_BPF_STXH
  | op_BPF_STXB,   op_BPF_STXB
  | op_BPF_STXDW,  op_BPF_STXDW
  | op_BPF_STX_ILLEGAL_INS, op_BPF_STX_ILLEGAL_INS => true
  | _, _ => false
  end.

Definition opcode_eqb (o o' : opcode) : bool :=
  match o , o' with
  | op_BPF_ALU64,      op_BPF_ALU64
  | op_BPF_ALU32,      op_BPF_ALU32
  | op_BPF_Branch,     op_BPF_Branch
  | op_BPF_Mem_ld_imm, op_BPF_Mem_ld_imm
  | op_BPF_Mem_ld_reg, op_BPF_Mem_ld_reg
  | op_BPF_Mem_st_imm, op_BPF_Mem_st_imm
  | op_BPF_Mem_st_reg, op_BPF_Mem_st_reg

  | op_BPF_ILLEGAL_INS, op_BPF_ILLEGAL_INS => true
  | _, _ => false
  end.


Open Scope Z_scope.
Definition opcode_alu64CompilableType :=
  MkCompilableType opcode_alu64 C_U8.

Definition opcode_alu64CompilableTypeMatchableType : MatchableType:=
  Eval compute in
 (mkEnumMatchableType
    opcode_alu64CompilableType  opcode_alu64_eqb
    (     (op_BPF_ADD64, 0x00)
       :: (op_BPF_SUB64, 0x10)
       :: (op_BPF_MUL64, 0x20)
       :: (op_BPF_DIV64, 0x30)
       :: (op_BPF_OR64,  0x40)
       :: (op_BPF_AND64, 0x50)
       :: (op_BPF_LSH64, 0x60)
       :: (op_BPF_RSH64, 0x70)
       :: (op_BPF_NEG64, 0x80)
       :: (op_BPF_MOD64, 0x90)
       :: (op_BPF_XOR64, 0xa0)
       :: (op_BPF_MOV64, 0xb0)
       :: (op_BPF_ARSH64,0xc0):: nil)
    op_BPF_ALU64_ILLEGAL_INS
    (fun m A => opcode_alu64_rect (fun _ => m A))).

Definition opcode_alu32CompilableType :=
  MkCompilableType opcode_alu32 C_U8.

Definition opcode_alu32CompilableTypeMatchableType : MatchableType:=
  Eval compute in
 (mkEnumMatchableType
    opcode_alu32CompilableType  opcode_alu32_eqb
    (     (op_BPF_ADD32, 0x00)
       :: (op_BPF_SUB32, 0x10)
       :: (op_BPF_MUL32, 0x20)
       :: (op_BPF_DIV32, 0x30)
       :: (op_BPF_OR32,  0x40)
       :: (op_BPF_AND32, 0x50)
       :: (op_BPF_LSH32, 0x60)
       :: (op_BPF_RSH32, 0x70)
       :: (op_BPF_NEG32, 0x80)
       :: (op_BPF_MOD32, 0x90)
       :: (op_BPF_XOR32, 0xa0)
       :: (op_BPF_MOV32, 0xb0)
       :: (op_BPF_ARSH32,0xc0) :: nil)
    op_BPF_ALU32_ILLEGAL_INS
    (fun m A => opcode_alu32_rect (fun _ => m A))).

Definition opcode_branchCompilableType :=
  MkCompilableType opcode_branch C_U8.

Definition opcode_branchCompilableTypeMatchableType : MatchableType:=
  Eval compute in
 (mkEnumMatchableType
    opcode_branchCompilableType  opcode_branch_eqb
    (     (op_BPF_JA,   0x00)
       :: (op_BPF_JEQ,  0x10)
       :: (op_BPF_JGT,  0x20)
       :: (op_BPF_JGE,  0x30)
       :: (op_BPF_JLT,  0xa0)
       :: (op_BPF_JLE,  0xb0)
       :: (op_BPF_JSET, 0x40)
       :: (op_BPF_JNE,  0x50)
       :: (op_BPF_JSGT, 0x60)
       :: (op_BPF_JSGE, 0x70)
       :: (op_BPF_JSLT, 0xc0)
       :: (op_BPF_JSLE, 0xd0)
       :: (op_BPF_CALL, 0x80)
       :: (op_BPF_RET,  0x90) :: nil)
    op_BPF_JMP_ILLEGAL_INS
    (fun m A => opcode_branch_rect (fun _ => m A))).

Definition opcode_mem_ld_immCompilableType :=
  MkCompilableType opcode_mem_ld_imm C_U8.

Definition opcode_mem_ld_immCompilableTypeMatchableType : MatchableType:=
  Eval compute in
 (mkEnumMatchableType
    opcode_mem_ld_immCompilableType  opcode_mem_ld_imm_eqb
    (     (op_BPF_LDDW, 0x18)
        :: nil)
    op_BPF_LDX_IMM_ILLEGAL_INS
    (fun m A => opcode_mem_ld_imm_rect (fun _ => m A))).

Definition opcode_mem_ld_regCompilableType :=
  MkCompilableType opcode_mem_ld_reg C_U8.

Definition opcode_mem_ld_regCompilableTypeMatchableType : MatchableType:=
  Eval compute in
 (mkEnumMatchableType
    opcode_mem_ld_regCompilableType  opcode_mem_ld_reg_eqb
    (     (op_BPF_LDXW, 0x61)
       :: (op_BPF_LDXH, 0x69)
       :: (op_BPF_LDXB, 0x71)
       :: (op_BPF_LDXDW,0x79) :: nil)
    op_BPF_LDX_REG_ILLEGAL_INS
    (fun m A => opcode_mem_ld_reg_rect (fun _ => m A))).

Definition opcode_mem_st_immCompilableType :=
  MkCompilableType opcode_mem_st_imm C_U8.

Definition opcode_mem_st_immCompilableTypeMatchableType : MatchableType:=
  Eval compute in
 (mkEnumMatchableType
    opcode_mem_st_immCompilableType  opcode_mem_st_imm_eqb
    (     (op_BPF_STW, 0x62)
       :: (op_BPF_STH, 0x6a)
       :: (op_BPF_STB, 0x72)
       :: (op_BPF_STDW, 0x7a) :: nil)
    op_BPF_ST_ILLEGAL_INS
    (fun m A => opcode_mem_st_imm_rect (fun _ => m A))).

Definition opcode_mem_st_regCompilableType :=
  MkCompilableType opcode_mem_st_reg C_U8.

Definition opcode_mem_st_regCompilableTypeMatchableType : MatchableType:=
  Eval compute in
 (mkEnumMatchableType
    opcode_mem_st_regCompilableType  opcode_mem_st_reg_eqb
    (     (op_BPF_STXW, 0x63)
       :: (op_BPF_STXH, 0x6b)
       :: (op_BPF_STXB, 0x73)
       :: (op_BPF_STXDW, 0x7b) :: nil)
    op_BPF_STX_ILLEGAL_INS
    (fun m A => opcode_mem_st_reg_rect (fun _ => m A))).

Definition opcodeCompilableType :=
  MkCompilableType opcode C_U8.

Definition opcodeCompilableTypeMatchableType : MatchableType:=
  Eval compute in
 (mkEnumMatchableType
    opcodeCompilableType  opcode_eqb
    (     (op_BPF_ALU64,      0x07)
       :: (op_BPF_ALU32,      0x04)
       :: (op_BPF_Branch,     0x05)
       :: (op_BPF_Mem_ld_imm, 0x00)
       :: (op_BPF_Mem_ld_reg, 0x01)
       :: (op_BPF_Mem_st_imm, 0x02)
       :: (op_BPF_Mem_st_reg, 0x03):: nil)
    op_BPF_ILLEGAL_INS
    (fun m A => opcode_rect (fun _ => m A))).
Close Scope Z_scope.

Definition byteToopcodeSymbolType :=
  MkCompilableSymbolType [nat8CompilableType] (Some opcodeCompilableType).

Definition int64ToopcodeSymbolType :=
  MkCompilableSymbolType [int64CompilableType] (Some opcodeCompilableType).


Instance CINT : CType nat := mkCType _ (cType nat8CompilableType).
Instance COP : CType opcode := mkCType _ (cType opcodeCompilableType).
Instance CINT64 : CType int64_t := mkCType _ (cType int64CompilableType).
(*
Definition Const_int64_to_opcode :=
  ltac: (mkprimitive int64_to_opcode
                (fun es => match es with
                           | [e1] => Ok (Csyntax.Ecast (Csyntax.Ebinop Cop.Oand e1 C_U64_0xff C_U64) C_U8)
                           | _       => Err PrimitiveEncodingFailed
                           end)). *)


Definition Const_byte_to_opcode :=
  ltac: (mkprimitive byte_to_opcode
                (fun es => match es with
                           | [e1] => Ok (Csyntax.Ecast (Csyntax.Ebinop Cop.Oand e1 C_NAT8_0x07 C_U8) C_U8)
                           | _       => Err PrimitiveEncodingFailed
                           end)).

Definition byte_to_opcode_alu64SymbolType :=
  MkCompilableSymbolType [nat8CompilableType] (Some opcode_alu64CompilableType).

Instance COP_alu64 : CType opcode_alu64 := mkCType _ (cType opcode_alu64CompilableType).

Definition Const_byte_to_opcode_alu64 :=
  ltac: (mkprimitive byte_to_opcode_alu64
                (fun es => match es with
                           | [e1] => Ok (Csyntax.Ecast (Csyntax.Ebinop Cop.Oand e1 C_NAT8_0xf0 C_U8) C_U8)
                           | _       => Err PrimitiveEncodingFailed
                           end)).

Definition byte_to_opcode_alu32SymbolType :=
  MkCompilableSymbolType [nat8CompilableType] (Some opcode_alu32CompilableType).

Instance COP_alu32 : CType opcode_alu32 := mkCType _ (cType opcode_alu32CompilableType).

Definition Const_byte_to_opcode_alu32 :=
  ltac: (mkprimitive byte_to_opcode_alu32
                (fun es => match es with
                           | [e1] => Ok (Csyntax.Ecast (Csyntax.Ebinop Cop.Oand e1 C_NAT8_0xf0 C_U8) C_U8)
                           | _       => Err PrimitiveEncodingFailed
                           end)).

Definition byte_to_opcode_branchSymbolType :=
  MkCompilableSymbolType [nat8CompilableType] (Some opcode_branchCompilableType).

Instance COP_opcode_branch : CType opcode_branch := mkCType _ (cType opcode_branchCompilableType).

Definition Const_byte_to_opcode_branch :=
  ltac: (mkprimitive byte_to_opcode_branch
                (fun es => match es with
                           | [e1] => Ok (Csyntax.Ecast (Csyntax.Ebinop Cop.Oand e1 C_NAT8_0xf0 C_U8) C_U8)
                           | _       => Err PrimitiveEncodingFailed
                           end)).

Definition byte_to_opcode_mem_ld_immSymbolType :=
  MkCompilableSymbolType [nat8CompilableType] (Some opcode_mem_ld_immCompilableType).

Instance COP_opcode_mem_ld_imm : CType opcode_mem_ld_imm := mkCType _ (cType opcode_mem_ld_immCompilableType).

Definition Const_byte_to_opcode_mem_ld_imm :=
  ltac: (mkprimitive byte_to_opcode_mem_ld_imm
                (fun es => match es with
                           | [e1] => Ok (Csyntax.Ecast (Csyntax.Ebinop Cop.Oand e1 C_NAT8_0xff C_U8) C_U8)
                           | _       => Err PrimitiveEncodingFailed
                           end)).

Definition byte_to_opcode_mem_ld_regSymbolType :=
  MkCompilableSymbolType [nat8CompilableType] (Some opcode_mem_ld_regCompilableType).

Instance COP_opcode_mem_ld_reg : CType opcode_mem_ld_reg := mkCType _ (cType opcode_mem_ld_regCompilableType).

Definition Const_byte_to_opcode_mem_ld_reg :=
  ltac: (mkprimitive byte_to_opcode_mem_ld_reg
                (fun es => match es with
                           | [e1] => Ok (Csyntax.Ecast (Csyntax.Ebinop Cop.Oand e1 C_NAT8_0xff C_U8) C_U8)
                           | _       => Err PrimitiveEncodingFailed
                           end)).

Definition byte_to_opcode_mem_st_immSymbolType :=
  MkCompilableSymbolType [nat8CompilableType] (Some opcode_mem_st_immCompilableType).

Instance COP_opcode_mem_st_imm : CType opcode_mem_st_imm := mkCType _ (cType opcode_mem_st_immCompilableType).

Definition Const_byte_to_opcode_mem_st_imm :=
  ltac: (mkprimitive byte_to_opcode_mem_st_imm
                (fun es => match es with
                           | [e1] => Ok (Csyntax.Ecast (Csyntax.Ebinop Cop.Oand e1 C_NAT8_0xff C_U8) C_U8)
                           | _       => Err PrimitiveEncodingFailed
                           end)).

Definition byte_to_opcode_mem_st_regSymbolType :=
  MkCompilableSymbolType [nat8CompilableType] (Some opcode_mem_st_regCompilableType).

Instance COP_opcode_mem_st_reg : CType opcode_mem_st_reg := mkCType _ (cType opcode_mem_st_regCompilableType).

Definition Const_byte_to_opcode_mem_st_reg :=
  ltac: (mkprimitive byte_to_opcode_mem_st_reg
                (fun es => match es with
                           | [e1] => Ok (Csyntax.Ecast (Csyntax.Ebinop Cop.Oand e1 C_NAT8_0xff C_U8) C_U8)
                           | _       => Err PrimitiveEncodingFailed
                           end)).

Close Scope nat_scope.

Module Exports.
  Definition opcode_alu64CompilableTypeMatchableType      := opcode_alu64CompilableTypeMatchableType.
  Definition opcode_alu32CompilableTypeMatchableType      := opcode_alu32CompilableTypeMatchableType.
  Definition opcode_branchCompilableTypeMatchableType     := opcode_branchCompilableTypeMatchableType.
  Definition opcode_mem_ld_immCompilableTypeMatchableType := opcode_mem_ld_immCompilableTypeMatchableType.
  Definition opcode_mem_ld_regCompilableTypeMatchableType := opcode_mem_ld_regCompilableTypeMatchableType.
  Definition opcode_mem_st_immCompilableTypeMatchableType := opcode_mem_st_immCompilableTypeMatchableType.
  Definition opcode_mem_st_regCompilableTypeMatchableType := opcode_mem_st_regCompilableTypeMatchableType.
  Definition opcodeCompilableTypeMatchableType            := opcodeCompilableTypeMatchableType.
  Definition Const_byte_to_opcode_alu64                   := Const_byte_to_opcode_alu64.
  Definition Const_byte_to_opcode_alu32                   := Const_byte_to_opcode_alu32.
  Definition Const_byte_to_opcode_branch                  := Const_byte_to_opcode_branch.
  Definition Const_byte_to_opcode_mem_ld_imm              := Const_byte_to_opcode_mem_ld_imm.
  Definition Const_byte_to_opcode_mem_ld_reg              := Const_byte_to_opcode_mem_ld_reg.
  Definition Const_byte_to_opcode_mem_st_imm              := Const_byte_to_opcode_mem_st_imm.
  Definition Const_byte_to_opcode_mem_st_reg              := Const_byte_to_opcode_mem_st_reg.
  Definition Const_byte_to_opcode                         := Const_byte_to_opcode. (*
  Definition Const_int64_to_opcode                        := Const_int64_to_opcode. *)
End Exports.
