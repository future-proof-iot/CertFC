From Coq Require Import List ZArith.
Import ListNotations.

From compcert Require Import Integers.

From dx Require Import ResultMonad IR.

Require Import CoqIntegers DxIntegers InfComp GenMatchable.

Open Scope Z_scope.

Inductive opcode: Type :=
  (** ALU64:25 *)
  | op_BPF_ADD64i
  | op_BPF_ADD64r
  | op_BPF_SUB64i
  | op_BPF_SUB64r
  | op_BPF_MUL64i
  | op_BPF_MUL64r
  | op_BPF_DIV64i
  | op_BPF_DIV64r
  | op_BPF_OR64i
  | op_BPF_OR64r
  | op_BPF_AND64i
  | op_BPF_AND64r
  | op_BPF_LSH64i
  | op_BPF_LSH64r
  | op_BPF_RSH64i
  | op_BPF_RSH64r
  | op_BPF_NEG64
  | op_BPF_MOD64i
  | op_BPF_MOD64r
  | op_BPF_XOR64i
  | op_BPF_XOR64r
  | op_BPF_MOV64i
  | op_BPF_MOV64r
  | op_BPF_ARSH64i
  | op_BPF_ARSH64r
  (** ALU32:25 *)
  | op_BPF_ADD32i
  | op_BPF_ADD32r
  | op_BPF_SUB32i
  | op_BPF_SUB32r
  | op_BPF_MUL32i
  | op_BPF_MUL32r
  | op_BPF_DIV32i
  | op_BPF_DIV32r
  | op_BPF_OR32i
  | op_BPF_OR32r
  | op_BPF_AND32i
  | op_BPF_AND32r
  | op_BPF_LSH32i
  | op_BPF_LSH32r
  | op_BPF_RSH32i
  | op_BPF_RSH32r
  | op_BPF_NEG32
  | op_BPF_MOD32i
  | op_BPF_MOD32r
  | op_BPF_XOR32i
  | op_BPF_XOR32r
  | op_BPF_MOV32i
  | op_BPF_MOV32r
  | op_BPF_ARSH32i
  | op_BPF_ARSH32r
  (**Branch: 23 *)
  | op_BPF_JA
  | op_BPF_JEQi
  | op_BPF_JEQr
  | op_BPF_JGTi
  | op_BPF_JGTr
  | op_BPF_JGEi
  | op_BPF_JGEr
  | op_BPF_JLTi
  | op_BPF_JLTr
  | op_BPF_JLEi
  | op_BPF_JLEr
  | op_BPF_JSETi
  | op_BPF_JSETr
  | op_BPF_JNEi
  | op_BPF_JNEr
  | op_BPF_JSGTi
  | op_BPF_JSGTr
  | op_BPF_JSGEi
  | op_BPF_JSGEr
  | op_BPF_JSLTi
  | op_BPF_JSLTr
  | op_BPF_JSLEi
  | op_BPF_JSLEr
  (** Load/Store: 13 *)
  | op_BPF_LDDW
  | op_BPF_LDXW
  | op_BPF_LDXH
  | op_BPF_LDXB
  | op_BPF_LDXDW
  | op_BPF_STW
  | op_BPF_STH
  | op_BPF_STB
  | op_BPF_STDW
  | op_BPF_STXW
  | op_BPF_STXH
  | op_BPF_STXB
  | op_BPF_STXDW

  | op_BPF_RET
  | op_BPF_ERROR_INS
.


Definition int64_to_opcode (ins: int64_t): opcode :=
  let op_z := Int64.unsigned (Int64.and ins int64_0xff) in
  match op_z with
  (*ALU64*)
  | 0x07 => op_BPF_ADD64i
  | 0x0f => op_BPF_ADD64r
  | 0x17 => op_BPF_SUB64i
  | 0x1f => op_BPF_SUB64r
  | 0x27 => op_BPF_MUL64i
  | 0x2f => op_BPF_MUL64r
  | 0x37 => op_BPF_DIV64i
  | 0x3f => op_BPF_DIV64r
  | 0x47 => op_BPF_OR64i
  | 0x4f => op_BPF_OR64r
  | 0x57 => op_BPF_AND64i
  | 0x5f => op_BPF_AND64r
  | 0x67 => op_BPF_LSH64i
  | 0x6f => op_BPF_LSH64r
  | 0x77 => op_BPF_RSH64i
  | 0x7f => op_BPF_RSH64r
  | 0x87 => op_BPF_NEG64
  | 0x97 => op_BPF_MOD64i
  | 0x9f => op_BPF_MOD64r
  | 0xa7 => op_BPF_XOR64i
  | 0xaf => op_BPF_XOR64r
  | 0xb7 => op_BPF_MOV64i
  | 0xbf => op_BPF_MOV64r
  | 0xc7 => op_BPF_ARSH64i
  | 0xcf => op_BPF_ARSH64r
  (*ALU32*)
  | 0x04 => op_BPF_ADD32i
  | 0x0c => op_BPF_ADD32r
  | 0x14 => op_BPF_SUB32i
  | 0x1c => op_BPF_SUB32r
  | 0x24 => op_BPF_MUL32i
  | 0x2c => op_BPF_MUL32r
  | 0x34 => op_BPF_DIV32i
  | 0x3c => op_BPF_DIV32r
  | 0x44 => op_BPF_OR32i
  | 0x4c => op_BPF_OR32r
  | 0x54 => op_BPF_AND32i
  | 0x5c => op_BPF_AND32r
  | 0x64 => op_BPF_LSH32i
  | 0x6c => op_BPF_LSH32r
  | 0x74 => op_BPF_RSH32i
  | 0x7c => op_BPF_RSH32r
  | 0x84 => op_BPF_NEG32
  | 0x94 => op_BPF_MOD32i
  | 0x9c => op_BPF_MOD32r
  | 0xa4 => op_BPF_XOR32i
  | 0xac => op_BPF_XOR32r
  | 0xb4 => op_BPF_MOV32i
  | 0xbc => op_BPF_MOV32r
  | 0xc4 => op_BPF_ARSH32i
  | 0xcc => op_BPF_ARSH32r

  | 0x05 => op_BPF_JA
  | 0x15 => op_BPF_JEQi
  | 0x1d => op_BPF_JEQr
  | 0x25 => op_BPF_JGTi
  | 0x2d => op_BPF_JGTr
  | 0x35 => op_BPF_JGEi
  | 0x3d => op_BPF_JGEr
  | 0xa5 => op_BPF_JLTi
  | 0xad => op_BPF_JLTr
  | 0xb5 => op_BPF_JLEi
  | 0xbd => op_BPF_JLEr
  | 0x45 => op_BPF_JSETi
  | 0x4d => op_BPF_JSETr
  | 0x55 => op_BPF_JNEi
  | 0x5d => op_BPF_JNEr
  | 0x65 => op_BPF_JSGTi
  | 0x6d => op_BPF_JSGTr
  | 0x75 => op_BPF_JSGEi
  | 0x7d => op_BPF_JSGEr
  | 0xc5 => op_BPF_JSLTi
  | 0xcd => op_BPF_JSLTr
  | 0xd5 => op_BPF_JSLEi
  | 0xdd => op_BPF_JSLEr

  | 0x18 => op_BPF_LDDW
  | 0x61 => op_BPF_LDXW
  | 0x69 => op_BPF_LDXH
  | 0x71 => op_BPF_LDXB
  | 0x79 => op_BPF_LDXDW
  | 0x62 => op_BPF_STW
  | 0x6a => op_BPF_STH
  | 0x72 => op_BPF_STB
  | 0x7a => op_BPF_STDW
  | 0x63 => op_BPF_STXW
  | 0x6b => op_BPF_STXH
  | 0x73 => op_BPF_STXB
  | 0x7b => op_BPF_STXDW
(*
  | 0x85 => op_BPF_CALL*)
  | 0x95 => op_BPF_RET

  | _    => op_BPF_ERROR_INS
  end.

(******************** Dx related *******************)

Definition opcode_eqb (o o' : opcode) : bool :=
  match o , o' with
  | op_BPF_ADD64i, op_BPF_ADD64i
  | op_BPF_ADD64r, op_BPF_ADD64r
  | op_BPF_SUB64i, op_BPF_SUB64i
  | op_BPF_SUB64r, op_BPF_SUB64r
  | op_BPF_MUL64i, op_BPF_MUL64i
  | op_BPF_MUL64r, op_BPF_MUL64r
  | op_BPF_DIV64i, op_BPF_DIV64i
  | op_BPF_DIV64r, op_BPF_DIV64r
  | op_BPF_OR64i,  op_BPF_OR64i
  | op_BPF_OR64r,  op_BPF_OR64r
  | op_BPF_AND64i, op_BPF_AND64i
  | op_BPF_AND64r, op_BPF_AND64r
  | op_BPF_LSH64i, op_BPF_LSH64i
  | op_BPF_LSH64r, op_BPF_LSH64r
  | op_BPF_RSH64i, op_BPF_RSH64i
  | op_BPF_RSH64r, op_BPF_RSH64r
  | op_BPF_NEG64,  op_BPF_NEG64
  | op_BPF_MOD64i, op_BPF_MOD64i
  | op_BPF_MOD64r, op_BPF_MOD64r
  | op_BPF_XOR64i, op_BPF_XOR64i
  | op_BPF_XOR64r, op_BPF_XOR64r
  | op_BPF_MOV64i, op_BPF_MOV64i
  | op_BPF_MOV64r, op_BPF_MOV64r
  | op_BPF_ARSH64i,op_BPF_MOV64r
  | op_BPF_ARSH64r,op_BPF_MOV64r
  (** ALU32:25 *)
  | op_BPF_ADD32i, op_BPF_ADD32i
  | op_BPF_ADD32r, op_BPF_ADD32r
  | op_BPF_SUB32i, op_BPF_SUB32i
  | op_BPF_SUB32r, op_BPF_SUB32r
  | op_BPF_MUL32i, op_BPF_MUL32i
  | op_BPF_MUL32r, op_BPF_MUL32r
  | op_BPF_DIV32i, op_BPF_DIV32i
  | op_BPF_DIV32r, op_BPF_DIV32r
  | op_BPF_OR32i,  op_BPF_OR32i
  | op_BPF_OR32r,  op_BPF_OR32r
  | op_BPF_AND32i, op_BPF_AND32i
  | op_BPF_AND32r, op_BPF_AND32r
  | op_BPF_LSH32i, op_BPF_LSH32i
  | op_BPF_LSH32r, op_BPF_LSH32r
  | op_BPF_RSH32i, op_BPF_RSH32i
  | op_BPF_RSH32r, op_BPF_RSH32r
  | op_BPF_NEG32,  op_BPF_NEG32
  | op_BPF_MOD32i, op_BPF_MOD32i
  | op_BPF_MOD32r, op_BPF_MOD32r
  | op_BPF_XOR32i, op_BPF_XOR32i
  | op_BPF_XOR32r, op_BPF_XOR32r
  | op_BPF_MOV32i, op_BPF_MOV32i
  | op_BPF_MOV32r, op_BPF_MOV32r
  | op_BPF_ARSH32i,op_BPF_MOV32r
  | op_BPF_ARSH32r,op_BPF_MOV32r
  (**Branch: 23 *)
  | op_BPF_JA,     op_BPF_JA
  | op_BPF_JEQi,   op_BPF_JEQi
  | op_BPF_JEQr,   op_BPF_JEQr
  | op_BPF_JGTi,   op_BPF_JGTi
  | op_BPF_JGTr,   op_BPF_JGTr
  | op_BPF_JGEi,   op_BPF_JGEi
  | op_BPF_JGEr,   op_BPF_JGEr
  | op_BPF_JLTi,   op_BPF_JLTi
  | op_BPF_JLTr,   op_BPF_JLTr
  | op_BPF_JLEi,   op_BPF_JLEi
  | op_BPF_JLEr,   op_BPF_JLEr
  | op_BPF_JSETi,  op_BPF_JSETi
  | op_BPF_JSETr,  op_BPF_JSETr
  | op_BPF_JNEi,   op_BPF_JNEi
  | op_BPF_JNEr,   op_BPF_JNEr
  | op_BPF_JSGTi,  op_BPF_JSGTi
  | op_BPF_JSGTr,  op_BPF_JSGTr
  | op_BPF_JSGEi,  op_BPF_JSGEi
  | op_BPF_JSGEr,  op_BPF_JSGEr
  | op_BPF_JSLTi,  op_BPF_JSLTi
  | op_BPF_JSLTr,  op_BPF_JSLTr
  | op_BPF_JSLEi,  op_BPF_JSLEi
  | op_BPF_JSLEr,  op_BPF_JSLEr
  (** Load/Store: 13 *)
  | op_BPF_LDDW,   op_BPF_LDDW
  | op_BPF_LDXW,   op_BPF_LDXW
  | op_BPF_LDXH,   op_BPF_LDXH
  | op_BPF_LDXB,   op_BPF_LDXB
  | op_BPF_LDXDW,  op_BPF_LDXDW
  | op_BPF_STW,    op_BPF_STW
  | op_BPF_STH,    op_BPF_STH
  | op_BPF_STB,    op_BPF_STB
  | op_BPF_STDW,   op_BPF_STDW
  | op_BPF_STXW,   op_BPF_STXW
  | op_BPF_STXH,   op_BPF_STXH
  | op_BPF_STXB,   op_BPF_STXB
  | op_BPF_STXDW,  op_BPF_STXDW

  | op_BPF_RET,    op_BPF_RET
  | op_BPF_ERROR_INS, op_BPF_ERROR_INS => true
  | _, _ => false
  end.

Definition opcodeCompilableType :=
  MkCompilableType opcode C_U8.

Definition opcodeMatchableType : MatchableType:=
  Eval compute in
 (mkEnumMatchableType
    opcodeCompilableType  opcode_eqb
    ((op_BPF_ADD64i, 0x07)
       :: (op_BPF_ADD64r, 0x0f)
       :: (op_BPF_SUB64i, 0x17)
       :: (op_BPF_SUB64r, 0x1f)
       :: (op_BPF_MUL64i, 0x27)
       :: (op_BPF_MUL64r, 0x2f)
       :: (op_BPF_DIV64i, 0x37)
       :: (op_BPF_DIV64r, 0x3f)
       :: (op_BPF_OR64i,  0x47)
       :: (op_BPF_OR64r,  0x4f)
       :: (op_BPF_AND64i, 0x57)
       :: (op_BPF_AND64r, 0x5f)
       :: (op_BPF_LSH64i, 0x67)
       :: (op_BPF_LSH64r, 0x6f)
       :: (op_BPF_RSH64i, 0x77)
       :: (op_BPF_RSH64r, 0x7f)
       :: (op_BPF_NEG64,  0x87)
       :: (op_BPF_MOD64i, 0x97)
       :: (op_BPF_MOD64r, 0x9f)
       :: (op_BPF_XOR64i, 0xa7)
       :: (op_BPF_XOR64r, 0xaf)
       :: (op_BPF_MOV64i, 0xb7)
       :: (op_BPF_MOV64r, 0xbf)
       :: (op_BPF_ARSH64i,0xc7)
       :: (op_BPF_ARSH64r,0xcf)
       :: (op_BPF_ADD32i, 0x04)
       :: (op_BPF_ADD32r, 0x0c)
       :: (op_BPF_SUB32i, 0x14)
       :: (op_BPF_SUB32r, 0x1c)
       :: (op_BPF_MUL32i, 0x24)
       :: (op_BPF_MUL32r, 0x2c)
       :: (op_BPF_DIV32i, 0x34)
       :: (op_BPF_DIV32r, 0x3c)
       :: (op_BPF_OR32i,  0x44)
       :: (op_BPF_OR32r,  0x4c)
       :: (op_BPF_AND32i, 0x54)
       :: (op_BPF_AND32r, 0x5c)
       :: (op_BPF_LSH32i, 0x64)
       :: (op_BPF_LSH32r, 0x6c)
       :: (op_BPF_RSH32i, 0x74)
       :: (op_BPF_RSH32r, 0x7c)
       :: (op_BPF_NEG32,  0x84)
       :: (op_BPF_MOD32i, 0x94)
       :: (op_BPF_MOD32r, 0x9c)
       :: (op_BPF_XOR32i, 0xa4)
       :: (op_BPF_XOR32r, 0xac)
       :: (op_BPF_MOV32i, 0xb4)
       :: (op_BPF_MOV32r, 0xbc)
       :: (op_BPF_ARSH32i,0xc4)
       :: (op_BPF_ARSH32r,0xcc)
       :: (op_BPF_JA, 0x05)
       :: (op_BPF_JEQi, 0x15)
       :: (op_BPF_JEQr, 0x1d)
       :: (op_BPF_JGTi, 0x25)
       :: (op_BPF_JGTr, 0x2d)
       :: (op_BPF_JGEi, 0x35)
       :: (op_BPF_JGEr, 0x3d)
       :: (op_BPF_JLTi, 0xa5)
       :: (op_BPF_JLTr, 0xad)
       :: (op_BPF_JLEi, 0xb5)
       :: (op_BPF_JLEr, 0xbd)
       :: (op_BPF_JSETi, 0x45)
       :: (op_BPF_JSETr, 0x4d)
       :: (op_BPF_JNEi, 0x55)
       :: (op_BPF_JNEr, 0x5d)
       :: (op_BPF_JSGTi, 0x65)
       :: (op_BPF_JSGTr, 0x6d)
       :: (op_BPF_JSGEi, 0x75)
       :: (op_BPF_JSGEr, 0x7d)
       :: (op_BPF_JSLTi, 0xc5)
       :: (op_BPF_JSLTr, 0xcd)
       :: (op_BPF_JSLEi, 0xd5)
       :: (op_BPF_JSLEr, 0xdd)
       :: (op_BPF_LDDW, 0x18)
       :: (op_BPF_LDXW, 0x61)
       :: (op_BPF_LDXH, 0x69)
       :: (op_BPF_LDXB, 0x71)
       :: (op_BPF_LDXDW, 0x79)
       :: (op_BPF_STW, 0x62)
       :: (op_BPF_STH, 0x6a)
       :: (op_BPF_STB, 0x72)
       :: (op_BPF_STDW, 0x7a)
       :: (op_BPF_STXW, 0x63)
       :: (op_BPF_STXH, 0x6b)
       :: (op_BPF_STXB, 0x73)
       :: (op_BPF_STXDW, 0x7b)
       :: (op_BPF_RET,0x95) :: nil) op_BPF_ERROR_INS (fun m A
=> opcode_rect (fun _ => m A))).

Definition int64ToopcodeSymbolType :=
  MkCompilableSymbolType [int64CompilableType] (Some opcodeCompilableType).


Instance CINT : CType int64_t := mkCType _ (cType int64CompilableType).
Instance COP : CType opcode := mkCType _ (cType opcodeCompilableType).

Definition Const_int64_to_opcode :=
  ltac: (mkprimitive int64_to_opcode
                (fun es => match es with
                           | [e1] => Ok (Csyntax.Ecast (Csyntax.Ebinop Cop.Oand e1 C_U64_0xff C_U64) C_U8)
                           | _       => Err PrimitiveEncodingFailed
                           end)).
Close Scope Z_scope.

(**)

Module Exports.
  Definition opcodeMatchableType := opcodeMatchableType.
  Definition Const_int64_to_opcode := Const_int64_to_opcode.
End Exports.
