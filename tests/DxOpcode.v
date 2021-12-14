From Coq Require Import List ZArith.
Import ListNotations.

From compcert Require Import Integers.

From dx Require Import ResultMonad IR.

Require Import CoqIntegers DxIntegers InfComp GenMatchable.

Open Scope Z_scope.

<<<<<<< HEAD
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
=======
Inductive opcode_alu64: Type := (**r 0xX7 *)
  (** ALU64:13 *)
  | op_BPF_ADD64
  | op_BPF_SUB64
  | op_BPF_MUL64
  | op_BPF_DIV64
  | op_BPF_OR64
  | op_BPF_AND64
  | op_BPF_LSH64
  | op_BPF_RSH64
  | op_BPF_NEG64
  | op_BPF_MOD64
  | op_BPF_XOR64
  | op_BPF_MOV64
  | op_BPF_ARSH64
  | op_BPF_ALU64_ILLEGAL_INS.

(**
#define BPF_INSTRUCTION_ALU_OP_MASK     0xf0

#define BPF_INSTRUCTION_ALU_ADD         0x00
#define BPF_INSTRUCTION_ALU_SUB         0x10
#define BPF_INSTRUCTION_ALU_MUL         0x20
#define BPF_INSTRUCTION_ALU_DIV         0x30
#define BPF_INSTRUCTION_ALU_OR          0x40
#define BPF_INSTRUCTION_ALU_AND         0x50
#define BPF_INSTRUCTION_ALU_LSH         0x60
#define BPF_INSTRUCTION_ALU_RSH         0x70
#define BPF_INSTRUCTION_ALU_NEG         0x80
#define BPF_INSTRUCTION_ALU_MOD         0x90
#define BPF_INSTRUCTION_ALU_XOR         0xA0
#define BPF_INSTRUCTION_ALU_MOV         0xB0
#define BPF_INSTRUCTION_ALU_ARSH        0xC0

*)

Definition byte_to_opcode_alu64 (op: int8_t): opcode_alu64 :=
  let opcode_alu := Byte.unsigned (Byte.and op int8_0xf0) in (**r masking operation *)
    match opcode_alu with
    | 0x00 => op_BPF_ADD64
    | 0x10 => op_BPF_SUB64
    | 0x20 => op_BPF_MUL64
    | 0x30 => op_BPF_DIV64
    | 0x40 => op_BPF_OR64
    | 0x50 => op_BPF_AND64
    | 0x60 => op_BPF_LSH64
    | 0x70 => op_BPF_RSH64
    | 0x80 => op_BPF_NEG64
    | 0x90 => op_BPF_MOD64
    | 0xa0 => op_BPF_XOR64
    | 0xb0 => op_BPF_MOV64
    | 0xc0 => op_BPF_ARSH64
    | _    => op_BPF_ALU64_ILLEGAL_INS
    end.

Inductive opcode_alu32: Type := (**r 0xX4 *)
  (** ALU32:13 *)
  | op_BPF_ADD32
  | op_BPF_SUB32
  | op_BPF_MUL32
  | op_BPF_DIV32
  | op_BPF_OR32
  | op_BPF_AND32
  | op_BPF_LSH32
  | op_BPF_RSH32
  | op_BPF_NEG32
  | op_BPF_MOD32
  | op_BPF_XOR32
  | op_BPF_MOV32
  | op_BPF_ARSH32
  | op_BPF_ALU32_ILLEGAL_INS.


Definition byte_to_opcode_alu32 (op: int8_t): opcode_alu32 :=
  let opcode_alu := Byte.unsigned (Byte.and op int8_0xf0) in (**r masking operation *)
    match opcode_alu with
    | 0x00 => op_BPF_ADD32
    | 0x10 => op_BPF_SUB32
    | 0x20 => op_BPF_MUL32
    | 0x30 => op_BPF_DIV32
    | 0x40 => op_BPF_OR32
    | 0x50 => op_BPF_AND32
    | 0x60 => op_BPF_LSH32
    | 0x70 => op_BPF_RSH32
    | 0x80 => op_BPF_NEG32
    | 0x90 => op_BPF_MOD32
    | 0xa0 => op_BPF_XOR32
    | 0xb0 => op_BPF_MOV32
    | 0xc0 => op_BPF_ARSH32
    | _    => op_BPF_ALU32_ILLEGAL_INS
    end.

Inductive opcode_branch: Type := (**r 0xX5 *)
  (**Branch: 13 *)
  | op_BPF_JA
  | op_BPF_JEQ
  | op_BPF_JGT
  | op_BPF_JGE
  | op_BPF_JLT
  | op_BPF_JLE
  | op_BPF_JSET
  | op_BPF_JNE
  | op_BPF_JSGT
  | op_BPF_JSGE
  | op_BPF_JSLT
  | op_BPF_JSLE
  | op_BPF_RET
  | op_BPF_JMP_ILLEGAL_INS.

(**
#define BPF_INSTRUCTION_ALU_OP_MASK     0xf0

#define BPF_INSTRUCTION_BRANCH_JA       0x00
#define BPF_INSTRUCTION_BRANCH_JEQ      0x10
#define BPF_INSTRUCTION_BRANCH_JGT      0x20
#define BPF_INSTRUCTION_BRANCH_JGE      0x30
#define BPF_INSTRUCTION_BRANCH_JLT      0xa0
#define BPF_INSTRUCTION_BRANCH_JLE      0xb0
#define BPF_INSTRUCTION_BRANCH_JSET     0x40
#define BPF_INSTRUCTION_BRANCH_JNE      0x50
#define BPF_INSTRUCTION_BRANCH_JSGT     0x60
#define BPF_INSTRUCTION_BRANCH_JSGE     0x70
#define BPF_INSTRUCTION_BRANCH_JSLT     0xc0
#define BPF_INSTRUCTION_BRANCH_JSLE     0xd0
#define BPF_INSTRUCTION_BRANCH_CALL     0x80
#define BPF_INSTRUCTION_BRANCH_EXIT     0x90
*)

Definition byte_to_opcode_branch (op: int8_t): opcode_branch :=
  let opcode_jmp := Byte.unsigned (Byte.and op int8_0xf0) in (**r masking operation *)
    match opcode_jmp with
    | 0x00 => op_BPF_JA
    | 0x10 => op_BPF_JEQ
    | 0x20 => op_BPF_JGT
    | 0x30 => op_BPF_JGE
    | 0xa0 => op_BPF_JLT
    | 0xb0 => op_BPF_JLE
    | 0x40 => op_BPF_JSET
    | 0x50 => op_BPF_JNE
    | 0x60 => op_BPF_JSGT
    | 0x70 => op_BPF_JSGE
    | 0xc0 => op_BPF_JSLT
    | 0xd0 => op_BPF_JSLE
  (*
    | 0x85 => op_BPF_CALL*)
    | 0x90 => op_BPF_RET
    | _    => op_BPF_JMP_ILLEGAL_INS
    end.

Inductive opcode_mem_ld_imm: Type :=  (**r 0xX8 *)
  (** Load/Store: 13 *)
  | op_BPF_LDDW
  | op_BPF_LDX_IMM_ILLEGAL_INS.

Definition byte_to_opcode_mem_ld_imm (op: int8_t): opcode_mem_ld_imm :=
  let opcode_ld := Byte.unsigned (Byte.and op int8_0xff) in (**r masking operation *)
    match opcode_ld with
    | 0x18 => op_BPF_LDDW
    | _    => op_BPF_LDX_IMM_ILLEGAL_INS
    end.

Inductive opcode_mem_ld_reg: Type :=  (**r 0xX1/0xX9 *)
  (** Load/Store: 13 *)
>>>>>>> optimization_32
  | op_BPF_LDXW
  | op_BPF_LDXH
  | op_BPF_LDXB
  | op_BPF_LDXDW
<<<<<<< HEAD
=======
  | op_BPF_LDX_REG_ILLEGAL_INS.

Definition byte_to_opcode_mem_ld_reg (op: int8_t): opcode_mem_ld_reg :=
  let opcode_ld := Byte.unsigned (Byte.and op int8_0xff) in (**r masking operation *)
    match opcode_ld with
    | 0x61 => op_BPF_LDXW
    | 0x69 => op_BPF_LDXH
    | 0x71 => op_BPF_LDXB
    | 0x79 => op_BPF_LDXDW
    | _    => op_BPF_LDX_REG_ILLEGAL_INS
    end.

Inductive opcode_mem_st_imm: Type :=  (**r 0xX2/0xXa *)
>>>>>>> optimization_32
  | op_BPF_STW
  | op_BPF_STH
  | op_BPF_STB
  | op_BPF_STDW
<<<<<<< HEAD
=======
  | op_BPF_ST_ILLEGAL_INS.

Definition byte_to_opcode_mem_st_imm (op: int8_t): opcode_mem_st_imm :=
  let opcode_st := Byte.unsigned (Byte.and op int8_0xff) in (**r masking operation *)
    match opcode_st with
    | 0x62 => op_BPF_STW
    | 0x6a => op_BPF_STH
    | 0x72 => op_BPF_STB
    | 0x7a => op_BPF_STDW
    | _    => op_BPF_ST_ILLEGAL_INS
    end.

Inductive opcode_mem_st_reg: Type :=  (**r 0xX3/0xXb *)
>>>>>>> optimization_32
  | op_BPF_STXW
  | op_BPF_STXH
  | op_BPF_STXB
  | op_BPF_STXDW
<<<<<<< HEAD

  | op_BPF_RET
  | op_BPF_ERROR_INS
.
=======
  | op_BPF_STX_ILLEGAL_INS.

Definition byte_to_opcode_mem_st_reg (op: int8_t): opcode_mem_st_reg :=
  let opcode_st := Byte.unsigned (Byte.and op int8_0xff) in (**r masking operation *)
    match opcode_st with
    | 0x63 => op_BPF_STXW
    | 0x6b => op_BPF_STXH
    | 0x73 => op_BPF_STXB
    | 0x7b => op_BPF_STXDW
    | _    => op_BPF_STX_ILLEGAL_INS
    end.

Inductive opcode: Type :=
  | op_BPF_ALU64   (**r 0xX7 / 0xXf *)
  | op_BPF_ALU32   (**r 0xX4 / 0xXc *)
  | op_BPF_Branch  (**r 0xX5 / 0xXd *)
  | op_BPF_Mem_ld_imm  (**r 0xX8 *)
  | op_BPF_Mem_ld_reg  (**r 0xX1/0xX9 *)
  | op_BPF_Mem_st_imm  (**r 0xX2/0xXa *)
  | op_BPF_Mem_st_reg  (**r 0xX3/0xXb *)
>>>>>>> optimization_32


<<<<<<< HEAD
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
=======
(**
#define BPF_INSTRUCTION_CLS_MASK        0x07

#define BPF_INSTRUCTION_CLS_LD          0x00
#define BPF_INSTRUCTION_CLS_LDX         0x01
#define BPF_INSTRUCTION_CLS_ST          0x02
#define BPF_INSTRUCTION_CLS_STX         0x03
#define BPF_INSTRUCTION_CLS_ALU32       0x04
#define BPF_INSTRUCTION_CLS_BRANCH      0x05
#define BPF_INSTRUCTION_CLS_ALU64       0x07
*)
Definition byte_to_opcode (op: int8_t): opcode :=
  let opc := Byte.unsigned (Byte.and op int8_0x07) in (**r masking operation *)
    match opc with
    | 0x07 => op_BPF_ALU64
    | 0x04 => op_BPF_ALU32
    | 0x05 => op_BPF_Branch
    | 0x00 => op_BPF_Mem_ld_imm
    | 0x01 => op_BPF_Mem_ld_reg
    | 0x02 => op_BPF_Mem_st_imm
    | 0x03 => op_BPF_Mem_st_reg
    | _    => op_BPF_ILLEGAL_INS
    end.

Definition int64_to_opcode (ins: int64_t): int8_t := Byte.repr (Int64.unsigned (Int64.and ins int64_0xff)).

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
>>>>>>> optimization_32
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
<<<<<<< HEAD
=======
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
>>>>>>> optimization_32

  | op_BPF_RET,    op_BPF_RET
  | op_BPF_ERROR_INS, op_BPF_ERROR_INS => true
  | _, _ => false
  end.

Definition opcodeCompilableType :=
  MkCompilableType opcode C_U8.

<<<<<<< HEAD
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
=======
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
>>>>>>> optimization_32
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
<<<<<<< HEAD
       :: (op_BPF_STXDW, 0x7b)
       :: (op_BPF_RET,0x95) :: nil) op_BPF_ERROR_INS (fun m A
=> opcode_rect (fun _ => m A))).
=======
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


Definition byteToopcodeSymbolType :=
  MkCompilableSymbolType [int8CompilableType] (Some opcodeCompilableType).
>>>>>>> optimization_32

Definition int64ToopcodeSymbolType :=
  MkCompilableSymbolType [int64CompilableType] (Some opcodeCompilableType).


Instance CINT : CType int8_t := mkCType _ (cType int8CompilableType).
Instance COP : CType opcode := mkCType _ (cType opcodeCompilableType).
Instance CINT64 : CType int64_t := mkCType _ (cType int64CompilableType).

Definition Const_int64_to_opcode :=
  ltac: (mkprimitive int64_to_opcode
                (fun es => match es with
                           | [e1] => Ok (Csyntax.Ecast (Csyntax.Ebinop Cop.Oand e1 C_U64_0xff C_U64) C_U8)
<<<<<<< HEAD
                           | _       => Err PrimitiveEncodingFailed
                           end)).
=======
                           | _       => Err PrimitiveEncodingFailed
                           end)).


Definition Const_byte_to_opcode :=
  ltac: (mkprimitive byte_to_opcode
                (fun es => match es with
                           | [e1] => Ok (Csyntax.Ecast (Csyntax.Ebinop Cop.Oand e1 C_U8_0x07 C_U8) C_U8)
                           | _       => Err PrimitiveEncodingFailed
                           end)).

Definition byte_to_opcode_alu64SymbolType :=
  MkCompilableSymbolType [int8CompilableType] (Some opcode_alu64CompilableType).

Instance COP_alu64 : CType opcode_alu64 := mkCType _ (cType opcode_alu64CompilableType).

Definition Const_byte_to_opcode_alu64 :=
  ltac: (mkprimitive byte_to_opcode_alu64
                (fun es => match es with
                           | [e1] => Ok (Csyntax.Ecast (Csyntax.Ebinop Cop.Oand e1 C_U8_0xf0 C_U8) C_U8)
                           | _       => Err PrimitiveEncodingFailed
                           end)).

Definition byte_to_opcode_alu32SymbolType :=
  MkCompilableSymbolType [int8CompilableType] (Some opcode_alu32CompilableType).

Instance COP_alu32 : CType opcode_alu32 := mkCType _ (cType opcode_alu32CompilableType).

Definition Const_byte_to_opcode_alu32 :=
  ltac: (mkprimitive byte_to_opcode_alu32
                (fun es => match es with
                           | [e1] => Ok (Csyntax.Ecast (Csyntax.Ebinop Cop.Oand e1 C_U8_0xf0 C_U8) C_U8)
                           | _       => Err PrimitiveEncodingFailed
                           end)).

Definition byte_to_opcode_branchSymbolType :=
  MkCompilableSymbolType [int8CompilableType] (Some opcode_branchCompilableType).

Instance COP_opcode_branch : CType opcode_branch := mkCType _ (cType opcode_branchCompilableType).

Definition Const_byte_to_opcode_branch :=
  ltac: (mkprimitive byte_to_opcode_branch
                (fun es => match es with
                           | [e1] => Ok (Csyntax.Ecast (Csyntax.Ebinop Cop.Oand e1 C_U8_0xf0 C_U8) C_U8)
                           | _       => Err PrimitiveEncodingFailed
                           end)).

Definition byte_to_opcode_mem_ld_immSymbolType :=
  MkCompilableSymbolType [int8CompilableType] (Some opcode_mem_ld_immCompilableType).

Instance COP_opcode_mem_ld_imm : CType opcode_mem_ld_imm := mkCType _ (cType opcode_mem_ld_immCompilableType).

Definition Const_byte_to_opcode_mem_ld_imm :=
  ltac: (mkprimitive byte_to_opcode_mem_ld_imm
                (fun es => match es with
                           | [e1] => Ok (Csyntax.Ecast (Csyntax.Ebinop Cop.Oand e1 C_U8_0xff C_U8) C_U8)
                           | _       => Err PrimitiveEncodingFailed
                           end)).

Definition byte_to_opcode_mem_ld_regSymbolType :=
  MkCompilableSymbolType [int8CompilableType] (Some opcode_mem_ld_regCompilableType).

Instance COP_opcode_mem_ld_reg : CType opcode_mem_ld_reg := mkCType _ (cType opcode_mem_ld_regCompilableType).

Definition Const_byte_to_opcode_mem_ld_reg :=
  ltac: (mkprimitive byte_to_opcode_mem_ld_reg
                (fun es => match es with
                           | [e1] => Ok (Csyntax.Ecast (Csyntax.Ebinop Cop.Oand e1 C_U8_0xff C_U8) C_U8)
                           | _       => Err PrimitiveEncodingFailed
                           end)).

Definition byte_to_opcode_mem_st_immSymbolType :=
  MkCompilableSymbolType [int8CompilableType] (Some opcode_mem_st_immCompilableType).

Instance COP_opcode_mem_st_imm : CType opcode_mem_st_imm := mkCType _ (cType opcode_mem_st_immCompilableType).

Definition Const_byte_to_opcode_mem_st_imm :=
  ltac: (mkprimitive byte_to_opcode_mem_st_imm
                (fun es => match es with
                           | [e1] => Ok (Csyntax.Ecast (Csyntax.Ebinop Cop.Oand e1 C_U8_0xff C_U8) C_U8)
                           | _       => Err PrimitiveEncodingFailed
                           end)).

Definition byte_to_opcode_mem_st_regSymbolType :=
  MkCompilableSymbolType [int8CompilableType] (Some opcode_mem_st_regCompilableType).

Instance COP_opcode_mem_st_reg : CType opcode_mem_st_reg := mkCType _ (cType opcode_mem_st_regCompilableType).

Definition Const_byte_to_opcode_mem_st_reg :=
  ltac: (mkprimitive byte_to_opcode_mem_st_reg
                (fun es => match es with
                           | [e1] => Ok (Csyntax.Ecast (Csyntax.Ebinop Cop.Oand e1 C_U8_0xff C_U8) C_U8)
                           | _       => Err PrimitiveEncodingFailed
                           end)).

>>>>>>> optimization_32
Close Scope Z_scope.

(**)

Module Exports.
<<<<<<< HEAD
  Definition opcodeMatchableType := opcodeMatchableType.
  Definition Const_int64_to_opcode := Const_int64_to_opcode.
=======
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
  Definition Const_byte_to_opcode                         := Const_byte_to_opcode.
  Definition Const_int64_to_opcode                        := Const_int64_to_opcode.
>>>>>>> optimization_32
End Exports.
