From Coq Require Import List ZArith.
Import ListNotations.

From compcert Require Import Integers.

From dx Require Import ResultMonad IR.

Require Import CoqIntegers DxZ DxIntegers.

Open Scope Z_scope.
Definition opcode_BPF_NEG32  := z_0x84.
Definition opcode_BPF_NEG64  := z_0x87.
Definition opcode_BPF_ADD32r := z_0x0c.
Definition opcode_BPF_ADD32i := z_0x04.
Definition opcode_BPF_ADD64r := z_0x0f.
Definition opcode_BPF_ADD64i := z_0x07.
Definition opcode_BPF_RET    := z_0x95.
Close Scope Z_scope.

Inductive opcode: Type :=
  | op_BPF_NEG32
  | op_BPF_NEG64
  | op_BPF_ADD32r
  | op_BPF_ADD32i
  | op_BPF_ADD64r
  | op_BPF_ADD64i
  | op_BPF_RET
  | op_BPF_ERROR_INS
.

Definition z_to_opcode (z:Z): opcode := 
  if (Z.eqb z opcode_BPF_ADD64i) then
    op_BPF_ADD64i
  else if (Z.eqb z opcode_BPF_ADD64r) then
    op_BPF_ADD64r
  else if (Z.eqb z opcode_BPF_NEG64) then
    op_BPF_NEG64
  else if (Z.eqb z opcode_BPF_ADD32i) then
    op_BPF_ADD32i
  else if (Z.eqb z opcode_BPF_ADD32r) then
    op_BPF_ADD32r
  else if (Z.eqb z opcode_BPF_NEG32) then
    op_BPF_NEG32
  else if (Z.eqb z opcode_BPF_RET) then
    op_BPF_RET
  else
    op_BPF_ERROR_INS.

(******************** Dx related *******************)
Definition opcodeCompilableType :=
  MkCompilableType opcode C_U32.

Definition zToopcodeSymbolType :=
  MkCompilableSymbolType [ZCompilableType] (Some opcodeCompilableType).

Definition Const_z_to_opcode :=
  MkPrimitive zToopcodeSymbolType
                z_to_opcode
                (fun es => match es with
                           | [e1] => Ok e1
                           | _       => Err PrimitiveEncodingFailed
                           end).

Definition opcodeMatchableType :=
  MkMatchableType opcodeCompilableType
    (fun x cases =>
      match cases with
      | [neg32; neg64; add32r; add32i; add64r; add64i; ret; err] =>
        Ok (Csyntax.Sswitch x
              (Csyntax.LScons (Some opcode_BPF_NEG32) neg32
                (Csyntax.LScons (Some opcode_BPF_NEG64) neg64
                  (Csyntax.LScons (Some opcode_BPF_ADD32r) add32r
                    (Csyntax.LScons (Some opcode_BPF_ADD32i) add32i
                      (Csyntax.LScons (Some opcode_BPF_ADD64r) add64r
                        (Csyntax.LScons (Some opcode_BPF_ADD64i) add64i
                          (Csyntax.LScons (Some opcode_BPF_RET) ret
                            (Csyntax.LScons None err
                          Csyntax.LSnil))))))))
            )
      | _ => Err MatchEncodingFailed
      end)
    [[]; []; []; []; []; []; []; []]
    [[]; []; []; []; []; []; []; []]
    (fun m A r whenneg32 whenneg64 whenadd32r whenadd32i whenadd64r whenadd64i whenret whenerr =>
      match r with
      | op_BPF_NEG32  => whenneg32
      | op_BPF_NEG64  => whenneg64
      | op_BPF_ADD32r => whenadd32r
      | op_BPF_ADD32i => whenadd32i
      | op_BPF_ADD64r => whenadd64r
      | op_BPF_ADD64i => whenadd64i
      | op_BPF_RET    => whenret
      | op_BPF_ERROR_INS => whenerr
      end).

Module Exports.
  Definition opcodeMatchableType := opcodeMatchableType.
  Definition Const_z_to_opcode := Const_z_to_opcode.
End Exports.
