From Coq Require Import List ZArith.
Import ListNotations.

From compcert Require Import Integers.

From dx Require Import ResultMonad IR.

Require Import CoqIntegers DxIntegers InfComp.

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
Definition opcodeCompilableType :=
  MkCompilableType opcode C_U8.

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


Definition opcodeMatchableType :=
  MkMatchableType opcodeCompilableType
    (fun x cases =>
      match cases with
      | [ ADD64i; ADD64r; SUB64i; SUB64r; MUL64i; MUL64r; DIV64i; DIV64r;
          OR64i;  OR64r;  AND64i; AND64r; LSH64i; LSH64r; RSH64i; RSH64r;
          NEG64;  MOD64i; MOD64r; XOR64i; XOR64r; MOV64i; MOV64r; ARSH64i; ARSH64r;
          ADD32i; ADD32r; SUB32i; SUB32r; MUL32i; MUL32r; DIV32i; DIV32r;
          OR32i;  OR32r;  AND32i; AND32r; LSH32i; LSH32r; RSH32i; RSH32r;
          NEG32;  MOD32i; MOD32r; XOR32i; XOR32r; MOV32i; MOV32r; ARSH32i; ARSH32r;
          JA; JEQi; JEQr; JGTi; JGTr; JGEi; JGEr; JLTi; JLTr; JLEi; JLEr; JSETi;
          JSETr; JNEi; JNEr; JSGTi; JSGTr; JSGEi; JSGEr; JSLTi; JSLTr; JSLEi; JSLEr;
          LDDW; LDXW; LDXH; LDXB; LDXDW; STW; STH; STB; STDW; STXW; STXH; STXB; STXDW;
          RET; ERR] =>
        Ok (Csyntax.Sswitch x
              (*ALU64*)
              (Csyntax.LScons (Some 0x07) ADD64i
              (Csyntax.LScons (Some 0x0f) ADD64r
              (Csyntax.LScons (Some 0x17) SUB64i
              (Csyntax.LScons (Some 0x1f) SUB64r
              (Csyntax.LScons (Some 0x27) MUL64i
              (Csyntax.LScons (Some 0x2f) MUL64r
              (Csyntax.LScons (Some 0x37) DIV64i
              (Csyntax.LScons (Some 0x3f) DIV64r
              (Csyntax.LScons (Some 0x47) OR64i
              (Csyntax.LScons (Some 0x4f) OR64r
              (Csyntax.LScons (Some 0x57) AND64i
              (Csyntax.LScons (Some 0x5f) AND64r
              (Csyntax.LScons (Some 0x67) LSH64i
              (Csyntax.LScons (Some 0x6f) LSH64r
              (Csyntax.LScons (Some 0x77) RSH64i
              (Csyntax.LScons (Some 0x7f) RSH64r
              (Csyntax.LScons (Some 0x87) NEG64
              (Csyntax.LScons (Some 0x97) MOD64i
              (Csyntax.LScons (Some 0x9f) MOD64r
              (Csyntax.LScons (Some 0xa7) XOR64i
              (Csyntax.LScons (Some 0xaf) XOR64r
              (Csyntax.LScons (Some 0xb7) MOV64i
              (Csyntax.LScons (Some 0xbf) MOV64r
              (Csyntax.LScons (Some 0xc7) ARSH64i
              (Csyntax.LScons (Some 0xcf) ARSH64r
              (*ALU32*)
              (Csyntax.LScons (Some 0x04) ADD32i
              (Csyntax.LScons (Some 0x0c) ADD32r
              (Csyntax.LScons (Some 0x14) SUB32i
              (Csyntax.LScons (Some 0x1c) SUB32r
              (Csyntax.LScons (Some 0x24) MUL32i
              (Csyntax.LScons (Some 0x2c) MUL32r
              (Csyntax.LScons (Some 0x34) DIV32i
              (Csyntax.LScons (Some 0x3c) DIV32r
              (Csyntax.LScons (Some 0x44) OR32i
              (Csyntax.LScons (Some 0x4c) OR32r
              (Csyntax.LScons (Some 0x54) AND32i
              (Csyntax.LScons (Some 0x5c) AND32r
              (Csyntax.LScons (Some 0x64) LSH32i
              (Csyntax.LScons (Some 0x6c) LSH32r
              (Csyntax.LScons (Some 0x74) RSH32i
              (Csyntax.LScons (Some 0x7c) RSH32r
              (Csyntax.LScons (Some 0x84) NEG32
              (Csyntax.LScons (Some 0x94) MOD32i
              (Csyntax.LScons (Some 0x9c) MOD32r
              (Csyntax.LScons (Some 0xa4) XOR32i
              (Csyntax.LScons (Some 0xac) XOR32r
              (Csyntax.LScons (Some 0xb4) MOV32i
              (Csyntax.LScons (Some 0xbc) MOV32r
              (Csyntax.LScons (Some 0xc4) ARSH32i
              (Csyntax.LScons (Some 0xcc) ARSH32r
              (*Branch*)
              (Csyntax.LScons (Some 0x05) JA
              (Csyntax.LScons (Some 0x15) JEQi
              (Csyntax.LScons (Some 0x1d) JEQr
              (Csyntax.LScons (Some 0x25) JGTi
              (Csyntax.LScons (Some 0x2d) JGTr
              (Csyntax.LScons (Some 0x35) JGEi
              (Csyntax.LScons (Some 0x3d) JGEr
              (Csyntax.LScons (Some 0xa5) JLTi
              (Csyntax.LScons (Some 0xad) JLTr
              (Csyntax.LScons (Some 0xb5) JLEi
              (Csyntax.LScons (Some 0xbd) JLEr
              (Csyntax.LScons (Some 0x45) JSETi
              (Csyntax.LScons (Some 0x4d) JSETr
              (Csyntax.LScons (Some 0x55) JNEi
              (Csyntax.LScons (Some 0x5d) JNEr
              (Csyntax.LScons (Some 0x65) JSGTi
              (Csyntax.LScons (Some 0x6d) JSGTr
              (Csyntax.LScons (Some 0x75) JSGEi
              (Csyntax.LScons (Some 0x7d) JSGEr
              (Csyntax.LScons (Some 0xc5) JSLTi
              (Csyntax.LScons (Some 0xcd) JSLTr
              (Csyntax.LScons (Some 0xd5) JSLEi
              (Csyntax.LScons (Some 0xdd) JSLEr
              (*Load/Store*)
              (Csyntax.LScons (Some 0x18) LDDW
              (Csyntax.LScons (Some 0x61) LDXW
              (Csyntax.LScons (Some 0x69) LDXH
              (Csyntax.LScons (Some 0x71) LDXB
              (Csyntax.LScons (Some 0x79) LDXDW
              (Csyntax.LScons (Some 0x62) STW
              (Csyntax.LScons (Some 0x6a) STH
              (Csyntax.LScons (Some 0x72) STB
              (Csyntax.LScons (Some 0x7a) STDW
              (Csyntax.LScons (Some 0x63) STXW
              (Csyntax.LScons (Some 0x6b) STXH
              (Csyntax.LScons (Some 0x73) STXB
              (Csyntax.LScons (Some 0x7b) STXDW

              (Csyntax.LScons (Some 0x95) RET
              (Csyntax.LScons None ERR
               Csyntax.LSnil))
              )))))))))))))
              )))))))))))))))))))))))
              )))))))))))))))))))))))))
              )))))))))))))))))))))))))
            )
      | _ => Err MatchEncodingFailed
      end)
    [ []; []; []; []; []; []; []; []; []; []; []; []; []; []; []; []; []; []; []; []; []; []; []; []; [];
      []; []; []; []; []; []; []; []; []; []; []; []; []; []; []; []; []; []; []; []; []; []; []; []; [];
      []; []; []; []; []; []; []; []; []; []; []; []; []; []; []; []; []; []; []; []; []; []; [];
      []; []; []; []; []; []; []; []; []; []; []; []; [];
      []; []
    ]
    [ []; []; []; []; []; []; []; []; []; []; []; []; []; []; []; []; []; []; []; []; []; []; []; []; [];
      []; []; []; []; []; []; []; []; []; []; []; []; []; []; []; []; []; []; []; []; []; []; []; []; [];
      []; []; []; []; []; []; []; []; []; []; []; []; []; []; []; []; []; []; []; []; []; []; [];
      []; []; []; []; []; []; []; []; []; []; []; []; [];
      []; []
    ]
    (fun m A r w00 w01 w02 w03 w04 w05 w06 w07 w08 w09
               w10 w11 w12 w13 w14 w15 w16 w17 w18 w19
               w20 w21 w22 w23 w24 w25 w26 w27 w28 w29
               w30 w31 w32 w33 w34 w35 w36 w37 w38 w39
               w40 w41 w42 w43 w44 w45 w46 w47 w48 w49
               w50 w51 w52 w53 w54 w55 w56 w57 w58 w59
               w60 w61 w62 w63 w64 w65 w66 w67 w68 w69
               w70 w71 w72 w73 w74 w75 w76 w77 w78 w79
               w80 w81 w82 w83 w84 w85
               w86 w87
     =>
      match r with
      (** ALU64:25 *)
      | op_BPF_ADD64i => w00
      | op_BPF_ADD64r => w01
      | op_BPF_SUB64i => w02
      | op_BPF_SUB64r => w03
      | op_BPF_MUL64i => w04
      | op_BPF_MUL64r => w05
      | op_BPF_DIV64i => w06
      | op_BPF_DIV64r => w07
      | op_BPF_OR64i  => w08
      | op_BPF_OR64r  => w09
      | op_BPF_AND64i => w10
      | op_BPF_AND64r => w11
      | op_BPF_LSH64i => w12
      | op_BPF_LSH64r => w13
      | op_BPF_RSH64i => w14
      | op_BPF_RSH64r => w15
      | op_BPF_NEG64  => w16
      | op_BPF_MOD64i => w17
      | op_BPF_MOD64r => w18
      | op_BPF_XOR64i => w19
      | op_BPF_XOR64r => w20
      | op_BPF_MOV64i => w21
      | op_BPF_MOV64r => w22
      | op_BPF_ARSH64i => w23
      | op_BPF_ARSH64r => w24
      (** ALU32:25 *)
      | op_BPF_ADD32i => w25
      | op_BPF_ADD32r => w26
      | op_BPF_SUB32i => w27
      | op_BPF_SUB32r => w28
      | op_BPF_MUL32i => w29
      | op_BPF_MUL32r => w30
      | op_BPF_DIV32i => w31
      | op_BPF_DIV32r => w32
      | op_BPF_OR32i  => w33
      | op_BPF_OR32r  => w34
      | op_BPF_AND32i => w35
      | op_BPF_AND32r => w36
      | op_BPF_LSH32i => w37
      | op_BPF_LSH32r => w38
      | op_BPF_RSH32i => w39
      | op_BPF_RSH32r => w40
      | op_BPF_NEG32  => w41
      | op_BPF_MOD32i => w42
      | op_BPF_MOD32r => w43
      | op_BPF_XOR32i => w44
      | op_BPF_XOR32r => w45
      | op_BPF_MOV32i => w46
      | op_BPF_MOV32r => w47
      | op_BPF_ARSH32i => w48
      | op_BPF_ARSH32r => w49
      (**Branch: 23 *)
      | op_BPF_JA   => w50
      | op_BPF_JEQi => w51
      | op_BPF_JEQr => w52
      | op_BPF_JGTi => w53
      | op_BPF_JGTr => w54
      | op_BPF_JGEi => w55
      | op_BPF_JGEr => w56
      | op_BPF_JLTi => w57
      | op_BPF_JLTr => w58
      | op_BPF_JLEi => w59
      | op_BPF_JLEr => w60
      | op_BPF_JSETi => w61
      | op_BPF_JSETr => w62
      | op_BPF_JNEi  => w63
      | op_BPF_JNEr  => w64
      | op_BPF_JSGTi => w65
      | op_BPF_JSGTr => w66
      | op_BPF_JSGEi => w67
      | op_BPF_JSGEr => w68
      | op_BPF_JSLTi => w69
      | op_BPF_JSLTr => w70
      | op_BPF_JSLEi => w71
      | op_BPF_JSLEr => w72 
      (** Load/Store: 13 *)
      | op_BPF_LDDW  => w73
      | op_BPF_LDXW  => w74
      | op_BPF_LDXH  => w75
      | op_BPF_LDXB  => w76
      | op_BPF_LDXDW => w77
      | op_BPF_STW   => w78
      | op_BPF_STH   => w79
      | op_BPF_STB   => w80
      | op_BPF_STDW  => w81
      | op_BPF_STXW  => w82
      | op_BPF_STXH  => w83
      | op_BPF_STXB  => w84
      | op_BPF_STXDW => w85

      | op_BPF_RET   => w86
      | op_BPF_ERROR_INS  => w87
      end).
Close Scope Z_scope.

(**)

Module Exports.
  Definition opcodeMatchableType := opcodeMatchableType.
  Definition Const_int64_to_opcode := Const_int64_to_opcode.
End Exports.
