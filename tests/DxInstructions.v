From Coq Require Import List ZArith.
Import ListNotations.

From compcert Require Import Integers Values AST Memory.

From dx.Type Require Import Bool Nat.

Require Import Int16 DxIntegers DxList64 DxRegs DxValues DxOpcode DxMonad DxFlag.


(** TODO: regarding the decode function: from int64 to bpf_instruction
  from: https://github.com/bergzand/RIOT/blob/10cecc628e89442777f2a798f6763e3f55ac9731/sys/include/bpf/instruction.h#L89

  typedef struct __attribute__((packed)) {
    uint8_t opcode;
    unsigned dst:4;
    unsigned src:4;
    int16_t offset;
    int32_t immediate;
} bpf_instruction_t;

In C, because `bpf_instruction_t` is int64 and it is a natural mapping from int64 bpf_instruction in C memory model,

However, compcert doesn't support `packed`, so we only can get a:

  typedef struct {
    uint8_t opcode;
    uint8_t dst_src; //here we need to translate it into above/similar structure
    int16_t offset;
    int32_t immediate;
} bpf_instruction_t;

and a decode function to get:

  typedef struct {
    uint8_t opcode;
    uint8_t dst;
    uint8_t src; //uint8_t or unsigned is ok
    int16_t offset;
    int32_t immediate;
} bpf_instruction_t;


There are two ways to do decode: 
  - loop exists: decode once
  - no loop: decode when necessary
*)

Open Scope monad_scope.

Definition list_get (l0: MyListType) (idx0: int64_t): M int64_t :=
  returnM (MyListIndex64 l0 idx0).

Definition get_opcode (ins0: int64_t): M opcode :=
  returnM (int64_to_opcode ins0).

Definition get_dst (ins1: int64_t): M reg :=
  returnM (int64_to_dst_reg ins1).

Definition get_src (ins2: int64_t): M reg :=
  returnM (int64_to_src_reg ins2).

Definition get_offset (i0:int64_t ):M sint16_t := returnM (int64_to_sint16 (Int64.shru (Int64.shl i0 int64_32) int64_48)).

Definition get_immediate (i1:int64_t):M vals32_t := returnM (val_intsoflongu (int64_to_vlong (Int64.shru i1 int64_32))).

Definition succ_return :M bpf_flag := returnM BPF_SUCC_RETURN.
Definition normal_return :M bpf_flag := returnM BPF_OK.
Definition ill_return :M bpf_flag := returnM BPF_ILLEGAL_INSTRUCTION.
Definition ill_len :M bpf_flag := returnM BPF_ILLEGAL_LEN.
Definition ill_div :M bpf_flag := returnM BPF_ILLEGAL_DIV.
Definition ill_shift :M bpf_flag := returnM BPF_ILLEGAL_SHIFT.

(** as I hope in C: ptr will be a `uint64 *ptr`, start_addr will be `uint64 *start_addr` and size is `uint32 *size`;
                    addr is `uint64`, chunk is `uint8`, m is `void`
                return: sint64
   The loadv/storev will run if the return value < 0, else report a memory error!!!
  *)

(*
Axiom region_ptr: MyListType.
Axiom region_start_addr: MyListType.
Axiom region_size: MyListType.

Fixpoint check_mem (num: nat) (addr: val) (chunk: memory_chunk) (m: mem): val :=
  match num with
  | O => Vundef (**r -1 *)
  | S n => 
    let ptr_i  := list_getnat region_ptr num in
    let start_addr_i := list_getnat region_start_addr num in
    let size_i := list_getnat region_size num in
    let ofs := Val.subl addr start_addr_i in
    let hi_ofs := Val.addl ofs (Vlong (Int64.repr (size_chunk chunk))) in
      if (andb (complu_le (Vlong Int64.zero) ofs) (complu_lt hi_ofs size_i)) then
        if (andb (complu_le ofs (Vlong (Int64.repr (Int64.max_unsigned-(size_chunk chunk)))))
                 (compl_eq (Vlong (Int64.zero)) (val64_modlu ofs (Vlong (Int64.repr (align_chunk chunk)))))) then
          Val.addl ptr_i ofs (**how to translate it to `true` *)
        else
          Vundef (**r -1 *)
      else
        check_mem n addr chunk m
  end.
*)


(** show pc < List.length l *)

Definition step (l0: MyListType) (len0: int64_t): M bpf_flag :=
  do pc <- eval_pc;
  do ins <- list_get l0 pc;
  do op <- get_opcode ins;
  do dst <- get_dst ins;
  do src <- get_src ins;
  do dst64 <- eval_reg dst;
  do src64 <- eval_reg src;
  do ofs <- get_offset ins; (* optiomiz...**)
  do imm <- get_immediate ins;
  match op with
  (** ALU64 *)
  | op_BPF_ADD64i   =>
    do _ <- upd_reg dst (Val.addl    dst64 (Val.longofintu imm));
      normal_return
  | op_BPF_ADD64r   => 
    do _ <- upd_reg dst (Val.addl    dst64 src64);
      normal_return

  | op_BPF_SUB64i   =>
    do _ <- upd_reg dst (Val.subl    dst64 (Val.longofintu imm));
      normal_return
  | op_BPF_SUB64r   =>
    do _ <- upd_reg dst (Val.subl    dst64 src64);
      normal_return

  | op_BPF_MUL64i   =>
    do _ <- upd_reg dst (Val.mull    dst64 (Val.longofintu imm));
      normal_return
  | op_BPF_MUL64r   =>
    do _ <- upd_reg dst (Val.mull    dst64 src64);
      normal_return
  (**r how to generate exit or printf function ? *)
  | op_BPF_DIV64i   =>
    if div64_checking (Val.longofintu imm) then
      do _ <- upd_reg dst (val64_divlu dst64 (Val.longofintu imm));
        normal_return
    else
      ill_div
  | op_BPF_DIV64r   =>
    if div64_checking src64 then
      do _ <- upd_reg dst (val64_divlu dst64 src64);
        normal_return
    else
      ill_div
  | op_BPF_OR64i    =>
    do _ <- upd_reg dst (Val.orl     dst64 (Val.longofintu imm));
        normal_return
  | op_BPF_OR64r    =>
    do _ <- upd_reg dst (Val.orl     dst64 (Val.longofintu imm));
        normal_return
  | op_BPF_AND64i   =>
    do _ <- upd_reg dst (Val.andl    dst64 (Val.longofintu imm));
        normal_return
  | op_BPF_AND64r   =>
    do _ <- upd_reg dst (Val.andl    dst64 (Val.longofintu imm));
        normal_return
  | op_BPF_LSH64i   =>
    if shift64_checking (Val.longofintu imm) then
      do _ <- upd_reg dst (Val.shll    dst64 imm);
        normal_return
    else
      ill_shift
  | op_BPF_LSH64r   =>
    if shift64_checking src64 then
      do _ <- upd_reg dst (Val.shll    dst64 (val_intuoflongu src64));
        normal_return
    else
      ill_shift
  | op_BPF_RSH64i   => 
    if shift64_checking (Val.longofintu imm) then
      do _ <- upd_reg dst (Val.shrlu   dst64 imm);
        normal_return
    else
      ill_shift
  | op_BPF_RSH64r   =>
    if shift64_checking src64 then
      do _ <- upd_reg dst (Val.shrlu   dst64 (val_intuoflongu src64));
        normal_return
    else
      ill_shift
  | op_BPF_NEG64    =>
    do _ <- upd_reg dst (Val.negl    dst64);
        normal_return
  | op_BPF_MOD64i   => 
    if div64_checking (Val.longofintu imm) then
      do _ <- upd_reg dst (val64_modlu dst64 imm);
        normal_return
    else
      ill_div
  | op_BPF_MOD64r   => 
    if div64_checking src64 then
      do _ <- upd_reg dst (val64_modlu dst64 (val_intuoflongu src64));
        normal_return
    else
      ill_div
  | op_BPF_XOR64i   =>
    do _ <- upd_reg dst (Val.xorl    dst64 (Val.longofintu imm));
        normal_return
  | op_BPF_XOR64r   =>
    do _ <- upd_reg dst (Val.xorl    dst64 src64);
        normal_return
  | op_BPF_MOV64i   =>
    do _ <- upd_reg dst (Val.longofintu imm);
        normal_return
  | op_BPF_MOV64r   =>
    do _ <- upd_reg dst src64;
        normal_return
  | op_BPF_ARSH64i  => 
    if shift64_checking (Val.longofintu imm) then
      do _ <- upd_reg dst (Val.shrl    dst64  imm);
        normal_return
    else
      ill_shift
  | op_BPF_ARSH64r  => 
    if shift64_checking src64 then
      do _ <- upd_reg dst (Val.shrl    dst64  (val_intuoflongu src64));
        normal_return
    else
      ill_shift
(*ALU32*)
  | op_BPF_ADD32i   =>
    do _ <- upd_reg dst (Val.longofintu (Val.add (val_intuoflongu dst64) imm));
        normal_return
  | op_BPF_ADD32r   =>
    do _ <- upd_reg dst (Val.longofintu (Val.add (val_intuoflongu dst64) (val_intuoflongu src64)));
        normal_return
  | op_BPF_SUB32i   =>
    do _ <- upd_reg dst (Val.longofintu (Val.sub (val_intuoflongu dst64) imm));
        normal_return
  | op_BPF_SUB32r   =>
    do _ <- upd_reg dst (Val.longofintu (Val.sub (val_intuoflongu dst64) (val_intuoflongu src64)));
        normal_return
  | op_BPF_MUL32i   =>
    do _ <- upd_reg dst (Val.longofintu (Val.mul (val_intuoflongu dst64) imm));
        normal_return
  | op_BPF_MUL32r   =>
    do _ <- upd_reg dst (Val.longofintu (Val.mul (val_intuoflongu dst64) (val_intuoflongu src64)));
        normal_return
  | op_BPF_DIV32i   =>
    if div32_checking imm then
      do _ <- upd_reg dst (Val.longofintu (val32_divu (val_intuoflongu dst64) imm));
        normal_return
    else
      ill_div
  | op_BPF_DIV32r   =>
    if div32_checking (val_intuoflongu src64) then
      do _ <- upd_reg dst (Val.longofintu (val32_divu (val_intuoflongu dst64) (val_intuoflongu src64)));
        normal_return
    else
      ill_div
  | op_BPF_OR32i   =>
    do _ <- upd_reg dst (Val.longofintu (Val.or  (val_intuoflongu dst64) imm));
        normal_return
  | op_BPF_OR32r   =>
    do _ <- upd_reg dst (Val.longofintu (Val.or  (val_intuoflongu dst64) (val_intuoflongu src64)));
        normal_return
  | op_BPF_AND32i   =>
    do _ <- upd_reg dst (Val.longofintu (Val.and (val_intuoflongu dst64) imm));
        normal_return
  | op_BPF_AND32r   =>
    do _ <- upd_reg dst (Val.longofintu (Val.and (val_intuoflongu dst64) (val_intuoflongu src64)));
        normal_return
  | op_BPF_LSH32i   =>
    if shift32_checking imm then
      do _ <- upd_reg dst (Val.longofintu (Val.shl (val_intuoflongu dst64) imm));
        normal_return
    else
      ill_shift
  | op_BPF_LSH32r   =>
    if shift32_checking (val_intuoflongu src64) then
      do _ <- upd_reg dst (Val.longofintu (Val.shl (val_intuoflongu dst64) (val_intuoflongu src64)));
        normal_return
    else
      ill_shift
  | op_BPF_RSH32i   =>
    if shift32_checking imm then
      do _ <- upd_reg dst (Val.longofintu (Val.shru (val_intuoflongu dst64) imm));
        normal_return
    else
      ill_shift
  | op_BPF_RSH32r   =>
    if shift32_checking (val_intuoflongu src64) then
      do _ <- upd_reg dst (Val.longofintu (Val.shru (val_intuoflongu dst64) (val_intuoflongu src64)));
        normal_return
    else
      ill_shift
  | op_BPF_NEG32    =>
    do _ <- upd_reg dst (Val.longofintu (Val.neg (val_intuoflongu (dst64))));
        normal_return
  | op_BPF_MOD32i   =>
    if div32_checking imm then
      do _ <- upd_reg dst (Val.longofintu (val32_modu (val_intuoflongu dst64) imm));
        normal_return
    else
      ill_div
  | op_BPF_MOD32r   =>
    if div32_checking (val_intuoflongu src64) then
      do _ <- upd_reg dst (Val.longofintu (val32_modu (val_intuoflongu dst64) (val_intuoflongu src64)));
        normal_return
    else
      ill_div
  | op_BPF_XOR32i   =>
    do _ <- upd_reg dst (Val.longofintu (Val.xor (val_intuoflongu dst64) imm));
        normal_return
  | op_BPF_XOR32r   =>
    do _ <- upd_reg dst (Val.longofintu (Val.xor (val_intuoflongu dst64) (val_intuoflongu src64)));
        normal_return
  | op_BPF_MOV32i   =>
    do _ <- upd_reg dst imm;
        normal_return
  | op_BPF_MOV32r   =>
    do _ <- upd_reg dst (val_intuoflongu src64);
        normal_return
  | op_BPF_ARSH32i  =>
    if shift32_checking imm then
      do _ <- upd_reg dst (Val.longofintu (Val.shr (val_intuoflongu dst64) imm));
        normal_return
    else
      ill_shift
  | op_BPF_ARSH32r  =>
    if shift32_checking (val_intuoflongu src64) then
      do _ <- upd_reg dst (Val.longofintu (Val.shr (val_intuoflongu dst64) (val_intuoflongu src64)));
        normal_return
    else
      ill_shift
  (**Branch: 23 *)
  | op_BPF_JA       =>
     do _ <- upd_pc (Int64.add pc (sint16_to_int64 ofs));
        normal_return
  | op_BPF_JEQi     =>
    if compl_eq dst64 (Val.longofintu imm) then
      do _ <- upd_pc (Int64.add pc (sint16_to_int64 ofs));
        normal_return
    else
      normal_return
  | op_BPF_JEQr     =>
    if compl_eq dst64 src64 then
      do _ <- upd_pc (Int64.add pc (sint16_to_int64 ofs));
        normal_return
    else
      normal_return
  | op_BPF_JGTi     =>
    if complu_gt dst64 (Val.longofintu imm) then
      do _ <- upd_pc (Int64.add pc (sint16_to_int64 ofs));
        normal_return
    else
      normal_return
  | op_BPF_JGTr     =>
    if complu_gt dst64 src64 then
      do _ <- upd_pc (Int64.add pc (sint16_to_int64 ofs));
        normal_return
    else
      normal_return
  | op_BPF_JGEi     =>
    if complu_ge dst64 (Val.longofintu imm) then
      do _ <- upd_pc (Int64.add pc (sint16_to_int64 ofs));
        normal_return
    else
      normal_return
  | op_BPF_JGEr     =>
    if complu_ge dst64 src64 then
      do _ <- upd_pc (Int64.add pc (sint16_to_int64 ofs));
        normal_return
    else
      normal_return
  | op_BPF_JLTi     =>
    if complu_lt dst64 (Val.longofintu imm) then
      do _ <- upd_pc (Int64.add pc (sint16_to_int64 ofs));
        normal_return
    else
      normal_return
  | op_BPF_JLTr     =>
    if complu_lt dst64 src64 then
      do _ <- upd_pc (Int64.add pc (sint16_to_int64 ofs));
        normal_return
    else
      normal_return
  | op_BPF_JLEi     =>
    if complu_le dst64 (Val.longofintu imm) then
      do _ <- upd_pc (Int64.add pc (sint16_to_int64 ofs));
        normal_return
    else
      normal_return
  | op_BPF_JLEr     =>
    if complu_le dst64 src64 then
      do _ <- upd_pc (Int64.add pc (sint16_to_int64 ofs));
        normal_return
    else
      normal_return
  | op_BPF_JSETi     =>
    if complu_set dst64 (Val.longofintu imm) then
      do _ <- upd_pc (Int64.add pc (sint16_to_int64 ofs));
        normal_return
    else
      normal_return
  | op_BPF_JSETr     =>
    if complu_set dst64 src64 then
      do _ <- upd_pc (Int64.add pc (sint16_to_int64 ofs));
        normal_return
    else
      normal_return
  | op_BPF_JNEi     =>
    if compl_ne dst64 (Val.longofintu imm) then
      do _ <- upd_pc (Int64.add pc (sint16_to_int64 ofs));
        normal_return
    else
      normal_return
  | op_BPF_JNEr     =>
    if compl_ne dst64 src64 then
      do _ <- upd_pc (Int64.add pc (sint16_to_int64 ofs));
        normal_return
    else
      normal_return
  | op_BPF_JSGTi     =>
    if compl_gt dst64 (Val.longofintu imm) then
      do _ <- upd_pc (Int64.add pc (sint16_to_int64 ofs));
        normal_return
    else
      normal_return
  | op_BPF_JSGTr     =>
    if compl_gt dst64 src64 then
      do _ <- upd_pc (Int64.add pc (sint16_to_int64 ofs));
        normal_return
    else
      normal_return
  | op_BPF_JSGEi     =>
    if compl_ge dst64 (Val.longofintu imm) then
      do _ <- upd_pc (Int64.add pc (sint16_to_int64 ofs));
        normal_return
    else
      normal_return
  | op_BPF_JSGEr     =>
    if compl_ge dst64 src64 then
      do _ <- upd_pc (Int64.add pc (sint16_to_int64 ofs));
        normal_return
    else
      normal_return
  | op_BPF_JSLTi     =>
    if compl_lt dst64 (Val.longofintu imm) then
      do _ <- upd_pc (Int64.add pc (sint16_to_int64 ofs));
        normal_return
    else
      normal_return
  | op_BPF_JSLTr     =>
    if compl_lt dst64 src64 then
      do _ <- upd_pc (Int64.add pc (sint16_to_int64 ofs));
        normal_return
    else
      normal_return
  | op_BPF_JSLEi     =>
    if compl_le dst64 (Val.longofintu imm) then
      do _ <- upd_pc (Int64.add pc (sint16_to_int64 ofs));
        normal_return
    else
      normal_return
  | op_BPF_JSLEr     =>
    if compl_le dst64 src64 then
      do _ <- upd_pc (Int64.add pc (sint16_to_int64 ofs));
        normal_return
    else
      normal_return
  (** Load/Store: 13 *)
  | op_BPF_LDDW      =>
    if (Int64.ltu (Int64.add pc Int64.one) len0) then (**r pc+1 < len: pc+1 is less than the length of l *)
      do next_ins <- list_get l0 (Int64.add pc Int64.one);
      do next_imm <- get_immediate next_ins;
      do _ <- upd_reg dst (Val.or (Val.longofint imm) (Val.shl  (Val.longofint next_imm) (int64_to_vlong int64_32)));
      do _ <- upd_pc (Int64.add pc Int64.one);
        normal_return
    else
      ill_len
  | op_BPF_LDXW      =>
    do v_xw <- load_mem Mint32 (Val.addl src64 (sint16_to_vlong ofs));
    do _ <- upd_reg_mem Mint32 dst v_xw;
      normal_return
  | op_BPF_LDXH      =>
    do v_xh <- load_mem Mint16unsigned (Val.addl src64 (sint16_to_vlong ofs));
    do _ <- upd_reg_mem Mint16unsigned dst v_xh;
      normal_return
  | op_BPF_LDXB      =>
    do v_xb <- load_mem Mint8unsigned (Val.addl src64 (sint16_to_vlong ofs));
    do _ <- upd_reg_mem Mint8unsigned dst v_xb;
      normal_return
  | op_BPF_LDXDW     =>
    do v_xdw <- load_mem Mint64 (Val.addl src64 (sint16_to_vlong ofs));
    do _ <- upd_reg_mem Mint64 dst v_xdw;
      normal_return
  | op_BPF_STW       =>
    do _ <- store_mem Mint32 (Val.addl dst64 (sint16_to_vlong ofs)) (Val.longofint imm);
      normal_return
  | op_BPF_STH       =>
    do _ <- store_mem Mint16unsigned (Val.addl dst64 (sint16_to_vlong ofs)) (Val.longofint imm);
      normal_return
  | op_BPF_STB       =>
    do _ <- store_mem Mint8unsigned (Val.addl dst64 (sint16_to_vlong ofs)) (Val.longofint imm);
      normal_return
  | op_BPF_STDW      =>
    do _ <- store_mem Mint64 (Val.addl dst64 (sint16_to_vlong ofs)) (Val.longofint imm);
      normal_return
  | op_BPF_STXW      =>
    do _ <- store_mem Mint32 (Val.addl dst64 (sint16_to_vlong ofs)) src64;
      normal_return
  | op_BPF_STXH      =>
    do _ <- store_mem Mint16unsigned (Val.addl dst64 (sint16_to_vlong ofs)) src64;
      normal_return
  | op_BPF_STXB      =>
    do _ <- store_mem Mint8unsigned (Val.addl dst64 (sint16_to_vlong ofs)) src64;
      normal_return
  | op_BPF_STXDW     =>
    do _ <- store_mem Mint64 (Val.addl dst64 (sint16_to_vlong ofs)) src64;
      normal_return

  | op_BPF_RET => succ_return
  | _ =>  ill_return
  end.

Fixpoint bpf_interpreter_aux (l1: MyListType) (len1: int64_t) (fuel1: nat) {struct fuel1}: M bpf_flag :=
  match fuel1 with
  | O => ill_len
  | S fuel0 =>
    do pc1 <- eval_pc;
      if Int64.ltu pc1 len1 then (**r pc < len: pc is less than the length of l *)
        do f1 <- step l1 len1;
        do _ <- upd_pc (Int64.add pc1 Int64.one);
          if flag_eq f1 BPF_OK then
            bpf_interpreter_aux l1 len1 fuel0
          else
            returnM f1
      else
        ill_len
  end.

Definition bpf_interpreter (l2: MyListType) (len2: int64_t) (fuel2: nat): M val64_t :=
  do f2 <- bpf_interpreter_aux l2 len2 fuel2;
    if flag_eq f2 BPF_SUCC_RETURN then
      eval_reg R0
    else
      returnM val64_zero.

Close Scope monad_scope.