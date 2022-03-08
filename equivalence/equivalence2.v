From Coq Require Import Logic.FunctionalExtensionality ZArith Lia.
From compcert Require Import Integers Values Memory Memdata.

From bpf.comm Require Import State Monad.
From bpf.src Require Import DxInstructions.

From bpf.monadicmodel Require Import Opcode rBPFInterpreter.

Ltac unfold_monad :=
  match goal with
  | |- _ =>
    unfold bindM, returnM
  end.

Ltac unfold_dx_type :=
  match goal with
  | |- _ =>
    unfold DxMonad.bindM, DxMonad.upd_reg, DxMonad.eval_flag, DxMonad.eval_reg, DxMonad.returnM, DxMonad.eval_ins_len, DxMonad.eval_pc, DxMonad.upd_pc_incr, DxMonad.upd_flag, DxMonad.eval_ins;
    unfold Opcode.int64_to_opcode;
    unfold DxIntegers.sint32_t, DxIntegers.int64_t, DxNat.nat8, DxValues.val64_t, DxValues.valu32_t, DxValues.vals32_t;
  unfold_monad
  end.

Ltac unfold_dx_name :=
  match goal with
  | |- _ =>
    unfold DxNat.nat8_zero, DxNat.nat8_0x08, DxNat.nat8_0x07, DxIntegers.int64_0xff, DxIntegers.int64_32, DxNat.nat8_0xf0, DxIntegers.int64_64, DxValues.val32_64, DxIntegers.int64_48, DxNat.nat8_0xff, DxValues.val64_zero, Regs.val64_zero, DxIntegers.int32_0, DxIntegers.int32_64
  end.

Ltac unfold_dx :=
  match goal with
  | |- _ =>
    unfold get_opcode_ins, get_opcode, Opcode.byte_to_opcode;
    unfold_dx_name; unfold_dx_type
  end.

Open Scope Z_scope.

Lemma equivalence_between_coq_and_dx_step:
  DxInstructions.step = rBPFInterpreter.step.
Proof.
  unfold rBPFInterpreter.step, DxInstructions.step.
  apply functional_extensionality.
  unfold_dx.
  intros.
  unfold DxInstructions.get_opcode_ins, DxInstructions.get_opcode, eval_pc, eval_ins.
  unfold_dx.
  unfold DxInstructions.get_dst, DxInstructions.get_src64, DxInstructions.get_src32, DxInstructions.get_immediate, DxInstructions.eval_immediate, DxInstructions.step_opcode_alu64, DxInstructions.get_src; unfold_dx.
  unfold get_dst, DxInstructions.step_opcode_mem_ld_imm; unfold_dx.
  unfold DxInstructions.get_opcode_mem_ld_imm, DxInstructions.get_immediate; unfold_dx.
  match goal with
  | |- context[(if ?X then _ else _) ] =>
    destruct X; [| reflexivity]
  end.
  destruct (match
    Nat.land
      (Z.to_nat
         (Int64.unsigned
            (Int64.and (State.eval_ins (State.eval_pc x) x) (Int64.repr 255))))
      7
  with
  | 0%nat => op_BPF_Mem_ld_imm
  | 1%nat => op_BPF_Mem_ld_reg
  | 2%nat => op_BPF_Mem_st_imm
  | 3%nat => op_BPF_Mem_st_reg
  | 4%nat => op_BPF_ALU32
  | 5%nat => op_BPF_Branch
  | 7%nat => op_BPF_ALU64
  | _ => op_BPF_ILLEGAL_INS
  end) eqn: Hopcode; unfold eval_reg, get_src64, get_src32; unfold_dx.
  - unfold DxInstructions.get_opcode_alu64; unfold_dx.
    unfold get_immediate, eval_immediate, step_opcode_alu64; unfold_dx.
    unfold get_opcode_alu64, DxValues.Val_slongofint, get_src, upd_reg; unfold_dx.
    unfold DxMonad.int64_to_dst_reg. TBC.
    destruct int64_to_dst_reg; [| reflexivity].
    destruct p.
    destruct (Nat.land
      (Z.to_nat
         (Z.land
            (Int.unsigned
               (Int.repr
                  (Int64.unsigned
                     (Int64.and (State.eval_ins (State.eval_pc x) x)
                        (Int64.repr 255))))) 255)) 7).
    + 
    + destruct (byte_to_opcode_alu64
    (Z.to_nat
       (Int64.unsigned
          (Int64.and (State.eval_ins (State.eval_pc x) x) (Int64.repr 255))))).
      all: try reflexivity.
    + destruct (byte_to_opcode_alu64
    (Z.to_nat
       (Int64.unsigned
          (Int64.and (State.eval_ins (State.eval_pc x) x) (Int64.repr 255))))).
      all: simpl; try reflexivity.
  - unfold eval_reg, get_src64, get_src32; unfold_dx.
    unfold DxInstructions.reg64_to_reg32, reg64_to_reg32; unfold_dx.
    destruct ((0 =?
   Nat.land
     (Z.to_nat
        (Int64.unsigned
           (Int64.and (State.eval_ins (State.eval_pc x) x) (Int64.repr 255))))
     8)%nat); unfold DxInstructions.step_opcode_alu32, DxInstructions.get_opcode_alu32; unfold_dx; unfold get_immediate, step_opcode_alu32, get_opcode_alu32; unfold_dx;
      destruct (byte_to_opcode_alu32
    (Z.to_nat
       (Int64.unsigned
          (Int64.and (State.eval_ins (State.eval_pc x) x) (Int64.repr 255))))); simpl; try reflexivity.
  - unfold DxInstructions.get_offset, DxInstructions.step_opcode_branch, get_offset, get_immediate, eval_immediate, get_src, step_opcode_branch; unfold_dx.
    unfold get_opcode_branch, DxInstructions.get_opcode_branch; unfold_dx.
    destruct ((0 =?
   Nat.land
     (Z.to_nat
        (Int64.unsigned
           (Int64.and (State.eval_ins (State.eval_pc x) x) (Int64.repr 255))))
     8)%nat); simpl; try reflexivity.
  - unfold byte_to_opcode_mem_ld_imm, eval_ins, get_immediate, step_opcode_mem_ld_imm, get_opcode_mem_ld_imm, byte_to_opcode_mem_ld_imm, eval_ins_len; unfold_dx.
    destruct (match
    Nat.land
      (Z.to_nat
         (Int64.unsigned
            (Int64.and (State.eval_ins (State.eval_pc x) x) (Int64.repr 255))))
      255
  with
  | 24%nat => op_BPF_LDDW
  | _ => op_BPF_LDX_IMM_ILLEGAL_INS
  end); simpl; try reflexivity.
  - unfold DxInstructions.get_offset, DxInstructions.get_addr_ofs, DxInstructions.step_opcode_mem_ld_reg, get_src, get_offset, get_addr_ofs, step_opcode_mem_ld_reg; unfold_dx.
    unfold DxInstructions.get_opcode_mem_ld_reg, get_opcode_mem_ld_reg, byte_to_opcode_mem_ld_reg; unfold_dx.
    destruct (match
    Nat.land
      (Z.to_nat
         (Int64.unsigned
            (Int64.and (State.eval_ins (State.eval_pc x) x) (Int64.repr 255))))
      255
  with
  | 97%nat => op_BPF_LDXW
  | 105%nat => op_BPF_LDXH
  | 113%nat => op_BPF_LDXB
  | 121%nat => op_BPF_LDXDW
  | _ => op_BPF_LDX_REG_ILLEGAL_INS
  end); simpl; try reflexivity.
  - unfold DxInstructions.get_offset, DxInstructions.get_addr_ofs, DxInstructions.step_opcode_mem_st_imm, get_offset, get_immediate, get_addr_ofs, step_opcode_mem_st_imm, DxInstructions.get_opcode_mem_st_imm, get_opcode_mem_st_imm; unfold_dx.
    unfold byte_to_opcode_mem_st_imm, byte_to_opcode_mem_st_imm; unfold_dx.
    destruct (match
    Nat.land
      (Z.to_nat
         (Int64.unsigned
            (Int64.and (State.eval_ins (State.eval_pc x) x) (Int64.repr 255))))
      255
  with
  | 98%nat => op_BPF_STW
  | 106%nat => op_BPF_STH
  | 114%nat => op_BPF_STB
  | 122%nat => op_BPF_STDW
  | _ => op_BPF_ST_ILLEGAL_INS
  end); simpl; try reflexivity.
  - unfold DxInstructions.get_offset, DxInstructions.get_addr_ofs, DxInstructions.step_opcode_mem_st_reg, get_offset, get_immediate, get_addr_ofs, step_opcode_mem_st_reg, DxInstructions.get_opcode_mem_st_reg, get_opcode_mem_st_reg; unfold_dx.
    unfold byte_to_opcode_mem_st_reg, byte_to_opcode_mem_st_reg; unfold_dx.
    destruct (match
    Nat.land
      (Z.to_nat
         (Int64.unsigned
            (Int64.and (State.eval_ins (State.eval_pc x) x) (Int64.repr 255))))
      255
  with
  | 99%nat => op_BPF_STXW
  | 107%nat => op_BPF_STXH
  | 115%nat => op_BPF_STXB
  | 123%nat => op_BPF_STXDW
  | _ => op_BPF_STX_ILLEGAL_INS
  end); simpl; try reflexivity.
  - reflexivity.
Qed.

Lemma equivalence_between_coq_and_dx_aux:
  forall f,
    rBPFInterpreter.bpf_interpreter_aux f = DxInstructions.bpf_interpreter_aux f.
Proof.
  unfold rBPFInterpreter.bpf_interpreter_aux, DxInstructions.bpf_interpreter_aux.
  unfold DxMonad.bindM, DxMonad.upd_reg, DxMonad.eval_flag, DxMonad.eval_reg, DxMonad.returnM, DxMonad.eval_ins_len, DxMonad.eval_pc, DxMonad.upd_pc_incr, DxMonad.upd_flag.
  unfold DxIntegers.sint32_t.
  unfold DxIntegers.int32_0.
  rewrite equivalence_between_coq_and_dx_step.
  reflexivity.
Qed.

Theorem equivalence_between_coq_and_dx_dx:
  forall f,
    rBPFInterpreter.bpf_interpreter f = DxInstructions.bpf_interpreter f.
Proof.
  intros.
  unfold rBPFInterpreter.bpf_interpreter, DxInstructions.bpf_interpreter.
  unfold DxMonad.bindM, DxMonad.upd_reg, DxMonad.eval_flag, DxMonad.eval_reg, DxMonad.returnM.
  rewrite equivalence_between_coq_and_dx_aux.
  reflexivity.
Qed.

Close Scope Z_scope.