(**r: equivalence between bpf.model (with formal syntax + semantics) and bpf.src (for dx) *)

From bpf.comm Require Import State Monad.
From bpf.src Require Import DxInstructions.

From bpf.model Require Import Semantics.

Lemma equivalence_between_formal_and_dx_step:
  Semantics.step = DxInstructions.step.
Proof.
  unfold Semantics.step, DxInstructions.step.
  unfold DxMonad.bindM, DxMonad.upd_reg, DxMonad.eval_flag, DxMonad.eval_reg, DxMonad.returnM, DxMonad.eval_ins_len, DxMonad.eval_pc, DxMonad.upd_pc_incr, DxMonad.upd_flag, DxMonad.eval_ins.
  unfold DxIntegers.sint32_t, DxIntegers.int64_t, DxIntegers.int8_t, DxValues.val64_t, DxValues.valu32_t, DxValues.vals32_t.
Qed.

Lemma equivalence_between_formal_and_dx_aux:
  forall f,
    Semantics.bpf_interpreter_aux f = DxInstructions.bpf_interpreter_aux f.
Proof.
  unfold Semantics.bpf_interpreter_aux, DxInstructions.bpf_interpreter_aux.
  unfold DxMonad.bindM, DxMonad.upd_reg, DxMonad.eval_flag, DxMonad.eval_reg, DxMonad.returnM, DxMonad.eval_ins_len, DxMonad.eval_pc, DxMonad.upd_pc_incr, DxMonad.upd_flag.
  unfold DxIntegers.sint32_t.
  unfold DxIntegers.int32_0.
Qed.

Theorem equivalence_between_formal_and_dx:
  forall f,
    (**r we should give the register invariant and memory invariant as preconditions? *)
    Semantics.bpf_interpreter f = DxInstructions.bpf_interpreter f.
Proof.
  intros.
  unfold Semantics.bpf_interpreter, DxInstructions.bpf_interpreter.
  unfold DxMonad.bindM, DxMonad.upd_reg, DxMonad.eval_flag, DxMonad.eval_reg, DxMonad.returnM.
Qed.