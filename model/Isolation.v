From compcert Require Import Values.
From bpf.comm Require Import State Monad.
From bpf.model Require Import Syntax Semantics CommonLib AlignChunk RegsInv MemInv.

Theorem step_preserving_inv:
  forall st1 st2
    (Hreg: register_inv st1)
    (Hmem: memory_inv st1)
    (Hsem: step st1 = Some (tt, st2)),
       register_inv st2 /\ memory_inv st2.
Proof.
  unfold step.
Ltac unfold_monad :=
  match goal with
  | |- _ =>
    unfold bindM, eval_pc, eval_ins, decodeM, upd_reg, upd_pc, upd_pc_incr, eval_reg, eval_ins_len, get_immediate, returnM
  end.
  unfold_monad.
  intros.
  destruct (Decode.decode _) in Hsem.
  - (* BPF_NEG *)
    apply reg_inv_eval_reg with (r:= r) in Hreg as Heval_reg.
    destruct Heval_reg as (vl & Heval_reg).
    destruct a; rewrite Heval_reg in Hsem; simpl in Hsem.
    + split.
      inversion Hsem.
      eapply reg_inv_upd_reg; eauto.
      TBC.
Qed.