(** Definition of matching relation between Coq and C representation *)

From dx.tests Require Import DxIntegers DxValues DxAST DxMemRegion DxRegs DxState DxMonad.
From compcert Require Import Coqlib Integers Values AST Clight Memory.

(**
struct memory_region {
  unsigned long long start_addr;
  unsigned long long block_size;
  unsigned long long block_ptr_id;
};

struct memory_regions {
  struct memory_region* bpf_ctx;
  struct memory_region* bpf_stk;
  struct memory_region* content;
};

struct bpf_state {
  unsigned long long state_pc;
  unsigned long long regsmap[11];
  int bpf_flag;
  struct memory_regions *mrs;
};
*)

Open Scope Z_scope.
(** state_block:  (ofs : ptrofs) starts from 0
    so, the stM should be the initial state before running the functions/operations
 *)
Definition match_state_block (stM: stateM) (blk: block) (m: mem) : Prop :=
  (Mem.load Mint64 m blk 0 = Some (Vlong (pc_loc stM))) /\ (**r load: the value should be same as the pc_loc value in the rBPF's monadic state *)
  (forall v_pc, Mem.store Mint64 m blk 0 (Vlong v_pc) = Some (bpf_m stM)) /\ (**r store: v_pc is vlong int64 & the new memory m_pc =  *)
  (exists regs_blk, Mem.load Mint64 m blk 8 = Some (Vptr regs_blk Ptrofs.zero)) /\ (**r regsmap is vlong pointer:load *)
  (forall v_regs, exists m_regs, Mem.store Mint64 m blk 8 v_regs = Some m_regs) /\ (**r regsmap is vlong pointer:store *)
  (exists flag, Mem.load Mint32 m blk 16 = Some (Vint flag)) /\ (**r flag is vint: load *)
  (forall v_flag, exists m_flag, Mem.store Mint32 m blk 16 v_flag = Some m_flag) /\ (**r flag is vint: store *)
  (exists mrs_blk, Mem.load Mint64 m blk 20 = Some (Vptr mrs_blk Ptrofs.zero)) /\
  (forall v_mrs, exists m_mrs, Mem.store Mint64 m blk 20 v_mrs = Some m_mrs). (* /\
  Mem.range_perm m blk 0 28 Cur Freeable.*) (** load and store all fields of bpf_state *)

(*
Lemma pc_store_valid:
  forall stM blk m v
    (Hst_blk: match_state_block stM blk m),
    exists m1,
      Mem.store Mint64 m blk 0 v = Some m1.
Proof.
  intros.
  unfold match_state_block in Hst_blk.
  destruct Hst_blk as ((pc & Hpc_mem) & (regs_blk & Hregs_blk_mem) & (flag & Hflag_mem) & (mrs_blk & Hmrs_blk_mem) & Hperm).
  
Qed. *)
Close Scope Z_scope.
