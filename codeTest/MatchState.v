(** Definition of matching relation between Coq and C representation *)

From dx.tests Require Import DxIntegers DxValues DxAST DxMemRegion DxRegs DxState DxFlag.
From compcert Require Import Coqlib Integers Values AST Clight Memory.

Definition match_region_at_ofs (mr:memory_region) (bl_regions : block) (ofs : ptrofs) (m: mem)  : Prop :=
  (exists v,  Mem.loadv AST.Mint64 m (Vptr bl_regions ofs) = Some v /\ Val.inject inject_id (block_ptr mr) v)    /\
    (exists v,  Mem.loadv AST.Mint64 m (Vptr bl_regions (Ptrofs.add ofs (Ptrofs.repr 8))) = Some v /\ Val.inject inject_id (start_addr mr) v) /\
    (exists v,  Mem.loadv AST.Mint64 m (Vptr bl_regions (Ptrofs.add ofs (Ptrofs.repr 16))) = Some v /\ Val.inject inject_id (block_size mr) v).

Definition size_of_region  := Ptrofs.repr (3 * 8). (* 3 * 64 bits *)

Fixpoint match_list_region  (m:mem) (bl_regions: block) (ofs:ptrofs) (l:list memory_region) :=
  match l with
  | nil => True
  | mr :: l' => match_region_at_ofs  mr bl_regions ofs m /\
                  match_list_region  m bl_regions (Ptrofs.add ofs size_of_region) l'
  end.

Definition match_regions  (mrs:memory_regions) (bl_regions: block) (m:mem) :=
    match_list_region  m bl_regions Ptrofs.zero (bpf_ctx mrs :: bpf_stk mrs :: content mrs ::nil).


Definition id_of_reg (r:reg) : Z :=
  match r with
  | R0 => 0
  | R1 => 1
  | R2 => 2
  | R3 => 3
  | R4 => 4
  | R5 => 5
  | R6 => 6
  | R7 => 7
  | R8 => 8
  | R9 => 9
  | R10 => 10
  end.

Section S.

  (* [bl_state] is the memory block for the monadic state *)
  Variable bl_state : block.

  Definition match_registers  (rmap:regmap) (bl_reg:block) (ofs : ptrofs) (m : mem) : Prop:=
    forall (r:reg),
    exists v, Mem.loadv AST.Mint64 m (Vptr bl_reg (Ptrofs.add ofs (Ptrofs.repr (8 * (id_of_reg r))))) = Some v /\
                Val.inject inject_id (eval_regmap r rmap) v.



  Definition Z_of_flag (f:DxFlag.bpf_flag) : Z :=
    match f with
    | BPF_SUCC_RETURN  => 1
    | BPF_OK  => 0
    | BPF_ILLEGAL_INSTRUCTION => -1
    | BPF_ILLEGAL_MEM => -2
    | BPF_ILLEGAL_JUMP => -3
    | BPF_ILLEGAL_CALL => -4
    | BPF_ILLEGAL_LEN  => -5
    | BPF_ILLEGAL_REGISTER => -6
    | BPF_NO_RETURN => -7
    | BPF_OUT_OF_BRANCHES => -8
    | BPF_ILLEGAL_DIV => -9
    | BPF_ILLEGAL_SHIFT => -10
    | BPF_ILLEGAL_ALU => -11
    | BPF_UNDEF_ERROR => -12
    end.

  Definition int_of_flag (f:bpf_flag)  :=
    Int.repr (Z_of_flag f).

  Definition size_of_regs := 10 * 8.

  Record match_state  (st:DxState.state) (m:mem) : Prop :=
    {
      minj     : Mem.inject (inject_id) (bpf_m st) m;
      mpc_load : Mem.loadv AST.Mint64 m (Vptr bl_state (Ptrofs.repr 0)) = Some (Vlong  (pc_loc st));
      mpc_store: forall pc m1,  Mem.store AST.Mint64 m bl_state 0 (Vlong pc) = Some m1; (** the relation between m1 and st? *)
      mregs    : match_registers  (regs_st st) bl_state (Ptrofs.repr 8) m;
      mflsgs  : Mem.loadv AST.Mint32 m (Vptr bl_state (Ptrofs.repr (size_of_regs + 8))) = Some (Vint  (int_of_flag (flag st)))
    }.

End S.

(* Useful matching relations *)
Require Import DxMonad.

Definition match_region (bl_region : block) (mr: memory_region) (v: val64_t) (st: stateM) (m:Memory.Mem.mem) :=
  exists o, v = Vptr bl_region (Ptrofs.mul size_of_region  o) /\
              match_region_at_ofs mr bl_region o m.
