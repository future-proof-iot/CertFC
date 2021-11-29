(** Definition of matching relation between Coq and C representation *)

From dx.tests Require Import DxIntegers DxValues DxAST DxMemRegion DxRegs DxState DxFlag.
From compcert Require Import Coqlib Integers Values AST Clight Memory.



Definition match_region (f: meminj) (mr:memory_region) (bl_regions : block) (ofs : ptrofs) (m: mem)  : Prop :=
  (exists v,  Mem.loadv AST.Mint64 m (Vptr bl_regions ofs) = Some v /\ Val.inject f (block_ptr mr) v)    /\
    (exists v,  Mem.loadv AST.Mint64 m (Vptr bl_regions (Ptrofs.add ofs (Ptrofs.repr 8))) = Some v /\ Val.inject f (start_addr mr) v) /\
    (exists v,  Mem.loadv AST.Mint64 m (Vptr bl_regions (Ptrofs.add ofs (Ptrofs.repr 16))) = Some v /\ Val.inject f (block_size mr) v).

Definition size_of_region  := Ptrofs.repr (3 * 8). (* 3 * 64 bits *)

Fixpoint match_list_region (f: meminj) (m:mem) (bl_regions: block) (ofs:ptrofs) (l:list memory_region) :=
  match l with
  | nil => True
  | mr :: l' => match_region f mr bl_regions ofs m /\
                  match_list_region f m bl_regions (Ptrofs.add ofs size_of_region) l'
  end.

Definition match_regions (f:meminj) (mrs:memory_regions) (bl_regions: block) (m:mem) :=
    match_list_region f m bl_regions Ptrofs.zero (bpf_ctx mrs :: bpf_stk mrs :: content mrs ::nil).


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

  Definition match_registers (f : meminj) (rmap:regmap) (bl_reg:block) (ofs : ptrofs) (m : mem) : Prop:=
    forall (r:reg),
    exists v, Mem.loadv AST.Mint64 m (Vptr bl_reg (Ptrofs.add ofs (Ptrofs.repr (8 * (id_of_reg r))))) = Some v /\
                Val.inject f (eval_regmap r rmap) v.



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

  Record match_meminj_state (f : meminj) (st:DxState.state) (m:mem) : Prop :=
    {
      minj  : Mem.inject f (fst (fst st)) m;
      mpc   : Mem.loadv AST.Mint64 m (Vptr bl_state (Ptrofs.repr 0)) = Some (Vlong  (pc_loc (snd (fst st))));
      mregs : match_registers f (regs_st (snd (fst st))) bl_state (Ptrofs.repr 8) m;
      mflsgs : Mem.loadv AST.Mint32 m (Vptr bl_state (Ptrofs.repr (size_of_regs + 8))) = Some (Vint  (int_of_flag (snd st)))
    }.

End S.


Inductive match_state (st: DxState.state) (m:mem) :Prop :=
| MakeMatch : forall f bl_state,
    match_meminj_state bl_state f st m -> match_state st m.
