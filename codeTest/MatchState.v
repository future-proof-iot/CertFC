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
      mpc      : Mem.loadv AST.Mint64 m (Vptr bl_state (Ptrofs.repr 0)) = Some (Vlong  (pc_loc st));
      mregs    : match_registers  (regs_st st) bl_state (Ptrofs.repr 8) m;
      mflags   : Mem.loadv AST.Mint32 m (Vptr bl_state (Ptrofs.repr (size_of_regs + 8))) = Some (Vint  (int_of_flag (flag st)));
      mperm    : Mem.range_perm m bl_state 0 (size_of_regs + 12) Cur Freeable
    }.

End S.

(* Permission Lemmas: deriving from riot-rbpf/MemInv.v *)
Lemma range_perm_included:
  forall m b p lo hi ofs_lo ofs_hi, 
    lo <= ofs_lo -> ofs_lo < ofs_hi -> ofs_hi <= hi ->  (**r `<` -> `<=` *)
    Mem.range_perm m b lo hi Cur Freeable ->
      Mem.range_perm m b ofs_lo ofs_hi Cur p.
Proof.
  intros.
  apply (Mem.range_perm_implies _ _ _ _ _ Freeable _); [idtac | apply perm_F_any].
  unfold Mem.range_perm in *; intros.
  apply H2.
  lia.
Qed.

(** Permission Lemmas: upd_pc *)
Lemma upd_pc_write_access:
  forall m0 blk st
    (Hst: match_state blk st m0),
    Mem.valid_access m0 Mint64 blk 0 Writable.
Proof.
  intros; unfold Mem.valid_access; destruct Hst; clear minj0 mpc0 mregs0 mflags0; simpl in mperm0.
  unfold size_chunk, align_chunk.
  split.
  - simpl; apply (range_perm_included _ _ Writable _ _ 0 8) in mperm0; [assumption | lia | lia | lia].
  - apply Z.divide_0_r.
Qed.

Lemma upd_pc_store:
  forall m0 blk pc st
    (Hst: match_state blk st m0),
    exists m1,
    Mem.store AST.Mint64 m0 blk 0 (Vlong pc) = Some m1.
Proof.
  intros.
  apply (upd_pc_write_access _ _ _) in Hst.
  apply (Mem.valid_access_store _ _ _ _ (Vlong pc)) in Hst.
  destruct Hst as (m2 & Hstore).
  exists m2; assumption.
Qed.


(** Permission Lemmas: upd_regs *)
Lemma upd_regs_write_access:
  forall m0 blk st r
    (Hst: match_state blk st m0),
    Mem.valid_access m0 Mint64 blk (8 * (id_of_reg r)) Writable.
Proof.
  intros; unfold Mem.valid_access; destruct Hst; clear minj0 mpc0 mregs0 mflags0; simpl in mperm0.
  unfold id_of_reg.
  unfold size_chunk, align_chunk.
  split.
  - apply (range_perm_included _ _ Writable _ _ (8 * (id_of_reg r)) (8 * (id_of_reg r +1))) in mperm0;
  destruct r; unfold id_of_reg in *; simpl in *; try lia;
  simpl; assumption.
  - apply Z.divide_factor_l.
Qed.

(** Permission Lemmas: upd_flags *)
Lemma upd_flags_write_access:
  forall m0 blk st
    (Hst: match_state blk st m0),
    Mem.valid_access m0 Mint32 blk (size_of_regs + 8) Writable.
Proof.
  intros; unfold Mem.valid_access; destruct Hst; clear minj0 mpc0 mregs0 mflags0; simpl in mperm0.
  unfold size_of_regs.
  unfold size_chunk, align_chunk.
  split.
  - simpl.
    apply (range_perm_included _ _ Writable _ _ 88 92) in mperm0; [assumption | lia | lia | lia].
  - assert (Heq: 10 * 8 + 8 = 4 * 22). { reflexivity. }
    rewrite Heq;apply Z.divide_factor_l.
Qed.

(** Permission Lemmas: upd_mem_regions *)

(* Useful matching relations *)
Require Import DxMonad.

Definition match_region (bl_region : block) (mr: memory_region) (v: val64_t) (st: stateM) (m:Memory.Mem.mem) :=
  exists o, v = Vptr bl_region (Ptrofs.mul size_of_region  o) /\
              match_region_at_ofs mr bl_region o m.

Require Import Clightlogic.

Lemma same_memory_match_region :
  forall bl_region st st' m m' mr v
         (UMOD : unmodifies_effect nil m m'),
    match_region bl_region mr v st m ->
    match_region bl_region mr v st' m'.
Proof.
  intros.
  unfold match_region in *.
  destruct H as (o & E & MR).
  exists o.
  split; auto.
  unfold match_region_at_ofs in *.
  unfold unmodifies_effect in UMOD.
  unfold Mem.loadv.
  repeat rewrite <- UMOD by (simpl ; tauto).
  intuition.
Qed.
