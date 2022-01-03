(** Definition of matching relation between Coq and C representation *)
From bpf.src Require Import DxIntegers DxValues DxAST DxState DxMemRegion DxRegs DxFlag.
From compcert Require Import Coqlib Integers Values AST Clight Memory Memtype.

From bpf.proof Require Import CommonLib.
From Coq Require Import ZArith.
Open Scope Z_scope.

(**r


Definition mem_region_def: Ctypes.composite_definition := 
  Ctypes.Composite mem_region_id Ctypes.Struct [
    (start_addr_id, C_U32);
    (size_id, C_U32);
    (perm_id, C_U32);
    (block_ptr_id, C_U32)
  ] Ctypes.noattr.

*)

Definition correct_perm (p: permission) (n: int): Prop :=
  match p with
  | Freeable => n = int32_3
  | Writable => n = int32_2
  | Readable => n = int32_1
  | Nonempty => n = int32_0
  end.

Definition match_region_at_ofs (mr:memory_region) (bl_regions : block) (ofs : Z) (m: mem)  : Prop :=
  (exists vl,  Mem.load AST.Mint32 m bl_regions ofs = Some (Vint vl) /\ (start_addr mr) = Vint vl)    /\ (**r start_addr mr = Vint vl*)
    (exists vl,  Mem.load AST.Mint32 m bl_regions (ofs + 4) = Some (Vint vl) /\ (block_size mr) = Vint vl) /\ (**r block_size mr = Vint vl*)
    (exists vl,  Mem.load AST.Mint32 m bl_regions (ofs + 8) = Some (Vint vl) /\ correct_perm (block_perm mr)  vl) /\ (**r block_perm mr = Vint vl*)
    (exists b o,  Mem.load AST.Mptr m bl_regions (ofs + 12) = Some (Vptr b o) /\ (block_ptr mr) = Vptr b o).

Definition size_of_region  := 4 * 4. (* 4 * 32 bits *)

Fixpoint match_list_region  (m:mem) (bl_regions: block) (ofs:Z) (l:list memory_region) :=
  match l with
  | nil => True
  | mr :: l' => match_region_at_ofs  mr bl_regions ofs m /\
                  match_list_region  m bl_regions (ofs+size_of_region) l'
  end.

Definition match_regions  (mrs:list memory_region) (bl_regions: block) (ofs : Z) (m:mem) :=
    match_list_region m bl_regions ofs mrs.


Section S.

  (* [bl_state] is the memory block for the monadic state *)
  Variable bl_state : block.

  Definition match_registers  (rmap:regmap) (bl_reg:block) (ofs : Z) (m : mem) : Prop:=
    forall (r:reg),
    exists vl, Mem.load Mint64 m bl_reg (ofs + (8 * (id_of_reg r))) = Some (Vlong vl) /\ (**r it should be `(eval_regmap r rmap)`*)
            Vlong vl = eval_regmap r rmap.
           (*Val.inject inject_id (eval_regmap r rmap) (Vlong vl) . (**r each register is Vlong *)*)


  Definition size_of_regs := 11 * 8. (**r we have 11 regs R0 - R10 *)
  Definition size_of_state (st: DxState.state) := 100 + 16 * (Z.of_nat (mrs_num st)).


(**r
Definition state_struct_def: Ctypes.composite_definition := 
  Ctypes.Composite state_id Ctypes.Struct [
    (pc_id, C_U32);
    (flag_id, C_S32);
    (regmaps_id, C_regmap);;
    (mem_num_id, C_U32)
    (mem_regs_id, mem_region_type)
  ] Ctypes.noattr.

*)

  Record match_state  (st: DxState.state) (m: mem) : Prop :=
    {
      minj     : Mem.inject inject_id (bpf_m st) m;
      mpc      : Mem.load AST.Mint32 m bl_state 0 = Some (Vint  (pc_loc st));
      mflags   : Mem.load AST.Mint32 m bl_state 4 = Some (Vint  (int_of_flag (flag st)));
      mregs    : match_registers  (regs_st st) bl_state 8 m;
      mrs_num  : Mem.load AST.Mint32 m bl_state (size_of_regs + 8) = Some (Vint  (Int.repr (Z.of_nat (DxState.mrs_num st)))) /\ (Z.of_nat(DxState.mrs_num st)) >= 1; (**r at least we have the memory region that corresponds to the input paramters of the interpreter *)
      mem_regs : match_regions (bpf_mrs st) bl_state (size_of_regs + 12) m /\ List.length (bpf_mrs st) = (DxState.mrs_num st); (**r the number of bpf_mrs is exactly the mrs_num *)
      mperm    : Mem.range_perm m bl_state 0 (size_of_state st) Cur Freeable;
      minvalid : forall chunk ofs p, ~Mem.valid_access (bpf_m st) chunk bl_state ofs p /\ ~Mem.perm (bpf_m st) bl_state ofs Cur p(**r ysh: bl_state doesn't exist in st *)
    }.

End S.

(* Permission Lemmas: deriving from riot-rbpf/MemInv.v *)
Lemma range_perm_included:
  forall m b p lo hi ofs_lo ofs_hi, 
    lo <= ofs_lo -> ofs_lo < ofs_hi -> ofs_hi <= hi ->  (**r `<` -> `<=` *)
    Mem.range_perm m b lo hi Cur p ->
      Mem.range_perm m b ofs_lo ofs_hi Cur p.
Proof.
  intros.
  apply (Mem.range_perm_implies _ _ _ _ _ p _); [idtac | constructor].
  unfold Mem.range_perm in *; intros.
  apply H2.
  lia.
Qed.

(** Permission Lemmas: upd_pc *)
Lemma upd_pc_write_access:
  forall m0 blk st
    (Hst: match_state blk st m0),
    Mem.valid_access m0 Mint32 blk 0 Writable.
Proof.
  intros; unfold Mem.valid_access; destruct Hst; clear - mem_regs0 mperm0; simpl in mem_regs0.
  unfold match_regions, size_of_state in *.
  apply (Mem.range_perm_implies _ _ _ _ _ _ Writable) in mperm0; [idtac | constructor].

  unfold size_chunk, align_chunk.
  split.
  - simpl; apply (range_perm_included _ _ Writable _ _ 0 4) in mperm0; [assumption | lia | lia | idtac].
    assert (H: 0<= Z.of_nat (DxState.mrs_num st)). { apply Nat2Z.is_nonneg. }
    lia.
  - apply Z.divide_0_r.
Qed.

Lemma upd_pc_store:
  forall m0 blk pc st
    (Hst: match_state blk st m0),
    exists m1,
    Mem.store AST.Mint32 m0 blk 0 (Vint pc) = Some m1.
Proof.
  intros.
  apply (upd_pc_write_access _ _ _) in Hst.
  apply (Mem.valid_access_store _ _ _ _ (Vint pc)) in Hst.
  destruct Hst as (m2 & Hstore).
  exists m2; assumption.
Qed.

(** Permission Lemmas: upd_flags *)
Lemma upd_flags_write_access:
  forall m0 blk st
    (Hst: match_state blk st m0),
    Mem.valid_access m0 Mint32 blk 4 Writable.
Proof.
  intros; unfold Mem.valid_access; destruct Hst; clear - mperm0; simpl in mperm0.
  unfold size_of_regs, size_of_state in *.
  apply (Mem.range_perm_implies _ _ _ _ _ _ Writable) in mperm0; [idtac | constructor].


  unfold size_chunk, align_chunk.
  split.
  - simpl.
    apply (range_perm_included _ _ Writable _ _ 4 8) in mperm0; [assumption | lia | lia | lia].
  - apply Z.divide_refl.
Qed.

Lemma upd_flags_store:
  forall m0 blk st v
    (Hst: match_state blk st m0),
    exists m1,
    Mem.store AST.Mint32 m0 blk 4 (Vint v) = Some m1.
Proof.
  intros.
  apply (upd_flags_write_access _ _ ) in Hst.
  apply (Mem.valid_access_store _ _ _ _ (Vint v)) in Hst.
  destruct Hst as (m2 & Hstore).
  exists m2; assumption.
Qed.

(** Permission Lemmas: upd_regs *)
Lemma upd_regs_write_access:
  forall m0 blk st r
    (Hst: match_state blk st m0),
    Mem.valid_access m0 Mint64 blk (8 + (8 * (id_of_reg r))) Writable.
Proof.
  intros; unfold Mem.valid_access; destruct Hst; clear - mperm0; simpl in mperm0.
  unfold size_of_regs, size_of_state in *.
  apply (Mem.range_perm_implies _ _ _ _ _ _ Writable) in mperm0; [idtac | constructor].
  assert (H: 0<= Z.of_nat (DxState.mrs_num st)). { apply Nat2Z.is_nonneg. }
  apply (range_perm_included _ _ Writable _ _ 0 100) in mperm0; [idtac | lia | lia | lia].

  unfold id_of_reg.
  unfold size_chunk, align_chunk.
  split.
  - apply (range_perm_included _ _ Writable _ _ (8 + (8 * (id_of_reg r))) (8 + (8 * (id_of_reg r +1)))) in mperm0;
  destruct r; simpl in *; try lia; try assumption.
  - assert (Heq: forall x, 8 + 8 * x = 8 * (1 + x)). {
      intros.
      rewrite Zred_factor2.
      reflexivity.
    }
    rewrite Heq.
    apply Z.divide_factor_l.
Qed.

Lemma upd_regs_store:
  forall m0 blk st r v
    (Hst: match_state blk st m0),
    exists m1,
    Mem.store AST.Mint64 m0 blk (8 + (8 * (id_of_reg r))) (Vlong v) = Some m1.
Proof.
  intros.
  apply (upd_regs_write_access _ _ _ r) in Hst.
  apply (Mem.valid_access_store _ _ _ _ (Vlong v)) in Hst.
  destruct Hst as (m2 & Hstore).
  exists m2; assumption.
Qed.

(** Permission Lemmas: upd_mem_regions *)

(** TODO: nothing to do because we never update memory_regions, it should be done before running the interpter *)

Require Import DxMonad.

(** TODO: *)

Definition my_match_region (bl_region : block) (mr: memory_region) (v: val64_t) (st: stateM) (m:Memory.Mem.mem) :=
  exists o, v = Vptr bl_region o /\
              match_region_at_ofs mr bl_region (Ptrofs.unsigned o) m.

(* Useful matching relations *)

Definition match_region (bl_region : block) (mr: memory_region) (v: val64_t) (st: stateM) (m:Memory.Mem.mem) :=
  exists o, v = Vptr bl_region (Ptrofs.mul (Ptrofs.repr size_of_region) o) /\
              match_region_at_ofs mr bl_region (Ptrofs.unsigned o) m.

From bpf.proof Require Import Clightlogic.

Lemma same_memory_match_region :
  forall bl_region st st' m m' mr v
         (UMOD : unmodifies_effect nil m m' st st'),
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
  destruct UMOD; subst.
  repeat rewrite <- UMOD by (simpl ; tauto).
  intuition.
Qed.

Lemma same_my_memory_match_region :
  forall bl_region st st' m m' mr v
         (UMOD : unmodifies_effect nil m m' st st'),
    my_match_region bl_region mr v st m ->
    my_match_region bl_region mr v st' m'.
Proof.
  intros.
  unfold my_match_region in *.
  destruct H as (o & E & MR).
  exists o.
  split; auto.
  unfold match_region_at_ofs in *.
  unfold unmodifies_effect in UMOD.
  destruct UMOD; subst.
  repeat rewrite <- UMOD by (simpl ; tauto).
  intuition.
Qed.
Close Scope Z_scope.