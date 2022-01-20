(** Definition of matching relation between Coq and C representation *)
From bpf.comm Require Import State MemRegion Regs Flag List64.
From bpf.src Require Import DxIntegers DxValues DxAST DxMemRegion DxRegs DxFlag DxList64.
From compcert Require Import Coqlib Integers Values AST Clight Memory Memtype.

From bpf.proof Require Import CommonLemma CommonLib Clightlogic.
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

Definition match_region_at_ofs (mr:memory_region) (bl_regions : block) (ofs : ptrofs) (m: mem)  : Prop :=
  (exists vl,  Mem.loadv AST.Mint32 m (Vptr bl_regions ofs) = Some (Vint vl) /\ (start_addr mr) = Vint vl)    /\ (**r start_addr mr = Vint vl*)
    (exists vl,  Mem.loadv AST.Mint32 m (Vptr bl_regions (Ptrofs.add ofs (Ptrofs.repr 4))) = Some (Vint vl) /\ (block_size mr) = Vint vl) /\ (**r block_size mr = Vint vl*)
    (exists vl,  Mem.loadv AST.Mint32 m (Vptr bl_regions (Ptrofs.add ofs (Ptrofs.repr 8))) = Some (Vint vl) /\ correct_perm (block_perm mr)  vl) /\ (**r block_perm mr = Vint vl*)
    (exists b o,  Mem.loadv AST.Mptr  m (Vptr bl_regions (Ptrofs.add ofs (Ptrofs.repr 12))) = Some (Vptr b o) /\ (block_ptr mr) = Vptr b o).


(*Definition size_of_region  :=  16. (* 4 * 32 bits *)*)

Fixpoint match_list_region (m:mem) (bl_regions: block) (ofs:ptrofs) (l:list memory_region) :=
  match l with
  | nil => True
  | mr :: l' => match_region_at_ofs  mr bl_regions ofs m /\
                  match_list_region  m bl_regions (Ptrofs.add ofs (Ptrofs.repr 16)) l'
  end.

Definition match_regions (mrs_blk: block) (st: State.state) (m:mem) :=
  List.length (bpf_mrs st) = (mrs_num st) /\ (**r the number of bpf_mrs is exactly the mrs_num *)
  Z.of_nat (List.length (bpf_mrs st)) * 16 <= Ptrofs.max_unsigned /\ (**r there is not overflow *)
  match_list_region m mrs_blk Ptrofs.zero (bpf_mrs st).

Fixpoint match_list_ins (m:mem) (b: block) (ofs:ptrofs) (l: MyListType) :=
  match l with
  | nil => True
  | hd :: tl => Mem.loadv AST.Mint64 m (Vptr b ofs) = Some (Vlong hd) /\
                  match_list_ins m b (Ptrofs.add ofs (Ptrofs.repr 8)) tl
  end.

Definition match_ins (ins_blk: block) (st: State.state) (m:mem) :=
  List.length (ins st) = (ins_len st) /\
  Z.of_nat (List.length (ins st)) * 8 <= Ptrofs.max_unsigned /\
  match_list_ins m ins_blk (Ptrofs.repr 0) (ins st).

Section S.

  (* [state_blk] is the memory block for the monadic state *)
  Variable state_blk : block.
  Variable mrs_blk  : block.
  Variable ins_blk  : block.

  Definition match_registers  (rmap:regmap) (bl_reg:block) (ofs : ptrofs) (m : mem) : Prop:=
    forall (r:reg),
    exists vl, Mem.loadv Mint64 m (Vptr bl_reg (Ptrofs.add ofs (Ptrofs.repr (8 * (id_of_reg r))))) = Some (Vlong vl) /\ (**r it should be `(eval_regmap r rmap)`*)
            Vlong vl = eval_regmap r rmap.
           (*Val.inject inject_id (eval_regmap r rmap) (Vlong vl) . (**r each register is Vlong *)*)


  (*Definition size_of_regs := 88. (**r 11 * 8: we have 11 regs R0 - R10 *)*)
  Definition size_of_state (st: State.state) := 100 + 16 * (Z.of_nat (mrs_num st)) + 8 *(Z.of_nat (ins_len st)).

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
  
Definition is_byte_memval (mv: memval): Prop :=
  match mv with
  | Undef => False
  | Byte b => True
  | Fragment _ _ _ => False
  end.

  Record match_state  (st: State.state) (m: mem) : Prop :=
    {
      munchange: Mem.unchanged_on (fun b _ => b <> state_blk /\ b <> mrs_blk /\ b <> ins_blk) (bpf_m st) m; (**r (bpf_m st) = m - {state_blk, mrs_blk, ins_blk} *)
      mpc      : Mem.loadv AST.Mint32 m (Vptr state_blk (Ptrofs.repr 0)) = Some (Vint  (pc_loc st));
      mflags   : Mem.loadv AST.Mint32 m (Vptr state_blk (Ptrofs.repr 4)) = Some (Vint  (int_of_flag (flag st)));
      mregs    : match_registers (regs_st st) state_blk (Ptrofs.repr 8) m;
      mins_len : Mem.loadv AST.Mint32 m (Vptr state_blk (Ptrofs.repr 96)) = Some (Vint  (Int.repr (Z.of_nat (ins_len st)))) /\ (Z.of_nat(ins_len st)) >= 0;
      mins     : Mem.loadv AST.Mptr m (Vptr state_blk (Ptrofs.repr 100)) = Some (Vptr ins_blk (Ptrofs.repr 0)) /\ match_ins ins_blk st m;
      mmrs_num : Mem.loadv AST.Mint32 m (Vptr state_blk (Ptrofs.repr 104)) = Some (Vint  (Int.repr (Z.of_nat (mrs_num st)))) /\
                 (Z.of_nat(mrs_num st)) >= 1; (**r at least we have the memory region that corresponds to the input paramters of the interpreter *)
      mem_regs : Mem.loadv AST.Mptr m (Vptr state_blk (Ptrofs.repr 108)) = Some (Vptr mrs_blk (Ptrofs.repr 0)) /\ match_regions mrs_blk st m;
      mperm    : Mem.range_perm m state_blk 0 (size_of_state st) Cur Freeable;
      minvalid : ~Mem.valid_block (bpf_m st) state_blk /\ ~Mem.valid_block (bpf_m st) mrs_blk /\ ~Mem.valid_block (bpf_m st) ins_blk /\ mrs_blk <> state_blk /\  mrs_blk <> ins_blk /\  ins_blk <> state_blk;
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
  forall m0 st_blk mrs_blk ins_blk st
    (Hst: match_state st_blk mrs_blk ins_blk st m0),
    Mem.valid_access m0 Mint32 st_blk 0 Writable.
Proof.
  intros; unfold Mem.valid_access; destruct Hst; clear - mem_regs0 mperm0; simpl in mem_regs0.
  unfold match_regions, size_of_state in *.
  apply (Mem.range_perm_implies _ _ _ _ _ _ Writable) in mperm0; [idtac | constructor].

  unfold size_chunk, align_chunk.
  split.
  - simpl; apply (range_perm_included _ _ Writable _ _ 0 4) in mperm0; [assumption | lia | lia | idtac].
    assert (H: 0<= Z.of_nat (State.mrs_num st)). { apply Nat2Z.is_nonneg. }
    lia.
  - apply Z.divide_0_r.
Qed.

Lemma upd_pc_store:
  forall m0 st_blk mrs_blk ins_blk pc st
    (Hst: match_state st_blk mrs_blk ins_blk st m0),
    exists m1,
    Mem.store AST.Mint32 m0 st_blk 0 (Vint pc) = Some m1.
Proof.
  intros.
  apply (upd_pc_write_access _ _ _) in Hst.
  apply (Mem.valid_access_store _ _ _ _ (Vint pc)) in Hst.
  destruct Hst as (m2 & Hstore).
  exists m2; assumption.
Qed.

(** Permission Lemmas: upd_flags *)
Lemma upd_flags_write_access:
  forall m0 st_blk mrs_blk ins_blk st
    (Hst: match_state st_blk mrs_blk ins_blk st m0),
    Mem.valid_access m0 Mint32 st_blk 4 Writable.
Proof.
  intros; unfold Mem.valid_access; destruct Hst; clear - mperm0; simpl in mperm0.
  unfold size_of_state in *.
  apply (Mem.range_perm_implies _ _ _ _ _ _ Writable) in mperm0; [idtac | constructor].

  unfold size_chunk, align_chunk.
  split.
  - simpl.
    apply (range_perm_included _ _ Writable _ _ 4 8) in mperm0; [assumption | lia | lia | lia].
  - apply Z.divide_refl.
Qed.

Lemma upd_flags_store:
  forall m0 st_blk mrs_blk ins_blk st v
    (Hst: match_state st_blk mrs_blk ins_blk st m0),
    exists m1,
    Mem.store AST.Mint32 m0 st_blk 4 (Vint v) = Some m1.
Proof.
  intros.
  apply (upd_flags_write_access _ _ ) in Hst.
  apply (Mem.valid_access_store _ _ _ _ (Vint v)) in Hst.
  destruct Hst as (m2 & Hstore).
  exists m2; assumption.
Qed.

(** Permission Lemmas: upd_regs *)
Lemma upd_regs_write_access:
  forall m0 st_blk mrs_blk ins_blk st r
    (Hst: match_state st_blk mrs_blk ins_blk st m0),
    Mem.valid_access m0 Mint64 st_blk (8 + (8 * (id_of_reg r))) Writable.
Proof.
  intros; unfold Mem.valid_access; destruct Hst; clear - mperm0; simpl in mperm0.
  unfold size_of_state in *.
  apply (Mem.range_perm_implies _ _ _ _ _ _ Writable) in mperm0; [idtac | constructor].
  assert (H: 0<= Z.of_nat (State.mrs_num st)). { apply Nat2Z.is_nonneg. }
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
  forall m0 st_blk mrs_blk ins_blk st r v
    (Hst: match_state st_blk mrs_blk ins_blk st m0),
    exists m1,
    Mem.store AST.Mint64 m0 st_blk (8 + (8 * (id_of_reg r))) (Vlong v) = Some m1.
Proof.
  intros.
  apply (upd_regs_write_access _ _ _ _ _ r) in Hst.
  apply (Mem.valid_access_store _ _ _ _ (Vlong v)) in Hst.
  destruct Hst as (m2 & Hstore).
  exists m2; assumption.
Qed.

(** Permission Lemmas: upd_mem_regions *)

(** TODO: nothing to do because we never update memory_regions, it should be done before running the interpter *)

Require Import DxMonad.

(** TODO: *)

Definition my_match_region (bl_region : block) (mr: memory_region) (v: val64_t) (st: State.state) (m:Memory.Mem.mem) :=
  exists o, v = Vptr bl_region o /\
              match_region_at_ofs mr bl_region o m.

(* Useful matching relations *)

Definition match_region (bl_region : block) (mr: memory_region) (v: val64_t) (st: State.state) (m:Memory.Mem.mem) :=
  exists o, v = Vptr bl_region (Ptrofs.repr (o * 16)) /\
              match_region_at_ofs mr bl_region (Ptrofs.repr o) m.


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

(**r a set of lemmas say upd_reg/flag/pc... don't change the memory/regs/flag/pc of rbpf *)

Lemma upd_reg_same_mem:
  forall st0 r vl,
    bpf_m st0 = bpf_m (State.upd_reg r vl st0).
Proof.
  unfold State.upd_reg.
  intros.
  reflexivity.
Qed.

Lemma upd_reg_same_pc:
  forall st0 r vl,
    pc_loc st0 = pc_loc (State.upd_reg r vl st0).
Proof.
  unfold State.upd_reg.
  intros.
  reflexivity.
Qed.

Lemma upd_reg_same_flag:
  forall st0 r vl,
    flag st0 = flag (State.upd_reg r vl st0).
Proof.
  unfold State.upd_reg.
  intros.
  reflexivity.
Qed.

Lemma upd_reg_same_mrs:
  forall st0 r vl,
    bpf_mrs st0 = bpf_mrs (State.upd_reg r vl st0).
Proof.
  unfold State.upd_reg.
  intros.
  reflexivity.
Qed.

Lemma upd_reg_same_mrs_num:
  forall st0 r vl,
    State.mrs_num st0 = State.mrs_num (State.upd_reg r vl st0).
Proof.
  unfold State.upd_reg.
  intros.
  reflexivity.
Qed.

Lemma upd_reg_same_ins:
  forall st0 r vl,
    ins st0 = ins (State.upd_reg r vl st0).
Proof.
  unfold State.upd_reg.
  intros.
  reflexivity.
Qed.

Lemma upd_reg_same_ins_len:
  forall st0 r vl,
    ins_len st0 = ins_len (State.upd_reg r vl st0).
Proof.
  unfold State.upd_reg.
  intros.
  reflexivity.
Qed.

Lemma upd_pc_same_mem:
  forall st0 pc,
    bpf_m st0 = bpf_m (State.upd_pc pc st0).
Proof.
  unfold State.upd_pc.
  intros.
  reflexivity.
Qed.

Lemma upd_pc_same_regs:
  forall st0 pc,
    regs_st st0 = regs_st (State.upd_pc pc st0).
Proof.
  unfold State.upd_pc.
  intros.
  reflexivity.
Qed.

Lemma upd_pc_same_flag:
  forall st0 pc,
    flag st0 = flag (State.upd_pc pc st0).
Proof.
  unfold State.upd_pc.
  intros.
  reflexivity.
Qed.

Lemma upd_pc_same_mrs:
  forall st0 pc,
    bpf_mrs st0 = bpf_mrs (State.upd_pc pc st0).
Proof.
  unfold State.upd_pc.
  intros.
  reflexivity.
Qed.

Lemma upd_pc_same_mrs_num:
  forall st0 pc,
    State.mrs_num st0 = State.mrs_num (State.upd_pc pc st0).
Proof.
  unfold State.upd_pc.
  intros.
  reflexivity.
Qed.

Lemma upd_pc_same_ins:
  forall st0 pc,
    ins st0 = ins (State.upd_pc pc st0).
Proof.
  unfold State.upd_pc.
  intros.
  reflexivity.
Qed.

Lemma upd_pc_same_ins_len:
  forall st0 pc,
    ins_len st0 = ins_len (State.upd_pc pc st0).
Proof.
  unfold State.upd_pc.
  intros.
  reflexivity.
Qed.

Lemma upd_pc_incr_same_mem:
  forall st0,
    bpf_m st0 = bpf_m (State.upd_pc_incr st0).
Proof.
  unfold State.upd_pc_incr.
  intros.
  reflexivity.
Qed.

Lemma upd_pc_incr_same_regs:
  forall st0,
    regs_st st0 = regs_st (State.upd_pc_incr st0).
Proof.
  unfold State.upd_pc_incr.
  intros.
  reflexivity.
Qed.

Lemma upd_pc_incr_same_flag:
  forall st0,
    flag st0 = flag (State.upd_pc_incr st0).
Proof.
  unfold State.upd_pc_incr.
  intros.
  reflexivity.
Qed.

Lemma upd_pc_incr_same_mrs:
  forall st0,
    bpf_mrs st0 = bpf_mrs (State.upd_pc_incr st0).
Proof.
  unfold State.upd_pc_incr.
  intros.
  reflexivity.
Qed.

Lemma upd_pc_incr_same_mrs_num:
  forall st0,
    State.mrs_num st0 = State.mrs_num (State.upd_pc_incr st0).
Proof.
  unfold State.upd_pc_incr.
  intros.
  reflexivity.
Qed.

Lemma upd_pc_incr_same_ins:
  forall st0,
    ins st0 = ins (State.upd_pc_incr st0).
Proof.
  unfold State.upd_pc_incr.
  intros.
  reflexivity.
Qed.

Lemma upd_pc_incr_same_ins_len:
  forall st0,
    ins_len st0 = ins_len (State.upd_pc_incr st0).
Proof.
  unfold State.upd_pc_incr.
  intros.
  reflexivity.
Qed.

Lemma upd_flag_same_mem:
  forall st0 f,
    bpf_m st0 = bpf_m (State.upd_flag f st0).
Proof.
  unfold State.upd_flag.
  intros.
  reflexivity.
Qed.

Lemma upd_flag_same_regs:
  forall st0 f,
    regs_st st0 = regs_st (State.upd_flag f st0).
Proof.
  unfold State.upd_flag.
  intros.
  reflexivity.
Qed.

Lemma upd_flag_same_pc:
  forall st0 f,
    pc_loc st0 = pc_loc (State.upd_flag f st0).
Proof.
  unfold State.upd_flag.
  intros.
  reflexivity.
Qed.

Lemma upd_flag_same_mrs:
  forall st0 f,
    bpf_mrs st0 = bpf_mrs (State.upd_flag f st0).
Proof.
  unfold State.upd_flag.
  intros.
  reflexivity.
Qed.

Lemma upd_flag_same_mrs_num:
  forall st0 f,
    State.mrs_num st0 = State.mrs_num (State.upd_flag f st0).
Proof.
  unfold State.upd_flag.
  intros.
  reflexivity.
Qed.

Lemma upd_flag_same_ins:
  forall st0 f,
    ins st0 = ins (State.upd_flag f st0).
Proof.
  unfold State.upd_flag.
  intros.
  reflexivity.
Qed.

Lemma upd_flag_same_ins_len:
  forall st0 f,
    ins_len st0 = ins_len (State.upd_flag f st0).
Proof.
  unfold State.upd_flag.
  intros.
  reflexivity.
Qed.

Lemma upd_unchanged_on:
  forall st m0 m1 st_blk mrs_blk ins_blk chunk ofs vl
  (Hst    : match_state st_blk mrs_blk ins_blk st m0)
  (Hstore : Mem.store chunk m0 st_blk ofs vl = Some m1),
    Mem.unchanged_on (fun b _ => b <> st_blk /\ b <> mrs_blk /\ b <> ins_blk) m0 m1.
Proof.
  intros.
  destruct Hst. (*
  destruct minj0.
  clear - mi_inj mi_freeblocks minvalid0 munchange0 mByte0 Hstore. *)
  eapply Mem.store_unchanged_on.
  rewrite Hstore.
  reflexivity.
  intros.
  intro.
  destruct H0 as (H0 & _).
  apply H0; reflexivity.
Qed.


(*
Lemma upd_preserves_match_list_region:
  forall lmr m0 m1 blk ofs0 ofs1 chunk vl
  (Hmax_range: Z.of_nat (Datatypes.length lmr) * 16 <= Ptrofs.max_unsigned - 100)
  (Hcomplex: forall n, 0 <= n < Z.of_nat (List.length lmr) ->
    (ofs0 + size_chunk chunk <= Ptrofs.unsigned (Ptrofs.add ofs1 (Ptrofs.repr (n * 16))) /\
    0 <= Ptrofs.unsigned ofs1 + (n * 16) <= Ptrofs.max_unsigned) /\
    (ofs0 + size_chunk chunk <= Ptrofs.unsigned (Ptrofs.add (Ptrofs.add ofs1 (Ptrofs.repr (n * 16))) (Ptrofs.repr 4)) /\
    0 <= Ptrofs.unsigned (Ptrofs.add ofs1 (Ptrofs.repr 16)) + n * 16 <= Ptrofs.max_unsigned) /\
    ofs0 + size_chunk chunk <= Ptrofs.unsigned (Ptrofs.add (Ptrofs.add ofs1 (Ptrofs.repr (n * 16))) (Ptrofs.repr 8)) /\
  ofs0 + size_chunk chunk <= Ptrofs.unsigned (Ptrofs.add (Ptrofs.add ofs1 (Ptrofs.repr (n * 16))) (Ptrofs.repr 12))
  )
  (Hstore : Mem.store chunk m0 blk ofs0 vl = Some m1)
  (mem_regs : match_list_region m0 blk ofs1 lmr),
    match_list_region m1 blk ofs1 lmr.
Proof.
  induction lmr.
  constructor.

  intros.
  simpl.


  destruct mem_regs0 as (mem_regs0 & mem_regs0_1).
  unfold match_region_at_ofs in *.
  destruct mem_regs0 as ((vi0 & Hstart & Hvi0_eq) & (vi1 & Hsize & Hvi1_eq) & (vi2 & Hperm & Hvi2_eq) & (vi3 & ofs & Hptr & Hvi3_eq)).
  unfold Mem.loadv in *.

  assert (Hcomplex0_1: 
    forall n,
      0 <= n ->
      0<= Ptrofs.unsigned ofs1 + 16 <= Ptrofs.max_unsigned ->
      0<= (n + 1) * 16 <= Ptrofs.max_unsigned ->
      Ptrofs.add ofs1 (Ptrofs.repr ((n + 1) * 16)) =
      Ptrofs.add (Ptrofs.add ofs1 (Ptrofs.repr 16)) (Ptrofs.repr (n * 16))
  ). {
    intros.
    unfold Ptrofs.add, Ptrofs.mul. (**r we must say n+1 is not overflow *)
    rewrite Ptrofs_unsigned_repr_16 in *.
    rewrite Ptrofs.unsigned_repr; [| assumption].
    rewrite Ptrofs.unsigned_repr; [| assumption].
    rewrite Ptrofs.unsigned_repr; [| lia].
    rewrite Z.mul_add_distr_r.
    simpl.
    rewrite Zplus_assoc_reverse.
    rewrite Z.add_comm with (n := n * 16).
    reflexivity.
   }

  split.

  split.

  exists vi0.
  split; [| assumption].
  rewrite <- Hstart.

  assert (Hcomplex0_0: ofs0 + size_chunk chunk <= Ptrofs.unsigned ofs1). {
    specialize (Hcomplex 0).
    fold Ptrofs.zero in Hcomplex.
    simpl in Hcomplex.
    fold Ptrofs.zero in Hcomplex.
    rewrite Ptrofs.add_zero in Hcomplex.
    assert (Hrange0: 0 <= 0 < Z.of_nat (Datatypes.length (a :: lmr))). { simpl. lia. }
    specialize (Hcomplex Hrange0).
    destruct Hcomplex as (Hcomplex0 & Hcomplex1 & Hcomplex2 & Hcomplex3).
    destruct Hcomplex0; assumption.
  }
  eapply Mem.load_store_other; eauto.

  split.
  exists vi1.
  split; [| assumption].
  rewrite <- Hsize.

  assert (Hcomplex1_0: ofs0 + size_chunk chunk <= Ptrofs.unsigned (Ptrofs.add ofs1 (Ptrofs.repr 4))). {
    specialize (Hcomplex 0).
    fold Ptrofs.zero in Hcomplex.
    simpl in Hcomplex.
    fold Ptrofs.zero in Hcomplex.
    rewrite Ptrofs.add_zero in Hcomplex.
    assert (Hrange: 0 <= 0 < Z.of_nat (Datatypes.length (a :: lmr))). { simpl; lia. }
    specialize (Hcomplex Hrange).
    destruct Hcomplex as (Hcomplex0 & Hcomplex1 & Hcomplex2 & Hcomplex3).
    destruct Hcomplex1; assumption.
  }
  eapply Mem.load_store_other; eauto.

  split.
  exists vi2.
  split; [| assumption].
  rewrite <- Hperm.
  assert (Hcomplex2_0: ofs0 + size_chunk chunk <= Ptrofs.unsigned (Ptrofs.add ofs1 (Ptrofs.repr 8))). {
    specialize (Hcomplex 0).
    simpl in Hcomplex.
    fold Ptrofs.zero in Hcomplex.
    rewrite Ptrofs.add_zero in Hcomplex.
    assert (Hrange: 0 <= 0 < Z.of_nat (Datatypes.length (a :: lmr))). { simpl; lia. }
    specialize (Hcomplex Hrange).
    destruct Hcomplex as (Hcomplex0 & Hcomplex1 & Hcomplex2 & Hcomplex3).
    assumption.
  }
  eapply Mem.load_store_other; eauto.

  exists vi3, ofs.
  split; [| assumption].
  rewrite <- Hptr.

  assert (Hcomplex3_0: ofs0 + size_chunk chunk <= Ptrofs.unsigned (Ptrofs.add ofs1 (Ptrofs.repr 12))). {
    specialize (Hcomplex 0).
    simpl in Hcomplex.
    fold Ptrofs.zero in Hcomplex.
    rewrite Ptrofs.add_zero in Hcomplex.
    assert (Hrange: 0 <= 0 < Z.of_nat (Datatypes.length (a :: lmr))). { simpl; lia. }
    specialize (Hcomplex Hrange).
    destruct Hcomplex as (Hcomplex0 & Hcomplex1 & Hcomplex2 & Hcomplex3).
    assumption.
  }
  eapply Mem.load_store_other; eauto.

  specialize (IHlmr m0 m1 blk ofs0 (Ptrofs.add ofs1 (Ptrofs.repr 16)) chunk vl).
  apply IHlmr.
  simpl in Hmax_range. simpl. lia.
  intros.
  assert (Hrange_1: 0 <= n+1 < Z.of_nat (Datatypes.length (a :: lmr))). {
    simpl; lia.
  }
  specialize (Hcomplex (n+1)%Z) as Hcomplex'.
  specialize (Hcomplex' Hrange_1).

  destruct Hcomplex' as (Hcomplex0 & Hcomplex1 & Hcomplex2 & Hcomplex3).
  -
    split.
    {
      split.
      rewrite <- Hcomplex0_1.
      destruct Hcomplex0; assumption.
      lia.

      specialize (Hcomplex 1) as Hcomplex1'.
      assert (Hlength1: 0 <= 1 < Z.of_nat (Datatypes.length (a :: lmr))). { lia. }
      specialize (Hcomplex1' Hlength1).
      destruct Hcomplex1' as ((_ & Hcomplex1') & _).
      unfold Ptrofs.add in Hcomplex1'.
      simpl in Hcomplex1'.
      lia.
      lia.

      (**r the main idea: using `Hcomplex0` *)
      specialize (Hcomplex n) as Hcomplex1'.
      assert (Hlength1: 0 <= n < Z.of_nat (Datatypes.length (a :: lmr))). { lia. }
      specialize (Hcomplex1' Hlength1).
      destruct Hcomplex1' as (_ & ( _ & Hcomplex1') & _).
      assumption.
    }
    split.
    {
      (**r the main idea: using `Hcomplex1` *)
      specialize (Hcomplex0_1 n).
      assert (Hn_ge_0: 0 <= n). { lia. }
      specialize (Hcomplex0_1 Hn_ge_0).
      specialize (Hcomplex 1) as Hcomplex1'.
      assert (Hlength1: 0 <= 1 < Z.of_nat (Datatypes.length (a :: lmr))). { lia. }
      specialize (Hcomplex1' Hlength1).
      destruct Hcomplex1' as (( _ & Hcomplex1') & _).
      simpl in Hcomplex1'.
      specialize (Hcomplex0_1 Hcomplex1'). (**r here we get the constain that `0 <= Ptrofs.unsigned ofs1 + 16 <= Ptrofs.max_unsigned` *)

      unfold Ptrofs.add.
      rewrite Ptrofs_unsigned_repr_16.
      rewrite Ptrofs.unsigned_repr with (z:= Ptrofs.unsigned ofs1 + 16); [| assumption].
      rewrite Ptrofs.unsigned_repr with (z:= n * 16); [| lia].
      rewrite Ptrofs_unsigned_repr_4.
      destruct Hcomplex1 as (Hcomplex1_0' & Hcomplex1_1').
      unfold Ptrofs.add in Hcomplex1_0'.
      rewrite Ptrofs.unsigned_repr with (z:= (n + 1) * 16) in Hcomplex1_0'; [| lia].
      rewrite Ptrofs_unsigned_repr_4 in Hcomplex1_0'.
      assert (Hmul_eq: (n + 1) * 16 = 16 + n * 16). { rewrite Z.mul_add_distr_r, Z.mul_1_l, Z.add_comm. reflexivity. }
      rewrite Hmul_eq in Hcomplex1_0'; clear Hmul_eq.
      rewrite <- Zplus_assoc_reverse in Hcomplex1_0'.
      split; [assumption |].

      unfold Ptrofs.add in Hcomplex1_1'.
      rewrite Ptrofs_unsigned_repr_16 in Hcomplex1_1'.
      assert (Hmax_range_32: 0 <= Ptrofs.unsigned ofs1 + 16 + 16 <= Ptrofs.max_unsigned). {
        rewrite Ptrofs.unsigned_repr in Hcomplex1_1'; [| assumption].
        lia.
      }
      rewrite Ptrofs.unsigned_repr; [| lia].
      rewrite Ptrofs.unsigned_repr in Hcomplex1_1'; [| lia].
      assert (Hmul_eq: (n + 1) * 16 = 16 + n * 16). { rewrite Z.mul_add_distr_r, Z.mul_1_l, Z.add_comm. reflexivity. }
      rewrite Hmul_eq in Hcomplex1_1'; clear Hmul_eq.
      rewrite <- Zplus_assoc_reverse in Hcomplex1_1'.
      lia.
    }

    specialize (Hcomplex0_1 n).
    assert (Hn_ge_0: 0 <= n). { lia. }
    specialize (Hcomplex0_1 Hn_ge_0).
    specialize (Hcomplex 1) as Hcomplex1'.
    assert (Hlength1: 0 <= 1 < Z.of_nat (Datatypes.length (a :: lmr))). { lia. }
    specialize (Hcomplex1' Hlength1).
    destruct Hcomplex1' as (( _ & Hcomplex1') & _).
    simpl in Hcomplex1'.
    specialize (Hcomplex0_1 Hcomplex1'). (**r here we get the constain that `0 <= Ptrofs.unsigned ofs1 + 16 <= Ptrofs.max_unsigned` *)

    unfold Ptrofs.add.
    rewrite Ptrofs_unsigned_repr_16.
    rewrite Ptrofs.unsigned_repr with (z:= Ptrofs.unsigned ofs1 + 16); [| assumption].
    rewrite Ptrofs.unsigned_repr with (z:= n * 16); [| lia].

    split.
    +
      (**r the main idea: using `Hcomplex2` *)
      unfold Ptrofs.add in Hcomplex2.
      rewrite Ptrofs_unsigned_repr_8 in Hcomplex2.
      rewrite Ptrofs.unsigned_repr with (z:= (n + 1) * 16) in Hcomplex2; [| lia].
      assert (Hmul_eq: (n + 1) * 16 = 16 + n * 16). { rewrite Z.mul_add_distr_r, Z.mul_1_l, Z.add_comm. reflexivity. }
      rewrite Hmul_eq in Hcomplex2; clear Hmul_eq.
      rewrite <- Zplus_assoc_reverse in Hcomplex2.
      assumption.
    +
      (**r the main idea: using `Hcomplex3` *)
      unfold Ptrofs.add in Hcomplex3.
      rewrite Ptrofs_unsigned_repr_12 in Hcomplex3.
      rewrite Ptrofs.unsigned_repr with (z:= (n + 1) * 16) in Hcomplex3; [| lia].
      assert (Hmul_eq: (n + 1) * 16 = 16 + n * 16). { rewrite Z.mul_add_distr_r, Z.mul_1_l, Z.add_comm. reflexivity. }
      rewrite Hmul_eq in Hcomplex3; clear Hmul_eq.
      rewrite <- Zplus_assoc_reverse in Hcomplex3.
      assumption.

  - assumption.
  - assumption.
Qed.
*)
(*
Lemma upd_preserves_match_list_ins:
  forall l m0 m1 blk ofs0 ofs1 chunk vl k
  (Hmax_range: Z.of_nat (List.length l) * 8 <= Ptrofs.max_unsigned - (104+16 * k) /\ k >= 1)
  (Hcomplex: forall n, 0 <= n < Z.of_nat (List.length l) ->
    (ofs0 + size_chunk chunk <= Ptrofs.unsigned (Ptrofs.add ofs1 (Ptrofs.repr (n * 8))) /\
    0 <= Ptrofs.unsigned ofs1 + (n * 8) <= Ptrofs.max_unsigned) /\
    (ofs0 + size_chunk chunk <= Ptrofs.unsigned (Ptrofs.add (Ptrofs.add ofs1 (Ptrofs.repr (n * 8))) (Ptrofs.repr 8)) /\
    0 <= Ptrofs.unsigned (Ptrofs.add ofs1 (Ptrofs.repr 8)) + n * 8 <= Ptrofs.max_unsigned)
  )
  (Hstore : Mem.store chunk m0 blk ofs0 vl = Some m1)
  (mem_regs : match_list_ins m0 blk ofs1 l),
    match_list_ins m1 blk ofs1 l.
Proof.
  induction l.
  constructor.

  intros.
  simpl.
  simpl in mem_regs0.
  destruct mem_regs0 as (Hload & mem_regs0).

  split.
  - rewrite <- Hload.
    eapply Mem.load_store_other; eauto.
    right; right.
    specialize (Hcomplex 0).
    assert (Hcomplex_pre: 0 <= 0 < Z.of_nat (Datatypes.length (a :: l))). { simpl; lia. }
    specialize (Hcomplex Hcomplex_pre); clear Hcomplex_pre.
    destruct Hcomplex as ((Hcomplex & _) & _).
    simpl in Hcomplex.
    fold Ptrofs.zero in Hcomplex.
    rewrite Ptrofs.add_zero in Hcomplex.
    assumption.
  - eapply IHl with (k:=k); [idtac | idtac | apply Hstore | apply mem_regs0].
    destruct Hmax_range as (Hmax_range & Htemp).
    split; [idtac| assumption]; clear Htemp.
    unfold Datatypes.length in Hmax_range.
    unfold Datatypes.length.
    lia.

    intros.
    (**r we need the case n = 1, i.e. Ptrofs.unsigned (Ptrofs.add ofs1 (Ptrofs.repr 8)) *)
    assert (Hcomplex1 := Hcomplex).
    specialize (Hcomplex1 1).
    assert (Hcomplex_pre: 0 <= 1 < Z.of_nat (Datatypes.length (a :: l))). { simpl; lia. }
    specialize (Hcomplex1 Hcomplex_pre); clear Hcomplex_pre.
    rewrite Z.mul_1_l in Hcomplex1.

    specialize (Hcomplex (n+1)).
    assert (Hcomplex_pre: 0 <= n + 1 < Z.of_nat (Datatypes.length (a :: l))). { simpl; lia. }
    specialize (Hcomplex Hcomplex_pre); clear Hcomplex_pre.

    clear - Hmax_range Hcomplex Hstore H Hcomplex1.
    unfold Ptrofs.add in *.
    rewrite Ptrofs_unsigned_repr_8 in *.

    destruct Hcomplex1 as ((Hcomplex1_0 & Hcomplex1_1) & Hcomplex1_2 & Hcomplex1_3).
    assert (Hmul_8: Ptrofs.unsigned (Ptrofs.repr (n * 8)) = n*8). {
      rewrite Ptrofs.unsigned_repr; [reflexivity | lia].
    }
    rewrite Hmul_8 in *; clear Hmul_8.
    assert (Hmul_8: Ptrofs.unsigned (Ptrofs.repr ((n+1) * 8)) = 8+ n*8). {
      destruct Hmax_range as (Hmax_range0 & Hmax_range1).
      unfold Datatypes.length in Hmax_range0, H.
      rewrite Ptrofs.unsigned_repr; [rewrite Z.mul_add_distr_r, Z.mul_1_l, Z.add_comm; reflexivity | lia].
    }
    rewrite Hmul_8 in *; clear Hmul_8.
    assert (Hofs1_8: Ptrofs.unsigned (Ptrofs.repr (Ptrofs.unsigned ofs1 + 8)) = Ptrofs.unsigned ofs1 + 8). {
      rewrite Ptrofs.unsigned_repr; [reflexivity | lia].
    }
    rewrite Hofs1_8 in *; clear Hofs1_8.
    split.
    destruct Hcomplex as (Hcomplex & _).
    rewrite Z.add_assoc in Hcomplex.
    destruct Hcomplex as (Hcomplex0 & Hcomplex1).
    split; [assumption| ].
    assert (Htmp: Ptrofs.unsigned ofs1 + (n + 1) * 8 = Ptrofs.unsigned ofs1 + 8 + n * 8). {
      rewrite Z.mul_add_distr_r, Z.mul_1_l.
      rewrite Z.add_comm with (n := n * 8).
      rewrite Z.add_assoc.
      reflexivity.
    }
    rewrite <- Htmp; clear Htmp; assumption.
    destruct Hcomplex as (_ & (Hcomplex0 & Hcomplex1)).
    split.
    rewrite Zplus_assoc_reverse.
    assumption.
    assert (Htmp: Ptrofs.unsigned (Ptrofs.repr (Ptrofs.unsigned ofs1 + 8 + 8)) = Ptrofs.unsigned ofs1 + 8 + 8). {
      rewrite Ptrofs.unsigned_repr;[reflexivity| lia].
    }
    rewrite Htmp; clear Htmp.
    rewrite Z.mul_add_distr_r, Z.mul_1_l in Hcomplex1.
    rewrite Z.add_comm with (n:= n * 8) in Hcomplex1.
    rewrite Z.add_assoc with (p:= n * 8) in Hcomplex1.
    assumption.
Qed.
*)
Lemma upd_preserves_match_list_ins:
  forall l chunk m0 m1 st_blk ins_blk ofs0 ofs1 vl
  (Hstore : Mem.store chunk m0 st_blk ofs0 vl = Some m1)
  (mem_regs : match_list_ins m0 ins_blk ofs1 l)
  (Hneq_blk : st_blk <> ins_blk),
    match_list_ins m1 ins_blk ofs1 l.
Proof.
  intro l.
  induction l.
  intros; simpl in *.
  constructor.

  intros; simpl in *.
  destruct mem_regs0 as (Hload & mem_regs0).
  split.
  rewrite <- Hload.
  eapply Mem.load_store_other; eauto.

  eapply IHl; eauto.
Qed.

Lemma upd_preserves_match_list_region:
  forall l chunk m0 m1 st_blk mrs_blk ofs0 ofs1 vl
  (Hstore : Mem.store chunk m0 st_blk ofs0 vl = Some m1)
  (mem_regs : match_list_region m0 mrs_blk ofs1 l)
  (Hneq_blk : st_blk <> mrs_blk),
    match_list_region m1 mrs_blk ofs1 l.
Proof.
  intro l.
  induction l.
  intros; simpl in *.
  constructor.

  intros; simpl in *.
  unfold match_region_at_ofs in *.
  destruct mem_regs0 as (Hload & mem_regs0).
  split.
  destruct Hload as ((vl0 & Hload0 & Heq0) & (vl1 & Hload1 & Heq1) & (vl2 & Hload2 & Heq2) & (blk3 & ofs3 & Hload3 & Heq_ptr)).

  split.
  exists vl0; rewrite <- Hload0; split; [
  eapply Mem.load_store_other; eauto | assumption].

  split.
  exists vl1; rewrite <- Hload1; split; [
  eapply Mem.load_store_other; eauto | assumption].

  split.
  exists vl2; rewrite <- Hload2; split; [
  eapply Mem.load_store_other; eauto | assumption].

  exists blk3, ofs3; rewrite <- Hload3; split; [
  eapply Mem.load_store_other; eauto | assumption].

  eapply IHl; eauto.
Qed.

Lemma upd_reg_preserves_match_state:
  forall st0 st1 m0 m1 st_blk mrs_blk ins_blk r vl
  (Hst    : match_state st_blk mrs_blk ins_blk st0 m0)
  (Hst1   : State.upd_reg r (Vlong vl) st0 = st1)
  (Hstore : Mem.store AST.Mint64 m0 st_blk (8 + 8 * id_of_reg r) (Vlong vl) = Some m1),
    match_state st_blk mrs_blk ins_blk st1 m1.
Proof.
  intros.
  subst.
  set (Hst' := Hst).
  destruct Hst'.
  split; unfold Mem.loadv in *.
  -
    rewrite <- (upd_reg_same_mem _ r (Vlong vl)).
    assert (Hunchanged_on': Mem.unchanged_on (fun (b : block) (_ : Z) => b <> st_blk /\ b <> mrs_blk /\ b <> ins_blk) m0 m1). {
      eapply Mem.store_unchanged_on; eauto.
      intros.
      intro.
      destruct H0 as (H0 & _).
      apply H0; reflexivity.
    }
    apply Mem.unchanged_on_trans with(m2:= m0); auto.
  -
    rewrite <- (upd_reg_same_pc _ r (Vlong vl)).
    rewrite <- mpc0.
    eapply Mem.load_store_other; eauto.
    right; left.
    unfold id_of_reg; simpl.
    fold Ptrofs.zero.
    rewrite Ptrofs.unsigned_zero.
    destruct r; try lia.
  - rewrite <- (upd_reg_same_flag _ r (Vlong vl)).
    rewrite <- mflags0.
    eapply Mem.load_store_other; eauto.
    right; left.
    rewrite Ptrofs_unsigned_repr_n; [| try simpl; lia].
    unfold id_of_reg; simpl; destruct r; try lia.
  - unfold match_registers in *.
    intros.
    specialize (mregs0 r0).
    destruct mregs0 as (vl0 & mregs0 & mregs1).
    unfold Mem.loadv, Ptrofs.add in *.

    rewrite Hreg_eq in *.
    destruct (reg_eq r0 r).
    + (**r case: r0 = r *)
      subst.
      exists vl.
      split.
      assert (Hload_result: Val.load_result Mint64 (Vlong vl) = (Vlong vl)). {
        reflexivity.
      }
      rewrite <- Hload_result.
      eapply Mem.load_store_same; eauto.
      unfold State.upd_reg; simpl.
      rewrite eval_upd_regmap_same.
      reflexivity.
    +
      exists vl0.
      unfold State.upd_reg, regs_st.
      
      rewrite eval_upd_regmap_other.
      split.
      2:{
        rewrite mregs1.
        reflexivity.
      }
      rewrite <- mregs0.
      eapply Mem.load_store_other; eauto.
      right.
      2:{ assumption. }
      destruct r0, r; simpl; [try (exfalso; apply n; reflexivity) || (try left; lia) || (try right; lia) ..].
  - simpl.
    destruct mins_len0 as (mins_len0 & mins_len1).
    split; [| assumption].

    rewrite Ptrofs_unsigned_repr_n in *; try (simpl; lia).
    rewrite <- mins_len0.
    eapply Mem.load_store_other; eauto.
    right; right.
    unfold id_of_reg, size_chunk; destruct r; lia.
  - (**r match_ins *)
    unfold match_ins.
    unfold match_ins in mins0.
    destruct mins0 as (Hload & mins_len & mins_max & mins0).
    split.
    rewrite <- Hload.
    eapply Mem.load_store_other; eauto.
    right; right.
    rewrite Ptrofs_unsigned_repr_n in *; try (simpl; lia).
    unfold id_of_reg, size_chunk; destruct r; lia.

    split; [assumption | ].
    split; [assumption | ].
    assert (Hins_eq : ins (State.upd_reg r (Vlong vl) st0) = ins st0). {
      unfold State.upd_reg.
      simpl.
      reflexivity.
    }
    rewrite Hins_eq; clear Hins_eq.
    destruct minvalid0 as (_ & _ & _ & _ & _ & minvalid0).
    eapply upd_preserves_match_list_ins; eauto.
  - rewrite <- (upd_reg_same_mrs_num _ r (Vlong vl)).
    destruct mmrs_num0 as (Hload & Hge).
    split; [| assumption].
    rewrite <- Hload.
    eapply Mem.load_store_other; eauto.
    right; right.
    unfold size_chunk.
    assert (Hle_104: 8 + 8 * id_of_reg r + 8 <= 104). { unfold id_of_reg; destruct r; lia. }
    rewrite Ptrofs_unsigned_repr_n; [| try simpl; lia].
    assumption.
  - unfold match_regions in *.
    destruct mem_regs0 as (Hload & mrs_len & mrs_max & mem_regs0).
    rewrite <- (upd_reg_same_mrs _ r (Vlong vl)).

    split.
    rewrite <- Hload.
    eapply Mem.load_store_other; eauto.
    right; right.
    rewrite Ptrofs_unsigned_repr_n in *; try (simpl; lia).
    unfold id_of_reg, size_chunk; destruct r; lia.

    split; [assumption | ].
    split; [assumption | ].
    destruct minvalid0 as (_ & _ & _ & minvalid0 & _ & _).
    eapply upd_preserves_match_list_region; eauto.

  - clear - mperm0 Hstore.
    unfold Mem.range_perm in *.
    intros.
    eapply Mem.perm_store_1.
    apply Hstore.
    apply mperm0.
    unfold size_of_state in *.
    rewrite <- upd_reg_same_mrs_num in *.
    assumption.
  - rewrite <- upd_reg_same_mem.
    assumption.
Qed.


Lemma upd_pc_preserves_match_state:
  forall st0 st1 m0 m1 st_blk mrs_blk ins_blk pc
  (Hst    : match_state st_blk mrs_blk ins_blk st0 m0)
  (Hst1   : State.upd_pc pc st0 = st1)
  (Hstore : Mem.store AST.Mint32 m0 st_blk 0 (Vint pc) = Some m1),
    match_state st_blk mrs_blk ins_blk st1 m1.
Proof.
  intros.
  subst.
  set (Hst' := Hst).
  split.
  -
    destruct Hst' as (Hunchanged_on, _, _, _, _, _, _, _, _, _).
    rewrite <- upd_pc_same_mem.
    assert (Hunchanged_on': Mem.unchanged_on (fun (b : block) (_ : Z) => b <> st_blk /\ b <> mrs_blk /\ b <> ins_blk) m0 m1). {
      eapply Mem.store_unchanged_on; eauto.
      intros.
      intro.
      destruct H0 as(H0 & _).
      apply H0; reflexivity.
    }
    apply Mem.unchanged_on_trans with(m2:= m0); auto.
  -
    destruct Hst' as (_ , Hpc, _, _, _, _, _, _, _, _).
    unfold Mem.loadv in *.
    fold Ptrofs.zero in *.
    rewrite Ptrofs.unsigned_zero in *.
    apply Mem.load_store_same in Hstore.
    rewrite Hstore.
    unfold Val.load_result.
    reflexivity.
  -
    destruct Hst' as (_ , _, Hflag, _, _, _, _, _, _, _).
    rewrite <- upd_pc_same_flag.
    rewrite <- Hflag.
    eapply Mem.load_store_other.
    apply Hstore.
    right; right.
    rewrite Ptrofs_unsigned_repr_n; [| try simpl; lia].
    reflexivity.
  -
    destruct Hst' as (_ , _, _, Hregs, _, _, _, _, _, _).
    rewrite <- upd_pc_same_regs.
    unfold match_registers in *.
    intros.
    specialize (Hregs r).
    destruct Hregs as (vl & Hload & Hvl_eq).
    exists vl.
    split; [| assumption].
    rewrite <- Hload.
    unfold Mem.loadv.
    eapply Mem.load_store_other.
    apply Hstore.
    right; right.
    unfold Ptrofs.add in *.
    unfold size_chunk.
    rewrite Ptrofs_unsigned_repr_n in *; try (simpl; lia).
    rewrite Ptrofs_unsigned_repr_id_of_reg in *.
    rewrite Ptrofs_unsigned_repr_n in *; try (simpl; lia).
    unfold id_of_reg; destruct r; lia.
    rewrite Ptrofs_unsigned_repr_n in *; try (simpl; lia).
    rewrite Ptrofs_unsigned_repr_n with (n:= 8 * id_of_reg r) in *; try (simpl; lia).
    all: unfold id_of_reg; destruct r; lia.
  - 
    destruct Hst' as (_ , _, _, _, (Hins_len & Hge), _, _, _, _, _).
    rewrite <- upd_pc_same_ins_len.
    split; [| assumption].
    rewrite <- Hins_len.
    simpl.
    eapply Mem.load_store_other; eauto.
    right; right.
    rewrite Ptrofs_unsigned_repr_n in *; try (simpl; lia).
  - 
    destruct Hst' as (_ , _, _, _, _, Hins, _, _, _, (_ & _ & _ & _ & _ & Hneq_blk)).
    unfold match_ins in *.
    destruct Hins as (Hload & Hins_len & Hins_max & Hins).
    rewrite <- upd_pc_same_ins.
    rewrite <- upd_pc_same_ins_len.
    split.
    rewrite <- Hload.
    eapply Mem.load_store_other; eauto.
    right; right.
    rewrite Ptrofs_unsigned_repr_n in *; try (simpl; lia).
    

    split; [assumption |].
    split; [assumption |].
    eapply upd_preserves_match_list_ins; eauto.
  - 
    destruct Hst' as (_ , _, _, _, _, _, (Hmrs_len & Hge), _, _, _).
    rewrite <- upd_pc_same_mrs_num.
    split; [| assumption].
    rewrite <- Hmrs_len.
    simpl.
    eapply Mem.load_store_other; eauto.
    right; right.
    rewrite Ptrofs_unsigned_repr_n in *; try (simpl; lia).
  - 
    destruct Hst' as (_ , _, _, _, _, _, _, Hmrs, _, (_ & _ & _ & Hneq_blk & _ & _)).
    unfold match_regions in *.
    rewrite <- upd_pc_same_mrs.
    rewrite <- upd_pc_same_mrs_num.
    destruct Hmrs as (Hload & Hmrs_len & Hmrs_ge & Hmrs).


    split.
    rewrite <- Hload.
    eapply Mem.load_store_other; eauto.
    right; right.
    rewrite Ptrofs_unsigned_repr_n in *; try (simpl; lia).

    split; [assumption| ].
    split; [assumption| ].
    eapply upd_preserves_match_list_region; eauto.
  -
    destruct Hst' as (_ , _, _, _, _, _, _, _, Hperm, _).
    unfold size_of_state in *.
    rewrite <- upd_pc_same_mrs_num.
    unfold Mem.range_perm in *.
    intros.
    eapply Mem.perm_store_1.
    apply Hstore.
    apply Hperm.
    assumption.
  -
    destruct Hst' as (_ , _, _, _, _, _, _, _, _, Hvalid).
    rewrite <- upd_pc_same_mem.
    assumption.
Qed.

Lemma upd_flag_preserves_match_state:
  forall st0 st1 m0 m1 st_blk mrs_blk ins_blk flag
  (Hst    : match_state st_blk mrs_blk ins_blk st0 m0)
  (Hst1   : State.upd_flag flag st0 = st1)
  (Hstore : Mem.store AST.Mint32 m0 st_blk 4 (Vint (int_of_flag flag)) = Some m1),
    match_state st_blk mrs_blk ins_blk st1 m1.
Proof.
  intros.
  subst.
  set (Hst' := Hst).
  split.
  -
    destruct Hst' as (Hunchanged_on, _, _, _, _, _, _, _, _, _).
    rewrite <- upd_flag_same_mem.
    assert (Hunchanged_on': Mem.unchanged_on (fun (b : block) (_ : Z) => b <> st_blk /\ b <> mrs_blk /\ b <> ins_blk) m0 m1). {
      eapply Mem.store_unchanged_on; eauto.
      intros.
      intro H0; destruct H0 as (H0 & _); apply H0; reflexivity.
    }
    apply Mem.unchanged_on_trans with(m2:= m0); auto.
  -
    destruct Hst' as (_ , Hpc, _, _, _, _, _, _, _, _).
    rewrite <- upd_flag_same_pc.
    rewrite <- Hpc.
    eapply Mem.load_store_other.
    apply Hstore.
    right; left.
    fold Ptrofs.zero; rewrite Ptrofs.unsigned_zero.
    reflexivity.
  -
    destruct Hst' as (_ , _, Hflag, _, _, _, _, _, _, _).

    unfold Mem.loadv in *.
    rewrite Ptrofs_unsigned_repr_n in *; try (simpl; lia).
    apply Mem.load_store_same in Hstore.
    rewrite Hstore.
    unfold Val.load_result.
    reflexivity.
  -
    destruct Hst' as (_ , _, _, Hregs, _, _, _, _, _, _).
    rewrite <- upd_flag_same_regs.
    unfold match_registers in *.
    intros.
    specialize (Hregs r).
    destruct Hregs as (vl & Hload & Hvl_eq).
    exists vl.
    split; [| assumption].
    rewrite <- Hload.
    unfold Mem.loadv.
    eapply Mem.load_store_other.
    apply Hstore.
    right; right.
    unfold Ptrofs.add in *.
    unfold size_chunk.
    rewrite Ptrofs_unsigned_repr_n in *; try (simpl; lia).
    rewrite Ptrofs_unsigned_repr_n in *; try (simpl; lia).
    rewrite Ptrofs_unsigned_repr_n in *; try (simpl; lia).
    4:
    rewrite Ptrofs_unsigned_repr_n in *; try (simpl; lia).
    4:
    rewrite Ptrofs_unsigned_repr_n in *; try (simpl; lia).
    all: unfold id_of_reg; destruct r; lia.
  -
    destruct Hst' as (_ , _, _, _, (Hins_len & Hge), _, _, _, _, _).
    rewrite <- upd_flag_same_ins_len.
    split; [| assumption].
    rewrite <- Hins_len.
    simpl.
    eapply Mem.load_store_other; eauto.
    right; right.
    rewrite Ptrofs_unsigned_repr_n in *; try (simpl; lia).
  - 
    destruct Hst' as (_ , _, _, _, _, Hins, _, _, _, (_ & _ & _ & _ & _ & Hneq_blk)).
    unfold match_ins in *.
    destruct Hins as (Hload & Hins_len & Hins_max & Hins).
    rewrite <- upd_flag_same_ins.
    rewrite <- upd_flag_same_ins_len.

    split.
    rewrite <- Hload.
    eapply Mem.load_store_other; eauto.
    right; right.
    rewrite Ptrofs_unsigned_repr_n in *; try (simpl; lia).

    split; [assumption |].
    split; [assumption |].
    eapply upd_preserves_match_list_ins; eauto.
  - 
    destruct Hst' as (_ , _, _, _, _, _, (Hmrs_len & Hge), _, _, _).
    rewrite <- upd_flag_same_mrs_num.
    split; [| assumption].
    rewrite <- Hmrs_len.
    simpl.
    eapply Mem.load_store_other; eauto.
    right; right.
    rewrite Ptrofs_unsigned_repr_n in *; try (simpl; lia).
  - 
    destruct Hst' as (_ , _, _, _, _, _, _, Hmrs, _, (_ & _ & _ & Hneq_blk & _ & _)).
    unfold match_regions in *.
    rewrite <- upd_flag_same_mrs.
    rewrite <- upd_flag_same_mrs_num.
    destruct Hmrs as (Hload & Hmrs_len & Hmrs_ge & Hmrs).

    split.
    rewrite <- Hload.
    eapply Mem.load_store_other; eauto.
    right; right.
    rewrite Ptrofs_unsigned_repr_n in *; try (simpl; lia).

    split; [assumption| ].
    split; [assumption| ].
    eapply upd_preserves_match_list_region; eauto.
  -
    destruct Hst' as (_ , _, _, _, _, _, _, _, Hperm, _).
    unfold size_of_state in *.
    rewrite <- upd_flag_same_mrs_num.
    unfold Mem.range_perm in *.
    intros.
    eapply Mem.perm_store_1.
    apply Hstore.
    apply Hperm.
    assumption.
  -
    destruct Hst' as (_ , _, _, _, _, _, _, _, _, Hvalid).
    rewrite <- upd_flag_same_mem.
    assumption.
Qed.

(*
Lemma mem_store_preserves_match_state:
  forall st0 st1 m0 m1 st_blk mrs_blk ins_blk chunk m b ofs v
  (Hst    : match_state st_blk mrs_blk ins_blk st0 m0)
  (Hrbpf_m: Mem.store chunk (bpf_m st0) b ofs v = Some m)
  (Hst1   : upd_mem m st0 = st1)
  (Hneq_blk: b <> st_blk /\ b <> mrs_blk /\ b <> ins_blk)
  (Hstore : Mem.store chunk m0 b ofs v = Some m1),
    match_state st_blk mrs_blk ins_blk st1 m1.
Proof.
  intros.
  subst.
  set (Hst' := Hst).
  split.
  -
    destruct Hst' as (Hunchanged_on, _, _, _, _, _, _, _, _, _).
    unfold bpf_m, upd_mem; simpl.
    assert (Hunchanged_on0: Mem.unchanged_on (fun (b0 : block) (_ : Z) => b0 <> b) (bpf_m st0) m). {
      eapply Mem.store_unchanged_on; eauto.
    }
    assert (Hunchanged_on': Mem.unchanged_on (fun (b : block) (_ : Z) => b <> st_blk /\ b <> mrs_blk /\ b <> ins_blk) m0 m1). {
      eapply Mem.store_unchanged_on; eauto.
      apply Hrbpf_m.
      intros.
      intro H0; destruct H0 as (H0 & _); apply H0; reflexivity.
    }
    apply Mem.unchanged_on_trans with(m2:= m0); auto.
  -
    destruct Hst' as (_ , Hpc, _, _, _, _, _, _, _, _).
    rewrite <- upd_flag_same_pc.
    rewrite <- Hpc.
    eapply Mem.load_store_other.
    apply Hstore.
    right; left.
    fold Ptrofs.zero; rewrite Ptrofs.unsigned_zero.
    reflexivity.
  -
    destruct Hst' as (_ , _, Hflag, _, _, _, _, _, _, _).

    unfold Mem.loadv in *.
    rewrite Ptrofs_unsigned_repr_n in *; try (simpl; lia).
    apply Mem.load_store_same in Hstore.
    rewrite Hstore.
    unfold Val.load_result.
    reflexivity.
  -
    destruct Hst' as (_ , _, _, Hregs, _, _, _, _, _, _).
    rewrite <- upd_flag_same_regs.
    unfold match_registers in *.
    intros.
    specialize (Hregs r).
    destruct Hregs as (vl & Hload & Hvl_eq).
    exists vl.
    split; [| assumption].
    rewrite <- Hload.
    unfold Mem.loadv.
    eapply Mem.load_store_other.
    apply Hstore.
    right; right.
    unfold Ptrofs.add in *.
    unfold size_chunk.
    rewrite Ptrofs_unsigned_repr_n in *; try (simpl; lia).
    rewrite Ptrofs_unsigned_repr_n in *; try (simpl; lia).
    rewrite Ptrofs_unsigned_repr_n in *; try (simpl; lia).
    4:
    rewrite Ptrofs_unsigned_repr_n in *; try (simpl; lia).
    4:
    rewrite Ptrofs_unsigned_repr_n in *; try (simpl; lia).
    all: unfold id_of_reg; destruct r; lia.
  -
    destruct Hst' as (_ , _, _, _, (Hins_len & Hge), _, _, _, _, _).
    rewrite <- upd_flag_same_ins_len.
    split; [| assumption].
    rewrite <- Hins_len.
    simpl.
    eapply Mem.load_store_other; eauto.
    right; right.
    rewrite Ptrofs_unsigned_repr_n in *; try (simpl; lia).
  - 
    destruct Hst' as (_ , _, _, _, _, Hins, _, _, _, (_ & _ & _ & _ & _ & Hneq_blk)).
    unfold match_ins in *.
    destruct Hins as (Hins_len & Hins_max & Hins).
    rewrite <- upd_flag_same_ins.
    rewrite <- upd_flag_same_ins_len.
    split; [assumption |].
    split; [assumption |].
    eapply upd_preserves_match_list_ins; eauto.
  - 
    destruct Hst' as (_ , _, _, _, _, _, (Hmrs_len & Hge), _, _, _).
    rewrite <- upd_flag_same_mrs_num.
    split; [| assumption].
    rewrite <- Hmrs_len.
    simpl.
    eapply Mem.load_store_other; eauto.
    right; right.
    rewrite Ptrofs_unsigned_repr_n in *; try (simpl; lia).
  - 
    destruct Hst' as (_ , _, _, _, _, _, _, Hmrs, _, (_ & _ & _ & Hneq_blk & _ & _)).
    unfold match_regions in *.
    rewrite <- upd_flag_same_mrs.
    rewrite <- upd_flag_same_mrs_num.
    destruct Hmrs as (Hmrs_len & Hmrs_ge & Hmrs).
    split; [assumption| ].
    split; [assumption| ].
    eapply upd_preserves_match_list_region; eauto.
  -
    destruct Hst' as (_ , _, _, _, _, _, _, _, Hperm, _).
    unfold size_of_state in *.
    rewrite <- upd_flag_same_mrs_num.
    unfold Mem.range_perm in *.
    intros.
    eapply Mem.perm_store_1.
    apply Hstore.
    apply Hperm.
    assumption.
  -
    destruct Hst' as (_ , _, _, _, _, _, _, _, _, Hvalid).
    rewrite <- upd_flag_same_mem.
    assumption.
Qed.

*)

Close Scope Z_scope.