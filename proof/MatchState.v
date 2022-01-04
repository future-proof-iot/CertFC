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

Definition match_region_at_ofs (mr:memory_region) (bl_regions : block) (ofs : ptrofs) (m: mem)  : Prop :=
  (exists vl,  Mem.loadv AST.Mint32 m (Vptr bl_regions ofs) = Some (Vint vl) /\ (start_addr mr) = Vint vl)    /\ (**r start_addr mr = Vint vl*)
    (exists vl,  Mem.loadv AST.Mint32 m (Vptr bl_regions (Ptrofs.add ofs (Ptrofs.repr 4))) = Some (Vint vl) /\ (block_size mr) = Vint vl) /\ (**r block_size mr = Vint vl*)
    (exists vl,  Mem.loadv AST.Mint32 m (Vptr bl_regions (Ptrofs.add ofs (Ptrofs.repr 8))) = Some (Vint vl) /\ correct_perm (block_perm mr)  vl) /\ (**r block_perm mr = Vint vl*)
    (exists b o,  Mem.loadv AST.Mptr  m (Vptr bl_regions (Ptrofs.add ofs (Ptrofs.repr 12))) = Some (Vptr b o) /\ (block_ptr mr) = Vptr b o).


Definition size_of_region  := Ptrofs.repr (4 * 4). (* 4 * 32 bits *)

Fixpoint match_list_region  (m:mem) (bl_regions: block) (ofs:ptrofs) (l:list memory_region) :=
  match l with
  | nil => True
  | mr :: l' => match_region_at_ofs  mr bl_regions ofs m /\
                  match_list_region  m bl_regions (Ptrofs.add ofs size_of_region) l'
  end.

Definition match_regions  (mrs:list memory_region) (bl_regions: block) (ofs : ptrofs) (m:mem) :=
    match_list_region m bl_regions ofs mrs.


Section S.

  (* [bl_state] is the memory block for the monadic state *)
  Variable bl_state : block.

  Variable ins_block: block.

  Definition match_registers  (rmap:regmap) (bl_reg:block) (ofs : ptrofs) (m : mem) : Prop:=
    forall (r:reg),
    exists vl, Mem.loadv Mint64 m (Vptr bl_reg (Ptrofs.add ofs (Ptrofs.repr (8 * (id_of_reg r))))) = Some (Vlong vl) /\ (**r it should be `(eval_regmap r rmap)`*)
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
  
Definition is_byte_memval (mv: memval): Prop :=
  match mv with
  | Undef => False
  | Byte b => True
  | Fragment _ _ _ => False
  end.

  Record match_state  (st: DxState.state) (m: mem) : Prop :=
    {
      minj     : Mem.inject inject_id (bpf_m st) m; (**r inject_id is enough because `mi_freeblocks` says the case `inject_id bl_state = None` and therefore we need the `minvalid` *)
      mpc      : Mem.loadv AST.Mint32 m (Vptr bl_state (Ptrofs.repr 0)) = Some (Vint  (pc_loc st));
      mflags   : Mem.loadv AST.Mint32 m (Vptr bl_state (Ptrofs.repr 4)) = Some (Vint  (int_of_flag (flag st)));
      mregs    : match_registers (regs_st st) bl_state (Ptrofs.repr 8) m;
      mrs_num  : Mem.loadv AST.Mint32 m (Vptr bl_state (Ptrofs.repr (size_of_regs + 8))) = Some (Vint  (Int.repr (Z.of_nat (DxState.mrs_num st)))) /\ (Z.of_nat(DxState.mrs_num st)) >= 1; (**r at least we have the memory region that corresponds to the input paramters of the interpreter *)
      mem_regs : match_regions (bpf_mrs st) bl_state (Ptrofs.repr (size_of_regs + 12)) m /\ List.length (bpf_mrs st) = (DxState.mrs_num st); (**r the number of bpf_mrs is exactly the mrs_num *)
      mperm    : Mem.range_perm m bl_state 0 (size_of_state st) Cur Freeable;
      minvalid : ~Mem.valid_block (bpf_m st) bl_state /\ ~Mem.valid_block (bpf_m st) ins_block;  (**r ysh: bl_state and ins_block don't exist in st *)
      munchange: Mem.unchanged_on (fun b _ => b <> bl_state /\ b <> ins_block) (bpf_m st) m; (**r (bpf_m st) = m - {bl_state, ins_block} *)
      mByte    : forall b ofs, (b <> bl_state /\ b <> ins_block) -> is_byte_memval (Maps.ZMap.get ofs (Maps.PMap.get b (Mem.mem_contents m)));
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
  forall m0 blk ins st
    (Hst: match_state blk ins st m0),
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
  forall m0 blk ins pc st
    (Hst: match_state blk ins st m0),
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
  forall m0 blk ins st
    (Hst: match_state blk ins st m0),
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
  forall m0 blk ins st v
    (Hst: match_state blk ins st m0),
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
  forall m0 blk ins st r
    (Hst: match_state blk ins st m0),
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
  forall m0 blk ins st r v
    (Hst: match_state blk ins st m0),
    exists m1,
    Mem.store AST.Mint64 m0 blk (8 + (8 * (id_of_reg r))) (Vlong v) = Some m1.
Proof.
  intros.
  apply (upd_regs_write_access _ _ _ _ r) in Hst.
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
              match_region_at_ofs mr bl_region o m.

(* Useful matching relations *)

Definition match_region (bl_region : block) (mr: memory_region) (v: val64_t) (st: stateM) (m:Memory.Mem.mem) :=
  exists o, v = Vptr bl_region (Ptrofs.mul size_of_region  o) /\
              match_region_at_ofs mr bl_region o m.

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

(**r a set of lemmas say upd_reg/flag/pc... don't change the memory of rbpf *)

Lemma upd_reg_same_mem:
  forall st0 r vl,
    bpf_m st0 = bpf_m (DxState.upd_reg r vl st0).
Proof.
  unfold DxState.upd_reg.
  intros.
  reflexivity.
Qed.

Lemma upd_pc_same_mem:
  forall st0 pc,
    bpf_m st0 = bpf_m (DxState.upd_pc pc st0).
Proof.
  unfold DxState.upd_pc.
  intros.
  reflexivity.
Qed.

Lemma upd_pc_incr_same_mem:
  forall st0,
    bpf_m st0 = bpf_m (DxState.upd_pc_incr st0).
Proof.
  unfold DxState.upd_pc_incr.
  intros.
  reflexivity.
Qed.

Lemma upd_flag_same_mem:
  forall st0 f,
    bpf_m st0 = bpf_m (DxState.upd_flag f st0).
Proof.
  unfold DxState.upd_flag.
  intros.
  reflexivity.
Qed.

Lemma upd_unchanged_on:
  forall st m0 m1 blk ins chunk ofs vl
  (Hst    : match_state blk ins st m0)
  (Hstore : Mem.store chunk m0 blk ofs vl = Some m1),
    Mem.unchanged_on (fun b _ => b <> blk /\ b <> ins) m0 m1.
Proof.
  intros.
  destruct Hst.
  destruct minj0.
  clear - mi_inj mi_freeblocks minvalid0 munchange0 mByte0 Hstore.
  eapply Mem.store_unchanged_on.
  rewrite Hstore.
  reflexivity.
  intros.
  intro.
  destruct H0.
  apply H0; reflexivity.
Qed.

Lemma upd_reg_preserves_match_state:
  forall st0 st1 m0 m1 blk ins r vl
  (Hst    : match_state blk ins st0 m0)
  (Hst1   : DxState.upd_reg r (Vlong vl) st0 = st1)
  (Hstore : Mem.store AST.Mint64 m0 blk (8 + 8 * id_of_reg r) (Vlong vl) = Some m1),
    match_state blk ins st1 m1.
Proof.
  intros.
  set (Hst' := Hst).
  destruct Hst'.
  split; unfold Mem.loadv in *.
  -
    destruct minj0.
    split.
    + (**r mi_inj *)
      clear - Hst Hst1 mi_inj mi_freeblocks minvalid0 munchange0 mByte0 Hstore.
      destruct minvalid0 as (minvalid_st & minvalid_ins).
      destruct mi_inj.

      (**r say rbpf blocks are all Byte *)
      unfold is_byte_memval in mByte0.

      split; intros; inversion H; subst; rewrite <- (upd_reg_same_mem _ r (Vlong vl)) in H0.
      * (**r mi_perm *)
        specialize (mi_perm b2 b2 0 ofs k p H H0).
        (**r Search (Mem.perm).*)
        apply Mem.perm_store_1 with (chunk:= Mint64) (m1:= m0) (b:=blk) (ofs:=(8 + 8 * id_of_reg r)%Z) (v:= (Vlong vl)).
        assumption.
        assumption.
      * (**r mi_align *)
        apply Z.divide_0_r.
      * (**r mi_memval *)
        specialize (mi_memval b2 ofs b2 0 H H0).
        destruct munchange0.

        (***r Search (memval_inject). *)
        repeat rewrite Z.add_0_r.
        destruct (Pos.eqb b2 blk) eqn: Hblk_eq.
        ** (**r b2 = blk *)
          apply Peqb_true_eq in Hblk_eq.
          subst b2.
          apply mi_freeblocks in minvalid_st.
          rewrite minvalid_st in H.
          inversion H.
        ** (**r b2 <> blk *)
          destruct (Pos.eqb b2 ins) eqn: Hins_eq.
          ++ (**r b2 = ins *)
            apply Peqb_true_eq in Hins_eq.
            subst b2.
            apply mi_freeblocks in minvalid_ins.
            rewrite minvalid_ins in H.
            inversion H.
          ++ (**r b2 <> ins *)
            (**r Search (Pos.eqb). *)
            rewrite Pos.eqb_neq in *.
            assert (Hb2_neq: b2 <> blk /\ b2 <> ins). {
              split; assumption.
            }
            specialize (unchanged_on_contents b2 ofs Hb2_neq H0).
            rewrite <- (upd_reg_same_mem _ r (Vlong vl)).
            rewrite <- unchanged_on_contents.
            assert (Hunchange: Mem.unchanged_on (fun b _ => b <> blk /\ b <> ins) m0 m1). {
              eapply upd_unchanged_on.
              apply Hst.
              apply Hstore.
            }
            destruct Hunchange.
            (**r we need : Mem.perm m0 b2 ofs0 Cur Readable *)
            assert (Hm0_perm: Mem.perm m0 b2 ofs Cur Readable). {
              specialize (mi_perm b2 b2 0 ofs Cur Readable H H0).
              rewrite Z.add_0_r in mi_perm.
              assumption.
            }
            specialize (unchanged_on_contents0 b2 ofs Hb2_neq Hm0_perm).
            rewrite unchanged_on_contents0.
            specialize (mByte0 b2 ofs Hb2_neq).
            destruct (Maps.ZMap.get _ (Maps.PMap.get _ (Mem.mem_contents _))) eqn: HByte in mByte0; [ inversion mByte0| idtac | inversion mByte0].
            rewrite HByte.
            constructor.
    + (**r mi_freeblocks *)
      intros.
      subst.
      rewrite <- (upd_reg_same_mem _ r (Vlong vl)) in H.
      apply mi_freeblocks.
      assumption.
    + (**r mi_mappedblocks *)
      intros.
      assert (Hunchange: Mem.unchanged_on (fun b _ => b <> blk /\ b <> ins) m0 m1). {
        eapply upd_unchanged_on; eauto.
      }
      eapply Mem.valid_block_unchanged_on; eauto.
    + (**r mi_no_overlap *)
      subst.
      rewrite <- (upd_reg_same_mem _ r (Vlong vl)).
      assumption.
    + (**r mi_representable *)
      subst.
      rewrite <- (upd_reg_same_mem _ r (Vlong vl)).
      assumption.
    + (**r mi_perm_inv *)
      subst.
      rewrite <- (upd_reg_same_mem _ r (Vlong vl)).
      intros.
      eapply mi_perm_inv; eauto.
      eapply Mem.perm_unchanged_on_2; eauto.
      eapply upd_unchanged_on; eauto.
      simpl.
      inversion H; subst.
      destruct minvalid0 as (minvalid_st & minvalid_ins).
      split.
      * specialize (mi_freeblocks _ minvalid_st); intro; subst; rewrite mi_freeblocks in H; inversion H.
      * specialize (mi_freeblocks _ minvalid_ins); intro; subst; rewrite mi_freeblocks in H; inversion H.
   -
    eapply Mem.load_unchanged_on; eauto. admit.
    eapply upd_unchanged_on; eauto.
    intros; simpl.
    split.

Close Scope Z_scope.