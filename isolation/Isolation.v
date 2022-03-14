From compcert Require Import Integers Values AST Memory Memtype.
From bpf.comm Require Import State Monad.
From bpf.model Require Import Syntax Semantics.
From bpf.isolation Require Import CommonISOLib AlignChunk RegsInv MemInv VerifierInv IsolationLemma.

From Coq Require Import ZArith Lia.

Open Scope Z_scope.

Axiom call_inv: forall st1 st2 b ofs res
  (Hreg : register_inv st1)
  (Hmem : memory_inv st1)
  (Hver: verifier_inv st1)
  (Hcall: exec_function (Vptr b ofs) st1 = Some (res, st2)),
    register_inv st2 /\ memory_inv st2 /\ verifier_inv st2.

Theorem step_preserving_inv:
  forall st1 st2 t
    (Hreg: register_inv st1)
    (Hmem: memory_inv st1)
    (Hver: verifier_inv st1)
    (Hsem: step st1 = Some (t, st2)),
       register_inv st2 /\ memory_inv st2 /\ verifier_inv st2.
Proof.
  unfold step.
  unfold_monad.
  intros.
  match goal with
  | H: match (if ?X then _ else _) with | _ => _ end = Some _ |- _ =>
    destruct X; [| inversion H]
  end.
  destruct (Decode.decode _) in Hsem; [| inversion Hsem].
  destruct i in Hsem.
  - (* BPF_NEG *)
    apply reg_inv_eval_reg with (r:= r) in Hreg as Heval_reg.
    destruct Heval_reg as (vl & Heval_reg).
    destruct a; rewrite Heval_reg in Hsem; simpl in Hsem.
    + inversion Hsem.
      split.
      eapply reg_inv_upd_reg; eauto.
      split.
      eapply mem_inv_upd_reg; eauto.
      unfold verifier_inv in *.
      simpl; assumption.
    + inversion Hsem.
      split.
      eapply reg_inv_upd_reg; eauto.
      split.
      eapply mem_inv_upd_reg; eauto.
      unfold verifier_inv in *.
      simpl; assumption.
  - (* BPF_BINARY *)
    eapply step_preserving_inv_alu; eauto.
  - (* BPF_JA *)
    match goal with
    | H : (if ?X then _ else _) = _ |- _ =>
      destruct X; inversion H
    end.
    split; [eapply reg_inv_upd_pc; eauto |
      split; [eapply mem_inv_upd_pc; eauto | unfold verifier_inv in *; simpl; assumption]].
  - (* BPF_JUMP *)
    eapply step_preserving_inv_branch; eauto.
  - (* BPF_LDDW *)
    destruct Int.ltu; simpl in Hsem.
    match goal with
    | H: match (if ?X then _ else _) with | _ => _ end = _ |- _ =>
      destruct X; [| inversion H]
    end.
    change Int64.iwordsize' with (Int.repr 64) in Hsem.
    unfold Int.ltu in Hsem.
    change (Int.unsigned (Int.repr 32)) with 32 in Hsem.
    change (Int.unsigned (Int.repr 64)) with 64 in Hsem.
    simpl in Hsem.
    match goal with
    | H: match (if ?X then _ else _) with | _ => _ end = _ |- _ =>
      destruct X; [| inversion H]
    end.

    inversion Hsem; clear Hsem.
    + split.
      apply reg_inv_upd_pc_incr with (st1:= (State.upd_reg r
          (Vlong
             (Int64.or (Int64.repr (Int.signed i))
                (Int64.shl'
                   (Int64.repr
                      (Int.signed
                         (Regs.get_immediate
                            (State.eval_ins
                               (Int.add (State.eval_pc st1) Int.one) st1))))
                   (Int.repr 32)))) st1)); auto.
      eapply reg_inv_upd_reg; eauto.
      split.
      apply mem_inv_upd_pc_incr with (st1:= (State.upd_reg r
          (Vlong
             (Int64.or (Int64.repr (Int.signed i))
                (Int64.shl'
                   (Int64.repr
                      (Int.signed
                         (Regs.get_immediate
                            (State.eval_ins
                               (Int.add (State.eval_pc st1) Int.one) st1))))
                   (Int.repr 32)))) st1)); auto.
      unfold verifier_inv in *; simpl; assumption.
    + inversion Hsem; split; [eapply reg_inv_upd_flag; eauto |
        split; [eapply mem_inv_upd_flag; eauto | unfold verifier_inv in *; simpl; assumption]].
  - (* BPF_LDX *)
    eapply step_preserving_inv_ld; eauto.
  - (* BPF_ST *)
    eapply step_preserving_inv_st; eauto.
  - (* BPF_CALL *)
    assert (Hget_call: forall i, exists ptr,
      _bpf_get_call (Vint i) st1 = Some (ptr, st1) /\
      (ptr = Vnullptr \/ (exists b ofs, ptr = Vptr b ofs /\ ((Mem.valid_pointer (bpf_m st1) b (Ptrofs.unsigned ofs)
        || Mem.valid_pointer (bpf_m st1) b (Ptrofs.unsigned ofs - 1)) = true)%bool))). {
      intro.
      apply lemma_bpf_get_call.
    }
    specialize (Hget_call (Int.repr (Int64.unsigned (Int64.repr (Int.signed i))))).
    destruct Hget_call as (ptr & Hget_call & Hres).
    rewrite Hget_call in Hsem.
    destruct Hres as [Hnull | (b & ofs & Hptr & Hvalid)]; unfold cmp_ptr32_nullM, rBPFValues.cmp_ptr32_null in Hsem; subst.
    + simpl in Hsem.
      rewrite Int.eq_true in Hsem.
      inversion Hsem; split; [eapply reg_inv_upd_flag; eauto |
        split; [eapply mem_inv_upd_flag; eauto | unfold verifier_inv in *; simpl; assumption]].
    + destruct Val.cmpu_bool eqn:cmp; [| inversion Hsem].
      destruct b0.
      * inversion Hsem; split; [eapply reg_inv_upd_flag; eauto |
          split; [eapply mem_inv_upd_flag; eauto | unfold verifier_inv in *; simpl; assumption]].
      * assert (Hexec: forall b ofs st1,
      exists v st2, exec_function (Vptr b ofs) st1 = Some (Vint v, st2) /\ rBPFValues.cmp_ptr32_null (State.eval_mem st1) (Vptr b ofs) = Some false). {
          apply lemma_exec_function0.
        }
        specialize (Hexec b ofs st1).
        destruct Hexec as (res & st & Hexec & _).
        rewrite Hexec in Hsem.
        apply call_inv in Hexec; auto.
        destruct res; inversion Hsem.
        destruct Hexec as (Hreg_st & Hmem_st & Hver_st).
        split; [eapply reg_inv_upd_reg; eauto |
          split; [eapply mem_inv_upd_reg; eauto | unfold verifier_inv in *; simpl; assumption]].
  - (* BPF_RET *)
    inversion Hsem.
    split; [eapply reg_inv_upd_flag; eauto |
      split; [eapply mem_inv_upd_flag; eauto | unfold verifier_inv in *; simpl; assumption]].
  - (* BPF_ERR *)
    inversion Hsem.
    split; [eapply reg_inv_upd_flag; eauto |
      split; [ eapply mem_inv_upd_flag; eauto | unfold verifier_inv in *; simpl; assumption]].
Qed.

Theorem inv_avoid_step_undef:
  forall st
    (Hpc: Int.cmpu Clt (State.eval_pc st) (Int.repr (Z.of_nat (ins_len st)))%bool = true)
    (Hreg: register_inv st)
    (Hmem: memory_inv st)
    (Hver: verifier_inv st),
      step st <> None.
Proof.
  intros.
  unfold step.
  unfold_monad.
  (**r if-false is impossible because of the interpreter *)
  rewrite Hpc.
  unfold verifier_inv, verifier_inv' in Hver.
  destruct Hver as (Hlen & Hwell_list_range & Hwell_ins).
  unfold well_list_range in Hwell_list_range.

  unfold State.eval_pc in Hpc.
  unfold State.eval_pc.
  unfold State.eval_ins, List64.MyListIndexs32, List64.MyList.index_s32.

  remember (Z.to_nat (Int.unsigned (pc_loc st))) as pc.
  rewrite Hlen in *.

  assert (Hpc_range: (pc < List.length (ins st))%nat). {
    rewrite Heqpc.
    clear - Hpc Hwell_list_range.
    unfold Int.cmpu in Hpc.
    apply Clt_Zlt_iff in Hpc.
    rewrite Int.unsigned_repr in Hpc.
    assert (Hpc_z: (Z.to_nat (Int.unsigned (pc_loc st)) < Z.to_nat (Z.of_nat (length (ins st))))%nat). {
      apply Z2Nat.inj_lt; auto.
      apply Int_unsigned_ge_0.
      lia.
    }
    rewrite Nat2Z.id in Hpc_z.
    assumption.
    change Int.max_unsigned with Ptrofs.max_unsigned.
    lia.
  }

  specialize (Hwell_ins pc Hpc_range).

  apply List.nth_error_nth' with (d:=Int64.zero) in Hpc_range.
  rewrite Hpc_range in *.

  unfold Decode.decode.

  unfold well_jump in Hwell_ins.
  destruct Hwell_ins as (Hdst & Hsrc & Hlddw & Hjmp).

  apply verifier_inv_dst_reg in Hdst.
  apply verifier_inv_src_reg in Hsrc.
  destruct Hdst as (dst & Hdst).
  destruct Hsrc as (src & Hsrc).
  rewrite Hdst, Hsrc.

  remember (Nat.land (Regs.get_opcode (List.nth pc (ins st) Int64.zero)) 7) as Hand.

  clear HeqHand.
  destruct Hand.
  { (**LD_IMM *)
    unfold Decode.get_instruction_ld.
    unfold well_lddw, is_lddw in Hlddw.
    rewrite opcode_and_255.

    remember (Regs.get_opcode (List.nth pc (ins st) Int64.zero)) as Hand24.
    do 24 (destruct Hand24; [intro Hfalse; inversion Hfalse |]).
    destruct Hand24.
    - destruct Int.ltu.
      + 
        rewrite Heqpc in Hlddw.
        rewrite Z2Nat.id in Hlddw; [| apply Int_unsigned_ge_0].
        rewrite Int.repr_unsigned in Hlddw.
        rewrite <- Hlen in Hlddw.
        rewrite Hlddw.
        simpl.
        change (Int64.iwordsize') with (Int.repr 64).
        change (Int.ltu (Int.repr 32) (Int.repr 64)) with true.
        simpl.
        unfold Int.cmpu in Hlddw.
        rewrite Hlddw.
        simpl.
        intro Hfalse; inversion Hfalse.
      + intro Hfalse; inversion Hfalse.
    - intro Hfalse; inversion Hfalse.
  }

  destruct Hand.
  { (**r LD_REG *)
    unfold Decode.get_instruction_ldx.
    rewrite opcode_and_255.

    remember (Regs.get_opcode (List.nth pc (ins st) Int64.zero)) as Hand.
    unfold step_load_x_operation.
    unfold eval_mem, eval_mem_regions, eval_reg, get_addr_ofs.
    unfold bindM, returnM.
    unfold rBPFValues.val_intuoflongu, rBPFValues.sint32_to_vint.
    unfold Val.longofint.
    eapply reg_inv_eval_reg in Hreg.
    destruct Hreg as (i & Hreg).
    do 97 (destruct Hand; [intro Hfalse; inversion Hfalse |]).
    destruct Hand.
    {
      rewrite Hreg.
      simpl.
      eapply check_memM_P in Hmem as Hcheck_mem; [| constructor].
      rewrite Hcheck_mem.
      unfold cmp_ptr32_nullM, bindM, returnM.

      remember ((check_memP Readable Mint32
         (Vint
            (Int.repr
               (Int64.unsigned
                  (Int64.add i
                     (Int64.repr
                        (Int.signed (Regs.get_offset (List.nth pc (ins st) Int64.zero))))))))
         st)) as res.
      symmetry in Heqres.
      unfold State.eval_mem.
      eapply mem_inv_check_mem_valid_pointer in Heqres; eauto.
      - destruct Heqres as [(b & ofs & Hptr & Hvalid)| Hptr]; subst.
        + simpl.
          rewrite Hvalid.
          rewrite Int.eq_true.
          simpl.
          eapply check_mem_load in Hcheck_mem; eauto.
          unfold load_mem, State.load_mem.
          destruct Hcheck_mem as (res & Hcheck_mem & His_long).
          rewrite Hcheck_mem.
          unfold is_vlong_or_vint in His_long.
          unfold _to_vlong.
          destruct res; inversion His_long.
          unfold upd_reg.
          intro Hfalse; inversion Hfalse.

          unfold upd_reg.
          intro Hfalse; inversion Hfalse.
          simpl. constructor.
          intro Hfalse; inversion Hfalse.
        + unfold rBPFValues.cmp_ptr32_null.
          unfold Val.cmpu_bool.
          change Vnullptr with (Vint Int.zero); simpl.
          rewrite Int.eq_true.
          intro Hfalse; inversion Hfalse.
      - constructor.
    }
    do 7 (destruct Hand; [intro Hfalse; inversion Hfalse |]).
    destruct Hand.
    {
      rewrite Hreg.
      simpl.
      eapply check_memM_P in Hmem as Hcheck_mem; [| constructor].
      rewrite Hcheck_mem.
      unfold cmp_ptr32_nullM, bindM, returnM.

      remember ((check_memP Readable Mint16unsigned
         (Vint
            (Int.repr
               (Int64.unsigned
                  (Int64.add i
                     (Int64.repr
                        (Int.signed (Regs.get_offset (List.nth pc (ins st) Int64.zero))))))))
         st)) as res.
      symmetry in Heqres.
      unfold State.eval_mem.
      eapply mem_inv_check_mem_valid_pointer in Heqres; eauto.
      - destruct Heqres as [(b & ofs & Hptr & Hvalid)| Hptr]; subst.
        + simpl.
          rewrite Hvalid.
          rewrite Int.eq_true.
          simpl.
          eapply check_mem_load in Hcheck_mem; eauto.
          unfold load_mem, State.load_mem.
          destruct Hcheck_mem as (res & Hcheck_mem & His_long).
          rewrite Hcheck_mem.
          unfold is_vlong_or_vint in His_long.
          unfold _to_vlong.
          destruct res; inversion His_long.
          unfold upd_reg.
          intro Hfalse; inversion Hfalse.

          unfold upd_reg.
          intro Hfalse; inversion Hfalse.
          simpl. constructor.
          intro Hfalse; inversion Hfalse.
        + unfold rBPFValues.cmp_ptr32_null.
          unfold Val.cmpu_bool.
          change Vnullptr with (Vint Int.zero); simpl.
          rewrite Int.eq_true.
          intro Hfalse; inversion Hfalse.
      - constructor.
    }
    do 7 (destruct Hand; [intro Hfalse; inversion Hfalse |]).
    destruct Hand.
    {
      rewrite Hreg.
      simpl.
      eapply check_memM_P in Hmem as Hcheck_mem; [| constructor].
      rewrite Hcheck_mem.
      unfold cmp_ptr32_nullM, bindM, returnM.

      remember ((check_memP Readable Mint8unsigned
         (Vint
            (Int.repr
               (Int64.unsigned
                  (Int64.add i
                     (Int64.repr
                        (Int.signed (Regs.get_offset (List.nth pc (ins st) Int64.zero))))))))
         st)) as res.
      symmetry in Heqres.
      unfold State.eval_mem.
      eapply mem_inv_check_mem_valid_pointer in Heqres; eauto.
      - destruct Heqres as [(b & ofs & Hptr & Hvalid)| Hptr]; subst.
        + simpl.
          rewrite Hvalid.
          rewrite Int.eq_true.
          simpl.
          eapply check_mem_load in Hcheck_mem; eauto.
          unfold load_mem, State.load_mem.
          destruct Hcheck_mem as (res & Hcheck_mem & His_long).
          rewrite Hcheck_mem.
          unfold is_vlong_or_vint in His_long.
          unfold _to_vlong.
          destruct res; inversion His_long.
          unfold upd_reg.
          intro Hfalse; inversion Hfalse.

          unfold upd_reg.
          intro Hfalse; inversion Hfalse.
          simpl. constructor.
          intro Hfalse; inversion Hfalse.
        + unfold rBPFValues.cmp_ptr32_null.
          unfold Val.cmpu_bool.
          change Vnullptr with (Vint Int.zero); simpl.
          rewrite Int.eq_true.
          intro Hfalse; inversion Hfalse.
      - constructor.
    }
    do 7 (destruct Hand; [intro Hfalse; inversion Hfalse |]).
    destruct Hand.
    {
      rewrite Hreg.
      simpl.
      eapply check_memM_P in Hmem as Hcheck_mem; [| constructor].
      rewrite Hcheck_mem.
      unfold cmp_ptr32_nullM, bindM, returnM.

      remember ((check_memP Readable Mint64
         (Vint
            (Int.repr
               (Int64.unsigned
                  (Int64.add i
                     (Int64.repr
                        (Int.signed (Regs.get_offset (List.nth pc (ins st) Int64.zero))))))))
         st)) as res.
      symmetry in Heqres.
      unfold State.eval_mem.
      eapply mem_inv_check_mem_valid_pointer in Heqres; eauto.
      - destruct Heqres as [(b & ofs & Hptr & Hvalid)| Hptr]; subst.
        + simpl.
          rewrite Hvalid.
          rewrite Int.eq_true.
          simpl.
          eapply check_mem_load in Hcheck_mem; eauto.
          unfold load_mem, State.load_mem.
          destruct Hcheck_mem as (res & Hcheck_mem & His_long).
          rewrite Hcheck_mem.
          unfold Mem.loadv in Hcheck_mem.
          apply Mem.load_type in Hcheck_mem.
          unfold Val.has_type in Hcheck_mem; simpl in Hcheck_mem.
          destruct res; inversion His_long; inversion Hcheck_mem.
          unfold upd_reg.
          intro Hfalse; inversion Hfalse.

          simpl. constructor.
          intro Hfalse; inversion Hfalse.
        + unfold rBPFValues.cmp_ptr32_null.
          unfold Val.cmpu_bool.
          change Vnullptr with (Vint Int.zero); simpl.
          rewrite Int.eq_true.
          intro Hfalse; inversion Hfalse.
      - constructor.
    }
    intro Hfalse; inversion Hfalse.
  }

  destruct Hand.
  { (**r ST_IMM *)
    unfold Decode.get_instruction_st, bindM, returnM.
    rewrite opcode_and_255.

    unfold step_store_operation.
    unfold eval_mem, eval_mem_regions, eval_reg, get_addr_ofs.
    unfold bindM, returnM.
    unfold rBPFValues.val_intuoflongu, Val.longofint, rBPFValues.sint32_to_vint.

    eapply reg_inv_eval_reg in Hreg.
    destruct Hreg as (i & Hreg).

    remember (Regs.get_opcode (List.nth pc (ins st) Int64.zero)) as Hand.
    do 98 (destruct Hand; [intro Hfalse; inversion Hfalse |]).
    destruct Hand.
    {
      rewrite Hreg.
      simpl.
      eapply check_memM_P with (perm := Writable) in Hmem as Hcheck_mem; [|constructor].
      rewrite Hcheck_mem.
      unfold cmp_ptr32_nullM, bindM, returnM.

      remember (check_memP Writable Mint32
         (Vint
            (Int.repr
               (Int64.unsigned
                  (Int64.add i
                     (Int64.repr
                        (Int.signed (Regs.get_offset (List.nth pc (ins st) Int64.zero))))))))
         st) as res.
      symmetry in Heqres.
      unfold State.eval_mem.
      eapply mem_inv_check_mem_valid_pointer in Heqres; eauto.
      - destruct Heqres as [(b & ofs & Hptr & Hvalid)| Hptr]; subst.
        + simpl.
          rewrite Hvalid.
          rewrite Int.eq_true.
          simpl.
          remember (Regs.get_immediate
                 (List.nth (Z.to_nat (Int.unsigned (pc_loc st))) (ins st) Int64.zero)) as imm.
          eapply check_mem_store with (v:= Vint imm) in Hcheck_mem; eauto.
          unfold store_mem_imm, State.store_mem_imm.
          destruct Hcheck_mem as (res & Hcheck_mem & Hmem').
          unfold vlong_or_vint_to_vint_or_vlong in Hcheck_mem.
          rewrite Hcheck_mem.
          intro Hfalse; inversion Hfalse.

          simpl. constructor.
          unfold is_vlong_or_vint; constructor.
          intro Hfalse; inversion Hfalse.
        + unfold rBPFValues.cmp_ptr32_null.
          unfold Val.cmpu_bool.
          change Vnullptr with (Vint Int.zero); simpl.
          rewrite Int.eq_true.
          intro Hfalse; inversion Hfalse.
      - constructor.
    }
    do 7 (destruct Hand; [intro Hfalse; inversion Hfalse |]).
    destruct Hand.
    {
      rewrite Hreg.
      simpl.
      eapply check_memM_P with (perm := Writable) in Hmem as Hcheck_mem; [|constructor].
      rewrite Hcheck_mem.
      unfold cmp_ptr32_nullM, bindM, returnM.

      remember (check_memP Writable Mint16unsigned
         (Vint
            (Int.repr
               (Int64.unsigned
                  (Int64.add i
                     (Int64.repr
                        (Int.signed (Regs.get_offset (List.nth pc (ins st) Int64.zero))))))))
         st) as res.
      symmetry in Heqres.
      unfold State.eval_mem.
      eapply mem_inv_check_mem_valid_pointer in Heqres; eauto.
      - destruct Heqres as [(b & ofs & Hptr & Hvalid)| Hptr]; subst.
        + simpl.
          rewrite Hvalid.
          rewrite Int.eq_true.
          simpl.
          remember (Regs.get_immediate
                 (List.nth (Z.to_nat (Int.unsigned (pc_loc st))) (ins st) Int64.zero)) as imm.
          eapply check_mem_store with (v:= Vint imm) in Hcheck_mem; eauto.
          unfold store_mem_imm, State.store_mem_imm.
          destruct Hcheck_mem as (res & Hcheck_mem & Hmem').
          unfold vlong_or_vint_to_vint_or_vlong in Hcheck_mem.
          rewrite Hcheck_mem.
          intro Hfalse; inversion Hfalse.

          simpl. constructor.
          unfold is_vlong_or_vint; constructor.
          intro Hfalse; inversion Hfalse.
        + unfold rBPFValues.cmp_ptr32_null.
          unfold Val.cmpu_bool.
          change Vnullptr with (Vint Int.zero); simpl.
          rewrite Int.eq_true.
          intro Hfalse; inversion Hfalse.
      - constructor.
    }
    do 7 (destruct Hand; [intro Hfalse; inversion Hfalse |]).
    destruct Hand.
    {
      rewrite Hreg.
      simpl.
      eapply check_memM_P with (perm := Writable) in Hmem as Hcheck_mem; [|constructor].
      rewrite Hcheck_mem.
      unfold cmp_ptr32_nullM, bindM, returnM.

      remember (check_memP Writable Mint8unsigned
         (Vint
            (Int.repr
               (Int64.unsigned
                  (Int64.add i
                     (Int64.repr
                        (Int.signed (Regs.get_offset (List.nth pc (ins st) Int64.zero))))))))
         st) as res.
      symmetry in Heqres.
      unfold State.eval_mem.
      eapply mem_inv_check_mem_valid_pointer in Heqres; eauto.
      - destruct Heqres as [(b & ofs & Hptr & Hvalid)| Hptr]; subst.
        + simpl.
          rewrite Hvalid.
          rewrite Int.eq_true.
          simpl.
          remember (Regs.get_immediate
                 (List.nth (Z.to_nat (Int.unsigned (pc_loc st))) (ins st) Int64.zero)) as imm.
          eapply check_mem_store with (v:= Vint imm) in Hcheck_mem; eauto.
          unfold store_mem_imm, State.store_mem_imm.
          destruct Hcheck_mem as (res & Hcheck_mem & Hmem').
          unfold vlong_or_vint_to_vint_or_vlong in Hcheck_mem.
          rewrite Hcheck_mem.
          intro Hfalse; inversion Hfalse.

          simpl. constructor.
          unfold is_vlong_or_vint; constructor.
          intro Hfalse; inversion Hfalse.
        + unfold rBPFValues.cmp_ptr32_null.
          unfold Val.cmpu_bool.
          change Vnullptr with (Vint Int.zero); simpl.
          rewrite Int.eq_true.
          intro Hfalse; inversion Hfalse.
      - constructor.
    }
    do 7 (destruct Hand; [intro Hfalse; inversion Hfalse |]).
    destruct Hand.
    {
      rewrite Hreg.
      simpl.
      eapply check_memM_P with (perm := Writable) in Hmem as Hcheck_mem; [|constructor].
      rewrite Hcheck_mem.
      unfold cmp_ptr32_nullM, bindM, returnM.

      remember (check_memP Writable Mint64
         (Vint
            (Int.repr
               (Int64.unsigned
                  (Int64.add i
                     (Int64.repr
                        (Int.signed (Regs.get_offset (List.nth pc (ins st) Int64.zero))))))))
         st) as res.
      symmetry in Heqres.
      unfold State.eval_mem.
      eapply mem_inv_check_mem_valid_pointer in Heqres; eauto.
      - destruct Heqres as [(b & ofs & Hptr & Hvalid)| Hptr]; subst.
        + simpl.
          rewrite Hvalid.
          rewrite Int.eq_true.
          simpl.
          remember (Regs.get_immediate
                 (List.nth (Z.to_nat (Int.unsigned (pc_loc st))) (ins st) Int64.zero)) as imm.
          eapply check_mem_store with (v:= Vint imm) in Hcheck_mem; eauto.
          unfold store_mem_imm, State.store_mem_imm.
          destruct Hcheck_mem as (res & Hcheck_mem & Hmem').
          unfold vlong_or_vint_to_vint_or_vlong in Hcheck_mem.
          rewrite Hcheck_mem.
          intro Hfalse; inversion Hfalse.

          simpl. constructor.
          unfold is_vlong_or_vint; constructor.
          intro Hfalse; inversion Hfalse.
        + unfold rBPFValues.cmp_ptr32_null.
          unfold Val.cmpu_bool.
          change Vnullptr with (Vint Int.zero); simpl.
          rewrite Int.eq_true.
          intro Hfalse; inversion Hfalse.
      - constructor.
    }
    intro Hfalse; inversion Hfalse.
  }

  destruct Hand.
  { (**r ST_REG *)
    unfold Decode.get_instruction_stx, bindM, returnM.
    rewrite opcode_and_255.

    unfold step_store_operation.
    unfold eval_mem, eval_mem_regions, eval_reg, get_addr_ofs.
    unfold bindM, returnM.
    unfold rBPFValues.val_intuoflongu, Val.longofint, rBPFValues.sint32_to_vint.

    eapply reg_inv_eval_reg with (r:= dst) in Hreg as Hreg_dst.
    eapply reg_inv_eval_reg with (r:= src) in Hreg as Hreg_src.
    destruct Hreg_dst as (r_dst & Hreg_dst).
    destruct Hreg_src as (r_src & Hreg_src).

    remember (Regs.get_opcode (List.nth pc (ins st) Int64.zero)) as Hand.
    do 99 (destruct Hand; [intro Hfalse; inversion Hfalse |]).
    destruct Hand.
    {
      rewrite Hreg_dst.
      simpl.
      eapply check_memM_P with (perm := Writable) in Hmem as Hcheck_mem; [|constructor].
      rewrite Hcheck_mem.
      unfold cmp_ptr32_nullM, bindM, returnM.

      remember (check_memP Writable Mint32
         (Vint
            (Int.repr
               (Int64.unsigned
                  (Int64.add r_dst
                     (Int64.repr
                        (Int.signed (Regs.get_offset (List.nth pc (ins st) Int64.zero))))))))
         st) as res.
      symmetry in Heqres.
      unfold State.eval_mem.
      unfold store_mem_reg, State.store_mem_reg.
      eapply mem_inv_check_mem_valid_pointer in Heqres; eauto.
      - destruct Heqres as [(b & ofs & Hptr & Hvalid)| Hptr]; subst.
        + simpl.
          rewrite Hvalid.
          rewrite Int.eq_true.
          simpl.
          rewrite Hreg_src.
          eapply check_mem_store with (v:= Vlong r_src) in Hcheck_mem; eauto.
          destruct Hcheck_mem as (res & Hcheck_mem & Hmem').
          unfold Mem.storev, vlong_or_vint_to_vint_or_vlong in Hcheck_mem.
          rewrite Hcheck_mem.
          intro Hfalse; inversion Hfalse.

          simpl. constructor.
          unfold is_vlong_or_vint; constructor.
          intro Hfalse; inversion Hfalse.
        + unfold rBPFValues.cmp_ptr32_null.
          unfold Val.cmpu_bool.
          change Vnullptr with (Vint Int.zero); simpl.
          rewrite Int.eq_true.
          intro Hfalse; inversion Hfalse.
      - constructor.
    }
    do 7 (destruct Hand; [intro Hfalse; inversion Hfalse |]).
    destruct Hand.
    {
      rewrite Hreg_dst.
      simpl.
      eapply check_memM_P with (perm := Writable) in Hmem as Hcheck_mem; [|constructor].
      rewrite Hcheck_mem.
      unfold cmp_ptr32_nullM, bindM, returnM.

      remember (check_memP Writable Mint16unsigned
         (Vint
            (Int.repr
               (Int64.unsigned
                  (Int64.add r_dst
                     (Int64.repr
                        (Int.signed (Regs.get_offset (List.nth pc (ins st) Int64.zero))))))))
         st) as res.
      symmetry in Heqres.
      unfold State.eval_mem.
      unfold store_mem_reg, State.store_mem_reg.
      eapply mem_inv_check_mem_valid_pointer in Heqres; eauto.
      - destruct Heqres as [(b & ofs & Hptr & Hvalid)| Hptr]; subst.
        + simpl.
          rewrite Hvalid.
          rewrite Int.eq_true.
          simpl.
          rewrite Hreg_src.
          eapply check_mem_store with (v:= Vlong r_src) in Hcheck_mem; eauto.
          destruct Hcheck_mem as (res & Hcheck_mem & Hmem').
          unfold Mem.storev, vlong_or_vint_to_vint_or_vlong in Hcheck_mem.
          rewrite Hcheck_mem.
          intro Hfalse; inversion Hfalse.

          simpl. constructor.
          unfold is_vlong_or_vint; constructor.
          intro Hfalse; inversion Hfalse.
        + unfold rBPFValues.cmp_ptr32_null.
          unfold Val.cmpu_bool.
          change Vnullptr with (Vint Int.zero); simpl.
          rewrite Int.eq_true.
          intro Hfalse; inversion Hfalse.
      - constructor.
    }
    do 7 (destruct Hand; [intro Hfalse; inversion Hfalse |]).
    destruct Hand.
    {
      rewrite Hreg_dst.
      simpl.
      eapply check_memM_P with (perm := Writable) in Hmem as Hcheck_mem; [|constructor].
      rewrite Hcheck_mem.
      unfold cmp_ptr32_nullM, bindM, returnM.

      remember (check_memP Writable Mint8unsigned
         (Vint
            (Int.repr
               (Int64.unsigned
                  (Int64.add r_dst
                     (Int64.repr
                        (Int.signed (Regs.get_offset (List.nth pc (ins st) Int64.zero))))))))
         st) as res.
      symmetry in Heqres.
      unfold State.eval_mem.
      unfold store_mem_reg, State.store_mem_reg.
      eapply mem_inv_check_mem_valid_pointer in Heqres; eauto.
      - destruct Heqres as [(b & ofs & Hptr & Hvalid)| Hptr]; subst.
        + simpl.
          rewrite Hvalid.
          rewrite Int.eq_true.
          simpl.
          rewrite Hreg_src.
          eapply check_mem_store with (v:= Vlong r_src) in Hcheck_mem; eauto.
          destruct Hcheck_mem as (res & Hcheck_mem & Hmem').
          unfold Mem.storev, vlong_or_vint_to_vint_or_vlong in Hcheck_mem.
          rewrite Hcheck_mem.
          intro Hfalse; inversion Hfalse.

          simpl. constructor.
          unfold is_vlong_or_vint; constructor.
          intro Hfalse; inversion Hfalse.
        + unfold rBPFValues.cmp_ptr32_null.
          unfold Val.cmpu_bool.
          change Vnullptr with (Vint Int.zero); simpl.
          rewrite Int.eq_true.
          intro Hfalse; inversion Hfalse.
      - constructor.
    }
    do 7 (destruct Hand; [intro Hfalse; inversion Hfalse |]).
    destruct Hand.
    {
      rewrite Hreg_dst.
      simpl.
      eapply check_memM_P with (perm := Writable) in Hmem as Hcheck_mem; [|constructor].
      rewrite Hcheck_mem.
      unfold cmp_ptr32_nullM, bindM, returnM.

      remember (check_memP Writable Mint64
         (Vint
            (Int.repr
               (Int64.unsigned
                  (Int64.add r_dst
                     (Int64.repr
                        (Int.signed (Regs.get_offset (List.nth pc (ins st) Int64.zero))))))))
         st) as res.
      symmetry in Heqres.
      unfold State.eval_mem.
      unfold store_mem_reg, State.store_mem_reg.
      eapply mem_inv_check_mem_valid_pointer in Heqres; eauto.
      - destruct Heqres as [(b & ofs & Hptr & Hvalid)| Hptr]; subst.
        + simpl.
          rewrite Hvalid.
          rewrite Int.eq_true.
          simpl.
          rewrite Hreg_src.
          eapply check_mem_store with (v:= Vlong r_src) in Hcheck_mem; eauto.
          destruct Hcheck_mem as (res & Hcheck_mem & Hmem').
          unfold Mem.storev, vlong_or_vint_to_vint_or_vlong in Hcheck_mem.
          rewrite Hcheck_mem.
          intro Hfalse; inversion Hfalse.

          simpl. constructor.
          unfold is_vlong_or_vint; constructor.
          intro Hfalse; inversion Hfalse.
        + unfold rBPFValues.cmp_ptr32_null.
          unfold Val.cmpu_bool.
          change Vnullptr with (Vint Int.zero); simpl.
          rewrite Int.eq_true.
          intro Hfalse; inversion Hfalse.
      - constructor.
    }
    intro Hfalse; inversion Hfalse.
  }

  destruct Hand.
  { (**r ALU32 *)
    remember (Regs.get_opcode (List.nth pc (ins st) Int64.zero)) as Hand.
    match goal with
    | |- context[if ?X then _ else _] =>
      destruct X
    end.
    - (**r ALU32_IMM *)
      remember (Regs.get_immediate (List.nth pc (ins st) Int64.zero)) as imm.
      unfold Decode.get_instruction_alu32_imm.

      unfold step_alu_binary_operation, eval_reg32, eval_src32, bindM, returnM.
      unfold eval_reg.
      unfold rBPFValues.sint32_to_vint, rBPFValues.val_intuoflongu, Val.longofintu.

      eapply reg_inv_eval_reg in Hreg.
      destruct Hreg as (i & Hreg).
      do 52 (destruct Hand; [try (rewrite Hreg; simpl); intro Hfalse; inversion Hfalse |]).
      destruct Hand.
        rewrite Hreg; simpl;
        destruct Int.eq; simpl; intro Hfalse; inversion Hfalse.
      do 47 (destruct Hand; [try (rewrite Hreg; simpl); intro Hfalse; inversion Hfalse |]).
      destruct Hand.
        rewrite Hreg; simpl.
        change Int.iwordsize with (Int.repr 32).
        destruct Int.ltu; simpl; intro Hfalse; inversion Hfalse.
      do 15 (destruct Hand; [try (rewrite Hreg; simpl); intro Hfalse; inversion Hfalse |]).
      destruct Hand.
        rewrite Hreg; simpl.
        change Int.iwordsize with (Int.repr 32).
        destruct Int.ltu; simpl; intro Hfalse; inversion Hfalse.
      do 31 (destruct Hand; [try (rewrite Hreg; simpl); intro Hfalse; inversion Hfalse |]).
      destruct Hand.
        rewrite Hreg; simpl.
        destruct Int.eq; simpl; intro Hfalse; inversion Hfalse.
      do 47 (destruct Hand; [try (rewrite Hreg; simpl); intro Hfalse; inversion Hfalse |]).
      destruct Hand.
        rewrite Hreg; simpl.
        change Int.iwordsize with (Int.repr 32).
        destruct Int.ltu; simpl; intro Hfalse; inversion Hfalse.
      intro Hfalse; inversion Hfalse.
    - (**r ALU32_REG *)
      unfold Decode.get_instruction_alu32_reg.
      unfold step_alu_binary_operation, eval_reg32, eval_src32, eval_reg32, rBPFValues.val_intuoflongu, Val.longofintu, eval_reg, bindM, returnM.

      eapply reg_inv_eval_reg with (r:= dst) in Hreg as Hreg_dst.
      eapply reg_inv_eval_reg with (r:= src) in Hreg as Hreg_src.
      destruct Hreg_dst as (r_dst & Hreg_dst).
      destruct Hreg_src as (r_src & Hreg_src).

      do 60 (destruct Hand; [try (rewrite Hreg_dst, Hreg_src; simpl); intro Hfalse; inversion Hfalse |]).
      destruct Hand.
        rewrite Hreg_dst, Hreg_src; simpl;
        destruct Int.eq; intro Hfalse; inversion Hfalse.
      do 47 (destruct Hand; [try (rewrite Hreg_dst, Hreg_src; simpl); intro Hfalse; inversion Hfalse |]).
      destruct Hand.
        rewrite Hreg_dst, Hreg_src; simpl.
        change Int.iwordsize with (Int.repr 32).
        destruct Int.ltu; intro Hfalse; inversion Hfalse.
      do 15 (destruct Hand; [try (rewrite Hreg_dst, Hreg_src; simpl); intro Hfalse; inversion Hfalse |]).
      destruct Hand.
        rewrite Hreg_dst, Hreg_src; simpl.
        change Int.iwordsize with (Int.repr 32).
        destruct Int.ltu; intro Hfalse; inversion Hfalse.
      do 31 (destruct Hand; [try (rewrite Hreg_dst, Hreg_src; simpl); intro Hfalse; inversion Hfalse |]).
      destruct Hand.
        rewrite Hreg_dst, Hreg_src; simpl.
        destruct Int.eq; intro Hfalse; inversion Hfalse.
      do 31 (destruct Hand; [try (rewrite Hreg_dst, Hreg_src; simpl); intro Hfalse; inversion Hfalse |]).
      destruct Hand.
        rewrite Hreg_src; simpl.
        intro Hfalse; inversion Hfalse.
      do 15 (destruct Hand; [try (rewrite Hreg_dst, Hreg_src; simpl); intro Hfalse; inversion Hfalse |]).
      destruct Hand.
        rewrite Hreg_dst, Hreg_src; simpl.
        change Int.iwordsize with (Int.repr 32).
        destruct Int.ltu; intro Hfalse; inversion Hfalse.
      intro Hfalse; inversion Hfalse.
  }

  destruct Hand.
  { (**r Branch *)
    remember (Regs.get_opcode (List.nth pc (ins st) Int64.zero)) as Hand.
    match goal with
    | |- context[if ?X then _ else _] =>
      destruct X
    end.
    - (**r Branch_IMM *)
      remember (Regs.get_immediate (List.nth pc (ins st) Int64.zero)) as imm.
      unfold is_jump in Hjmp, HeqHand.
      unfold Decode.get_instruction_branch_imm.
      rewrite <- HeqHand in Hjmp.
      remember (Regs.get_offset (List.nth pc (ins st) Int64.zero)) as ofs.
      rewrite Heqpc in Hjmp.
      rewrite Z2Nat.id in Hjmp; [| apply Int_unsigned_ge_0].
      rewrite Int.repr_unsigned in Hjmp.
      rewrite <- Hlen in Hjmp.
      (*
      unfold step_alu_binary_operation, eval_reg32, eval_src32, bindM, returnM.
      unfold eval_reg.
      unfold rBPFValues.sint32_to_vint, rBPFValues.val_intuoflongu, Val.longofintu. *)
      unfold step_branch_cond, eval_reg, eval_src, Val.longofint, rBPFValues.sint32_to_vint, rBPFValues.compl_eq, bindM, returnM.

Ltac destruct_if_jmp Hjmp :=
  match goal with
  | |- (if ?X then _ else _) _ <> None =>
    destruct X; [rewrite Hjmp |]; intro Hfalse; inversion Hfalse
  | |- Some _ <> None =>
      intro Hfalse; inversion Hfalse
  end.
      eapply reg_inv_eval_reg in Hreg.
      destruct Hreg as (i & Hreg).
      do 21 (destruct Hand; [try (rewrite Hjmp); intro Hfalse; inversion Hfalse |]).
      unfold Int.cmpu in Hjmp.
      do 64 (destruct Hand; [try (rewrite Hreg; simpl); destruct_if_jmp Hjmp |]).
      do 48 (destruct Hand; [try (rewrite Hreg; simpl); destruct_if_jmp Hjmp |]).
      destruct Hand.
      assert (Heq: forall (i : int) (st1 : state),
  exists ptr : val,
    _bpf_get_call (Vint i) st1 = Some (ptr, st1) /\
    (ptr = Vnullptr \/ (exists (b : block) (ofs : ptrofs), ptr = Vptr b ofs /\ ((Mem.valid_pointer (bpf_m st1) b (Ptrofs.unsigned ofs)
        || Mem.valid_pointer (bpf_m st1) b (Ptrofs.unsigned ofs - 1)) = true)%bool))) by (apply lemma_bpf_get_call).
      specialize (Heq (Int.repr (Int64.unsigned (Int64.repr (Int.signed imm)))) st).
      destruct Heq as (ptr & Heq & Hptr).
      rewrite Heq.
      unfold cmp_ptr32_nullM, rBPFValues.cmp_ptr32_null.
      destruct Hptr as [Hptr| (b & ofs' & Hptr & Hvalid)]; subst.
      { simpl.
        rewrite Int.eq_true; simpl.
        intro Hfalse; inversion Hfalse.
      }
      { simpl.
        unfold State.eval_mem.
        rewrite Int.eq_true, Hvalid; simpl. clear Heq.
        assert (Heq: forall (b : block) (ofs : ptrofs) (st1 : state),
  exists (v : int) (st2 : state),
    exec_function (Vptr b ofs) st1 = Some (Vint v, st2) /\
    rBPFValues.cmp_ptr32_null (State.eval_mem st1) (Vptr b ofs) = Some false) by (apply lemma_exec_function0).
        specialize (Heq b ofs' st).
        destruct Heq as (v & st2 & Heq & _).
        rewrite Heq.
        simpl.
        intro Hfalse; inversion Hfalse.
      }

      do 48 (destruct Hand; [try (rewrite Hreg; simpl); destruct_if_jmp Hjmp |]).
      do 32 (destruct Hand; [try (rewrite Hreg; simpl); destruct_if_jmp Hjmp |]).
      intro Hfalse; inversion Hfalse.
    - (**r Branch_REG *)
      unfold Decode.get_instruction_branch_reg.
      unfold is_jump in Hjmp, HeqHand.
      rewrite <- HeqHand in Hjmp.
      remember (Regs.get_offset (List.nth pc (ins st) Int64.zero)) as ofs.
      rewrite Heqpc in Hjmp.
      rewrite Z2Nat.id in Hjmp; [| apply Int_unsigned_ge_0].
      rewrite Int.repr_unsigned in Hjmp.
      rewrite <- Hlen in Hjmp.

      unfold step_branch_cond, eval_src, eval_reg, Val.longofint, rBPFValues.sint32_to_vint, rBPFValues.compl_eq, bindM, returnM.

      eapply reg_inv_eval_reg with (r:= dst) in Hreg as Hreg_dst.
      eapply reg_inv_eval_reg with (r:= src) in Hreg as Hreg_src.
      destruct Hreg_dst as (r_dst & Hreg_dst).
      destruct Hreg_src as (r_src & Hreg_src).

      unfold Int.cmpu in Hjmp.
      do 30 (destruct Hand; [try (rewrite Hreg_dst, Hreg_src; simpl); destruct_if_jmp Hjmp |]).
      do 192 (destruct Hand; [try (rewrite Hreg_dst, Hreg_src; simpl); destruct_if_jmp Hjmp |]).
      intro Hfalse; inversion Hfalse.
  }


  destruct Hand.
  { (**r ILL_INS *)
    intro Hfalse; inversion Hfalse.
  }

  destruct Hand.
  { (**r ALU64 *)
    remember (Regs.get_opcode (List.nth pc (ins st) Int64.zero)) as Hand.
    match goal with
    | |- context[if ?X then _ else _] =>
      destruct X
    end.
    - (**r ALU64_IMM *)
      remember (Regs.get_immediate (List.nth pc (ins st) Int64.zero)) as imm.
      unfold Decode.get_instruction_alu64_imm.

      unfold step_alu_binary_operation, eval_src, eval_reg, upd_reg, bindM, Val.longofint, rBPFValues.sint32_to_vint, returnM.

      eapply reg_inv_eval_reg in Hreg.
      destruct Hreg as (i & Hreg).
      do 55 (destruct Hand; [try (rewrite Hreg; simpl); intro Hfalse; inversion Hfalse |]).
      destruct Hand.
        rewrite Hreg; simpl.
        destruct Int64.eq; intro Hfalse; inversion Hfalse.
      do 47 (destruct Hand; [try (rewrite Hreg; simpl); intro Hfalse; inversion Hfalse |]).
      destruct Hand.
        unfold rBPFValues.compu_lt_32, rBPFValues.val_intuoflongu.
        rewrite Hreg; simpl.
        destruct Int.ltu; intro Hfalse; inversion Hfalse.
      do 15 (destruct Hand; [try (rewrite Hreg; simpl); intro Hfalse; inversion Hfalse |]).
      destruct Hand.
        unfold rBPFValues.compu_lt_32, rBPFValues.val_intuoflongu.
        rewrite Hreg; simpl.
        destruct Int.ltu; intro Hfalse; inversion Hfalse.
      do 31 (destruct Hand; [try (rewrite Hreg; simpl); intro Hfalse; inversion Hfalse |]).
      destruct Hand.
        unfold rBPFValues.compl_ne.
        rewrite Hreg; simpl.
        destruct Int64.eq; intro Hfalse; inversion Hfalse.
      do 47 (destruct Hand; [try (rewrite Hreg; simpl); intro Hfalse; inversion Hfalse |]).
      destruct Hand.
        unfold rBPFValues.compu_lt_32, rBPFValues.val_intuoflongu.
        rewrite Hreg; simpl.
        destruct Int.ltu; intro Hfalse; inversion Hfalse.
      intro Hfalse; inversion Hfalse.
    - (**r ALU64_REG *)
      unfold Decode.get_instruction_alu64_reg.

      unfold step_alu_binary_operation, eval_src, eval_reg, upd_reg, rBPFValues.val_intuoflongu, Val.longofintu, eval_reg, bindM, returnM.

      eapply reg_inv_eval_reg with (r:= dst) in Hreg as Hreg_dst.
      eapply reg_inv_eval_reg with (r:= src) in Hreg as Hreg_src.
      destruct Hreg_dst as (r_dst & Hreg_dst).
      destruct Hreg_src as (r_src & Hreg_src).

      do 63 (destruct Hand; [try (rewrite Hreg_dst, Hreg_src; simpl); intro Hfalse; inversion Hfalse |]).
      destruct Hand.
        rewrite Hreg_dst, Hreg_src; simpl.
        destruct Int64.eq; intro Hfalse; inversion Hfalse.

      do 47 (destruct Hand; [try (rewrite Hreg_dst, Hreg_src; simpl); intro Hfalse; inversion Hfalse |]).
      destruct Hand.
        rewrite Hreg_dst, Hreg_src; simpl.
        destruct Int.ltu; intro Hfalse; inversion Hfalse.

      do 15 (destruct Hand; [try (rewrite Hreg_dst, Hreg_src; simpl); intro Hfalse; inversion Hfalse |]).
      destruct Hand.
        rewrite Hreg_dst, Hreg_src; simpl.
        destruct Int.ltu; intro Hfalse; inversion Hfalse.

      do 31 (destruct Hand; [try (rewrite Hreg_dst, Hreg_src; simpl); intro Hfalse; inversion Hfalse |]).
      destruct Hand.
        rewrite Hreg_dst, Hreg_src; simpl.
        destruct Int64.eq; intro Hfalse; inversion Hfalse.

      do 31 (destruct Hand; [try (rewrite Hreg_dst, Hreg_src; simpl); intro Hfalse; inversion Hfalse |]).
      destruct Hand.
        rewrite Hreg_src; simpl.
        intro Hfalse; inversion Hfalse.
      do 15 (destruct Hand; [try (rewrite Hreg_dst, Hreg_src; simpl); intro Hfalse; inversion Hfalse |]).
      destruct Hand.
        rewrite Hreg_dst, Hreg_src; simpl.
        destruct Int.ltu; intro Hfalse; inversion Hfalse.

      intro Hfalse; inversion Hfalse.
  }
  intro Hfalse; inversion Hfalse.
Qed.

Theorem bpf_interpreter_aux_preserving_inv:
  forall fuel st1 st2 t
    (Hreg: register_inv st1)
    (Hmem: memory_inv st1)
    (Hver: verifier_inv st1)
    (Hsem: bpf_interpreter_aux fuel st1 = Some (t, st2)),
       register_inv st2 /\ memory_inv st2 /\ verifier_inv st2.
Proof.
  induction fuel; intros.
  - simpl in Hsem.
    inversion Hsem; split; [eapply reg_inv_upd_flag; eauto |
        split; [eapply mem_inv_upd_flag; eauto | unfold verifier_inv in *; simpl; assumption]].
  - simpl in Hsem.
    unfold eval_ins_len, eval_pc, eval_flag, upd_pc_incr, bindM, returnM in Hsem.
    destruct Int.ltu.
    + destruct step eqn: Hstep; [| inversion Hsem].
      destruct p.
      destruct Flag.flag_eq.
      * destruct Int.ltu.
        {
          eapply step_preserving_inv in Hstep; eauto.
          destruct Hstep as (Hreg_s & Hmem_s & Hver_s).
          assert (Hinv: register_inv (State.upd_pc_incr s) /\ memory_inv (State.upd_pc_incr s) /\ verifier_inv (State.upd_pc_incr s)). {
            split; [eapply reg_inv_upd_pc_incr; eauto |
          split; [eapply mem_inv_upd_pc_incr; eauto | unfold verifier_inv in *; simpl; assumption]].
          }
          destruct Int.cmpu; [| inversion Hsem].
          destruct Hinv as (Hreg_s' & Hmem_s' & Hver_s').
          specialize (IHfuel (State.upd_pc_incr s) st2 t Hreg_s' Hmem_s' Hver_s' Hsem).
          congruence.
        }
        {
          eapply step_preserving_inv in Hstep; eauto.
          destruct Hstep as (Hreg_s & Hmem_s & Hver_s).
          assert (Hinv: register_inv (State.upd_pc_incr s) /\ memory_inv (State.upd_pc_incr s) /\ verifier_inv (State.upd_pc_incr s)). {
            split; [eapply reg_inv_upd_pc_incr; eauto |
          split; [eapply mem_inv_upd_pc_incr; eauto | unfold verifier_inv in *; simpl; assumption]].
          }
          inversion Hsem.
          clear - Hreg_s Hmem_s Hver_s.

          split; [eapply reg_inv_upd_flag; eauto |
          split; [eapply mem_inv_upd_flag; eauto | unfold verifier_inv in *; simpl; assumption]].
        }

      * inversion Hsem. subst.
        eapply step_preserving_inv in Hstep; eauto.
    + inversion Hsem; split; [eapply reg_inv_upd_flag; eauto |
        split; [eapply mem_inv_upd_flag; eauto | unfold verifier_inv in *; simpl; assumption]].
Qed.

Theorem bpf_interpreter_preserving_inv:
  forall fuel st1 st2 t
    (Hreg: register_inv st1)
    (Hmem: memory_inv st1)
    (Hver: verifier_inv st1)
    (Hsem: bpf_interpreter fuel st1 = Some (t, st2)),
       register_inv st2 /\ memory_inv st2 /\ verifier_inv st2.
Proof.
  intros.
  unfold bpf_interpreter in Hsem.
  unfold eval_mem_regions, get_mem_region, get_start_addr, upd_reg, eval_flag, eval_reg, bindM, returnM in Hsem.
  destruct (0 <? mrs_num st1)%nat; [| inversion Hsem].
  destruct List.nth_error; [| inversion Hsem].
  destruct Val.longofintu; inversion Hsem.
  destruct bpf_interpreter_aux eqn: Haux; [| inversion Hsem].
  destruct p.
  eapply bpf_interpreter_aux_preserving_inv in Haux; eauto.
  - destruct Flag.flag_eq.
    + inversion H0.
      subst.
      auto.
    + inversion H0.
      subst.
      auto.
  - destruct Flag.flag_eq.
    + eapply reg_inv_upd_reg; eauto.
    + eapply reg_inv_upd_reg; eauto.
Qed.

Theorem inv_avoid_bpf_interpreter_aux_undef:
  forall f st
    (Hreg: register_inv st)
    (Hmem: memory_inv st)
    (Hver: verifier_inv st),
      bpf_interpreter_aux f st <> None.
Proof.
  induction f.
  intros.
  - simpl.
    unfold upd_flag.
    intro Hfalse; inversion Hfalse.
  - simpl.
    intros.
    unfold eval_ins_len, eval_pc, eval_flag, upd_pc_incr, upd_flag, bindM, returnM.
    unfold State.eval_pc, State.eval_ins_len.

    destruct Int.ltu eqn: Hltu.
    + eapply inv_avoid_step_undef in Hreg as Hstep; eauto.
      destruct step eqn: H.
      * destruct p.
        destruct Flag.flag_eq; [| intro Hfalse; inversion Hfalse].
        destruct (Int.ltu (Int.add (pc_loc s) Int.one) (Int.repr (Z.of_nat (ins_len s)))) eqn: Hltu'.
        unfold Int.cmpu.
        rewrite Hltu'.
        eapply step_preserving_inv in H; eauto.
        clear - IHf H.
        remember (State.upd_pc_incr s) as st1.
        assert (Hupd_inv: register_inv st1 /\ memory_inv st1 /\ verifier_inv st1). {
          destruct H as (Hreg & Hmem & Hver).
          subst.
          split; [eapply reg_inv_upd_pc_incr; eauto |
            split; [eapply mem_inv_upd_pc_incr; eauto | unfold verifier_inv in *; simpl; assumption]].
        }
        destruct Hupd_inv as (Hreg & Hmem & Hver).
        apply IHf; auto.
        intro Hfalse; inversion Hfalse.
      * assumption.
    + intro Hfalse; inversion Hfalse.
Qed.

Theorem inv_avoid_bpf_interpreter_undef:
  forall st f
    (Hreg: register_inv st)
    (Hmem: memory_inv st)
    (Hver: verifier_inv st),
      bpf_interpreter f st <> None.
Proof.
  intros.
  unfold bpf_interpreter.
  unfold eval_mem_regions, get_mem_region, get_start_addr, upd_reg, eval_flag, eval_reg, bindM, returnM.
  set (Hmem' := Hmem).
  unfold memory_inv in Hmem'.
  destruct Hmem' as (Hlen_low & Hlen & _ & Hinv_memory_regions).
  assert (Hlt: Nat.ltb 0 (mrs_num st) = true). {
    rewrite Nat.ltb_lt.
    lia.
  }
  rewrite Hlt. clear Hlt.
  unfold State.eval_mem_regions.
  assert (Hlt: (0 < length (bpf_mrs st))%nat). {
    rewrite Hlen.
    lia.
  }
  set (Hneq := Hlt).
  rewrite <- List.nth_error_Some in Hneq.
  erewrite List.nth_error_nth' with (d:= MemRegion.default_memory_region); [| assumption].

  apply List.nth_In with (d:= MemRegion.default_memory_region) in Hlt.
  eapply In_inv_memory_regions in Hlt; eauto.
  remember (List.nth 0 (bpf_mrs st) MemRegion.default_memory_region) as mr.
  unfold inv_memory_region in Hlt.
  destruct Hlt as (b & _ & _ & _ & (base & len & Hstart & _)).
  rewrite Hstart.
  simpl.

  remember (State.upd_reg Regs.R1 (Vlong (Int64.repr (Int.unsigned base))) st) as st1.
  assert (Hinv: register_inv st1 /\ memory_inv st1 /\ verifier_inv st1). {
    subst.
    split.
    eapply reg_inv_upd_reg; eauto.
    split.
    eapply mem_inv_upd_reg; eauto.
    unfold verifier_inv in *; unfold State.upd_reg; simpl.
    assumption.
  }
  clear - Hinv.
  destruct Hinv as (Hreg & Hmem & Hver).

  eapply inv_avoid_bpf_interpreter_aux_undef in Hmem; eauto.

  destruct (bpf_interpreter_aux f st1) eqn: Haux.
  destruct p.
  destruct Flag.flag_eq; intro Hfalse; inversion Hfalse.
  intro.
  apply Hmem.
  apply Haux.
Qed.