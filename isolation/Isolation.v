From compcert Require Import Integers Values.
From bpf.comm Require Import State Monad.
From bpf.model Require Import Syntax Semantics.
From bpf.isolation Require Import CommonISOLib AlignChunk RegsInv MemInv IsolationLemma.

From Coq Require Import ZArith Lia.

Open Scope Z_scope.

Axiom call_inv: forall st1 st2 b ofs res
  (Hreg : register_inv st1)
  (Hmem : memory_inv st1)
  (Hcall: exec_function (Vptr b ofs) st1 = Some (res, st2)),
    register_inv st2 /\ memory_inv st2.

Theorem step_preserving_inv:
  forall st1 st2
    (Hreg: register_inv st1)
    (Hmem: memory_inv st1)
    (Hsem: step st1 = Some (tt, st2)),
       register_inv st2 /\ memory_inv st2.
Proof.
  unfold step.
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
      eapply mem_inv_upd_reg; eauto.
      inversion Hsem.
      reflexivity.
    + split.
      inversion Hsem.
      eapply reg_inv_upd_reg; eauto.
      eapply mem_inv_upd_reg; eauto.
      inversion Hsem.
      reflexivity.
  - (* BPF_BINARY *)
    eapply step_preserving_inv_alu; eauto.
  - (* BPF_JA *)
    inversion Hsem; clear Hsem.
    split; [eapply reg_inv_upd_pc; eauto | eapply mem_inv_upd_pc; eauto].
  - (* BPF_JUMP *)
    eapply step_preserving_inv_branch; eauto.
  - (* BPF_LDDW *)
    destruct Int.lt; simpl in Hsem.
    change Int64.iwordsize' with (Int.repr 64) in Hsem.
    unfold Int.ltu in Hsem.
    change (Int.unsigned (Int.repr 32)) with 32 in Hsem.
    change (Int.unsigned (Int.repr 64)) with 64 in Hsem.
    simpl in Hsem.

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
    + inversion Hsem; split; [eapply reg_inv_upd_flag; eauto | eapply mem_inv_upd_flag; eauto].
  - (* BPF_LDX *)
    eapply step_preserving_inv_ld; eauto.
  - (* BPF_ST *)
    eapply step_preserving_inv_st; eauto.
  - (* BPF_CALL *)
    assert (Hget_call: forall i, exists ptr,
      _bpf_get_call (Vint i) st1 = Some (ptr, st1) /\
      (ptr = Vnullptr \/ (exists b ofs, ptr = Vptr b ofs))). {
      intro.
      apply lemma_bpf_get_call.
    }
    specialize (Hget_call (Int.repr (Int64.unsigned (Int64.repr (Int.signed i))))).
    destruct Hget_call as (ptr & Hget_call & Hres).
    rewrite Hget_call in Hsem.
    destruct Hres as [Hnull | (b & ofs & Hptr)]; unfold cmp_ptr32_nullM, rBPFValues.cmp_ptr32_null in Hsem; subst.
    + simpl in Hsem.
      rewrite Int.eq_true in Hsem.
      inversion Hsem; split; [eapply reg_inv_upd_flag; eauto | eapply mem_inv_upd_flag; eauto].
    + destruct Val.cmpu_bool eqn:cmp; [| inversion Hsem].
      destruct b0.
      * inversion Hsem; split; [eapply reg_inv_upd_flag; eauto | eapply mem_inv_upd_flag; eauto].
      * assert (Hexec: forall b ofs st1,
      exists v st2, exec_function (Vptr b ofs) st1 = Some (Vint v, st2) /\ rBPFValues.cmp_ptr32_null (State.eval_mem st1) (Vptr b ofs) = Some false). {
          apply lemma_exec_function0.
        }
        specialize (Hexec b ofs st1).
        destruct Hexec as (res & st & Hexec & _).
        rewrite Hexec in Hsem.
        apply call_inv in Hexec; auto.
        destruct res; inversion Hsem.
        destruct Hexec as (Hreg_st & Hmem_st).
        split; [eapply reg_inv_upd_reg; eauto | eapply mem_inv_upd_reg; eauto].
  - (* BPF_RET *)
    inversion Hsem.
    split; [eapply reg_inv_upd_flag; eauto | eapply mem_inv_upd_flag; eauto].
  - (* BPF_ERR *)
    inversion Hsem.
    split; [eapply reg_inv_upd_flag; eauto | eapply mem_inv_upd_flag; eauto].
Qed.

Theorem inv_avoid_undef:
  forall st
    (Hreg: register_inv st)
    (Hmem: memory_inv st),
      step st <> None.
Proof.
  intros.
  unfold step.
  unfold_monad.
  destruct ( Decode.decode _).
  - (* BPF_NEG *)
    apply reg_inv_eval_reg with (r:= r) in Hreg as Heval_reg.
    destruct Heval_reg as (vl & Heval_reg).
    destruct a; rewrite Heval_reg; simpl; intro H ; inversion H.
  - (* BPF_BINARY *)
    unfold step_alu_binary_operation.
    unfold_monad.
    apply reg_inv_eval_reg with (r:= r) in Hreg as Heval_reg.
    destruct Heval_reg as (vl & Heval_reg).
    destruct a; rewrite Heval_reg; simpl; clear Heval_reg.
    + destruct s.
      apply reg_inv_eval_reg with (r:= r0) in Hreg as Heval_reg.
      destruct Heval_reg as (vl0 & Heval_reg).
      rewrite Heval_reg; simpl; clear Heval_reg.
      destruct b; intro H; inversion H.
      all: try (destruct negb eqn: Hnegb; [rewrite Bool.negb_true_iff in Hnegb; rewrite Hnegb in H1; simpl in H1; inversion H1 | rewrite Bool.negb_false_iff in Hnegb; inversion H1]).
      all: try (clear H; destruct Int.ltu eqn: Hltu;
       unfold Val.longofintu in H1; inversion H1).

      destruct b; intro H; inversion H.
      all: try (destruct negb eqn: Hnegb; [rewrite Bool.negb_true_iff in Hnegb; rewrite Hnegb in H1; simpl in H1; inversion H1 | rewrite Bool.negb_false_iff in Hnegb; inversion H1]).
      all: try (clear H; destruct Int.ltu eqn: Hltu;
       unfold Val.longofintu in H1; inversion H1).
    + destruct s.
      apply reg_inv_eval_reg with (r:= r0) in Hreg as Heval_reg.
      destruct Heval_reg as (vl0 & Heval_reg).
      rewrite Heval_reg; simpl; clear Heval_reg.
      destruct b; intro H; inversion H.
      all: try (destruct negb eqn: Hnegb; [rewrite Bool.negb_true_iff in Hnegb; rewrite Hnegb in H1; simpl in H1; inversion H1 | rewrite Bool.negb_false_iff in Hnegb; inversion H1]).
      all: try (clear H; destruct Int.ltu eqn: Hltu;
       unfold Val.longofintu in H1; inversion H1).

      destruct b; intro H; inversion H.
      all: try (destruct negb eqn: Hnegb; [rewrite Bool.negb_true_iff in Hnegb; rewrite Hnegb in H1; simpl in H1; inversion H1 | rewrite Bool.negb_false_iff in Hnegb; inversion H1]).
      all: try (clear H; destruct Int.ltu eqn: Hltu;
       unfold Val.longofintu in H1; inversion H1).
  - (* BPF_JA *)
    intro H; inversion H.
  - (* BPF_JUMP *)
    unfold step_branch_cond.
    unfold_monad.
    destruct s; destruct_if; intro H; inversion H.
  - (* BPF_LDDW *)
    destruct_if; intro H; inversion H.
  - (* BPF_LDX *)
    unfold step_load_x_operation.
    unfold_monad.
    unfold Val.addl.

    apply reg_inv_eval_reg with (r:= r0) in Hreg as Heval_reg.
    destruct Heval_reg as (vl & Heval_reg).
    rewrite Heval_reg; clear Heval_reg.
    unfold rBPFValues.sint32_to_vint.

    unfold rBPFValues.val_intuoflongu, Val.longofint.
    remember (Int.repr (Int64.unsigned (Int64.add vl (Int64.repr (Int.signed o))))) as addr.
    assert (Hcheck_mem: exists ret, check_mem Memtype.Readable m (Vint addr) st = Some (ret, st)). {
      rewrite check_memM_P; auto.
      eexists; reflexivity.
      constructor.
    }
    destruct Hcheck_mem as (ret & Hcheck_mem);
    rewrite Hcheck_mem.
    unfold cmp_ptr32_nullM.
    assert (Hcheck_mem' := Hcheck_mem).
    rewrite check_memM_P in Hcheck_mem; auto.
    2:{ constructor. }
    inversion Hcheck_mem.
    rewrite H0.
    unfold check_memP in H0.
    unfold State.eval_mem.

    destruct is_well_chunk_boolP eqn: Hwell_chunk_bool.
    2:{
      subst.
      unfold rBPFValues.cmp_ptr32_null; simpl.
      rewrite Int.eq_true.
      intro H; inversion H.
    }
    remember (check_mem_auxP st (eval_mem_num st) Memtype.Readable m 
            (Vint addr) (State.eval_mem_regions st)) as res.
    symmetry in Heqres.
    eapply mem_inv_check_mem_auxP_valid_pointer in Heqres; eauto.
    2:{ constructor. }
    destruct Heqres as [ (b & ofs & Hptr & Hvalid) | Hnull]; subst.
    2:{ unfold rBPFValues.cmp_ptr32_null; simpl.
        rewrite Int.eq_true.
        change Vnullptr with (Vint Int.zero); simpl.
        rewrite Int.eq_true.
        intro H; inversion H.
    }
    unfold rBPFValues.cmp_ptr32_null; simpl.
    rewrite Int.eq_true, Hvalid; simpl.
    rewrite Hvalid.
    unfold State.load_mem.
    (**r from the fact Hptr and Hcheck_mem, we know Hwell_chunk *)
    assert (Hwell_chunk: is_well_chunk m). {
      unfold is_well_chunk_boolP in Hwell_chunk_bool.
      unfold is_well_chunk.
      destruct m; try inversion Hwell_chunk_bool.
      all: constructor.
    }
    unfold State._to_vlong, Regs.val64_zero.
    unfold rBPFValues.cmp_ptr32_null in *; simpl in Hcheck_mem.
    rewrite Int.eq_true, Hvalid in Hcheck_mem; simpl in Hcheck_mem.
    inversion Hcheck_mem.

    assert (Hneq: match
  Val.cmpu_bool (Memory.Mem.valid_pointer (bpf_m st)) Ceq Vnullptr (Vptr b ofs)
with
| Some false => Vptr b ofs
| _ => Vnullptr
end <> Vnullptr). {
      change Vnullptr with (Vint Int.zero); simpl.
      rewrite Int.eq_true, Hvalid; simpl.
      intro H; inversion H.
    }

    rewrite H0.
    destruct m.
    all: try (intro H; inversion H).
    all: eapply check_mem_load in Hmem; eauto.
    all: destruct Hmem as (res & Hmem & Hvlong_vint); clear H.
    all: unfold load_mem, State.load_mem, Memory.Mem.loadv in H2.
    all: simpl in Hmem; rewrite Int.eq_true, Hvalid in Hmem; simpl in Hmem.
    all: rewrite Hmem in H2.
    all: unfold is_vlong_or_vint in Hvlong_vint.
    all: destruct res; try inversion Hvlong_vint; inversion H2.
    unfold Memory.Mem.loadv in Hmem.
    eapply Memory.Mem.load_type in Hmem; eauto.
  - (* BPF_ST *)
    unfold step_store_operation.
    unfold_monad.
    unfold Val.addl.

    destruct s.
    +
      apply reg_inv_eval_reg with (r:= r) in Hreg as Heval_reg.
      destruct Heval_reg as (vl & Heval_reg).
      rewrite Heval_reg; clear Heval_reg.

      apply reg_inv_eval_reg with (r:= r0) in Hreg as Heval_reg.
      destruct Heval_reg as (vl0 & Heval_reg).
      rewrite Heval_reg; clear Heval_reg.
      unfold rBPFValues.sint32_to_vint.



      unfold rBPFValues.val_intuoflongu, Val.longofint.
      remember (Int.repr (Int64.unsigned (Int64.add vl (Int64.repr (Int.signed o))))) as addr.
      assert (Hcheck_mem: exists ret, check_mem Memtype.Writable m (Vint addr) st = Some (ret, st)). {
        rewrite check_memM_P; auto.
        eexists; reflexivity.
        constructor.
      }
      destruct Hcheck_mem as (ret & Hcheck_mem);
      rewrite Hcheck_mem.
      unfold cmp_ptr32_nullM.
      assert (Hcheck_mem' := Hcheck_mem).
      rewrite check_memM_P in Hcheck_mem; auto.
      2:{ constructor. }
      inversion Hcheck_mem.
      rewrite H0.
      unfold check_memP in H0.
      unfold State.eval_mem.

      destruct is_well_chunk_boolP eqn: Hwell_chunk_bool.
      2:{
        subst.
        unfold rBPFValues.cmp_ptr32_null; simpl.
        rewrite Int.eq_true.
        intro H; inversion H.
      }
      remember (check_mem_auxP st (eval_mem_num st) Memtype.Writable m 
              (Vint addr) (State.eval_mem_regions st)) as res.
      symmetry in Heqres.
      eapply mem_inv_check_mem_auxP_valid_pointer in Heqres; eauto.
      2:{ constructor. }
      destruct Heqres as [ (b & ofs & Hptr & Hvalid) | Hnull]; subst.
      2:{ unfold rBPFValues.cmp_ptr32_null; simpl.
          rewrite Int.eq_true.
          change Vnullptr with (Vint Int.zero); simpl.
          rewrite Int.eq_true.
          intro H; inversion H.
      }
      unfold rBPFValues.cmp_ptr32_null; simpl.
      rewrite Int.eq_true, Hvalid; simpl.
      rewrite Hvalid.
      unfold store_mem_reg, State.store_mem_reg.
      (**r from the fact Hptr and Hcheck_mem, we know Hwell_chunk *)
      assert (Hwell_chunk: is_well_chunk m). {
        unfold is_well_chunk_boolP in Hwell_chunk_bool.
        unfold is_well_chunk.
        destruct m; try inversion Hwell_chunk_bool.
        all: constructor.
      }
      unfold store_mem_reg, State.store_mem_reg, State.vlong_to_vint_or_vlong, State._to_vlong, Regs.val64_zero.
      unfold rBPFValues.cmp_ptr32_null in *; simpl in Hcheck_mem.
      rewrite Int.eq_true, Hvalid in Hcheck_mem; simpl in Hcheck_mem.
      inversion Hcheck_mem.
      rewrite H0.
      assert (Hneq: match
  Val.cmpu_bool (Memory.Mem.valid_pointer (bpf_m st)) Ceq Vnullptr (Vptr b ofs)
with
| Some false => Vptr b ofs
| _ => Vnullptr
end <> Vnullptr). {
      change Vnullptr with (Vint Int.zero); simpl.
      rewrite Int.eq_true, Hvalid; simpl.
      intro H; inversion H.
    }

      destruct m; try inversion Hwell_chunk.
      all: eapply check_mem_store with (v := Vlong vl0) in Hmem; eauto.
      all: unfold Val.cmpu_bool in Hmem; change Vnullptr with (Vint Int.zero) in Hmem; simpl in Hmem.
      all: rewrite Int.eq_true, Hvalid in Hmem; simpl in Hmem.
      all: simpl; destruct Hmem as (m & Hstore & Hinv); unfold vlong_or_vint_to_vint_or_vlong, vlong_to_vint_or_vlong in Hstore; rewrite Hstore.
      all: intro H; inversion H.
    +
      apply reg_inv_eval_reg with (r:= r) in Hreg as Heval_reg.
      destruct Heval_reg as (vl & Heval_reg).
      rewrite Heval_reg; clear Heval_reg.
      unfold rBPFValues.sint32_to_vint.

      unfold rBPFValues.val_intuoflongu, Val.longofint.
      remember (Int.repr (Int64.unsigned (Int64.add vl (Int64.repr (Int.signed o))))) as addr.
      assert (Hcheck_mem: exists ret, check_mem Memtype.Writable m (Vint addr) st = Some (ret, st)). {
        rewrite check_memM_P; auto.
        eexists; reflexivity.
        constructor.
      }
      destruct Hcheck_mem as (ret & Hcheck_mem);
      rewrite Hcheck_mem.
      unfold cmp_ptr32_nullM.
      assert (Hcheck_mem' := Hcheck_mem).
      rewrite check_memM_P in Hcheck_mem; auto.
      2:{ constructor. }
      inversion Hcheck_mem.
      rewrite H0.
      unfold check_memP in H0.
      unfold State.eval_mem.

      destruct is_well_chunk_boolP eqn: Hwell_chunk_bool.
      2:{
        subst.
        unfold rBPFValues.cmp_ptr32_null; simpl.
        rewrite Int.eq_true.
        intro H; inversion H.
      }
      remember (check_mem_auxP st (eval_mem_num st) Memtype.Writable m 
              (Vint addr) (State.eval_mem_regions st)) as res.
      symmetry in Heqres.
      eapply mem_inv_check_mem_auxP_valid_pointer in Heqres; eauto.
      2:{ constructor. }
      destruct Heqres as [ (b & ofs & Hptr & Hvalid) | Hnull]; subst.
      2:{ unfold rBPFValues.cmp_ptr32_null; simpl.
          rewrite Int.eq_true.
          change Vnullptr with (Vint Int.zero); simpl.
          rewrite Int.eq_true.
          intro H; inversion H.
      }
      unfold rBPFValues.cmp_ptr32_null; simpl.
      rewrite Int.eq_true, Hvalid; simpl.
      rewrite Hvalid.
      unfold store_mem_reg, State.store_mem_reg.
      (**r from the fact Hptr and Hcheck_mem, we know Hwell_chunk *)
      assert (Hwell_chunk: is_well_chunk m). {
        unfold is_well_chunk_boolP in Hwell_chunk_bool.
        unfold is_well_chunk.
        destruct m; try inversion Hwell_chunk_bool.
        all: constructor.
      }
      unfold store_mem_imm, State.store_mem_imm, vint_to_vint_or_vlong, State._to_vlong, Regs.val64_zero.
      unfold rBPFValues.cmp_ptr32_null in *; simpl in Hcheck_mem.
      rewrite Int.eq_true, Hvalid in Hcheck_mem; simpl in Hcheck_mem.
      inversion Hcheck_mem.
      rewrite H0.
      assert (Hneq: match
  Val.cmpu_bool (Memory.Mem.valid_pointer (bpf_m st)) Ceq Vnullptr (Vptr b ofs)
with
| Some false => Vptr b ofs
| _ => Vnullptr
end <> Vnullptr). {
      change Vnullptr with (Vint Int.zero); simpl.
      rewrite Int.eq_true, Hvalid; simpl.
      intro H; inversion H.
    }

      destruct m; try inversion Hwell_chunk.
      all: eapply check_mem_store with (v := Vint i) in Hmem; eauto.
      all: unfold Val.cmpu_bool in Hmem; change Vnullptr with (Vint Int.zero) in Hmem; simpl in Hmem.
      all: rewrite Int.eq_true, Hvalid in Hmem; simpl in Hmem.
      all: simpl; destruct Hmem as (m & Hstore & Hinv); unfold vlong_or_vint_to_vint_or_vlong, vint_to_vint_or_vlong in Hstore; rewrite Hstore.
      all: intro H; inversion H.
  - (* BPF_CALL *)
    assert (Hget_call: forall i, exists ptr,
      _bpf_get_call (Vint i) st = Some (ptr, st) /\
      (ptr = Vnullptr \/ (exists b ofs, ptr = Vptr b ofs))). {
      intro.
      apply lemma_bpf_get_call.
    }
    specialize (Hget_call (Int.repr (Int64.unsigned (Int64.repr (Int.signed i))))).
    destruct Hget_call as (ptr & Hget_call & Hres).
    rewrite Hget_call.
    unfold cmp_ptr32_nullM.
    destruct Hres as [Hnull | (b & ofs & Hptr)]; subst.
    + simpl.
      rewrite Int.eq_true.
      intro H; inversion H.
    + assert (Hexec: forall b ofs st1,
      exists v st2, exec_function (Vptr b ofs) st1 = Some (Vint v, st2) /\ rBPFValues.cmp_ptr32_null (State.eval_mem st1) (Vptr b ofs) = Some false). {
          apply lemma_exec_function0.
        }
        specialize (Hexec b ofs st).
        destruct Hexec as (res & st1 & Hexec & Hvalid).
        rewrite Hvalid, Hexec.
        simpl.
        intro H; inversion H.
  - (* BPF_RET *)
    intro H; inversion H.
  - (* BPF_ERR *)
    intro H; inversion H.
Qed.