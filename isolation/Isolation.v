From compcert Require Import Integers Values.
From bpf.comm Require Import State Monad.
From bpf.model Require Import Syntax Semantics.
From bpf.isolation Require Import CommonISOLib AlignChunk RegsInv MemInv IsolationLemma.

From Coq Require Import ZArith Lia.

Open Scope Z_scope.

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
    unfold Int64.iwordsize', Int64.zwordsize, Int64.wordsize, Wordsize_64.wordsize in Hsem; simpl in Hsem.
    unfold Int.ltu in Hsem.
    rewrite Int.unsigned_repr in Hsem; [idtac| rewrite Int_max_unsigned_eq; lia].
    rewrite Int.unsigned_repr in Hsem; [idtac| rewrite Int_max_unsigned_eq; lia].
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

    assert (Hcheck_mem: exists ret, check_mem Memtype.Readable m
    (rBPFValues.val_intuoflongu
       match Val.longofint (Vint o) with
       | Vlong n2 => Vlong (Int64.add vl n2)
       | Vptr b2 ofs2 =>
           if Archi.ptr64
           then Vptr b2 (Ptrofs.add ofs2 (Ptrofs.of_int64 vl))
           else Vundef
       | _ => Vundef
       end)
    st = Some (ret, st)). {
      eapply check_mem_same_state.
    }
    destruct Hcheck_mem as (ret & Hcheck_mem);
    rewrite Hcheck_mem.
    destruct rBPFValues.comp_eq_ptr8_zero eqn: Hptr; [intro H; inversion H|].

    unfold load_mem, State.load_mem.
    (**r from the fact Hptr and Hcheck_mem, we know Hwell_chunk *)
    assert (Hwell_chunk: is_well_chunk m). {
      unfold rBPFValues.comp_eq_ptr8_zero in Hptr.
      unfold check_mem, bindM, returnM in Hcheck_mem.
      Transparent Archi.ptr64.
      destruct m; simpl in Hcheck_mem; inversion Hcheck_mem; unfold Vnullptr in *; subst; simpl in Hptr;
      try (rewrite Int.eq_true in Hptr; inversion Hptr).
      all: unfold is_well_chunk; constructor.
    }
    unfold State._to_vlong, Regs.val64_zero.
    assert (Hneq: ret <> Vnullptr). {
      unfold rBPFValues.comp_eq_ptr8_zero in Hptr.
      unfold Vnullptr; simpl.
      intro.
      rewrite H in Hptr.
      rewrite Int.eq_true in Hptr.
      inversion Hptr.
    }

    unfold rBPFValues.val_intuoflongu, Val.longofint in Hcheck_mem.
    destruct m.
    all: try (intro H; inversion H).
    all: eapply check_mem_load' in Hmem; eauto.
    all: destruct Hmem as (res & Hmem & Hvlong_vint); clear H; rewrite Hmem in H1.
    all: unfold is_vlong_or_vint in Hvlong_vint.
    all: destruct res; try inversion Hvlong_vint; inversion H1.
    unfold Memory.Mem.loadv in Hmem.
    destruct ret; inversion Hmem.
    eapply Memory.Mem.load_type in H0; eauto.
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

      assert (Hcheck_mem: exists ret, check_mem Memtype.Writable m
      (rBPFValues.val_intuoflongu
       match Val.longofint (Vint o) with
       | Vlong n2 => Vlong (Int64.add vl n2)
       | Vptr b2 ofs2 =>
           if Archi.ptr64
           then Vptr b2 (Ptrofs.add ofs2 (Ptrofs.of_int64 vl))
           else Vundef
       | _ => Vundef
       end)
      st = Some (ret, st)). {
        eapply check_mem_same_state.
      }
      destruct Hcheck_mem as (ret & Hcheck_mem);
      rewrite Hcheck_mem.
      destruct rBPFValues.comp_eq_ptr8_zero eqn: Hptr; [intro H; inversion H|].

      unfold load_mem, State.load_mem.
      (**r from the fact Hptr and Hcheck_mem, we know Hwell_chunk *)
      assert (Hwell_chunk: is_well_chunk m). {
        unfold rBPFValues.comp_eq_ptr8_zero in Hptr.
        unfold check_mem, bindM, returnM in Hcheck_mem.
        Transparent Archi.ptr64.
        destruct m; simpl in Hcheck_mem; inversion Hcheck_mem; unfold Vnullptr in *; subst; simpl in Hptr;
        try (rewrite Int.eq_true in Hptr; inversion Hptr).
        all: unfold is_well_chunk; constructor.
      }
      unfold State._to_vlong, Regs.val64_zero.
      assert (Hneq: ret <> Vnullptr). {
        unfold rBPFValues.comp_eq_ptr8_zero in Hptr.
        unfold Vnullptr; simpl.
        intro.
        rewrite H in Hptr.
        rewrite Int.eq_true in Hptr.
        inversion Hptr.
      }

      unfold rBPFValues.val_intuoflongu, Val.longofint in Hcheck_mem.
      unfold store_mem_reg, State.store_mem_reg, State.vlong_to_vint_or_vlong.
      assert (Heq: match m with
    | AST.Mint8unsigned | AST.Mint16unsigned | AST.Mint32 | AST.Mint64 =>
        match
          Memory.Mem.storev m (bpf_m st) ret
            match m with
            | AST.Mint8unsigned | AST.Mint16unsigned | AST.Mint32 =>
                Vint (Int.repr (Int64.unsigned vl0))
            | AST.Mint64 => Vlong vl0
            | _ => Vundef
            end
        with
        | Some m0 => Some (upd_mem m0 st)
        | None => None
        end
    | _ => Some (State.upd_flag Flag.BPF_ILLEGAL_MEM st)
    end = match
          Memory.Mem.storev m (bpf_m st) ret
            match m with
            | AST.Mint8unsigned | AST.Mint16unsigned | AST.Mint32 =>
                Vint (Int.repr (Int64.unsigned vl0))
            | AST.Mint64 => Vlong vl0
            | _ => Vundef
            end
        with
        | Some m0 => Some (upd_mem m0 st)
        | None => None
        end). {
        destruct m; try inversion Hwell_chunk; try reflexivity.
      }
      rewrite Heq; clear Heq.
      destruct m; try inversion Hwell_chunk.
      all: eapply check_mem_store' with (v := Vlong vl0) in Hmem; eauto.
      all: destruct Hmem as (m & Hstore & Hinv); unfold vlong_or_vint_to_vint_or_vlong, vlong_to_vint_or_vlong in Hstore; rewrite Hstore.
      all: intro H; inversion H.
    +
      apply reg_inv_eval_reg with (r:= r) in Hreg as Heval_reg.
      destruct Heval_reg as (vl & Heval_reg).
      rewrite Heval_reg; clear Heval_reg.
      unfold rBPFValues.sint32_to_vint.

      assert (Hcheck_mem: exists ret, check_mem Memtype.Writable m
      (rBPFValues.val_intuoflongu
       match Val.longofint (Vint o) with
       | Vlong n2 => Vlong (Int64.add vl n2)
       | Vptr b2 ofs2 =>
           if Archi.ptr64
           then Vptr b2 (Ptrofs.add ofs2 (Ptrofs.of_int64 vl))
           else Vundef
       | _ => Vundef
       end)
      st = Some (ret, st)). {
        eapply check_mem_same_state.
      }
      destruct Hcheck_mem as (ret & Hcheck_mem);
      rewrite Hcheck_mem.
      destruct rBPFValues.comp_eq_ptr8_zero eqn: Hptr; [intro H; inversion H|].

      unfold load_mem, State.load_mem.
      (**r from the fact Hptr and Hcheck_mem, we know Hwell_chunk *)
      assert (Hwell_chunk: is_well_chunk m). {
        unfold rBPFValues.comp_eq_ptr8_zero in Hptr.
        unfold check_mem, bindM, returnM in Hcheck_mem.
        Transparent Archi.ptr64.
        destruct m; simpl in Hcheck_mem; inversion Hcheck_mem; unfold Vnullptr in *; subst; simpl in Hptr;
        try (rewrite Int.eq_true in Hptr; inversion Hptr).
        all: unfold is_well_chunk; constructor.
      }
      unfold State._to_vlong, Regs.val64_zero.
      assert (Hneq: ret <> Vnullptr). {
        unfold rBPFValues.comp_eq_ptr8_zero in Hptr.
        unfold Vnullptr; simpl.
        intro.
        rewrite H in Hptr.
        rewrite Int.eq_true in Hptr.
        inversion Hptr.
      }

      unfold rBPFValues.val_intuoflongu, Val.longofint in Hcheck_mem.
      unfold store_mem_imm, State.store_mem_imm, State.vint_to_vint_or_vlong.
      assert (Heq: match m with
    | AST.Mint8unsigned | AST.Mint16unsigned | AST.Mint32 | AST.Mint64 =>
        match
          Memory.Mem.storev m (bpf_m st) ret
            match m with
            | AST.Mint8unsigned | AST.Mint16unsigned | AST.Mint32 => Vint i
            | AST.Mint64 => Vlong (Int64.repr (Int.unsigned i))
            | _ => Vundef
            end
        with
        | Some m0 => Some (upd_mem m0 st)
        | None => None
        end
    | _ => Some (State.upd_flag Flag.BPF_ILLEGAL_MEM st)
    end = match
          Memory.Mem.storev m (bpf_m st) ret
            match m with
            | AST.Mint8unsigned | AST.Mint16unsigned | AST.Mint32 => Vint i
            | AST.Mint64 => Vlong (Int64.repr (Int.unsigned i))
            | _ => Vundef
            end
        with
        | Some m0 => Some (upd_mem m0 st)
        | None => None
        end). {
        destruct m; try inversion Hwell_chunk; try reflexivity.
      }
      rewrite Heq; clear Heq.
      destruct m; try inversion Hwell_chunk.
      all: eapply check_mem_store' with (v := Vint i) in Hmem; eauto.
      all: destruct Hmem as (m & Hstore & Hinv); unfold vlong_or_vint_to_vint_or_vlong, vint_to_vint_or_vlong in Hstore; rewrite Hstore.
      all: intro H; inversion H.
  - (* BPF_RET *)
    intro H; inversion H.
  - (* BPF_ERR *)
    intro H; inversion H.
Qed.