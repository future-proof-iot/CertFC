From compcert Require Import Integers Values Memory AST.
From bpf.comm Require Import State Monad.
From bpf.model Require Import Syntax Semantics.
From bpf.isolation Require Import CommonISOLib AlignChunk RegsInv MemInv.

From Coq Require Import ZArith List.
Import ListNotations.

Open Scope Z_scope.

Ltac unfold_monad :=
  match goal with
  | |- _ =>
    unfold eval_pc, eval_ins, eval_mrs_num, eval_mem, eval_mem_regions, get_addr_ofs, decodeM, upd_reg, upd_flag, eval_src32, eval_src, eval_reg32, upd_pc, upd_pc_incr, eval_reg, eval_ins_len, get_immediate, bindM, returnM
  end.


Ltac destruct_if :=
  repeat match goal with
  | |- context [if ?X then _ else _] =>
    destruct X
  end.

Lemma step_preserving_inv_alu:
  forall st1 st2 a b r s
    (Hreg : register_inv st1)
    (Hmem : memory_inv st1)
    (Hsem : step_alu_binary_operation a b r s st1 = Some (tt, st2)),
      register_inv st2 /\ memory_inv st2.
Proof.
  unfold step_alu_binary_operation; unfold_monad; intros.
  apply reg_inv_eval_reg with (r := r) in Hreg as Heval_reg;
  destruct Heval_reg as (src & Heval_reg).
  destruct a; rewrite Heval_reg in Hsem; clear Heval_reg; simpl in Hsem.
  - (**r A32 *)
    destruct s.
    + (**r inl r *)
      apply reg_inv_eval_reg with (r := r0) in Hreg as Heval_reg;
      destruct Heval_reg as (src0 & Heval_reg).
      rewrite Heval_reg in Hsem; clear Heval_reg; simpl in Hsem.
      destruct b; inversion Hsem; clear Hsem.
      * split; [eapply reg_inv_upd_reg; eauto | eapply mem_inv_upd_reg; eauto].
      * split; [eapply reg_inv_upd_reg; eauto | eapply mem_inv_upd_reg; eauto].
      * split; [eapply reg_inv_upd_reg; eauto | eapply mem_inv_upd_reg; eauto].
      * split; (destruct negb eqn: Hnegb; [rewrite Bool.negb_true_iff in Hnegb; rewrite Hnegb in H0; simpl in H0; inversion H0 | rewrite Bool.negb_false_iff in Hnegb; inversion H0]).
        eapply reg_inv_upd_reg; eauto.
        eapply reg_inv_upd_flag; eauto.
        eapply mem_inv_upd_reg; eauto.
        eapply mem_inv_upd_flag; eauto.
      * split; [eapply reg_inv_upd_reg; eauto | eapply mem_inv_upd_reg; eauto].
      * split; [eapply reg_inv_upd_reg; eauto | eapply mem_inv_upd_reg; eauto].
      * split; destruct Int.ltu eqn: Hltu; simpl in H0; inversion H0; clear H0.
        eapply reg_inv_upd_reg; eauto.
        eapply reg_inv_upd_flag; eauto.
        eapply mem_inv_upd_reg; eauto.
        eapply mem_inv_upd_flag; eauto.
      * split; destruct Int.ltu eqn: Hltu; simpl in H0; inversion H0; clear H0.
        eapply reg_inv_upd_reg; eauto.
        eapply reg_inv_upd_flag; eauto.
        eapply mem_inv_upd_reg; eauto.
        eapply mem_inv_upd_flag; eauto.
      * split; (destruct negb eqn: Hnegb; [rewrite Bool.negb_true_iff in Hnegb; rewrite Hnegb in H0; simpl in H0; inversion H0 | rewrite Bool.negb_false_iff in Hnegb; inversion H0]).
        eapply reg_inv_upd_reg; eauto.
        eapply reg_inv_upd_flag; eauto.
        eapply mem_inv_upd_reg; eauto.
        eapply mem_inv_upd_flag; eauto.
      * split; [eapply reg_inv_upd_reg; eauto | eapply mem_inv_upd_reg; eauto].
      * split; [eapply reg_inv_upd_reg; eauto | eapply mem_inv_upd_reg; eauto].
      * split; destruct Int.ltu eqn: Hltu; simpl in H0; inversion H0; clear H0.
        eapply reg_inv_upd_reg; eauto.
        eapply reg_inv_upd_flag; eauto.
        eapply mem_inv_upd_reg; eauto.
        eapply mem_inv_upd_flag; eauto.
    + (**r inr i *)
      destruct b; inversion Hsem; clear Hsem.
      * split; [eapply reg_inv_upd_reg; eauto | eapply mem_inv_upd_reg; eauto].
      * split; [eapply reg_inv_upd_reg; eauto | eapply mem_inv_upd_reg; eauto].
      * split; [eapply reg_inv_upd_reg; eauto | eapply mem_inv_upd_reg; eauto].
      * split; (destruct negb eqn: Hnegb; [rewrite Bool.negb_true_iff in Hnegb; rewrite Hnegb in H0; simpl in H0; inversion H0 | rewrite Bool.negb_false_iff in Hnegb; inversion H0]).
        eapply reg_inv_upd_reg; eauto.
        eapply reg_inv_upd_flag; eauto.
        eapply mem_inv_upd_reg; eauto.
        eapply mem_inv_upd_flag; eauto.
      * split; [eapply reg_inv_upd_reg; eauto | eapply mem_inv_upd_reg; eauto].
      * split; [eapply reg_inv_upd_reg; eauto | eapply mem_inv_upd_reg; eauto].
      * split; destruct Int.ltu eqn: Hltu; simpl in H0; inversion H0; clear H0.
        eapply reg_inv_upd_reg; eauto.
        eapply reg_inv_upd_flag; eauto.
        eapply mem_inv_upd_reg; eauto.
        eapply mem_inv_upd_flag; eauto.
      * split; destruct Int.ltu eqn: Hltu; simpl in H0; inversion H0; clear H0.
        eapply reg_inv_upd_reg; eauto.
        eapply reg_inv_upd_flag; eauto.
        eapply mem_inv_upd_reg; eauto.
        eapply mem_inv_upd_flag; eauto.
      * split; (destruct negb eqn: Hnegb; [rewrite Bool.negb_true_iff in Hnegb; rewrite Hnegb in H0; simpl in H0; inversion H0 | rewrite Bool.negb_false_iff in Hnegb; inversion H0]).
        eapply reg_inv_upd_reg; eauto.
        eapply reg_inv_upd_flag; eauto.
        eapply mem_inv_upd_reg; eauto.
        eapply mem_inv_upd_flag; eauto.
      * split; [eapply reg_inv_upd_reg; eauto | eapply mem_inv_upd_reg; eauto].
      * split; [eapply reg_inv_upd_reg; eauto | eapply mem_inv_upd_reg; eauto].
      * split; destruct Int.ltu eqn: Hltu; simpl in H0; inversion H0; clear H0.
        eapply reg_inv_upd_reg; eauto.
        eapply reg_inv_upd_flag; eauto.
        eapply mem_inv_upd_reg; eauto.
        eapply mem_inv_upd_flag; eauto.
  - (**r A64 *)
    destruct s.
    + (**r inl r *)
      apply reg_inv_eval_reg with (r := r0) in Hreg as Heval_reg;
      destruct Heval_reg as (src0 & Heval_reg).
      rewrite Heval_reg in Hsem; clear Heval_reg; simpl in Hsem.
      destruct b; inversion Hsem; clear Hsem.
      * split; [eapply reg_inv_upd_reg; eauto | eapply mem_inv_upd_reg; eauto].
      * split; [eapply reg_inv_upd_reg; eauto | eapply mem_inv_upd_reg; eauto].
      * split; [eapply reg_inv_upd_reg; eauto | eapply mem_inv_upd_reg; eauto].
      * split; (destruct negb eqn: Hnegb; [rewrite Bool.negb_true_iff in Hnegb; rewrite Hnegb in H0; simpl in H0; inversion H0 | rewrite Bool.negb_false_iff in Hnegb; inversion H0]).
        eapply reg_inv_upd_reg; eauto.
        eapply reg_inv_upd_flag; eauto.
        eapply mem_inv_upd_reg; eauto.
        eapply mem_inv_upd_flag; eauto.
      * split; [eapply reg_inv_upd_reg; eauto | eapply mem_inv_upd_reg; eauto].
      * split; [eapply reg_inv_upd_reg; eauto | eapply mem_inv_upd_reg; eauto].
      * split; destruct Int.ltu eqn: Hltu; simpl in H0; inversion H0; clear H0.
        eapply reg_inv_upd_reg; eauto.
        eapply reg_inv_upd_flag; eauto.
        eapply mem_inv_upd_reg; eauto.
        eapply mem_inv_upd_flag; eauto.
      * split; destruct Int.ltu eqn: Hltu; simpl in H0; inversion H0; clear H0.
        eapply reg_inv_upd_reg; eauto.
        eapply reg_inv_upd_flag; eauto.
        eapply mem_inv_upd_reg; eauto.
        eapply mem_inv_upd_flag; eauto.
      * split; (destruct negb eqn: Hnegb; [rewrite Bool.negb_true_iff in Hnegb; rewrite Hnegb in H0; simpl in H0; inversion H0 | rewrite Bool.negb_false_iff in Hnegb; inversion H0]).
        eapply reg_inv_upd_reg; eauto.
        eapply reg_inv_upd_flag; eauto.
        eapply mem_inv_upd_reg; eauto.
        eapply mem_inv_upd_flag; eauto.
      * split; [eapply reg_inv_upd_reg; eauto | eapply mem_inv_upd_reg; eauto].
      * split; [eapply reg_inv_upd_reg; eauto | eapply mem_inv_upd_reg; eauto].
      * split; destruct Int.ltu eqn: Hltu; simpl in H0; inversion H0; clear H0.
        eapply reg_inv_upd_reg; eauto.
        eapply reg_inv_upd_flag; eauto.
        eapply mem_inv_upd_reg; eauto.
        eapply mem_inv_upd_flag; eauto.
    + (**r inr i *)
      destruct b; inversion Hsem; clear Hsem.
      * split; [eapply reg_inv_upd_reg; eauto | eapply mem_inv_upd_reg; eauto].
      * split; [eapply reg_inv_upd_reg; eauto | eapply mem_inv_upd_reg; eauto].
      * split; [eapply reg_inv_upd_reg; eauto | eapply mem_inv_upd_reg; eauto].
      * split; (destruct negb eqn: Hnegb; [rewrite Bool.negb_true_iff in Hnegb; rewrite Hnegb in H0; simpl in H0; inversion H0 | rewrite Bool.negb_false_iff in Hnegb; inversion H0]).
        eapply reg_inv_upd_reg; eauto.
        eapply reg_inv_upd_flag; eauto.
        eapply mem_inv_upd_reg; eauto.
        eapply mem_inv_upd_flag; eauto.
      * split; [eapply reg_inv_upd_reg; eauto | eapply mem_inv_upd_reg; eauto].
      * split; [eapply reg_inv_upd_reg; eauto | eapply mem_inv_upd_reg; eauto].
      * split; destruct Int.ltu eqn: Hltu; simpl in H0; inversion H0; clear H0.
        eapply reg_inv_upd_reg; eauto.
        eapply reg_inv_upd_flag; eauto.
        eapply mem_inv_upd_reg; eauto.
        eapply mem_inv_upd_flag; eauto.
      * split; destruct Int.ltu eqn: Hltu; simpl in H0; inversion H0; clear H0.
        eapply reg_inv_upd_reg; eauto.
        eapply reg_inv_upd_flag; eauto.
        eapply mem_inv_upd_reg; eauto.
        eapply mem_inv_upd_flag; eauto.
      * split; (destruct negb eqn: Hnegb; [rewrite Bool.negb_true_iff in Hnegb; rewrite Hnegb in H0; simpl in H0; inversion H0 | rewrite Bool.negb_false_iff in Hnegb; inversion H0]).
        eapply reg_inv_upd_reg; eauto.
        eapply reg_inv_upd_flag; eauto.
        eapply mem_inv_upd_reg; eauto.
        eapply mem_inv_upd_flag; eauto.
      * split; [eapply reg_inv_upd_reg; eauto | eapply mem_inv_upd_reg; eauto].
      * split; [eapply reg_inv_upd_reg; eauto | eapply mem_inv_upd_reg; eauto].
      * split; destruct Int.ltu eqn: Hltu; simpl in H0; inversion H0; clear H0.
        eapply reg_inv_upd_reg; eauto.
        eapply reg_inv_upd_flag; eauto.
        eapply mem_inv_upd_reg; eauto.
        eapply mem_inv_upd_flag; eauto.
Qed.

Lemma step_preserving_inv_branch:
  forall st1 st2 c r s o
    (Hreg : register_inv st1)
    (Hmem : memory_inv st1)
    (Hsem : match step_branch_cond c r s st1 with
       | Some (x', st') =>
           (if x'
            then
             fun st : state =>
             Some
               (tt, State.upd_pc (Integers.Int.add (State.eval_pc st1) o) st)
            else fun st : state => Some (tt, st)) st'
       | None => None
       end = Some (tt, st2)),
      register_inv st2 /\ memory_inv st2.
Proof.
  unfold step_branch_cond; unfold_monad; intros.
  apply reg_inv_eval_reg with (r := r) in Hreg as Heval_reg;
  destruct Heval_reg as (src & Heval_reg).
  rewrite Heval_reg in Hsem; clear Heval_reg; simpl in Hsem.
  destruct s.
  - (**r inl r *)
    apply reg_inv_eval_reg with (r := r0) in Hreg as Heval_reg;
    destruct Heval_reg as (src0 & Heval_reg).
    rewrite Heval_reg in Hsem; clear Heval_reg; simpl in Hsem.
    destruct (match c with
         | Eq => Int64.eq src src0
         | Gt Ctypes.Signed => Int64.lt src0 src
         | Gt Ctypes.Unsigned => Int64.ltu src0 src
         | Ge Ctypes.Signed => negb (Int64.lt src src0)
         | Ge Ctypes.Unsigned => negb (Int64.ltu src src0)
         | Lt Ctypes.Signed => Int64.lt src src0
         | Lt Ctypes.Unsigned => Int64.ltu src src0
         | Le Ctypes.Signed => negb (Int64.lt src0 src)
         | Le Ctypes.Unsigned => negb (Int64.ltu src0 src)
         | SEt => negb (Int64.eq (Int64.and src src0) Int64.zero)
         | Ne => negb (Int64.eq src src0)
         end); inversion Hsem; clear Hsem.
    + split; [eapply reg_inv_upd_pc; eauto | eapply mem_inv_upd_pc; eauto].
    + subst; intuition.
  - (**r inr i *)
    destruct (match c with
         | Eq => Int64.eq src (Int64.repr (Int.signed i))
         | Gt Ctypes.Signed => Int64.lt (Int64.repr (Int.signed i)) src
         | Gt Ctypes.Unsigned => Int64.ltu (Int64.repr (Int.signed i)) src
         | Ge Ctypes.Signed => negb (Int64.lt src (Int64.repr (Int.signed i)))
         | Ge Ctypes.Unsigned =>
             negb (Int64.ltu src (Int64.repr (Int.signed i)))
         | Lt Ctypes.Signed => Int64.lt src (Int64.repr (Int.signed i))
         | Lt Ctypes.Unsigned => Int64.ltu src (Int64.repr (Int.signed i))
         | Le Ctypes.Signed => negb (Int64.lt (Int64.repr (Int.signed i)) src)
         | Le Ctypes.Unsigned =>
             negb (Int64.ltu (Int64.repr (Int.signed i)) src)
         | SEt =>
             negb
               (Int64.eq (Int64.and src (Int64.repr (Int.signed i)))
                  Int64.zero)
         | Ne => negb (Int64.eq src (Int64.repr (Int.signed i)))
         end); inversion Hsem; clear Hsem.
    + split; [eapply reg_inv_upd_pc; eauto | eapply mem_inv_upd_pc; eauto].
    + subst; intuition.
Qed.

Lemma check_mem_same_state :
  forall perm chunk addr st1,
    exists ret,
      check_mem perm chunk addr st1 = Some (ret, st1).
Proof.
  unfold check_mem, is_well_chunk_bool; unfold_monad; intros.
  
  assert (Hcheck_mem_aux: forall n p c v st mrs, exists v', check_mem_aux n p c v mrs st = Some (v', st)). {
    intros.
    induction n.
    simpl.
    unfold_monad.
    eexists; reflexivity.
    simpl.
    unfold_monad.
    destruct IHn as (v' & IHn).
    unfold get_mem_region.
    unfold_monad.
    unfold eval_mrs_regions.
    assert (Hcheck_mem_aux2: forall mr p c v st, exists v', check_mem_aux2 mr p c v st = Some (v', st)). {
      intros.
      unfold check_mem_aux2, is_well_chunk_bool, get_block_ptr, get_start_addr, get_block_size, get_sub, get_add, get_block_perm.
      unfold_monad.
      destruct v0; destruct_if.
      all: eexists; try reflexivity.
   }
    specialize (Hcheck_mem_aux2 (MemRegion.MyMemRegionsIndexnat mrs n) p v c st).
    destruct Hcheck_mem_aux2 as (v0 & Hcheck_mem_aux2).
    rewrite Hcheck_mem_aux2; clear Hcheck_mem_aux2.
    destruct rBPFValues.comp_eq_ptr8_zero.
    + eexists; eauto.
    + eexists; try reflexivity.
  }
  unfold eval_mrs_regions.
  destruct chunk eqn:Hchunk; specialize (Hcheck_mem_aux (eval_mem_num st1) perm chunk addr st1 (State.eval_mem_regions st1));
  destruct Hcheck_mem_aux as ( v0 & Hcheck_mem_aux).
  all: try inversion Hcheck_mem; try (eexists; reflexivity).
  all: subst; rewrite Hcheck_mem_aux.
  all: destruct rBPFValues.comp_eq_ptr8_zero; eexists; reflexivity.
Qed.

Lemma step_preserving_inv_ld:
  forall st1 st2 m r r0 o
    (Hreg : register_inv st1)
    (Hmem : memory_inv st1)
    (Hsem : step_load_x_operation m r r0 o st1 = Some (tt, st2)),
      register_inv st2 /\ memory_inv st2.
Proof.
  unfold step_load_x_operation; unfold_monad; intros.
  apply reg_inv_eval_reg with (r := r0) in Hreg as Heval_reg;
  destruct Heval_reg as (src & Heval_reg).
  rewrite Heval_reg in Hsem; clear Heval_reg; simpl in Hsem.
  assert (Hcheck_mem: exists ret, check_mem Memtype.Readable m
           (Vint
              (Int.repr
                 (Int64.unsigned (Int64.add src (Int64.repr (Int.signed o))))))
           st1 = Some (ret, st1)). {
    eapply check_mem_same_state.
  }
  destruct Hcheck_mem as (ret & Hcheck_mem); rewrite Hcheck_mem in Hsem; clear Hcheck_mem.
  destruct rBPFValues.comp_eq_ptr8_zero; inversion Hsem; clear Hsem.
  split; [eapply reg_inv_upd_flag; eauto | eapply mem_inv_upd_flag; eauto].
  destruct State.load_mem in H0; inversion H0.
  split; [eapply reg_inv_upd_reg; eauto | eapply mem_inv_upd_reg; eauto].
Qed.

Lemma step_preserving_inv_st:
  forall st1 st2 m r s o
    (Hreg : register_inv st1)
    (Hmem : memory_inv st1)
    (Hsem : step_store_operation m r s o st1 = Some (tt, st2)),
      register_inv st2 /\ memory_inv st2.
Proof.
  unfold step_store_operation; unfold_monad; intros.
  assert (Hcheck_mem: exists ret, check_mem Memtype.Writable m
         (rBPFValues.val_intuoflongu
            (Val.addl (State.eval_reg r st1)
               (Val.longofint (rBPFValues.sint32_to_vint o)))) st1 = Some (ret, st1)). {
    eapply check_mem_same_state.
  }


  destruct s.
  - (**r inl r *)
    destruct Hcheck_mem as (ret & Hcheck_mem); rewrite Hcheck_mem in Hsem.
    destruct rBPFValues.comp_eq_ptr8_zero eqn: Hptr.
    + inversion Hsem; clear Hsem.
      split; [eapply reg_inv_upd_flag; eauto | eapply mem_inv_upd_flag; eauto].
    +
      (**r from the fact Hptr and Hcheck_mem, we know Hwell_chunk *)
      assert (Hwell_chunk: is_well_chunk m). {
        unfold rBPFValues.comp_eq_ptr8_zero in Hptr.
        unfold check_mem, bindM, returnM in Hcheck_mem.
        Transparent Archi.ptr64.
        destruct m; simpl in Hcheck_mem; inversion Hcheck_mem; unfold Vnullptr in *; subst; simpl in Hptr;
        try (rewrite Int.eq_true in Hptr; inversion Hptr).
        all: unfold is_well_chunk; constructor.
      }
      apply reg_inv_eval_reg with (r := r0) in Hreg as Heval_reg;
      destruct Heval_reg as (src & Heval_reg).
      rewrite Heval_reg in Hsem; clear Heval_reg; simpl in Hsem.
      unfold store_mem_reg in Hsem.
      destruct State.store_mem_reg eqn: Hstore; [| inversion Hsem].
      inversion Hsem; subst.
      split; [eapply reg_inv_store_reg; eauto | eapply mem_inv_store_reg; eauto].
  - (**r inr i *)
    destruct Hcheck_mem as (ret & Hcheck_mem); rewrite Hcheck_mem in Hsem.
    destruct rBPFValues.comp_eq_ptr8_zero eqn: Hptr.
    + inversion Hsem; clear Hsem.
      split; [eapply reg_inv_upd_flag; eauto | eapply mem_inv_upd_flag; eauto].
    +
      (**r from the fact Hptr and Hcheck_mem, we know Hwell_chunk *)
      assert (Hwell_chunk: is_well_chunk m). {
        unfold rBPFValues.comp_eq_ptr8_zero in Hptr.
        unfold check_mem, bindM, returnM in Hcheck_mem.
        Transparent Archi.ptr64.
        destruct m; simpl in Hcheck_mem; inversion Hcheck_mem; unfold Vnullptr in *; subst; simpl in Hptr;
        try (rewrite Int.eq_true in Hptr; inversion Hptr).
        all: unfold is_well_chunk; constructor.
      }
      unfold rBPFValues.sint32_to_vint, store_mem_imm in Hsem.
      destruct State.store_mem_imm eqn: Hstore; [| inversion Hsem].
      inversion Hsem; subst.
      split; [eapply reg_inv_store_imm; eauto | eapply mem_inv_store_imm; eauto].
Qed.

Definition is_well_chunk_boolP (chunk: memory_chunk) : bool :=
  match chunk with
  | Mint8unsigned | Mint16unsigned | Mint32 | Mint64 => true
  | _ => false
  end.

Lemma is_well_chunk_boolM_P:
  forall chunk st,
    is_well_chunk_bool chunk st = Some (is_well_chunk_boolP chunk, st).
Proof.
  unfold is_well_chunk_bool, is_well_chunk_boolP.
  unfold_monad.
  intros.
  destruct chunk; reflexivity.
Qed.

From bpf.comm Require Import MemRegion rBPFMemType rBPFAST rBPFValues.

Definition check_mem_aux2P (mr: memory_region) (perm: permission) (addr: val) (chunk: memory_chunk): val :=
  if is_well_chunk_boolP chunk then
    let ptr    := block_ptr mr in
    let start  := start_addr mr in
    let size   := block_size mr in
    let lo_ofs := Val.sub addr start in
    let hi_ofs := Val.add lo_ofs (memory_chunk_to_valu32 chunk) in
      if (andb (compu_le_32 Vzero lo_ofs) (compu_lt_32 hi_ofs size)) then
        if (andb (compu_le_32 lo_ofs (memory_chunk_to_valu32_upbound chunk))
                 (comp_eq_32 Vzero (val32_modu lo_ofs (memory_chunk_to_valu32 chunk)))) then
            let mr_perm  := block_perm mr in
              if (perm_ge mr_perm perm) then
                Val.add ptr lo_ofs
              else
                Vnullptr
          else
            Vnullptr (**r = 0 *)
        else
          Vnullptr
    else
      Vnullptr.

(*
Lemma check_mem_aux2P_ptr:
  forall mr perm addr chunk st1
    (Hmem_inv: memory_inv st1),
    (exists b ofs, check_mem_aux2P mr perm addr chunk = Vptr b ofs) \/  check_mem_aux2P mr perm addr chunk = Vnullptr.
Proof.
  intros.
  unfold check_mem_aux2P.
  destruct_if; intuition.
  unfold memory_inv, inv_memory_regions in Hmem_inv.
  unfold 
  left. eexists;
Qed.*)

Lemma check_mem_aux2M_P:
  forall mr perm addr chunk st,
    check_mem_aux2 mr perm addr chunk st = Some (check_mem_aux2P mr perm addr chunk, st).
Proof.
  unfold check_mem_aux2, check_mem_aux2P.
  unfold get_block_ptr, get_start_addr, get_block_size, get_sub, get_add, get_block_perm.
  unfold_monad.
  intros.
  rewrite is_well_chunk_boolM_P.
  destruct_if; reflexivity.
Qed.

Fixpoint check_mem_auxP (num: nat) (perm: permission) (chunk: memory_chunk) (addr: val) (mrs: MyMemRegionsType) {struct num}: val :=
  match num with
  | O => Vnullptr
  | S n =>
    let cur_mr    := MyMemRegionsIndexnat mrs n in
    let check_mem := check_mem_aux2P cur_mr perm addr chunk in
      if comp_eq_ptr8_zero check_mem then
        check_mem_auxP n perm chunk addr mrs
      else
        check_mem
  end.

Lemma check_mem_auxM_P:
  forall n perm chunk addr st mrs,
    check_mem_aux n perm chunk addr mrs st = Some (check_mem_auxP n perm chunk addr mrs, st).
Proof.
  unfold check_mem_aux, get_mem_region, eval_mrs_regions, check_mem_auxP.
  unfold_monad.
  intros.
  induction n.
  reflexivity.
  rewrite check_mem_aux2M_P.
  destruct_if; try reflexivity.
  rewrite IHn.
  reflexivity.
Qed.

Definition check_memP (perm: permission) (chunk: memory_chunk) (addr: val) (st: State.state): val :=
  let well_chunk := is_well_chunk_boolP chunk in
    if well_chunk then
      let mem_reg_num := eval_mem_num st in
      let mrs         := State.eval_mem_regions st in
      let check_mem  := check_mem_auxP mem_reg_num perm chunk addr mrs in
        if comp_eq_ptr8_zero check_mem then
          Vnullptr
        else
          check_mem
    else
      Vnullptr.

Lemma check_memM_P:
  forall perm chunk addr st,
    check_mem perm chunk addr st = Some (check_memP perm chunk addr st, st).
Proof.
  unfold check_mem, eval_mrs_num, eval_mrs_regions, check_memP.
  unfold_monad.
  intros.
  rewrite is_well_chunk_boolM_P.
  destruct is_well_chunk_boolP; try reflexivity.
  rewrite check_mem_auxM_P.
  destruct_if; try reflexivity.
Qed.

Lemma well_chunk_iff:
  forall chunk,
    is_well_chunk chunk <-> is_well_chunk_boolP chunk = true.
Proof.
  unfold is_well_chunk, is_well_chunk_boolP.
  intros.
  destruct chunk; split; try constructor; intro H; inversion H.
Qed.

Fixpoint check_mem_auxL (perm: permission) (chunk: memory_chunk) (addr: val) (mrs: list memory_region): val :=
  match mrs with
  | [] => Vnullptr
  | hd :: tl =>
    let check_mem := check_mem_aux2P hd perm addr chunk in
      if comp_eq_ptr8_zero check_mem then
        check_mem_auxL perm chunk addr tl
      else
        check_mem
  end.

Definition check_memL (perm: permission) (chunk: memory_chunk) (addr: val) (st: State.state): val :=
  let well_chunk := is_well_chunk_boolP chunk in
    if well_chunk then
      let mem_reg_num := eval_mem_num st in
      let mrs         := State.eval_mem_regions st in
      let check_mem  := check_mem_auxP mem_reg_num perm chunk addr mrs in
        if comp_eq_ptr8_zero check_mem then
          Vnullptr
        else
          check_mem
    else
      Vnullptr.
(*
Lemma check_mem_auxP_L:
  forall perm chunk addr l,
    (*(Hlist: bpf_mrs st = List.rev l), *)
    check_mem_auxP (List.length l) perm chunk addr l = check_mem_auxL perm chunk addr (List.rev l).
Proof.
  intros perm chunk addr l.
  unfold check_mem_auxP.
  unfold State.eval_mem_regions, MyMemRegionsIndexnat, Memory_regions.index_nat.
  induction l.
  intros.
  simpl.

  reflexivity.
  simpl in *.

  intros.
  destruct (length l).
  admit.

  assert (Heq_a: (nth (length l) (bpf_mrs st) default_memory_region) = a). {
    rewrite Hlist.
    rewrite <- rev_length.
    rewrite nth_middle with (l' := []).
    reflexivity.
  }
  rewrite Heq_a; clear Heq_a.
  destruct comp_eq_ptr8_zero; [| reflexivity].
  rewrite Hlist.
  simpl.
  apply IHl.
Qed.*)

Lemma check_mem_aux2P_spec:
  forall mr chunk st1 p base len b b0 vi ofs
    (H0 : check_mem_aux2P mr p (Vint vi) chunk = Vptr b ofs)
    (Hptr : block_ptr mr = Vptr b0 Ptrofs.zero)
    (Hvalid : Mem.valid_block (bpf_m st1) b0)
    (Hbyte : is_byte_block b0 (bpf_m st1))
    (Hstar : start_addr mr = Vint base)
    (Hsize : block_size mr = Vint len)
    (Hperm : perm_order (block_perm mr) p)
    (Hrange_perm : Mem.range_perm (bpf_m st1) b0 0 (Int.unsigned len) Cur (block_perm mr)),
        is_well_chunk chunk /\
        ofs = Ptrofs.of_int (Int.sub vi base) /\
        b = b0 /\
        0 <= (Ptrofs.unsigned ofs) + size_chunk chunk < Int.unsigned len /\
        Mem.valid_access (bpf_m st1) chunk b (Ptrofs.unsigned ofs) (block_perm mr).
Proof.
  unfold check_mem_aux2P.
  intros.
  destruct is_well_chunk_boolP eqn: Hwell_chunk; [| inversion H0].
  split.
  apply well_chunk_iff.
  assumption.

  destruct ((compu_le_32 Vzero (Val.sub (Vint vi) (start_addr mr)) &&
        compu_lt_32
          (Val.add (Val.sub (Vint vi) (start_addr mr))
             (memory_chunk_to_valu32 chunk)) (block_size mr))%bool) eqn: Hlow; [| inversion H0].
  destruct ((compu_le_32 (Val.sub (Vint vi) (start_addr mr))
          (memory_chunk_to_valu32_upbound chunk) &&
        comp_eq_32 Vzero
          (val32_modu (Val.sub (Vint vi) (start_addr mr))
             (memory_chunk_to_valu32 chunk)))%bool) eqn: Hhigh; [| inversion H0].
  destruct (perm_ge (block_perm mr) p); [| inversion H0].

  Transparent Archi.ptr64.
  rewrite Hptr, Hstar, Hsize in *.
  unfold Val.add, Val.sub in H0.
  simpl in H0.
  rewrite Ptrofs.add_zero_l in H0.
  inversion H0.
  split.
  reflexivity.

  subst.
  unfold compu_le_32, compu_lt_32, comp_eq_32, Vzero, Val.sub in *.
  unfold memory_chunk_to_valu32, memory_chunk_to_valu32_upbound, Val.add in *.
  rewrite Ptrofs.agree32_of_int; [| reflexivity].
  (**r with the fact `is_well_chunk_boolP`, we get the following lemma *)
  assert (Heq_well_chunk: well_chunk_Z chunk = size_chunk chunk). {
    unfold is_well_chunk_boolP in Hwell_chunk.
    destruct chunk; try inversion Hwell_chunk.
    all: unfold well_chunk_Z, size_chunk; reflexivity.
  }
  rewrite Heq_well_chunk in *; clear Heq_well_chunk.
  (**r b = b0 *)
  split.
  reflexivity.

  (**r Hlow is for _ <= _ < _ and Hhigh is for valid_access *)
  apply andb_prop in Hlow, Hhigh.
  destruct Hlow as (Hlow1 & Hlow2).
  destruct Hhigh as (Hhigh1 & Hhigh2).
  apply (hi_ofs_max_unsigned (Int.sub vi base) chunk) in Hhigh1.
  apply Clt_implies_Zlt_add in Hlow2 as Hlow2'; [| assumption].
  split.
  assumption.

  apply Cle_implies_Zle in Hlow1.
  apply Clt_implies_Zlt_add with (hi := len) in Hhigh1; [| assumption].
  unfold Mem.valid_access.
  split.
  eapply range_perm_included; eauto.
  apply Int_unsigned_ofs_size_chunk_ge_0.
  intuition.

  unfold val32_modu in Hhigh2.

  rewrite <- well_chunk_iff in Hwell_chunk.
  destruct Val.modu eqn: Hmod; [| inversion Hhigh2].
  destruct v; try inversion Hhigh2.
  unfold Val.modu in Hmod.
  destruct Int.eq eqn: Hmod2; [inversion Hmod|].
  eapply modu_zero_is_aligned; eauto.
  inversion Hmod.
  rewrite <- H2 in H1.
  assumption.
Qed.

Lemma check_mem_aux2P_spec':
  forall mr chunk st1 p base len b vi ptr
    (H0 : check_mem_aux2P mr p (Vint vi) chunk = ptr)
    (Hneq : ptr <> Vnullptr)
    (Hptr : block_ptr mr = Vptr b Ptrofs.zero)
    (Hvalid : Mem.valid_block (bpf_m st1) b)
    (Hbyte : is_byte_block b (bpf_m st1))
    (Hstar : start_addr mr = Vint base)
    (Hsize : block_size mr = Vint len)
    (Hperm : perm_order (block_perm mr) p)
    (Hrange_perm : Mem.range_perm (bpf_m st1) b 0 (Int.unsigned len) Cur (block_perm mr)),
      exists ofs,
        is_well_chunk chunk /\
        ofs = Ptrofs.of_int (Int.sub vi base) /\
        0 <= (Ptrofs.unsigned ofs) + size_chunk chunk < Int.unsigned len /\
        ptr = Vptr b ofs /\
        Mem.valid_access (bpf_m st1) chunk b (Ptrofs.unsigned ofs) (block_perm mr).
Proof.
  unfold check_mem_aux2P.
  intros.
  destruct is_well_chunk_boolP eqn: Hwell_chunk; [| rewrite H0 in Hneq; exfalso; apply Hneq; reflexivity].
  rewrite Hptr, Hstar, Hsize in *.
  unfold Val.add, Val.sub in H0.
  rewrite Ptrofs.add_zero_l in H0.
  exists (Ptrofs.of_int (Int.sub vi base)).
  split.
  apply well_chunk_iff.
  assumption.

  destruct ((compu_le_32 Vzero (Vint (Int.sub vi base)) &&
        compu_lt_32
          match memory_chunk_to_valu32 chunk with
          | Vint n2 => Vint (Int.add (Int.sub vi base) n2)
          | Vptr b2 ofs2 =>
              if Archi.ptr64
              then Vundef
              else Vptr b2 (Ptrofs.add ofs2 (Ptrofs.of_int (Int.sub vi base)))
          | _ => Vundef
          end (Vint len))%bool) eqn: Hlow; [| rewrite H0 in Hneq; exfalso; apply Hneq; reflexivity].
  destruct ((compu_le_32 (Vint (Int.sub vi base))
          (memory_chunk_to_valu32_upbound chunk) &&
        comp_eq_32 Vzero
          (val32_modu (Vint (Int.sub vi base)) (memory_chunk_to_valu32 chunk)))%bool) eqn: Hhigh; [| rewrite H0 in Hneq; exfalso; apply Hneq; reflexivity].
  destruct (perm_ge (block_perm mr) p); [| rewrite H0 in Hneq; exfalso; apply Hneq; reflexivity].

  Transparent Archi.ptr64.
  simpl in H0.
  inversion H0.
  split.
  reflexivity.

  subst.
  unfold compu_le_32, compu_lt_32, comp_eq_32, Vzero, Val.sub in *.
  unfold memory_chunk_to_valu32, memory_chunk_to_valu32_upbound, Val.add in *.
  rewrite Ptrofs.agree32_of_int; [| reflexivity].
  (**r with the fact `is_well_chunk_boolP`, we get the following lemma *)
  assert (Heq_well_chunk: well_chunk_Z chunk = size_chunk chunk). {
    unfold is_well_chunk_boolP in Hwell_chunk.
    destruct chunk; try inversion Hwell_chunk.
    all: unfold well_chunk_Z, size_chunk; reflexivity.
  }
  rewrite Heq_well_chunk in *; clear Heq_well_chunk.

  (**r Hlow is for _ <= _ < _ and Hhigh is for valid_access *)
  apply andb_prop in Hlow, Hhigh.
  destruct Hlow as (Hlow1 & Hlow2).
  destruct Hhigh as (Hhigh1 & Hhigh2).
  apply (hi_ofs_max_unsigned (Int.sub vi base) chunk) in Hhigh1.
  apply Clt_implies_Zlt_add in Hlow2 as Hlow2'; [| assumption].
  split.
  assumption.

  split.
  reflexivity.

  apply Cle_implies_Zle in Hlow1.
  apply Clt_implies_Zlt_add with (hi := len) in Hhigh1; [| assumption].
  unfold Mem.valid_access.
  split.
  eapply range_perm_included; eauto.
  apply Int_unsigned_ofs_size_chunk_ge_0.
  intuition.

  unfold val32_modu in Hhigh2.

  rewrite <- well_chunk_iff in Hwell_chunk.
  destruct Val.modu eqn: Hmod; [| inversion Hhigh2].
  destruct v; try inversion Hhigh2.
  unfold Val.modu in Hmod.
  destruct Int.eq eqn: Hmod2; [inversion Hmod|].
  eapply modu_zero_is_aligned; eauto.
  inversion Hmod.
  rewrite <- H2 in H1.
  assumption.
Qed.

Lemma check_mem_load:
  forall chunk st1 vi b ofs
    (Hwell_chunk : is_well_chunk chunk)
    (Hmem_inv: memory_inv st1)
    (Hcheck_mem: check_mem Readable chunk (Vint vi) st1 = Some ((Vptr b ofs), st1)),
    exists res,
      (Memory.Mem.loadv chunk (bpf_m st1) (Vptr b ofs) = Some res)/\
      is_vlong_or_vint res.
Proof.
  intros.
  rewrite check_memM_P in Hcheck_mem.
  inversion Hcheck_mem; clear Hcheck_mem.

  unfold check_memP in *.
  rewrite well_chunk_iff in Hwell_chunk.
  rewrite Hwell_chunk in *.
  Transparent Archi.ptr64.
  destruct comp_eq_ptr8_zero.
  inversion H0.

  unfold eval_mem_num, State.eval_mem_regions in *.

  induction (mrs_num st1).
  simpl in *.
  inversion H0.

  simpl in *.
  destruct comp_eq_ptr8_zero.
  apply IHn.
  specialize (IHn H0).
  assumption.
  remember (MyMemRegionsIndexnat (bpf_mrs st1) n) as mr.

  (**r we rely on the fact if Heqmr get the default memory region, check_mem_aux2P should return Vnullptr! *)
  assert (Hdefault: check_mem_aux2P default_memory_region Readable (Vint vi) chunk = Vnullptr). {
    unfold check_mem_aux2P, default_memory_region.
    unfold start_addr, block_size, block_perm, block_ptr.
    Transparent Archi.ptr64.
    assert (Hnullptr: Vint Int.zero = Vnullptr). {
      unfold Vnullptr; reflexivity.
    }
    rewrite <- Hnullptr; clear Hnullptr.
    assert (Hperm: perm_ge Nonempty Readable = false). {
      unfold perm_ge.
      unfold Mem.perm_order_dec.
      reflexivity.
    }
    rewrite Hperm; clear Hperm.
    destruct_if; try reflexivity.
  }
  rewrite H0.

  unfold memory_inv in Hmem_inv.
  unfold MyMemRegionsIndexnat in Heqmr.

  unfold State.eval_mem_regions, Memory_regions.index_nat in Heqmr.
  assert (Hin_mem_regions: List.In mr (bpf_mrs st1)). {
    destruct nth_error eqn: Hnth_error.
    + apply List.nth_error_In in Hnth_error.
      subst.
      assumption.
    + subst.
      rewrite Hdefault in H0.
      inversion H0.
  }
  (**r now we get the evidence `In mr (bpf_mrs st1)`, and reuse the lemma `In_inv_memory_regions` *)
  apply In_inv_memory_regions with (m:=bpf_m st1) in Hin_mem_regions; [| intuition].
  assert (Hin_mem_regions' := Hin_mem_regions).
  unfold inv_memory_region in Hin_mem_regions'.

  destruct Hin_mem_regions' as (b0 & Hptr & Hvalid & Hbyte & base & len & Hstar & Hsize & Hperm & Hrange_perm).
  eapply check_mem_aux2P_spec in H0; eauto.
  destruct H0 as (Hwell_chunk' & Hofs & Hb_eq & Hofs_range & Hvalid_access).
  subst b0.

  apply Mem.valid_access_implies with (p2:= Readable) in Hvalid_access; [| assumption].
  apply Mem.valid_access_load in Hvalid_access.
  destruct Hvalid_access as (v & Hload).
  exists v.
  split; [unfold Mem.loadv; assumption | ].

  assert (Hofs_range_c: 0 <= Ptrofs.unsigned ofs /\ Ptrofs.unsigned ofs + size_chunk chunk < Int.unsigned len). {
      split.
      apply ptrofs_unsigned_ge_0.
      destruct Hofs_range as [Ha Hb]; assumption.
    }

  eapply load_some_well_chunk_vlong_or_vint; eauto.
Qed.

Lemma check_mem_load':
  forall chunk st1 vi pt
    (Hwell_chunk : is_well_chunk chunk)
    (Hmem_inv: memory_inv st1)
    (Hcheck_mem: check_mem Readable chunk (Vint vi) st1 = Some (pt, st1))
    (Hneq: pt <> Vnullptr),
    exists res,
      (Memory.Mem.loadv chunk (bpf_m st1) pt = Some res)/\
      is_vlong_or_vint res.
Proof.
  intros.
  rewrite check_memM_P in Hcheck_mem.
  inversion Hcheck_mem; clear Hcheck_mem.

  unfold check_memP in *.
  rewrite well_chunk_iff in Hwell_chunk.
  rewrite Hwell_chunk in *.
  Transparent Archi.ptr64.
  destruct comp_eq_ptr8_zero.
  rewrite H0 in Hneq.
  exfalso; apply Hneq; reflexivity.

  unfold eval_mem_num, State.eval_mem_regions in *.

  induction (mrs_num st1).
  simpl in *.
  rewrite H0 in Hneq.
  exfalso; apply Hneq; reflexivity.

  simpl in *.
  
  destruct comp_eq_ptr8_zero.
  apply IHn.
  specialize (IHn H0).
  assumption.
  remember (MyMemRegionsIndexnat (bpf_mrs st1) n) as mr.

  (**r we rely on the fact if Heqmr get the default memory region, check_mem_aux2P should return Vnullptr! *)
  assert (Hdefault: check_mem_aux2P default_memory_region Readable (Vint vi) chunk = Vnullptr). {
    unfold check_mem_aux2P, default_memory_region.
    unfold start_addr, block_size, block_perm, block_ptr.
    Transparent Archi.ptr64.
    assert (Hnullptr: Vint Int.zero = Vnullptr). {
      unfold Vnullptr; reflexivity.
    }
    rewrite <- Hnullptr; clear Hnullptr.
    assert (Hperm: perm_ge Nonempty Readable = false). {
      unfold perm_ge.
      unfold Mem.perm_order_dec.
      reflexivity.
    }
    rewrite Hperm; clear Hperm.
    destruct_if; try reflexivity.
  }
  rewrite H0.

  unfold memory_inv in Hmem_inv.
  unfold MyMemRegionsIndexnat in Heqmr.

  unfold State.eval_mem_regions, Memory_regions.index_nat in Heqmr.
  assert (Hin_mem_regions: List.In mr (bpf_mrs st1)). {
    destruct nth_error eqn: Hnth_error.
    + apply List.nth_error_In in Hnth_error.
      subst.
      assumption.
    + subst.
      rewrite Hdefault in Hneq.
      exfalso; apply Hneq; reflexivity.
  }
  (**r now we get the evidence `In mr (bpf_mrs st1)`, and reuse the lemma `In_inv_memory_regions` *)
  apply In_inv_memory_regions with (m:=bpf_m st1) in Hin_mem_regions; [| intuition].
  assert (Hin_mem_regions' := Hin_mem_regions).
  unfold inv_memory_region in Hin_mem_regions'.

  destruct Hin_mem_regions' as (b0 & Hptr & Hvalid & Hbyte & base & len & Hstar & Hsize & Hperm & Hrange_perm).
  eapply check_mem_aux2P_spec' in H0; eauto.
  destruct H0 as (ofs & Hwell_chunk' & Hofs & Hofs_range & Hptr_eq & Hvalid_access).

  subst pt.
  apply Mem.valid_access_implies with (p2:= Readable) in Hvalid_access; [| assumption].
  apply Mem.valid_access_load in Hvalid_access.
  destruct Hvalid_access as (v & Hload).
  exists v.
  unfold Mem.loadv.
  split; [assumption | ].

  assert (Hofs_range_c: 0 <= Ptrofs.unsigned ofs /\ Ptrofs.unsigned ofs + size_chunk chunk < Int.unsigned len). {
      split.
      apply ptrofs_unsigned_ge_0.
      destruct Hofs_range as [Ha Hb]; assumption.
    }

  eapply load_some_well_chunk_vlong_or_vint; eauto.
Qed.

Definition vlong_or_vint_to_vint_or_vlong (chunk: memory_chunk) (v: val): val :=
  match v with
  | Vlong n => vlong_to_vint_or_vlong chunk v
  | Vint  n => vint_to_vint_or_vlong chunk v
  | _       => Vundef
  end.

Lemma check_mem_store:
  forall chunk st1 vi b ofs v
    (Hwell_chunk : is_well_chunk chunk)
    (Hmem_inv: memory_inv st1)
    (Hvlong_vint: is_vlong_or_vint v)
    (Hcheck_mem: check_mem Writable chunk (Vint vi) st1 = Some ((Vptr b ofs), st1)),
    exists m,
      (Mem.storev chunk (bpf_m st1) (Vptr b ofs) (vlong_or_vint_to_vint_or_vlong chunk v) = Some m)/\
      memory_inv (upd_mem m st1).
Proof.
  intros.
  rewrite check_memM_P in Hcheck_mem.
  inversion Hcheck_mem; clear Hcheck_mem.

  unfold check_memP in *.
  rewrite well_chunk_iff in Hwell_chunk.
  rewrite Hwell_chunk in *.
  Transparent Archi.ptr64.
  destruct comp_eq_ptr8_zero.
  inversion H0.

  unfold eval_mem_num, State.eval_mem_regions in *.

  induction (mrs_num st1).
  simpl in *.
  inversion H0.

  simpl in *.
  destruct comp_eq_ptr8_zero.
  apply IHn.
  specialize (IHn H0).
  assumption.
  remember (MyMemRegionsIndexnat (bpf_mrs st1) n) as mr.

  (**r we rely on the fact if Heqmr get the default memory region, check_mem_aux2P should return Vnullptr! *)
  assert (Hdefault: check_mem_aux2P default_memory_region Writable (Vint vi) chunk = Vnullptr). {
    unfold check_mem_aux2P, default_memory_region.
    unfold start_addr, block_size, block_perm, block_ptr.
    Transparent Archi.ptr64.
    assert (Hnullptr: Vint Int.zero = Vnullptr). {
      unfold Vnullptr; reflexivity.
    }
    rewrite <- Hnullptr; clear Hnullptr.
    assert (Hperm: perm_ge Nonempty Writable = false). {
      unfold perm_ge.
      unfold Mem.perm_order_dec.
      reflexivity.
    }
    rewrite Hperm; clear Hperm.
    destruct_if; try reflexivity.
  }
  rewrite H0.

  unfold memory_inv in Hmem_inv.
  unfold MyMemRegionsIndexnat in Heqmr.

  unfold State.eval_mem_regions, Memory_regions.index_nat in Heqmr.
  assert (Hin_mem_regions: List.In mr (bpf_mrs st1)). {
    destruct nth_error eqn: Hnth_error.
    + apply List.nth_error_In in Hnth_error.
      subst.
      assumption.
    + subst.
      rewrite Hdefault in H0.
      inversion H0.
  }
  (**r now we get the evidence `In mr (bpf_mrs st1)`, and reuse the lemma `In_inv_memory_regions` *)
  apply In_inv_memory_regions with (m:=bpf_m st1) in Hin_mem_regions; [| intuition].
  assert (Hperm_w: perm_order (block_perm mr) Writable). {
    unfold check_mem_aux2P in H0.
    rewrite Hwell_chunk in H0.
    destruct ((compu_le_32 Vzero (Val.sub (Vint vi) (start_addr mr)) &&
         compu_lt_32
           (Val.add (Val.sub (Vint vi) (start_addr mr))
              (memory_chunk_to_valu32 chunk)) (block_size mr))%bool); [| inversion H0].
    destruct ((compu_le_32 (Val.sub (Vint vi) (start_addr mr))
          (memory_chunk_to_valu32_upbound chunk) &&
        comp_eq_32 Vzero
          (val32_modu (Val.sub (Vint vi) (start_addr mr))
             (memory_chunk_to_valu32 chunk)))%bool); [| inversion H0].
    unfold perm_ge in H0.
    destruct Mem.perm_order_dec eqn: Hp.
    assumption.
    inversion H0.
  }

  assert (Hin_mem_regions' := Hin_mem_regions).
  unfold inv_memory_region in Hin_mem_regions'.

  destruct Hin_mem_regions' as (b0 & Hptr & Hvalid & Hbyte & base & len & Hstar & Hsize & Hperm & Hrange_perm).
  eapply check_mem_aux2P_spec in H0; eauto.
  destruct H0 as (Hwell_chunk' & Hofs & Hb_eq & Hofs_range & Hvalid_access).
  subst b0.

  apply Mem.valid_access_implies with (p2:= Writable) in Hvalid_access; [| assumption].
  eapply Mem.valid_access_store in Hvalid_access; eauto.
  destruct Hvalid_access as (m2 & Hstore).
  exists m2.
  split; [ apply Hstore | ].

  (**r prove the memory_inv *)
  unfold is_vlong_or_vint in Hvlong_vint.
  destruct v; inversion Hvlong_vint.

  - apply mem_inv_store_imm with (st1 := st1) (st2:= upd_mem m2 st1) (addr:= Vptr b ofs) (i:= i) in Hwell_chunk'; auto.
  unfold State.store_mem_imm, vint_to_vint_or_vlong.
  assert (Heq: match chunk with
| Mint8unsigned | Mint16unsigned | Mint32 | Mint64 =>
    match
      Mem.storev chunk (bpf_m st1) (Vptr b ofs)
        match chunk with
        | Mint8unsigned | Mint16unsigned | Mint32 => Vint i
        | Mint64 => Vlong (Int64.repr (Int.unsigned i))
        | _ => Vundef
        end
    with
    | Some m => Some (upd_mem m st1)
    | None => None
    end
| _ => Some (State.upd_flag Flag.BPF_ILLEGAL_MEM st1)
end = match
      Mem.storev chunk (bpf_m st1) (Vptr b ofs)
        match chunk with
        | Mint8unsigned | Mint16unsigned | Mint32 => Vint i
        | Mint64 => Vlong (Int64.repr (Int.unsigned i))
        | _ => Vundef
        end
    with
    | Some m => Some (upd_mem m st1)
    | None => None
    end). {
      destruct chunk; try inversion Hwell_chunk'; try reflexivity.
    }
    rewrite Heq; clear Heq.
    unfold Mem.storev.
    unfold vlong_or_vint_to_vint_or_vlong, vint_to_vint_or_vlong in Hstore.
    rewrite Hstore.
    reflexivity.
  - unfold vlong_or_vint_to_vint_or_vlong, vlong_to_vint_or_vlong in Hstore.
    apply mem_inv_store_reg with (st1 := st1) (st2:= upd_mem m2 st1) (addr:= Vptr b ofs) (src:= i) in Hwell_chunk'; auto.
  unfold State.store_mem_reg, vlong_to_vint_or_vlong.
    destruct chunk; try inversion Hwell_chunk'; simpl.
    all: try (rewrite Hstore; reflexivity).
Qed.

Lemma check_mem_store':
  forall chunk st1 vi v pt
    (Hwell_chunk : is_well_chunk chunk)
    (Hmem_inv: memory_inv st1)
    (Hvlong_vint: is_vlong_or_vint v)
    (Hcheck_mem: check_mem Writable chunk (Vint vi) st1 = Some (pt, st1))
    (Hneq: pt <> Vnullptr),
    exists m,
      (Mem.storev chunk (bpf_m st1) pt (vlong_or_vint_to_vint_or_vlong chunk v) = Some m)/\
      memory_inv (upd_mem m st1).
Proof.
  intros.
  rewrite check_memM_P in Hcheck_mem.
  inversion Hcheck_mem; clear Hcheck_mem.

  unfold check_memP in *.
  rewrite well_chunk_iff in Hwell_chunk.
  rewrite Hwell_chunk in *.
  Transparent Archi.ptr64.
  destruct comp_eq_ptr8_zero.
  rewrite H0 in Hneq; exfalso; apply Hneq; reflexivity.

  unfold eval_mem_num, State.eval_mem_regions in *.

  induction (mrs_num st1).
  simpl in *.
  rewrite H0 in Hneq; exfalso; apply Hneq; reflexivity.

  simpl in *.
  destruct comp_eq_ptr8_zero.
  apply IHn.
  specialize (IHn H0).
  assumption.

  remember (MyMemRegionsIndexnat (bpf_mrs st1) n) as mr.

  (**r we rely on the fact if Heqmr get the default memory region, check_mem_aux2P should return Vnullptr! *)
  assert (Hdefault: check_mem_aux2P default_memory_region Writable (Vint vi) chunk = Vnullptr). {
    unfold check_mem_aux2P, default_memory_region.
    unfold start_addr, block_size, block_perm, block_ptr.
    Transparent Archi.ptr64.
    assert (Hnullptr: Vint Int.zero = Vnullptr). {
      unfold Vnullptr; reflexivity.
    }
    rewrite <- Hnullptr; clear Hnullptr.
    assert (Hperm: perm_ge Nonempty Writable = false). {
      unfold perm_ge.
      unfold Mem.perm_order_dec.
      reflexivity.
    }
    rewrite Hperm; clear Hperm.
    destruct_if; try reflexivity.
  }
  rewrite H0.

  unfold memory_inv in Hmem_inv.
  unfold MyMemRegionsIndexnat in Heqmr.

  unfold State.eval_mem_regions, Memory_regions.index_nat in Heqmr.
  assert (Hin_mem_regions: List.In mr (bpf_mrs st1)). {
    destruct nth_error eqn: Hnth_error.
    + apply List.nth_error_In in Hnth_error.
      subst.
      assumption.
    + subst.
      rewrite Hdefault in Hneq; exfalso; apply Hneq; reflexivity.
  }
  (**r now we get the evidence `In mr (bpf_mrs st1)`, and reuse the lemma `In_inv_memory_regions` *)
  apply In_inv_memory_regions with (m:=bpf_m st1) in Hin_mem_regions; [| intuition].
  assert (Hperm_w: perm_order (block_perm mr) Writable). {
    unfold check_mem_aux2P in H0.
    rewrite Hwell_chunk in H0.
    destruct ((compu_le_32 Vzero (Val.sub (Vint vi) (start_addr mr)) &&
         compu_lt_32
           (Val.add (Val.sub (Vint vi) (start_addr mr))
              (memory_chunk_to_valu32 chunk)) (block_size mr))%bool); [| rewrite H0 in Hneq; exfalso; apply Hneq; reflexivity].
    destruct ((compu_le_32 (Val.sub (Vint vi) (start_addr mr))
          (memory_chunk_to_valu32_upbound chunk) &&
        comp_eq_32 Vzero
          (val32_modu (Val.sub (Vint vi) (start_addr mr))
             (memory_chunk_to_valu32 chunk)))%bool); [| rewrite H0 in Hneq; exfalso; apply Hneq; reflexivity].
    unfold perm_ge in H0.
    destruct Mem.perm_order_dec eqn: Hp.
    assumption.
    rewrite H0 in Hneq; exfalso; apply Hneq; reflexivity.
  }

  assert (Hin_mem_regions' := Hin_mem_regions).
  unfold inv_memory_region in Hin_mem_regions'.

  destruct Hin_mem_regions' as (b0 & Hptr & Hvalid & Hbyte & base & len & Hstar & Hsize & Hperm & Hrange_perm).
  eapply check_mem_aux2P_spec' in H0; eauto.
  destruct H0 as (ofs & Hwell_chunk' & Hofs & Hofs_range & Hptr_eq & Hvalid_access).
  subst pt.

  apply Mem.valid_access_implies with (p2:= Writable) in Hvalid_access; [| assumption].
  eapply Mem.valid_access_store in Hvalid_access; eauto.
  destruct Hvalid_access as (m2 & Hstore).
  exists m2.
  split; [ apply Hstore | ].

  (**r prove the memory_inv *)
  unfold is_vlong_or_vint in Hvlong_vint.
  destruct v; inversion Hvlong_vint.

  - apply mem_inv_store_imm with (st1 := st1) (st2:= upd_mem m2 st1) (addr:= Vptr b0 ofs) (i:= i) in Hwell_chunk'; auto.
  unfold State.store_mem_imm, vint_to_vint_or_vlong.
  assert (Heq: match chunk with
| Mint8unsigned | Mint16unsigned | Mint32 | Mint64 =>
    match
      Mem.storev chunk (bpf_m st1) (Vptr b0 ofs)
        match chunk with
        | Mint8unsigned | Mint16unsigned | Mint32 => Vint i
        | Mint64 => Vlong (Int64.repr (Int.unsigned i))
        | _ => Vundef
        end
    with
    | Some m => Some (upd_mem m st1)
    | None => None
    end
| _ => Some (State.upd_flag Flag.BPF_ILLEGAL_MEM st1)
end = match
      Mem.storev chunk (bpf_m st1) (Vptr b0 ofs)
        match chunk with
        | Mint8unsigned | Mint16unsigned | Mint32 => Vint i
        | Mint64 => Vlong (Int64.repr (Int.unsigned i))
        | _ => Vundef
        end
    with
    | Some m => Some (upd_mem m st1)
    | None => None
    end). {
      destruct chunk; try inversion Hwell_chunk'; try reflexivity.
    }
    rewrite Heq; clear Heq.
    unfold Mem.storev.
    unfold vlong_or_vint_to_vint_or_vlong, vint_to_vint_or_vlong in Hstore.
    rewrite Hstore.
    reflexivity.
  - unfold vlong_or_vint_to_vint_or_vlong, vlong_to_vint_or_vlong in Hstore.
    apply mem_inv_store_reg with (st1 := st1) (st2:= upd_mem m2 st1) (addr:= Vptr b0 ofs) (src:= i) in Hwell_chunk'; auto.
  unfold State.store_mem_reg, vlong_to_vint_or_vlong.
    destruct chunk; try inversion Hwell_chunk'; simpl.
    all: try (rewrite Hstore; reflexivity).
Qed.
