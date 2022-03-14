From compcert Require Import Integers Values Memory AST.
From bpf.comm Require Import State Monad.
From bpf.comm Require Import MemRegion rBPFMemType rBPFAST rBPFValues.
From bpf.model Require Import Syntax Semantics.
From bpf.isolation Require Import CommonISOLib AlignChunk RegsInv MemInv VerifierInv.

From Coq Require Import ZArith List Lia.
Import ListNotations.

Open Scope Z_scope.

Global Transparent Archi.ptr64.

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

Ltac destruct_ifN Hname :=
  match goal with
  | |- context [if ?X then _ else _] =>
    destruct X eqn: Hname
  end.



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

Definition check_mem_aux2P (mr: memory_region) (perm: permission) (addr: val) (chunk: memory_chunk): val := (*
  if is_well_chunk_boolP chunk then *)
    let start  := start_addr mr in
    let size   := block_size mr in
    let mr_perm:= block_perm mr in
    let lo_ofs := Val.sub addr start in
    let hi_ofs := Val.add lo_ofs (memory_chunk_to_valu32 chunk) in
      if andb (andb
                  (compu_lt_32 hi_ofs size)
                  (andb (compu_le_32 lo_ofs (memory_chunk_to_valu32_upbound chunk))
                        (comp_eq_32 Vzero (val32_modu lo_ofs (memory_chunk_to_valu32 chunk)))))
                (perm_ge mr_perm perm) then
        Val.add (block_ptr mr) lo_ofs (**r Vptr b lo_ofs *)
      else
        Vnullptr. (*
    else
      Vnullptr.*)

Lemma check_mem_aux2M_P:
  forall mr perm addr chunk st,
    check_mem_aux2 mr perm addr chunk st = Some (check_mem_aux2P mr perm addr chunk, st).
Proof.
  unfold check_mem_aux2, check_mem_aux2P.
  unfold get_start_addr, get_block_size, get_sub, get_add, get_block_perm.
  unfold_monad.
  intros.
  destruct_if; reflexivity.
Qed.

Lemma mem_inv_check_mem_aux2P_valid_pointer:
  forall mr p c v st v'
    (Hmem : memory_inv st)
    (Hin_mem_regions: In mr (bpf_mrs st))
    (Hcheck_mem_aux2P: check_mem_aux2P mr p (Vint c) v = v'),
      (exists b ofs, v' = Vptr b ofs /\ (Mem.valid_pointer (bpf_m st) b (Ptrofs.unsigned ofs)
    || Mem.valid_pointer (bpf_m st) b (Ptrofs.unsigned ofs - 1))%bool = true)
        \/ v' = Vnullptr.
Proof.
  intros.
  unfold memory_inv in Hmem.
  destruct Hmem as (Hlen_low & Hlen & Hdisjoint & Hinv_mem).
  eapply In_inv_memory_regions in Hinv_mem; eauto.
  unfold inv_memory_region in Hinv_mem.
  destruct Hinv_mem as (b & Hptr & Hvalid & His_byte & (start & size & Hstart & Hsize & Hperm & Hrange_perm)).
  unfold Mem.range_perm in Hrange_perm.

  unfold check_mem_aux2P in Hcheck_mem_aux2P.
  unfold is_well_chunk_boolP, compu_lt_32, memory_chunk_to_valu32, compu_le_32, memory_chunk_to_valu32_upbound, comp_eq_32, Vzero, val32_modu, memory_chunk_to_valu32, perm_ge, Vnullptr in Hcheck_mem_aux2P.
  rewrite Hptr, Hstart, Hsize in Hcheck_mem_aux2P.
  revert Hcheck_mem_aux2P.

  assert (Heq: Ptrofs.unsigned (Ptrofs.repr (Int.unsigned (Int.sub c start))) = Int.unsigned (Int.sub c start)). {
    rewrite Ptrofs.unsigned_repr; [reflexivity|].
    change Ptrofs.max_unsigned with Int.max_unsigned.
    apply Int.unsigned_range_2.
  }
  assert (Hle: 0 <= Int.unsigned (Int.sub c start)). {
    assert (Hle1: 0 <= Int.unsigned (Int.sub c start) <= Int.max_unsigned).
    apply Int.unsigned_range_2.
    lia.
  }
  destruct v; simpl.
  all: try (intro Hcheck_mem_aux2P; inversion Hcheck_mem_aux2P; right; reflexivity).
  all: destruct_ifN Hcond; try (unfold Ptrofs.of_int; rewrite Ptrofs.add_zero_l; intro Hcheck_mem_aux2P; try inversion Hcheck_mem_aux2P).
  all: try (intro H; inversion H; right; reflexivity).
  all: left;
    eexists; eexists; split; [ reflexivity |];
    rewrite Bool.orb_true_iff; left;
    rewrite Mem.valid_pointer_nonempty_perm;
    apply Mem.perm_implies with (p1 := MemRegion.block_perm mr); [ | constructor];
    apply Hrange_perm;
    repeat rewrite Bool.andb_true_iff in Hcond.
    all: rewrite Heq; clear Heq;
    split; [ assumption|];
    destruct Hcond as ((Hcond & Hcond0 & _) & _);
    unfold Int.add in Hcond;
    apply Clt_Zlt_iff in Hcond;
    apply Cle_Zle_iff in Hcond0.
Ltac change_const :=
  let I := fresh "I" in
    repeat match goal with
    | H0: Int.unsigned (Int.sub _ _) <= Int.unsigned (Int.repr ?X) |- _ =>
      change (Int.unsigned (Int.repr X)) with X in H0
    | H1: Int.unsigned
            (Int.repr
               (Int.unsigned (Int.sub ?X ?Z) + Int.unsigned (Int.repr ?Y))) <
          Int.unsigned ?W |- _ =>
      change (Int.unsigned (Int.repr Y)) with Y in H1;
      assert (I: Int.unsigned (Int.repr (Int.unsigned (Int.sub X Z) + Y)) = Int.unsigned (Int.sub X Z) + Y); [
      rewrite Int.unsigned_repr; [reflexivity | change Int.max_unsigned with 4294967295; lia] |
      rewrite I in H1; lia
    ]
    end.
    all: change_const.
Qed.

Fixpoint check_mem_auxP (st: state) (num: nat) (perm: permission) (chunk: memory_chunk) (addr: val) (mrs: MyMemRegionsType) {struct num}: val :=
  match num with
  | O => Vnullptr
  | S n =>
    let cur_mr    := MyMemRegionsIndexnat mrs n in
    let check_mem := check_mem_aux2P cur_mr perm addr chunk in
      match cmp_ptr32_null (bpf_m st) check_mem with
      | Some res =>
        if res then
          check_mem_auxP st n perm chunk addr mrs
        else
          check_mem
      | None => check_mem
      end
  end.

Lemma check_mem_auxM_P:
  forall n perm chunk addr st
    (Hlt: (n <= mrs_num st)%nat)
    (Hperm: perm_order perm Readable)
    (Hmem_inv : memory_inv st),
    check_mem_aux n perm chunk (Vint addr) (bpf_mrs st) st = Some (check_mem_auxP st n perm chunk (Vint addr) (bpf_mrs st), st).
Proof.
  unfold check_mem_aux, get_mem_region, eval_mrs_regions, check_mem_auxP.
  unfold_monad.
  intros.
  induction n.
  reflexivity.
  assert (Hlt': (n < mrs_num st)%nat) by lia.
  assert (Hlt'': (n <= mrs_num st)%nat) by lia.
  specialize (IHn Hlt''); clear Hlt''.
  rewrite <- Nat.ltb_lt in Hlt'.
  rewrite Hlt'.
  rewrite Nat.ltb_lt in Hlt'.
  set (Hmem_inv' := Hmem_inv).
  unfold memory_inv in Hmem_inv'.
  destruct Hmem_inv' as (_ & Hlen & _ & _).
  rewrite <- Hlen in Hlt'.
  apply nth_error_nth' with (d:= default_memory_region) in Hlt'.
  rewrite Hlt'.
  rewrite check_mem_aux2M_P.
  unfold cmp_ptr32_nullM, State.eval_mem.

  assert (Hcmp: exists res, cmp_ptr32_null (bpf_m st)
      (check_mem_aux2P (MyMemRegionsIndexnat (bpf_mrs st) n) perm 
         (Vint addr) chunk) = Some res). {
    remember (MyMemRegionsIndexnat _ _) as mr.
    unfold MyMemRegionsIndexnat, Memory_regions.index_nat in Heqmr.
    destruct (nth_error _ _) eqn: Hnth_error.
    (**r considering two cases: (MyMemRegionsIndexnat (bpf_mrs st) n) =? In mr (bpf_mr st) \/ default_memory_region *)
    - subst m.
      apply List.nth_error_In in Hnth_error.
      eapply mem_inv_check_mem_aux2P_valid_pointer with (p:= perm) (c:= addr) (v:= chunk) in Hnth_error; eauto.
      destruct Hnth_error as [ Hnth_0 | Hnth_1].
      + destruct Hnth_0 as (b & ofs & Hcheck_mem_aux2P & Hvalid).
        rewrite Hcheck_mem_aux2P.
        unfold cmp_ptr32_null; simpl.
        rewrite Hvalid.
        exists false.
        rewrite Int.eq_true.
        rewrite Bool.andb_true_l.
        reflexivity.
      + unfold cmp_ptr32_null; simpl.
        rewrite Hnth_1.
        unfold Vnullptr; simpl.
        exists true.
        rewrite Int.eq_true.
        reflexivity.
    - subst.
      unfold check_mem_aux2P, default_memory_region.
      unfold start_addr, block_size, block_perm, block_ptr.
      assert (Hnullptr: Vint Int.zero = Vnullptr). {
        unfold Vnullptr; reflexivity.
      }
      rewrite <- Hnullptr; clear Hnullptr.
      assert (Hperm_ge: perm_ge Nonempty perm = false). {
        unfold perm_ge.
        unfold Mem.perm_order_dec.
        destruct perm; try reflexivity.
        inversion Hperm.
      }
      rewrite Hperm_ge; clear Hperm_ge.
      rewrite Bool.andb_false_r.
      destruct_if; try reflexivity.
      all: unfold cmp_ptr32_null; simpl;
      exists true;
      rewrite Int.eq_true;
      reflexivity.
  }

  destruct Hcmp as (res & Hcmp).
  assert (Heq: MyMemRegionsIndexnat (bpf_mrs st) n = nth n (bpf_mrs st) default_memory_region). {
    unfold MyMemRegionsIndexnat, Memory_regions.index_nat.
    rewrite Hlt'.
    reflexivity.
  }
  rewrite <- Heq; clear Heq.
  rewrite Hcmp.
  destruct res; [ | reflexivity].
  unfold cmp_ptr32_nullM, State.eval_mem in IHn.
  rewrite IHn.
  reflexivity.
Qed.

Definition check_memP (perm: permission) (chunk: memory_chunk) (addr: val) (st: State.state): val :=
  let well_chunk := is_well_chunk_boolP chunk in
    if well_chunk then
      let mem_reg_num := eval_mem_num st in
      let mrs         := State.eval_mem_regions st in
      let check_mem  := check_mem_auxP st mem_reg_num perm chunk addr mrs in
        match cmp_ptr32_null (bpf_m st) check_mem with
        | Some res =>
          if res then
            Vnullptr
          else
            check_mem
        | None => Vnullptr
        end
      else
        Vnullptr.

Lemma mem_inv_check_mem_auxP_valid_pointer:
  forall st perm chunk addr v
    (Hperm: perm_order perm Readable)
    (Hmem : memory_inv st)
    (Hcheck_mem_auxP: check_mem_auxP st (mrs_num st) perm chunk (Vint addr) (bpf_mrs st) = v),
      (exists b ofs, v = Vptr b ofs /\ (Mem.valid_pointer (bpf_m st) b (Ptrofs.unsigned ofs) || Mem.valid_pointer (bpf_m st) b (Ptrofs.unsigned ofs - 1) = true)%bool)
        \/ v = Vnullptr.
Proof.
  intros.

  induction (mrs_num st).
  simpl in Hcheck_mem_auxP.
  subst. right; reflexivity.

  simpl in Hcheck_mem_auxP.

  destruct (cmp_ptr32_null _ _) eqn: Hcmp.
  - destruct b eqn: Hb.
    + apply IHn.
      assumption.
    + unfold cmp_ptr32_null in Hcmp.
      unfold Val.cmpu_bool, Vnullptr in Hcmp; simpl in Hcmp.
      rewrite Hcheck_mem_auxP in Hcmp.
      destruct v; try inversion Hcmp.
      * eapply mem_inv_check_mem_aux2P_valid_pointer in Hcheck_mem_auxP; eauto.
        unfold MyMemRegionsIndexnat, Memory_regions.index_nat in *.
        assert (Hmem' := Hmem).
        destruct Hmem' as (Hlen & Hdisjoint & Hmem').
        destruct nth_error eqn: Hnth; unfold check_mem_aux2P in Hcheck_mem_auxP.
        ** apply nth_error_In in Hnth.
           assumption.
        ** exfalso; unfold default_memory_region, start_addr, block_size, block_perm, block_ptr in Hcheck_mem_auxP.
           assert (Hperm_ge: perm_ge Nonempty perm = false). {
             unfold perm_ge; destruct perm; try constructor.
             inversion Hperm.
           }
           rewrite Hperm_ge in Hcheck_mem_auxP; clear Hperm_ge.
           rewrite Bool.andb_false_r in Hcheck_mem_auxP.
           destruct is_well_chunk_boolP; change Vnullptr with (Vint Int.zero) in *;inversion Hcheck_mem_auxP; subst; rewrite Int.eq_true in H0; inversion H0.
      * left.
        exists b0, i.
        split; [reflexivity | ].
        rewrite Int.eq_true in H0.
        rewrite Bool.andb_true_l in H0.
        destruct (Mem.valid_pointer _ _ _ || Mem.valid_pointer _ _ _)%bool eqn: Hvalid; [reflexivity| inversion H0].
    - unfold cmp_ptr32_null, Val.cmpu_bool, Vnullptr in Hcmp; simpl in Hcmp.
      rewrite Hcheck_mem_auxP in Hcmp.
      assert (Hcheck_mem_auxP' := Hcheck_mem_auxP).
      assert (Hmem' := Hmem).
      destruct Hmem' as (_ & Hlen & Hdisjoint & Hmem').
      unfold MyMemRegionsIndexnat, Memory_regions.index_nat in Hcheck_mem_auxP, Hcheck_mem_auxP'.
      unfold check_mem_aux2P in Hcheck_mem_auxP.
      destruct v; try inversion Hcmp;
      change Vnullptr with (Vint Int.zero) in *. (*
      all: destruct is_well_chunk_boolP; [| inversion Hcheck_mem_auxP]. *)
      all: match goal with
           | H: (if ?X then _ else _) = _ |- _ =>
              destruct X; [| inversion H]
           end.
      5:{ inversion H0. }
      5:{
        destruct nth_error eqn: Hnth; [
        apply nth_error_In in Hnth;
        eapply In_inv_memory_regions in Hmem'; eauto; unfold inv_memory_region in Hmem';
        destruct Hmem' as (b' & Hptr & Hvalid & Hbyte & (start & len & Hstart & Hsize & Hperm_order & Hrange));
        rewrite Hptr, Hstart in Hcheck_mem_auxP |
        unfold default_memory_region, start_addr, block_size, block_perm, block_ptr in Hcheck_mem_auxP;
        change Vnullptr with (Vint Int.zero) in Hcheck_mem_auxP]. 2:{
          assert (Hperm_ge: perm_ge Nonempty perm = false). {
            unfold perm_ge; destruct perm; try constructor.
            inversion Hperm.
          }
          rewrite Hperm_ge in Hcheck_mem_auxP; clear Hperm_ge.
          rewrite Bool.andb_false_r in Hcheck_mem_auxP.
          inversion Hcheck_mem_auxP.
        }
        eapply mem_inv_check_mem_aux2P_valid_pointer in Hcheck_mem_auxP'; eauto.
      }
      all: destruct nth_error eqn: Hnth; [apply nth_error_In in Hnth;
      eapply In_inv_memory_regions in Hmem'; eauto; unfold inv_memory_region in Hmem';
      destruct Hmem' as (b' & Hptr & Hvalid & Hbyte & (start & len & Hstart & Hsize & Hperm_order & Hrange));
      rewrite Hptr, Hstart in Hcheck_mem_auxP; inversion Hcheck_mem_auxP |
      unfold default_memory_region, start_addr, block_size, block_perm, block_ptr in Hcheck_mem_auxP;
      change Vnullptr with (Vint Int.zero) in Hcheck_mem_auxP;
      inversion Hcheck_mem_auxP
      ].
Qed.

Lemma check_memM_P:
  forall perm chunk addr st
    (Hperm: perm_order perm Readable)
    (Hmem_inv : memory_inv st),
    check_mem perm chunk (Vint addr) st = Some (check_memP perm chunk (Vint addr) st, st).
Proof.
  unfold check_mem, eval_mrs_num, eval_mrs_regions, check_memP, cmp_ptr32_nullM, State.eval_mem, State.eval_mem_regions, eval_mem_num.
  unfold_monad.
  intros.
  rewrite is_well_chunk_boolM_P.
  destruct is_well_chunk_boolP; try reflexivity.
  rewrite check_mem_auxM_P; auto.
  remember (check_mem_auxP st (mrs_num st) perm chunk (Vint addr) (bpf_mrs st)) as res.
  symmetry in Heqres.
  eapply mem_inv_check_mem_auxP_valid_pointer in Heqres; eauto.
  destruct Heqres as [(b & ofs & Hptr & Hvalid) | Hnull]; subst; unfold cmp_ptr32_null, Val.cmpu_bool; change Vnullptr with (Vint Int.zero) in *; simpl; rewrite Int.eq_true.
  - rewrite Hvalid; simpl; reflexivity.
  - reflexivity.
Qed.

Lemma well_chunk_iff:
  forall chunk,
    is_well_chunk chunk <-> is_well_chunk_boolP chunk = true.
Proof.
  unfold is_well_chunk, is_well_chunk_boolP.
  intros.
  destruct chunk; split; try constructor; intro H; inversion H.
Qed.


Lemma check_mem_aux2P_spec:
  forall mr chunk st1 p base len b vi ptr
    (Hwell_chunk: is_well_chunk chunk)
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
  intros. (*
  destruct is_well_chunk_boolP eqn: Hwell_chunk; [| rewrite H0 in Hneq; exfalso; apply Hneq; reflexivity]. *)
  rewrite Hptr, Hstar, Hsize in *.
  unfold Val.add, Val.sub in H0.
  rewrite Ptrofs.add_zero_l in H0.
  exists (Ptrofs.of_int (Int.sub vi base)).
  split.
  assumption.

  unfold compu_lt_32, compu_le_32, memory_chunk_to_valu32, memory_chunk_to_valu32_upbound, comp_eq_32,
  val32_modu, Val.add, Val.sub, Vzero in H0.
  match goal with
  | H: (if ?X then _ else _) = _ |- _ =>
    destruct X eqn: Hcmp
  end.
  2:{ exfalso; apply Hneq; rewrite H0; reflexivity. }
  
  simpl in H0.
  subst.
  split; [reflexivity | ].

  rewrite Ptrofs.agree32_of_int; [| reflexivity].

  (**r with the fact `is_well_chunk_boolP`, we get the following lemma *)
  assert (Heq_well_chunk: well_chunk_Z chunk = size_chunk chunk). {
    unfold is_well_chunk_boolP in Hwell_chunk.
    destruct chunk; try inversion Hwell_chunk.
    all: unfold well_chunk_Z, size_chunk; reflexivity.
  }
  rewrite Heq_well_chunk in *; clear Heq_well_chunk.

  apply andb_prop in Hcmp.
  destruct Hcmp as (Hcmp & Hperm_ge).
  apply andb_prop in Hcmp.
  destruct Hcmp as (Hlow & Hcmp).
  apply andb_prop in Hcmp.
  destruct Hcmp as (Hhigh & Hmod).

  (**r Hlow is for _ <= _ < _ and Hhigh is for valid_access *)
  apply (hi_ofs_max_unsigned (Int.sub vi base) chunk) in Hhigh.
  apply Clt_implies_Zlt_add in Hlow as Hlow'; [| assumption].
  split; [ assumption | ].

  split.
  reflexivity.

  unfold Mem.valid_access.
  split.
  eapply range_perm_included; eauto.
  apply Int_unsigned_ge_0.
  apply Int_unsigned_ofs_size_chunk_ge_0.
  intuition.

  destruct Val.modu eqn: Hmod1; [| inversion Hmod].
  destruct v; try inversion Hmod.
  unfold Val.modu in Hmod1.
  destruct Int.eq eqn: Hmod2; [inversion Hmod1|].
  eapply modu_zero_is_aligned; eauto.
  inversion Hmod1.
  rewrite <- H1 in H0.
  assumption.
Qed.

Lemma mem_inv_check_mem_valid_pointer:
  forall st perm chunk addr v
    (Hperm: perm_order perm Readable)
    (Hmem : memory_inv st)
    (Hcheck_memP: check_memP perm chunk (Vint addr) st = v),
      (exists b ofs, v = Vptr b ofs /\ (Mem.valid_pointer (bpf_m st) b (Ptrofs.unsigned ofs) || Mem.valid_pointer (bpf_m st) b (Ptrofs.unsigned ofs - 1) = true)%bool)
        \/ v = Vnullptr.
Proof.
  unfold check_memP; intros.
  unfold is_well_chunk_boolP in Hcheck_memP.
  unfold cmp_ptr32_null in Hcheck_memP.
  unfold Val.cmpu_bool in Hcheck_memP.
  unfold State.eval_mem_regions in Hcheck_memP.
  remember (check_mem_auxP st (eval_mem_num st) perm chunk (Vint addr) (bpf_mrs st)) as res.
  symmetry in Heqres.
  eapply mem_inv_check_mem_auxP_valid_pointer with (perm:= perm) (addr := addr) in Heqres; eauto.
  change Vnullptr with (Vint (Int.zero)) in *.
  simpl in *.
  destruct chunk; try (right; symmetry; assumption).
  all: destruct Heqres as [(b & ofs & Hptr & Hvalid)| Hptr]; rewrite Hptr in *.
  all: rewrite Int.eq_true in Hcheck_memP; try rewrite Bool.andb_true_l in Hcheck_memP.
  all: try (right; symmetry; assumption).
  all: left; exists b, ofs.
  all: rewrite Hvalid in Hcheck_memP.
  all: auto.
Qed.

Lemma step_preserving_inv_alu:
  forall st1 st2 a b r s t
    (Hreg : register_inv st1)
    (Hmem : memory_inv st1)
    (Hver : verifier_inv st1)
    (Hsem : step_alu_binary_operation a b r s st1 = Some (t, st2)),
      register_inv st2 /\ memory_inv st2 /\ verifier_inv st2.
Proof.
  unfold step_alu_binary_operation; unfold_monad; intros.
  apply reg_inv_eval_reg with (r := r) in Hreg as Heval_reg;
  destruct Heval_reg as (src & Heval_reg).
  destruct a; rewrite Heval_reg in Hsem; clear Heval_reg; simpl in Hsem.
  all: destruct s.
  all: try (apply reg_inv_eval_reg with (r := r0) in Hreg as Heval_reg;
    destruct Heval_reg as (src0 & Heval_reg);
    rewrite Heval_reg in Hsem; clear Heval_reg; simpl in Hsem).
  all: destruct b; inversion Hsem; clear Hsem;
      [ split; [eapply reg_inv_upd_reg; eauto |
          split; [eapply mem_inv_upd_reg; eauto | unfold verifier_inv in *; simpl; assumption]] |
        split; [eapply reg_inv_upd_reg; eauto |
          split; [eapply mem_inv_upd_reg; eauto | unfold verifier_inv in *; simpl; assumption]] |
        split; [eapply reg_inv_upd_reg; eauto |
          split; [eapply mem_inv_upd_reg; eauto | unfold verifier_inv in *; simpl; assumption]] |

        split; (destruct negb eqn: Hnegb; [rewrite Bool.negb_true_iff in Hnegb; rewrite Hnegb in H0; simpl in H0; inversion H0 | rewrite Bool.negb_false_iff in Hnegb; inversion H0]);
        [ eapply reg_inv_upd_reg; eauto |
          eapply reg_inv_upd_flag; eauto |
          split; [eapply mem_inv_upd_reg; eauto | unfold verifier_inv in *; simpl; assumption] |
          split; [eapply mem_inv_upd_flag; eauto | unfold verifier_inv in *; simpl; assumption]] |
        split; [eapply reg_inv_upd_reg; eauto |
          split; [eapply mem_inv_upd_reg; eauto | unfold verifier_inv in *; simpl; assumption]] |
        split; [eapply reg_inv_upd_reg; eauto |
          split; [eapply mem_inv_upd_reg; eauto | unfold verifier_inv in *; simpl; assumption]] |
        split; destruct Int.ltu eqn: Hltu; simpl in H0; inversion H0; clear H0;
        [ eapply reg_inv_upd_reg; eauto |
          eapply reg_inv_upd_flag; eauto |
          split; [eapply mem_inv_upd_reg; eauto | unfold verifier_inv in *; simpl; assumption] |
          split; [eapply mem_inv_upd_flag; eauto | unfold verifier_inv in *; simpl; assumption]] |
        split; destruct Int.ltu eqn: Hltu; simpl in H0; inversion H0; clear H0;
        [ eapply reg_inv_upd_reg; eauto |
          eapply reg_inv_upd_flag; eauto |
          split; [eapply mem_inv_upd_reg; eauto | unfold verifier_inv in *; simpl; assumption] |
          split; [eapply mem_inv_upd_flag; eauto | unfold verifier_inv in *; simpl; assumption]] |
        split; (destruct negb eqn: Hnegb; [rewrite Bool.negb_true_iff in Hnegb; rewrite Hnegb in H0; simpl in H0; inversion H0 | rewrite Bool.negb_false_iff in Hnegb; inversion H0]);
        [ eapply reg_inv_upd_reg; eauto |
          eapply reg_inv_upd_flag; eauto |
          split; [eapply mem_inv_upd_reg; eauto | unfold verifier_inv in *; simpl; assumption] |
          split; [eapply mem_inv_upd_flag; eauto | unfold verifier_inv in *; simpl; assumption]] |
        split; [eapply reg_inv_upd_reg; eauto |
          split; [eapply mem_inv_upd_reg; eauto | unfold verifier_inv in *; simpl; assumption]] |
        split; [eapply reg_inv_upd_reg; eauto |
          split; [eapply mem_inv_upd_reg; eauto | unfold verifier_inv in *; simpl; assumption]] |
        split; destruct Int.ltu eqn: Hltu; simpl in H0; inversion H0; clear H0;
        [ eapply reg_inv_upd_reg; eauto |
          eapply reg_inv_upd_flag; eauto|
          split; [eapply mem_inv_upd_reg; eauto | unfold verifier_inv in *; simpl; assumption] |
          split; [eapply mem_inv_upd_flag; eauto | unfold verifier_inv in *; simpl; assumption]]].
Qed.

Lemma step_preserving_inv_branch:
  forall st1 st2 c r s o t
    (Hreg : register_inv st1)
    (Hmem : memory_inv st1)
    (Hver : verifier_inv st1)
    (Hsem : match step_branch_cond c r s st1 with
       | Some (x', st') =>
           (if x'
            then
             fun st : state =>
             if Int.cmpu Clt (Int.add (State.eval_pc st1) o)
                 (Int.repr (Z.of_nat (ins_len st)))
             then Some (tt, State.upd_pc (Int.add (State.eval_pc st1) o) st)
             else None
            else fun st : state => Some (tt, st)) st'
       | None => None
       end = Some (t, st2)),
      register_inv st2 /\ memory_inv st2 /\ verifier_inv st2.
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
    + match goal with
      | H : (if ?X then _ else _) = _ |- _ =>
        destruct X; inversion H
      end.
      split; [eapply reg_inv_upd_pc; eauto |
        split; [eapply mem_inv_upd_pc; eauto | unfold verifier_inv in *; simpl; assumption]].
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
    + match goal with
      | H : (if ?X then _ else _) = _ |- _ =>
        destruct X; inversion H
      end.
      split; [eapply reg_inv_upd_pc; eauto |
        split; [eapply mem_inv_upd_pc; eauto | unfold verifier_inv in *; simpl; assumption]].
    + subst; intuition.
Qed.

Lemma step_preserving_inv_ld:
  forall st1 st2 m r r0 o t
    (Hreg_inv : register_inv st1)
    (Hmem_inv : memory_inv st1)
    (Hver : verifier_inv st1)
    (Hsem : step_load_x_operation m r r0 o st1 = Some (t, st2)),
      register_inv st2 /\ memory_inv st2 /\ verifier_inv st2.
Proof.
  unfold step_load_x_operation; unfold_monad; intros.
  apply reg_inv_eval_reg with (r := r0) in Hreg_inv as Heval_reg;
  destruct Heval_reg as (src & Heval_reg).
  (**r addr = Vint ... *)
  rewrite Heval_reg in Hsem.
  unfold val_intuoflongu, Val.longofint, sint32_to_vint, Val.addl in Hsem.
  remember (Int.repr (Int64.unsigned (Int64.add src (Int64.repr (Int.signed o))))) as addr.

  assert (Hperm: perm_order Readable Readable). { constructor. }

  assert (Hcheck_mem: exists ret, check_mem Memtype.Readable m (Vint addr) st1 = Some (ret, st1)). {
    rewrite check_memM_P; auto.
    eexists; reflexivity.
  }
  destruct Hcheck_mem as (ret & Hcheck_mem); rewrite Hcheck_mem in Hsem; clear Hcheck_mem.
  unfold cmp_ptr32_nullM in Hsem.
  destruct cmp_ptr32_null; inversion Hsem; clear Hsem.
  destruct b; inversion H0; subst.
  - split; [eapply reg_inv_upd_flag; eauto |
      split; [eapply mem_inv_upd_flag; eauto | unfold verifier_inv in *; simpl; assumption]].
  - unfold load_mem in H1.
    destruct State.load_mem in H1; inversion H1.
    destruct v in H1; inversion H1.
    split; [eapply reg_inv_upd_reg; eauto |
      split; [eapply mem_inv_upd_reg; eauto | unfold verifier_inv in *; simpl; assumption]].
Qed.

Lemma step_preserving_inv_st:
  forall st1 st2 m r s o t
    (Hreg_inv : register_inv st1)
    (Hmem_inv : memory_inv st1)
    (Hver : verifier_inv st1)
    (Hsem : step_store_operation m r s o st1 = Some (t, st2)),
      register_inv st2 /\ memory_inv st2 /\ verifier_inv st2.
Proof.
  unfold step_store_operation; unfold_monad; intros.
  apply reg_inv_eval_reg with (r := r) in Hreg_inv as Heval_reg;
  destruct Heval_reg as (src & Heval_reg).
  (**r addr = Vint ... *)
  rewrite Heval_reg in Hsem.
  unfold val_intuoflongu, Val.longofint, sint32_to_vint, Val.addl in Hsem.
  remember (Int.repr (Int64.unsigned (Int64.add src (Int64.repr (Int.signed o))))) as addr.

  assert (Hperm: perm_order Writable Readable). { constructor. }
  assert (Hcheck_mem: exists ret, check_mem Writable m (Vint addr) st1 = Some (ret, st1)). {
    rewrite check_memM_P; auto.
    eexists; reflexivity.
  }

  destruct s; destruct Hcheck_mem as (ret & Hcheck_mem); rewrite Hcheck_mem in Hsem;
  unfold cmp_ptr32_nullM in Hsem;
  (destruct cmp_ptr32_null eqn: Hptr; [| inversion Hsem]).
  - (**r inl r *)
    destruct b; inversion Hsem; subst.
    + split; [eapply reg_inv_upd_flag; eauto |
        split; [eapply mem_inv_upd_flag; eauto | unfold verifier_inv in *; simpl; assumption]].
    + clear H0.
      (**r from the fact Hptr and Hcheck_mem, we know Hwell_chunk *)
      assert (Hwell_chunk: is_well_chunk m). {
        unfold rBPFValues.cmp_ptr32_null in Hptr.
        unfold check_mem, bindM, returnM in Hcheck_mem.
        destruct m; simpl in Hcheck_mem; inversion Hcheck_mem; unfold Vnullptr in *; subst; simpl in Hptr;
        try (rewrite Int.eq_true in Hptr; inversion Hptr).
        all: unfold is_well_chunk; try constructor.
      }
      apply reg_inv_eval_reg with (r := r0) in Hreg_inv as Heval_reg0;
      destruct Heval_reg0 as (src0 & Heval_reg0).
      rewrite Heval_reg0 in Hsem; clear Heval_reg0; simpl in Hsem.
      unfold store_mem_reg in Hsem.
      destruct State.store_mem_reg eqn: Hstore; [| inversion Hsem].
      inversion Hsem; subst.
      split; [eapply reg_inv_store_reg; eauto |
        split; [eapply mem_inv_store_reg; eauto | unfold verifier_inv in *; simpl]].
      unfold State.store_mem_reg in Hstore.
      destruct m; try inversion Hstore.
      all: destruct Mem.storev in Hstore; inversion Hstore.
      all: simpl; assumption.

  - (**r inr i *)
    destruct b; inversion Hsem; subst.
    + split; [eapply reg_inv_upd_flag; eauto |
        split; [ eapply mem_inv_upd_flag; eauto | unfold verifier_inv in *; simpl; assumption]].
    +
      (**r from the fact Hptr and Hcheck_mem, we know Hwell_chunk *)
      assert (Hwell_chunk: is_well_chunk m). {
        unfold rBPFValues.cmp_ptr32_null in Hptr.
        unfold check_mem, bindM, returnM in Hcheck_mem.
        destruct m; simpl in Hcheck_mem; inversion Hcheck_mem; unfold Vnullptr in *; subst; simpl in Hptr;
        try (rewrite Int.eq_true in Hptr; inversion Hptr).
        all: unfold is_well_chunk; constructor.
      }
      unfold rBPFValues.sint32_to_vint, store_mem_imm in Hsem.
      destruct State.store_mem_imm eqn: Hstore; [| inversion Hsem].
      inversion Hsem; subst.
      split; [eapply reg_inv_store_imm; eauto |
        split; [eapply mem_inv_store_imm; eauto | unfold verifier_inv in *; simpl]].
      unfold State.store_mem_imm in Hstore.
      destruct m; try inversion Hstore.
      all: destruct Mem.storev in Hstore; inversion Hstore.
      all: simpl; assumption.
Qed.

Lemma check_mem_load:
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
  rewrite check_memM_P in Hcheck_mem; auto.
  2:{ constructor. }
  inversion Hcheck_mem; clear Hcheck_mem.

  unfold check_memP in *.
  rewrite well_chunk_iff in Hwell_chunk.
  rewrite Hwell_chunk in *.
  change Vnullptr with (Vint Int.zero) in *.
  destruct cmp_ptr32_null eqn: Hcmp; [| rewrite H0 in Hneq; exfalso; apply Hneq; reflexivity].
  destruct b; [rewrite H0 in Hneq; exfalso; apply Hneq; reflexivity | ].

  unfold eval_mem_num, State.eval_mem_regions in *.

  induction (mrs_num st1).
  { (**r  mrs_num st1 = 0 *)
    simpl in H0.
    change Vnullptr with (Vint Int.zero) in H0.
    rewrite H0 in Hneq.
    exfalso; apply Hneq; reflexivity.
  }

  simpl in *.
  destruct (cmp_ptr32_null _ (check_mem_aux2P _ _ _ _))eqn: Hcmp1;
  [| rewrite Hcmp1 in Hcmp ]; inversion Hcmp.
  destruct b.
  {
    apply IHn; auto.
  }
  rewrite H0.

  unfold MyMemRegionsIndexnat, Memory_regions.index_nat in H0.
  destruct nth_error eqn: Hnth.
  2:{ (**r it is impossible to return Vptr b ofs in H0 *)
    unfold default_memory_region, check_mem_aux2P in H0.
    unfold compu_lt_32, compu_le_32, memory_chunk_to_valu32, memory_chunk_to_valu32_upbound, comp_eq_32,
  val32_modu, Val.add, Val.sub, Vzero, start_addr, block_size, block_perm, block_ptr in H0.
    change Vnullptr with (Vint Int.zero) in H0.
    match goal with
    | H: (if ?X then _ else _) = _ |- _ =>
      destruct X eqn: Heq; [ | rewrite H0 in Hneq; exfalso; apply Hneq; reflexivity]
    end.
    assert (Hperm_ge: perm_ge Nonempty Readable = false). {
      unfold perm_ge; constructor.
    }
    rewrite Hperm_ge in Heq; clear Hperm_ge.
    rewrite Bool.andb_false_r in Heq.
    inversion Heq.
  }

  apply nth_error_In in Hnth.
  destruct Hmem_inv as (_ & Hlen & Hdisjoint & Hmem_inv).
  (**r now we get the evidence `In mr (bpf_mrs st1)`, and reuse the lemma `In_inv_memory_regions` *)
  apply In_inv_memory_regions with (m:=bpf_m st1) (mr := m) in Hmem_inv; [| intuition].
  assert (Hmem_inv' := Hmem_inv).
  unfold inv_memory_region in Hmem_inv'.

  destruct Hmem_inv' as (b0 & Hptr & Hvalid & Hbyte & base & len & Hstar & Hsize & Hperm & Hrange_perm).
  eapply check_mem_aux2P_spec in H0; eauto.
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
  apply well_chunk_iff; assumption.
Qed.

Definition vlong_or_vint_to_vint_or_vlong (chunk: memory_chunk) (v: val): val :=
  match v with
  | Vlong n => vlong_to_vint_or_vlong chunk v
  | Vint  n => vint_to_vint_or_vlong chunk v
  | _       => Vundef
  end.

Lemma check_mem_store:
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
  rewrite check_memM_P in Hcheck_mem; auto.
  2:{ constructor. }
  inversion Hcheck_mem; clear Hcheck_mem.

  unfold check_memP in *.
  rewrite well_chunk_iff in Hwell_chunk.
  rewrite Hwell_chunk in *.
  change Vnullptr with (Vint Int.zero) in *.
  destruct cmp_ptr32_null eqn: Hcmp; [| rewrite H0 in Hneq; exfalso; apply Hneq; reflexivity].
  destruct b; [rewrite H0 in Hneq; exfalso; apply Hneq; reflexivity | ].

  unfold eval_mem_num, State.eval_mem_regions in *.

  induction (mrs_num st1).
  { (**r  mrs_num st1 = 0 *)
    simpl in H0.
    change Vnullptr with (Vint Int.zero) in H0.
    rewrite H0 in Hneq.
    exfalso; apply Hneq; reflexivity.
  }

  simpl in *.
  destruct (cmp_ptr32_null _ (check_mem_aux2P _ _ _ _))eqn: Hcmp1;
  [| rewrite Hcmp1 in Hcmp ]; inversion Hcmp.
  destruct b.
  {
    apply IHn; auto.
  }
  rewrite H0.

  unfold MyMemRegionsIndexnat, Memory_regions.index_nat in H0.
  destruct nth_error eqn: Hnth.
  2:{ (**r it is impossible to return Vptr b ofs in H0 *)
    unfold default_memory_region, check_mem_aux2P in H0.
    unfold compu_lt_32, compu_le_32, memory_chunk_to_valu32, memory_chunk_to_valu32_upbound, comp_eq_32,
  val32_modu, Val.add, Val.sub, Vzero, start_addr, block_size, block_perm, block_ptr in H0.
    change Vnullptr with (Vint Int.zero) in H0.
    match goal with
    | H: (if ?X then _ else _) = _ |- _ =>
      destruct X eqn: Heq; [ | rewrite H0 in Hneq; exfalso; apply Hneq; reflexivity]
    end.
    assert (Hperm_ge: perm_ge Nonempty Writable = false). {
      unfold perm_ge; constructor.
    }
    rewrite Hperm_ge in Heq; clear Hperm_ge.
    rewrite Bool.andb_false_r in Heq.
    inversion Heq.
  }

  apply nth_error_In in Hnth.
  assert (Hmem_inv' := Hmem_inv).
  destruct Hmem_inv' as (_ & Hlen & Hdisjoint & Hmem_inv').
  (**r now we get the evidence `In mr (bpf_mrs st1)`, and reuse the lemma `In_inv_memory_regions` *)
  apply In_inv_memory_regions with (m:=bpf_m st1) (mr := m) in Hmem_inv'; [| intuition].


  destruct Hmem_inv' as (b0 & Hptr & Hvalid & Hbyte & base & len & Hstart & Hsize & Hperm & Hrange_perm).

  assert (Hperm_w: perm_order (block_perm m) Writable). {
    unfold check_mem_aux2P in H0.
    rewrite Hptr, Hstart, Hsize in H0.
    unfold compu_lt_32, compu_le_32, memory_chunk_to_valu32, memory_chunk_to_valu32_upbound, comp_eq_32,
    val32_modu, Val.add, Val.sub, Vzero in H0.
    change Vnullptr with (Vint Int.zero) in H0.

    clear Hcmp1.
    match goal with
    | H: (if ?X then _ else _) = _ |- _ =>
      destruct X eqn: Hcmp1
    end.
    2:{ exfalso; apply Hneq; rewrite H0; reflexivity. }
    clear - Hcmp1.
    rewrite Bool.andb_true_iff in Hcmp1.
    destruct Hcmp1 as (_ & Hperm).
    unfold perm_ge in Hperm.
    destruct Mem.perm_order_dec; [ assumption | inversion Hperm].
  }

  eapply check_mem_aux2P_spec in H0; eauto.
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
    rewrite mem_inv_store_imm_well_chunk; [| rewrite well_chunk_iff; assumption].
    unfold vint_to_vint_or_vlong.

    unfold vlong_or_vint_to_vint_or_vlong, vint_to_vint_or_vlong in Hstore.
    rewrite Hstore.
    reflexivity.
  - unfold vlong_or_vint_to_vint_or_vlong, vlong_to_vint_or_vlong in Hstore.
    apply mem_inv_store_reg with (st1 := st1) (st2:= upd_mem m2 st1) (addr:= Vptr b0 ofs) (src:= i) in Hwell_chunk'; auto.
  unfold State.store_mem_reg, vlong_to_vint_or_vlong.
    destruct chunk; try inversion Hwell_chunk'; simpl.
    all: try (rewrite Hstore; reflexivity).
  - apply well_chunk_iff; assumption.
Qed.
