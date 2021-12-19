From bpf.src Require Import DxIntegers DxValues DxList64 DxMemRegion DxState DxMonad DxFlag DxRegs DxInstructions.
From Coq Require Import List Lia ZArith.
From compcert Require Import Integers Values Clight Memory.
Import ListNotations.

From bpf.proof Require Import Clightlogic MatchState CorrectRel CommonLemma.
From bpf.benchmark Require Import clightlogicexample.

(**

void step_opcode_mem_ld_imm(struct bpf_state* st, int imm, int pc, int len, unsigned int dst, unsigned char op, unsigned long long *l)
{
  unsigned char opcode_ld;
  unsigned long long next_ins;
  int next_imm;
  opcode_ld = get_opcode_mem_ld_imm(op);
  switch (opcode_ld) {
    case 24:
      if (pc + 1 < len) {
        next_ins = list_get(l, pc + 1);
        next_imm = get_immediate(next_ins);
        upd_reg(st, dst,
                (unsigned long long) (unsigned int) imm
                  | (unsigned long long) (unsigned int) next_imm << 32U);
        upd_pc_incr(st);
        upd_flag(st, 0);
        return;
      } else {
        upd_flag(st, -5);
        return;
      }
    default:
      upd_flag(st, -1);
      return;
    
  }
}

Definition step_opcode_mem_ld_imm (imm: sint32_t) (pc: sint32_t) (len: sint32_t) (dst: reg) (op: int8_t)  (l: MyListType): M unit :=
  do opcode_ld <- get_opcode_mem_ld_imm op;
  match opcode_ld with
  | op_BPF_LDDW      =>
    if (Int.lt (Int.add pc Int.one) len) then (**r pc+1 < len: pc+1 is less than the length of l *)
      do next_ins <- list_get l (Int.add pc Int.one);
      do next_imm <- get_immediate next_ins;
      do _ <- upd_reg dst (Val.or (Val.longofint (sint32_to_vint imm)) (Val.shl  (Val.longofint (sint32_to_vint next_imm)) (sint32_to_vint int32_32)));
      do _ <- upd_pc_incr;
        upd_flag BPF_OK
    else
      upd_flag BPF_ILLEGAL_LEN
  | op_BPF_LDX_IMM_ILLEGAL_INS => upd_flag BPF_ILLEGAL_INSTRUCTION
  end.

*)

Section Step_opcode_mem_ld_imm.

  (** The program contains our function of interest [fn] *)
  Definition p : Clight.program := prog.

  (* [Args,Res] provides the mapping between the Coq and the C types *)
  (* Definition Args : list CompilableType := [stateCompilableType].*)
  Definition args : list Type := [(sint32_t:Type); (sint32_t:Type); (sint32_t:Type); (reg:Type); (int8_t:Type); (MyListType:Type)].
  Definition res : Type := unit.

  (* [f] is a Coq Monadic function with the right type *)
  Definition f : arrow_type args (M res) := step_opcode_mem_ld_imm.

  Variable state_block: block. (**r a block storing all rbpf state information? *)
  Variable ins_block: block.
  Variable ins_block_length: nat.

  (* [fn] is the Cligth function which has the same behaviour as [f] *)
  Definition fn: Clight.function := f_step_opcode_mem_ld_imm.

  Definition modifies : list block := [state_block]. (* of the C code *)

  Definition stateM_correct (st:unit) (v: val) (stm:stateM) (m: Memory.Mem.mem) :=
    v = Vptr state_block Ptrofs.zero /\ match_state state_block stm m.

  (* [match_arg] relates the Coq arguments and the C arguments *)
  Definition match_arg_list : DList.t (fun x => x -> val -> stateM -> Memory.Mem.mem -> Prop) ((unit:Type) ::args) :=
    (DList.DCons stateM_correct
                (DList.DCons (stateless sint32_correct)
                (DList.DCons (stateless (pc_correct ins_block_length))
                (DList.DCons (stateless (len_correct ins_block_length))
                (DList.DCons (stateless reg_correct)
                (DList.DCons (stateless int8_correct)
                (DList.DCons (MyListType_correct ins_block ins_block_length)
                             (DList.DNil _)))))))).



Ltac build_app_aux T :=
  match T with
  | ?F ?X => let ty := type of X in
             let r := build_app_aux F in
             constr:((mk ty X) :: r)
  | ?X    => constr:(@nil dpair)
  end.                                    

Ltac get_function T :=
  match T with
  | ?F ?X => get_function F
  | ?X    => X
  end.

Ltac build_app T :=
  let a := build_app_aux T in
  let v := (eval simpl in (DList.of_list_dp (List.rev a))) in
  let f := get_function T in
  match type of v with
  | DList.t _ ?L =>
      change T with (app (f: arrow_type L _) v)
  end.

Ltac change_app_for_body :=
  match goal with
  | |- @correct_body _ _ ?F _ _ _ _ _ _ _ _
    => build_app F
  end.

Ltac change_app_for_statement :=
  match goal with
  | |- @correct_statement _ _ ?F _ _ _ _ _ _ _ _
    => build_app F
  end.

Ltac prove_incl :=
  simpl; unfold incl; simpl; intuition congruence.

Ltac prove_in_inv :=
  simpl; intuition subst; discriminate.

Ltac correct_forward :=
  match goal with
  | |- @correct_body _ _ (bindM ?F1 ?F2)  _
                     (Ssequence
                        (Ssequence
                           (Scall _ _ _)
                           (Sset ?V ?T))
                        ?R)
                     _ _ _ _ _ _  =>
      eapply correct_statement_seq_body;
      [ change_app_for_statement ;
        let b := match T with
                 | Ecast _ _ => constr:(true)
                 | _         => constr:(false)
                 end in
        eapply correct_statement_call with (has_cast := b)
      |]
  | |- @correct_body _ _ (match  ?x with true => _ | false => _ end) _
                     (Sifthenelse _ _ _)
                     _ _ _ _ _ _  =>
      eapply correct_statement_if_body; [prove_in_inv | destruct x ]
  end.


  (* [match_res] relates the Coq result and the C result *)
  Definition match_res : res -> val -> stateM -> Memory.Mem.mem -> Prop := fun x v st m => True.

  Instance correct_function3_step_opcode_mem_ld_imm : correct_function3 p args res f fn modifies false match_arg_list match_res.
  Proof.
    correct_function_from_body.
    correct_body.
    unfold INV, f, step_opcode_mem_ld_imm.
    simpl.
    correct_forward.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - typeclasses eauto.
    -  {  unfold INV.
        unfold var_inv_preserve.
        intros.
        unfold match_temp_env in *.
        rewrite Forall_fold_right in *.
        simpl in *.
        intuition. clear - H2 H.
        unfold match_elt in *;
          unfold fst in *.
        destruct (Maps.PTree.get _mr3 le);auto.
        simpl in *.
        destruct H2 ; split; auto.
        eapply same_my_memory_match_region;eauto.
      }
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - prove_in_inv.
    - prove_in_inv.
    - reflexivity.
    - reflexivity.
    - intros.
    change (match_temp_env INV le st m) in H.
    unfold INV in H.
    get_invariant _chunk1.
    exists (v::nil).
    split.
    unfold map_opt. unfold exec_expr. rewrite p0.
    reflexivity.
    intros. simpl.
    tauto.
  -
    intros.
    simpl.
    repeat intro.
    destruct (f c c0 c1 c2 c3 c4 st) eqn: Hf; [idtac | constructor].
    destruct p0 as (r & st1).
    repeat intro.

    get_invariant_more _st.
    get_invariant_more _pc.
    get_invariant_more _len.
    get_invariant_more _dst.
    get_invariant_more _op.
    get_invariant_more _l.

    unfold stateM_correct in H1.
    destruct H1 as (Hv_eq & Hst).

    unfold stateless, pc_correct in H3.
    destruct H3 as (Hv0_eq & Hc0_range & Hc0_range_max).

    unfold stateless, len_correct in H5.
    destruct H5 as (Hv1_eq & Hc1_eq).

    unfold stateless, reg_correct in H7.
    unfold stateless, int8_correct in H9.
    unfold MyListType_correct in H11.
    destruct H11 as (Hv4_eq & H11).
    subst.
    specialize H11 with (Z.to_nat (Int.signed c0)).
    assert (Hc0_eq: Z.of_nat (Z.to_nat (Int.signed c0)) = Int.signed c0). {
      rewrite Z2Nat.id.
      reflexivity.
      lia.
    }
    rewrite Hc0_eq in H11.
    apply H11 in Hc0_range as Hload.
    destruct Hload as (vl & Hnth & Hload).

    
    (** pc \in [ (state_block,0), (state_block,8) ) *)
    (**according to the type:
         static void upd_flag(struct bpf_state* st, int f)
       1. return value should be Vundef
       2. the memory is m_flag
      *)
    exists Vundef.
    eexists.
    exists Events.E0.

    repeat split; unfold step2.
    - (* goal: Smallstep.star  _ _ (State _ (Ssequence ... *)
      apply Smallstep.plus_star.
      forward_clight.
      forward_clight.
      forward_clight.
      forward_clight.
      forward_clight.
      repeat (econstructor; eauto; try deref_loc_tactic); try reflexivity.
      simpl.
      reflexivity.
      forward_clight.

      reflexivity.
    - simpl.
      constructor.
    -
      unfold unmodifies_effect.
      intros.
      destruct (Pos.eq_dec state_block b).
      subst b.
      exfalso.
      apply H1.
      left; reflexivity.
      apply POrderedType.PositiveOrder.neq_sym in n.
      symmetry.
      apply (Mem.load_store_other AST.Mint32 m _ _ _ m1 Hstore chk _ _).
      left; assumption.
  Qed.

End Upd_flag.

Existing  Instance correct_function3_step_opcode_mem_ld_imm.
