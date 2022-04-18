From bpf.comm Require Import Regs State Monad LemmaNat rBPFMonadOp.
From bpf.monadicmodel Require Import Opcode rBPFInterpreter.
From Coq Require Import List Lia ZArith.
From compcert Require Import Integers Values Clight Memory.
Import ListNotations.

From bpf.clightlogic Require Import Clightlogic CorrectRel CommonLemma.

From bpf.clight Require Import interpreter.

From bpf.simulation Require Import correct_eval_ins_len correct_get_opcode_mem_ld_imm correct_eval_ins correct_get_immediate correct_upd_pc_incr correct_upd_reg correct_upd_flag.

From bpf.simulation Require Import MatchState InterpreterRel.

(**
Check step_opcode_mem_ld_imm.

step_opcode_mem_ld_imm
     : int -> int -> reg -> nat -> M unit

*)
Open Scope Z_scope.

Section Step_opcode_mem_ld_imm.
  Context {S: special_blocks}.

  (** The program contains our function of interest [fn] *)
  Definition p : Clight.program := prog.

  (* [Args,Res] provides the mapping between the Coq and the C types *)
  (* Definition Args : list CompilableType := [stateCompilableType].*)
  Definition args : list Type := [(int:Type); (val:Type); (int:Type); (reg:Type); (nat:Type)].
  Definition res : Type := unit.

  (* [f] is a Coq Monadic function with the right type *)
  Definition f : arrow_type args (M State.state res) := step_opcode_mem_ld_imm.


  (* [fn] is the Cligth function which has the same behaviour as [f] *)
  Definition fn: Clight.function := f_step_opcode_mem_ld_imm.

  (* [match_arg] relates the Coq arguments and the C arguments *)
  Definition match_arg_list : DList.t (fun x => x -> Inv State.state) ((unit:Type) ::args) :=
  (dcons (fun _ => StateLess _ is_state_handle)
    (dcons (stateless int32_correct)
      (dcons (stateless val64_correct)
        (dcons (stateless int32_correct)
          (dcons (stateless reg_correct)
            (dcons (stateless opcode_correct)
                  (DList.DNil _))))))).

  (* [match_res] relates the Coq result and the C result *)
  Definition match_res : res -> Inv State.state := fun _ => StateLess _ (eq Vundef).

  Instance correct_function_step_opcode_mem_ld_imm : forall a, correct_function _ p args res f fn modifies false match_state match_arg_list match_res a.
  Proof.
    correct_function_from_body args.
    correct_body.
    (** how to use correct_* *)
    unfold INV.
    unfold f, app, step_opcode_mem_ld_imm.
    simpl.
    correct_forward.

    unfold INV; intro H.
    correct_Forall.
    get_invariant _op.
    exists (v::nil).
    split.
    unfold map_opt, exec_expr. rewrite p0; reflexivity.
    intros; simpl.
    tauto.

    intros.
    destruct x eqn: HLD.
    - (**r op_BPF_LDDW_low *)
      eapply correct_statement_switch with (n:= 24%Z).
      + simpl.
        eapply correct_statement_seq_body_drop.
        intros.

        instantiate (1 := modifies).
        correct_forward.

        unfold INV; intro H.
        correct_Forall.
        get_invariant _st.
        get_invariant _dst.
        get_invariant _imm.
        exists (v ::v0 :: 
                (Vlong (Int64.repr (Int.signed c))) :: nil). (**r star here *)
        unfold map_opt, exec_expr.
        rewrite p0, p1, p2.
        unfold eval_inv,stateless, int32_correct in c6.
        subst.
        split.
        simpl; reflexivity.
        intros; simpl.
        unfold stateless, val64_correct.
        unfold stateless in c5.
        unfold eval_inv, is_state_handle in c4.
        split; [auto|].
        split; [auto|].
        split; [split; [reflexivity| eexists; reflexivity]| constructor].

        intros.
        correct_forward.
        unfold match_res.
        intros.
        get_invariant _st.
        unfold eval_inv, is_state_handle in c4.
        reflexivity.

        reflexivity.
      + reflexivity.
      + intros.
        get_invariant _opcode_ld.
        unfold eval_inv,correct_get_opcode_mem_ld_imm.match_res, opcode_mem_ld_imm_correct in c4.
        subst.
        unfold exec_expr.
        rewrite p0.
        reflexivity.
      + change Int.modulus with 4294967296.
        lia.
    - (**r op_BPF_LDDW_high *)
      eapply correct_statement_switch with (n:= 16%Z).
      + simpl.
        eapply correct_statement_seq_body_drop.
        intros.

        correct_forward.

        unfold INV; intro H.
        correct_Forall.
        get_invariant _st.
        get_invariant _dst.
        get_invariant _dst64.
        get_invariant _imm.
        exists (v ::v0 ::
                (Val.orl v1
                  (Vlong (Int64.shl' (Int64.repr (Int.signed c)) (Int.repr 32)))) :: nil). (**r star here *)
        unfold map_opt, exec_expr.
        rewrite p0, p1, p2, p3.
        unfold eval_inv,stateless, val64_correct in c6.
        unfold eval_inv,stateless, int32_correct in c7.
        destruct c6 as (Hc0_eq & vl & Hvl_eq).
        subst.
        simpl.
        split.
        unfold Cop.sem_shl, Cop.sem_shift; simpl.
        change (Int.ltu (Int.repr 32) Int64.iwordsize') with true; simpl.
        unfold Int64.shl', Int64.shl.
        change (Int.unsigned (Int.repr 32)) with 32.
        change (Int64.unsigned (Int64.repr 32)) with 32.
        reflexivity.
        intros; simpl.
        unfold stateless, val64_correct.
        unfold stateless in c5.
        unfold eval_inv, is_state_handle in c4.
        split; [auto|].
        split; [auto|].
        split; [split; [reflexivity| eexists; reflexivity]| constructor].

        intros.
        correct_forward.
        unfold match_res.
        intros.
        unfold eval_inv.
        reflexivity.
        reflexivity.
      + reflexivity.
      + intros.
        get_invariant _opcode_ld.
        unfold eval_inv,correct_get_opcode_mem_ld_imm.match_res, opcode_mem_ld_imm_correct in c4.
        subst.
        unfold exec_expr.
        rewrite p0.
        reflexivity.
      + change Int.modulus with 4294967296.
        lia.
    - eapply correct_statement_switch_ex.
      + reflexivity.
      + intros.
        assert (Hillegal_ins: exists n i,
          eval_inv (correct_get_opcode_mem_ld_imm.match_res op_BPF_LDX_IMM_ILLEGAL_INS) n st0 m0 /\
          n = Vint (Int.repr (Z.of_nat i)) /\
          (i <> 0x18%nat /\ i <> 0x10%nat) /\ (i <= 255)%nat /\
          exec_expr (Smallstep.globalenv (semantics2 p)) empty_env le0 m0
            (Etempvar _opcode_ld Clightdefs.tuchar) =
              Some (Vint (Int.repr (Z.of_nat i)))).
        {
          get_invariant _opcode_ld.
          unfold correct_get_opcode_mem_ld_imm.match_res in c4.
          exists v.
          assert (c4':=c4).
          unfold opcode_mem_ld_imm_correct in c4'.
          destruct c4' as (i & V & ILL & RANGE).
          exists i.
          split ; auto.
          split ; auto.
          split ; auto.
          split ; auto.
          unfold exec_expr. congruence.
        }
        destruct Hillegal_ins as (n & i & Hprop & Hn_eq & Hill & Hrange & EX).
        exists (Z.of_nat i).
        split; auto.
        split.

        change Int.modulus with 4294967296.
        lia.

        unfold select_switch.
        unfold select_switch_case.
        destruct Coqlib.zeq; try lia.
        destruct Coqlib.zeq; try lia.
        (* default *)
        simpl.
        (**r s1 -> (Ssequence s1 s2) *)
        eapply correct_statement_seq_body_drop.
        intros.

        change (upd_flag Flag.BPF_ILLEGAL_INSTRUCTION) with
          (bindM (upd_flag Flag.BPF_ILLEGAL_INSTRUCTION) (fun _ : unit => returnM tt)).
        correct_forward.

        unfold INV; intro HH.
        correct_Forall.
        get_invariant _st.
        exists (v ::
                (Vint (Int.neg (Int.repr 1))) :: nil). (**r star here *)
        unfold map_opt, exec_expr.
        rewrite p0.
        unfold Cop.sem_unary_operation; simpl.
        split.
        reflexivity.
        intros.
        unfold stateless, flag_correct, CommonLib.int_of_flag; simpl.
        split; auto.
        intros.

        (**r goal: correct_body p unit (returnM tt) fn (Sreturn None) modifies *)
        correct_forward.
        unfold match_res.
        intros.
        get_invariant _st.
        unfold eval_inv, is_state_handle in c4.
        reflexivity.
        reflexivity.
      - reflexivity.
  Qed.

End Step_opcode_mem_ld_imm.

Close Scope Z_scope.

Existing Instance correct_function_step_opcode_mem_ld_imm.