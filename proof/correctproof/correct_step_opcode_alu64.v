From bpf.comm Require Import Regs State Monad.
From bpf.src Require Import DxNat DxValues DxMonad DxInstructions.
From Coq Require Import List Lia ZArith.
From compcert Require Import Integers Values Clight Memory.
Import ListNotations.

From bpf.proof Require Import Clightlogic MatchState CorrectRel CommonLemma CommonLib CommonLemmaNat.

From bpf.clight Require Import interpreter.

From bpf.proof.correctproof Require Import correct_get_opcode_alu64 correct_upd_reg
correct_upd_flag.
(**
Check step_opcode_alu64.
step_opcode_alu64
     : val64_t -> val64_t -> DxRegs.reg -> int8_t -> M unit

*)
Open Scope Z_scope.

Section Step_opcode_alu64.

  (** The program contains our function of interest [fn] *)
  Definition p : Clight.program := prog.

  (* [Args,Res] provides the mapping between the Coq and the C types *)
  (* Definition Args : list CompilableType := [stateCompilableType].*)
  Definition args : list Type := [(val64_t:Type); (val64_t:Type); (reg:Type); (nat8:Type)].
  Definition res : Type := unit.

  (* [f] is a Coq Monadic function with the right type *)
  Definition f : arrow_type args (M res) := step_opcode_alu64.

  Variable state_block: block. (**r a block storing all rbpf state information? *)
  Variable mrs_block: block.
  Variable ins_block: block.

  Definition modifies : list block := [state_block]. (* of the C code *)

  Definition stateM_correct (st:unit) (v: val) (stm:State.state) (m: Memory.Mem.mem) :=
    v = Vptr state_block Ptrofs.zero /\ match_state state_block mrs_block ins_block stm m.

  (* [fn] is the Cligth function which has the same behaviour as [f] *)
  Definition fn: Clight.function := f_step_opcode_alu64.

  (* [match_arg] relates the Coq arguments and the C arguments *)
  Definition match_arg_list : DList.t (fun x => x -> val -> State.state -> Memory.Mem.mem -> Prop) ((unit:Type) ::args) :=
    (DList.DCons stateM_correct
      (DList.DCons (stateless val64_correct)
       (DList.DCons (stateless val64_correct)
          (DList.DCons (stateless reg_correct)
            (DList.DCons (stateless opcode_alu64_nat8_correct)
                    (DList.DNil _)))))).

  (* [match_res] relates the Coq result and the C result *)
  Definition match_res : res -> val -> State.state -> Memory.Mem.mem -> Prop := fun x v st m => match_state state_block mrs_block ins_block st m.


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

Ltac correct_forward L :=
  match goal with
  | |- @correct_body _ _ (bindM ?F1 ?F2)  _
                     (Ssequence
                        (Ssequence
                           (Scall _ _ _)
                           (Sset ?V ?T))
                        ?R)
                     _ _ _ _ _ _  =>
      eapply L;
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

  Lemma Cop_add : forall vl1 vl2 m,
       Cop.sem_binary_operation (globalenv p) Cop.Oadd
                                (Vlong vl1) Clightdefs.tulong (Vlong vl2) Clightdefs.tulong m =
         Some (Vlong (Int64.add vl1 vl2)).
  Proof.
    reflexivity.
  Qed.

  Instance correct_function3_step_opcode_alu64 : forall a, correct_function3 p args res f fn modifies false match_arg_list match_res a.
  Proof.
    correct_function_from_body args.
    correct_body.

    unfold f, step_opcode_alu64.
    simpl.
    (** goal: correct_body _ _ (bindM (get_opcode_alu64 _) ... *)
    correct_forward correct_statement_seq_body_nil.

    my_reflex.
    my_reflex.
    reflexivity.
    typeclasses eauto.

    { unfold INV.
      unfold var_inv_preserve. (**r unmodifies_effect is not enough, we also need unmodifies_effect_state *)
      intros.
      unfold match_temp_env in *.
      rewrite Forall_fold_right in *.
      simpl in *.
      destruct H; subst.
      intuition.
    }

    reflexivity.
    reflexivity.
    reflexivity.
    prove_in_inv.
    prove_in_inv.
    reflexivity.
    reflexivity.

    unfold INV; intro H.
    correct_Forall.
    get_invariant _op.
    exists (v::nil).
    split.
    unfold map_opt. unfold exec_expr. rewrite p0.
    reflexivity.
    intros. simpl.
    tauto.

    (** goal: correct_body _ _
              match x with
              | op_BPF_ADD64 => bindM (upd_reg ... *)
    intros.
    unfold INV.
    destruct x eqn: Halu. (**r case discussion on each alu64_instruction *)
    - (**r op_BPF_ADD64 *)
      eapply correct_statement_switch with (n:= 0).
      + simpl.
        (**r s1 -> (Ssequence s1 s2) *)
        eapply correct_statement_seq_body_drop.
        intros.
        (**r because upd_reg return unit, here we use *_unit? *)
        eapply correct_statement_seq_body_unit.
        change_app_for_statement.
        (**r goal: correct_statement p unit (app f a) fn (Scall None (Evar ... *)
        eapply correct_statement_call_none.
        my_reflex.
        my_reflex.
        reflexivity.
        typeclasses eauto.
        unfold correct_upd_reg.match_res. intuition.
        { unfold modifies.
          instantiate (1:= ins_block).
          unfold var_inv_preserve.
          unfold match_temp_env.
          intros.
          instantiate (1 := mrs_block) in H0.
          inversion H1; subst; clear H1.
          inversion H5; subst; clear H5.
          inversion H6; subst; clear H6.
          inversion H7; subst; clear H7.
          inversion H8; subst; clear H8.
          inversion H9; subst; clear H9.
          repeat constructor;auto.

          revert H3. (**r moves the hypotheses  to the goal *)
          unfold match_elt,fst.
          destruct (Maps.PTree.get _st le1); try congruence.
          unfold snd.
          intro HH ; destruct HH ; split; auto.
          unfold correct_upd_reg.match_res in H0.
          unfold stateM_correct in *.
          tauto.
        }
        reflexivity.
        reflexivity.
        reflexivity.
        reflexivity.
        reflexivity.

        unfold INV; intro H.
        correct_Forall.
        get_invariant _st.
        get_invariant _dst.
        get_invariant _dst64.
        get_invariant _src64.
        destruct c5 as (c5_1 & c5_2).
        unfold val64_correct,stateless in c5_1.
        destruct c5_1 as (EQ & (vl1 & VL)); subst.
        destruct c6 as (c6_1 & c6_2).
        destruct c6_1 as (EQ & (vl2 & VL)); subst.
        exists (v ::v0 :: Vlong (Int64.add vl1 vl2) :: nil).
        unfold map_opt, exec_expr.
        rewrite p0.
        rewrite p1. rewrite p2. rewrite p3.
        split.
        reflexivity.
        intros.
        simpl.
        intuition.
        unfold stateless,val64_correct.
        split; auto. eexists ; reflexivity.
        intros.

        (**r goal: correct_body p unit (returnM tt) fn (Sreturn None) modifies *)
        eapply correct_body_Sreturn_None. (*(** from `upd_flag DxFlag.BPF_OK` to `bindM (upd_flag DxFlag.BPF_OK) returnM` *)
        eapply correct_statement_seq_body_unit.
        change_app_for_statement.
        eapply correct_statement_call_none.
        my_reflex.
        my_reflex.
        reflexivity.
        typeclasses eauto.
        
        unfold correct_upd_flag.match_res. intuition.
        { unfold modifies.
          instantiate (1:= ins_block).
          unfold var_inv_preserve.
          unfold match_temp_env.
          intros.
          inversion H1; subst; clear H1.
          inversion H5; subst; clear H5.
          inversion H6; subst; clear H6.
          inversion H7; subst; clear H7.
          inversion H8; subst; clear H8.
          inversion H9; subst; clear H9.
          repeat constructor;auto.

          revert H3. (**r moves the hypotheses  to the goal *)
          unfold match_elt,fst.
          destruct (Maps.PTree.get _st le2); try congruence.
          unfold snd.
          intro HH ; destruct HH ; split; auto.
          unfold correct_upd_flag.match_res in H0.
          unfold stateM_correct in *.
          tauto.
        }
        reflexivity.
        reflexivity.
        reflexivity.
        reflexivity.
        reflexivity.

        unfold INV; intro H.
        correct_Forall.
        get_invariant _st.
        get_invariant _src64.
        get_invariant _dst.
        get_invariant _op.
        (**r goal: ... [Etempvar _st ...; Econst_int (Int.repr 0) ... ] ... *)
        exists (v :: Vint (Int.repr 0) :: nil).
        unfold map_opt, exec_expr.
        rewrite p0.
        split.
        reflexivity.
        intros.
        simpl.
        intuition.
        unfold stateless,flag_correct.
        unfold int_of_flag, Z_of_flag; reflexivity.

        intros. destruct x1.
        eapply correct_body_Sreturn_None. *)
        unfold match_res, correct_get_opcode_alu64.match_res.
        intros.
        get_invariant _st.
        destruct c3 as (c3 & _); unfold stateM_correct in c3.
        destruct c3 as (_ & c3); assumption.
        reflexivity.
      + reflexivity.
      + intros.
        get_invariant _opcode_alu64.
        unfold exec_expr.
        rewrite p0. f_equal.
        unfold correct_get_opcode_alu64.match_res in c3.
        unfold opcode_alu64_correct in c3.
        (* opcode_alu64_correct should be a mapping between opcodes and int *)
        destruct c3; assumption.
      + compute. intuition congruence.
    - (**r op_BPF_SUB64 *)
      eapply correct_statement_switch with (n:= 16).
      + simpl.
        (**r s1 -> (Ssequence s1 s2) *)
        eapply correct_statement_seq_body_drop.
        intros.
        (**r because upd_reg return unit, here we use *_unit? *)
        eapply correct_statement_seq_body_unit.
        change_app_for_statement.
        (**r goal: correct_statement p unit (app f a) fn (Scall None (Evar ... *)
        eapply correct_statement_call_none.
        my_reflex.
        my_reflex.
        reflexivity.
        typeclasses eauto.
        unfold correct_upd_reg.match_res. intuition.
        { unfold modifies.
          instantiate (1:= ins_block).
          unfold var_inv_preserve.
          unfold match_temp_env.
          intros.
          instantiate (1 := mrs_block) in H0.
          inversion H1; subst; clear H1.
          inversion H5; subst; clear H5.
          inversion H6; subst; clear H6.
          inversion H7; subst; clear H7.
          inversion H8; subst; clear H8.
          inversion H9; subst; clear H9.
          repeat constructor;auto.

          revert H3. (**r moves the hypotheses  to the goal *)
          unfold match_elt,fst.
          destruct (Maps.PTree.get _st le1); try congruence.
          unfold snd.
          intro HH ; destruct HH ; split; auto.
          unfold correct_upd_reg.match_res in H0.
          unfold stateM_correct in *.
          tauto.
        }
        reflexivity.
        reflexivity.
        reflexivity.
        reflexivity.
        reflexivity.

        unfold INV; intro H.
        correct_Forall.
        get_invariant _st.
        get_invariant _dst.
        get_invariant _dst64.
        get_invariant _src64.
        destruct c5 as (c5_1 & c5_2).
        unfold val64_correct,stateless in c5_1.
        destruct c5_1 as (EQ & (vl1 & VL)); subst.
        destruct c6 as (c6_1 & c6_2).
        destruct c6_1 as (EQ & (vl2 & VL)); subst.
        exists (v ::v0 :: Vlong (Int64.sub vl1 vl2) :: nil). (**r star here *)
        unfold map_opt, exec_expr.
        rewrite p0.
        rewrite p1. rewrite p2. rewrite p3.
        split.
        reflexivity.
        intros.
        simpl.
        intuition.
        unfold stateless,val64_correct.
        split; auto. eexists ; reflexivity.
        intros.

        (**r goal: correct_body p unit (returnM tt) fn (Sreturn None) modifies *)
        eapply correct_body_Sreturn_None.
        unfold match_res, correct_get_opcode_alu64.match_res.
        intros.
        get_invariant _st.
        destruct c3 as (c3 & _); unfold stateM_correct in c3.
        destruct c3 as (_ & c3); assumption.
        reflexivity.
      + reflexivity.
      + intros.
        get_invariant _opcode_alu64.
        unfold exec_expr.
        rewrite p0. f_equal.
        unfold correct_get_opcode_alu64.match_res in c3.
        unfold opcode_alu64_correct in c3.
        (* opcode_alu64_correct should be a mapping between opcodes and int *)
        destruct c3; assumption.
      + compute. intuition congruence.
    - (**r op_BPF_MUL64 *)
      eapply correct_statement_switch with (n:= 32).
      + simpl.
        (**r s1 -> (Ssequence s1 s2) *)
        eapply correct_statement_seq_body_drop.
        intros.
        (**r because upd_reg return unit, here we use *_unit? *)
        eapply correct_statement_seq_body_unit.
        change_app_for_statement.
        (**r goal: correct_statement p unit (app f a) fn (Scall None (Evar ... *)
        eapply correct_statement_call_none.
        my_reflex.
        my_reflex.
        reflexivity.
        typeclasses eauto.
        unfold correct_upd_reg.match_res. intuition.
        { unfold modifies.
          instantiate (1:= ins_block).
          unfold var_inv_preserve.
          unfold match_temp_env.
          intros.
          instantiate (1 := mrs_block) in H0.
          inversion H1; subst; clear H1.
          inversion H5; subst; clear H5.
          inversion H6; subst; clear H6.
          inversion H7; subst; clear H7.
          inversion H8; subst; clear H8.
          inversion H9; subst; clear H9.
          repeat constructor;auto.

          revert H3. (**r moves the hypotheses  to the goal *)
          unfold match_elt,fst.
          destruct (Maps.PTree.get _st le1); try congruence.
          unfold snd.
          intro HH ; destruct HH ; split; auto.
          unfold correct_upd_reg.match_res in H0.
          unfold stateM_correct in *.
          tauto.
        }
        reflexivity.
        reflexivity.
        reflexivity.
        reflexivity.
        reflexivity.

        unfold INV; intro H.
        correct_Forall.
        get_invariant _st.
        get_invariant _dst.
        get_invariant _dst64.
        get_invariant _src64.
        destruct c5 as (c5_1 & c5_2).
        unfold val64_correct,stateless in c5_1.
        destruct c5_1 as (EQ & (vl1 & VL)); subst.
        destruct c6 as (c6_1 & c6_2).
        destruct c6_1 as (EQ & (vl2 & VL)); subst.
        exists (v ::v0 :: Vlong (Int64.mul vl1 vl2) :: nil). (**r star here *)
        unfold map_opt, exec_expr.
        rewrite p0.
        rewrite p1. rewrite p2. rewrite p3.
        split.
        reflexivity.
        intros.
        simpl.
        intuition.
        unfold stateless,val64_correct.
        split; auto. eexists ; reflexivity.
        intros.

        (**r goal: correct_body p unit (returnM tt) fn (Sreturn None) modifies *)
        eapply correct_body_Sreturn_None.
        unfold match_res, correct_get_opcode_alu64.match_res.
        intros.
        get_invariant _st.
        destruct c3 as (c3 & _); unfold stateM_correct in c3.
        destruct c3 as (_ & c3); assumption.
        reflexivity.
      + reflexivity.
      + intros.
        get_invariant _opcode_alu64.
        unfold exec_expr.
        rewrite p0. f_equal.
        unfold correct_get_opcode_alu64.match_res in c3.
        unfold opcode_alu64_correct in c3.
        (* opcode_alu64_correct should be a mapping between opcodes and int *)
        destruct c3; assumption.
      + compute. intuition congruence.
    - (**r op_BPF_DIV64 *)
      eapply correct_statement_switch with (n:= 48).
      + simpl.
        (**r s1 -> (Ssequence s1 s2) *)
        eapply correct_statement_seq_body_drop.
        intros.
        (**r correct_body p unit (if rBPFValues.compl_ne c0 val64_zero then ... *)
        eapply correct_statement_if_body_expr.
        destruct (rBPFValues.compl_ne c0 val64_zero) eqn: Hdiv_zero.


        eapply correct_statement_seq_body_unit.
        change_app_for_statement.
        (**r goal: correct_statement p unit (app f a) fn (Scall None (Evar ... *)
        eapply correct_statement_call_none.
        my_reflex.
        my_reflex.
        reflexivity.
        typeclasses eauto.
        unfold correct_upd_reg.match_res. intuition.
        { unfold modifies.
          instantiate (1:= ins_block).
          unfold var_inv_preserve.
          unfold match_temp_env.
          intros.
          instantiate (1 := mrs_block) in H0.
          inversion H1; subst; clear H1.
          inversion H5; subst; clear H5.
          inversion H6; subst; clear H6.
          inversion H7; subst; clear H7.
          inversion H8; subst; clear H8.
          inversion H9; subst; clear H9.
          repeat constructor;auto.

          revert H3. (**r moves the hypotheses  to the goal *)
          unfold match_elt,fst.
          destruct (Maps.PTree.get _st le1); try congruence.
          unfold snd.
          intro HH ; destruct HH ; split; auto.
          unfold correct_upd_reg.match_res in H0.
          unfold stateM_correct in *.
          tauto.
        }
        reflexivity.
        reflexivity.
        reflexivity.
        reflexivity.
        reflexivity.

        unfold INV; intro H.
        correct_Forall.
        get_invariant _st.
        get_invariant _dst.
        get_invariant _dst64.
        get_invariant _src64.
        destruct c5 as (c5_1 & c5_2).
        unfold val64_correct,stateless in c5_1.
        destruct c5_1 as (EQ & (vl1 & VL)); subst.
        destruct c6 as (c6_1 & c6_2).
        destruct c6_1 as (EQ & (vl2 & VL)); subst.
        unfold rBPFValues.val64_divlu, Val.divlu. (**r star here *)
        unfold rBPFValues.compl_ne, val64_zero in Hdiv_zero.
        rewrite Bool.negb_true_iff in Hdiv_zero.
        rewrite Hdiv_zero.
        exists (v ::v0 :: Vlong (Int64.divu vl1 vl2) :: nil). (**r star here *)
        unfold map_opt, exec_expr.
        rewrite p0.
        rewrite p1. rewrite p2. rewrite p3.
        split.
        simpl.
        unfold Cop.sem_div, Cop.sem_binarith;
        simpl.
        Transparent Archi.ptr64.
        unfold Cop.sem_cast; simpl.
        rewrite Hdiv_zero.
        reflexivity.
        intros.
        simpl.
        intuition.
        unfold stateless,val64_correct.
        split; auto. eexists ; reflexivity.
        intros.

        (**r goal: correct_body p unit (returnM tt) fn (Sreturn None) modifies *)
        eapply correct_body_Sreturn_None.
        unfold match_res, correct_get_opcode_alu64.match_res.
        intros.
        get_invariant _st.
        destruct c3 as (c3 & _); unfold stateM_correct in c3.
        destruct c3 as (_ & c3); assumption.
        reflexivity.

        unfold rBPFValues.compl_ne, val64_zero in Hdiv_zero.
        (**r goal: correct_body p unit (upd_flag Flag.BPF_ILLEGAL_DIV) fn ... *)
        eapply correct_statement_seq_body_unit.
        change_app_for_statement.
        (**r goal: correct_statement p unit (app f a) fn (Scall None (Evar ... *)
        eapply correct_statement_call_none.
        my_reflex.
        reflexivity.
        reflexivity.
        typeclasses eauto.
        unfold correct_upd_flag.match_res. intuition.
        { unfold modifies.
          instantiate (1:= ins_block).
          unfold var_inv_preserve.
          unfold match_temp_env.
          intros.
          instantiate (1 := mrs_block) in H0.
          inversion H1; subst; clear H1.
          inversion H5; subst; clear H5.
          inversion H6; subst; clear H6.
          inversion H7; subst; clear H7.
          inversion H8; subst; clear H8.
          inversion H9; subst; clear H9.
          repeat constructor;auto.

          revert H3. (**r moves the hypotheses  to the goal *)
          unfold match_elt,fst.
          destruct (Maps.PTree.get _st le1); try congruence.
          unfold snd.
          intro HH ; destruct HH ; split; auto.
          unfold correct_upd_flag.match_res in H0.
          unfold stateM_correct in *.
          tauto.
        }
        reflexivity.
        reflexivity.
        reflexivity.
        admit.
        reflexivity.

        unfold INV; intro H.
        correct_Forall.
        get_invariant _st.
        get_invariant _dst.
        get_invariant _dst64.
        get_invariant _src64.
        destruct c5 as (c5_1 & c5_2).
        unfold val64_correct,stateless in c5_1.
        destruct c5_1 as (EQ & (vl1 & VL)); subst.
        destruct c6 as (c6_1 & c6_2).
        destruct c6_1 as (EQ & (vl2 & VL)); subst.
        exists (v ::Vint (Int.neg (Int.repr 9)) :: nil). (**r star here *)
        unfold map_opt, exec_expr.
        rewrite p0.
        split.
        simpl.
        reflexivity.
        intros.
        simpl.
        intuition.
        unfold stateless,val64_correct.
        split; auto.
        intros.

        (**r goal: correct_body p unit (returnM tt) fn (Sreturn None) modifies *)
        eapply correct_body_Sreturn_None.
        unfold match_res, correct_get_opcode_alu64.match_res.
        intros.
        get_invariant _st.
        destruct c3 as (c3 & _); unfold stateM_correct in c3.
        destruct c3 as (_ & c3); assumption.
        reflexivity.
        reflexivity.

        intros.
        get_invariant _src64.
        unfold exec_expr.
        rewrite p0. unfold val64_zero, rBPFValues.compl_ne, Int64.zero.
        unfold Cop.sem_binary_operation, Cop.sem_cmp, Cop.sem_binarith, Cop.sem_cast; simpl.
        unfold stateless, val64_correct in c3.
        destruct c3 as ((c3_0 & c3_vl & c3_1) & c3).
        subst.
        reflexivity.

      + reflexivity.
      + intros.
        get_invariant _opcode_alu64.
        unfold exec_expr.
        rewrite p0. f_equal.
        unfold correct_get_opcode_alu64.match_res in c3.
        unfold opcode_alu64_correct in c3.
        (* opcode_alu64_correct should be a mapping between opcodes and int *)
        destruct c3; assumption.
      + compute. intuition congruence.
    - (**r op_BPF_OR64 *)
      eapply correct_statement_switch with (n:= 64).
      + simpl.
        (**r s1 -> (Ssequence s1 s2) *)
        eapply correct_statement_seq_body_drop.
        intros.
        (**r because upd_reg return unit, here we use *_unit? *)
        eapply correct_statement_seq_body_unit.
        change_app_for_statement.
        (**r goal: correct_statement p unit (app f a) fn (Scall None (Evar ... *)
        eapply correct_statement_call_none.
        my_reflex.
        reflexivity.
        reflexivity.
        typeclasses eauto.
        unfold correct_upd_reg.match_res. intuition.
        { unfold modifies.
          instantiate (1:= ins_block).
          unfold var_inv_preserve.
          unfold match_temp_env.
          intros.
          instantiate (1 := mrs_block) in H0.
          inversion H1; subst; clear H1.
          inversion H5; subst; clear H5.
          inversion H6; subst; clear H6.
          inversion H7; subst; clear H7.
          inversion H8; subst; clear H8.
          inversion H9; subst; clear H9.
          repeat constructor;auto.

          revert H3. (**r moves the hypotheses  to the goal *)
          unfold match_elt,fst.
          destruct (Maps.PTree.get _st le1); try congruence.
          unfold snd.
          intro HH ; destruct HH ; split; auto.
          unfold correct_upd_reg.match_res in H0.
          unfold stateM_correct in *.
          tauto.
        }
        reflexivity.
        reflexivity.
        reflexivity.
        reflexivity.
        reflexivity.

        unfold INV; intro H.
        correct_Forall.
        get_invariant _st.
        get_invariant _dst.
        get_invariant _dst64.
        get_invariant _src64.
        destruct c5 as (c5_1 & c5_2).
        unfold val64_correct,stateless in c5_1.
        destruct c5_1 as (EQ & (vl1 & VL)); subst.
        destruct c6 as (c6_1 & c6_2).
        destruct c6_1 as (EQ & (vl2 & VL)); subst.
        exists (v ::v0 :: Vlong (Int64.or vl1 vl2) :: nil). (**r star here *)
        unfold map_opt, exec_expr.
        rewrite p0.
        rewrite p1. rewrite p2. rewrite p3.
        split.
        reflexivity.
        intros.
        simpl.
        intuition.
        unfold stateless,val64_correct.
        split; auto. eexists ; reflexivity.
        intros.

        (**r goal: correct_body p unit (returnM tt) fn (Sreturn None) modifies *)
        eapply correct_body_Sreturn_None.
        unfold match_res, correct_get_opcode_alu64.match_res.
        intros.
        get_invariant _st.
        destruct c3 as (c3 & _); unfold stateM_correct in c3.
        destruct c3 as (_ & c3); assumption.
        reflexivity.
      + reflexivity.
      + intros.
        get_invariant _opcode_alu64.
        unfold exec_expr.
        rewrite p0. f_equal.
        unfold correct_get_opcode_alu64.match_res in c3.
        unfold opcode_alu64_correct in c3.
        (* opcode_alu64_correct should be a mapping between opcodes and int *)
        destruct c3; assumption.
      + compute. intuition congruence.
    - (**r op_BPF_AND64 *)
      eapply correct_statement_switch with (n:= 80).
      + simpl.
        (**r s1 -> (Ssequence s1 s2) *)
        eapply correct_statement_seq_body_drop.
        intros.
        (**r because upd_reg return unit, here we use *_unit? *)
        eapply correct_statement_seq_body_unit.
        change_app_for_statement.
        (**r goal: correct_statement p unit (app f a) fn (Scall None (Evar ... *)
        eapply correct_statement_call_none.
        my_reflex.
        reflexivity.
        reflexivity.
        typeclasses eauto.
        unfold correct_upd_reg.match_res. intuition.
        { unfold modifies.
          instantiate (1:= ins_block).
          unfold var_inv_preserve.
          unfold match_temp_env.
          intros.
          instantiate (1 := mrs_block) in H0.
          inversion H1; subst; clear H1.
          inversion H5; subst; clear H5.
          inversion H6; subst; clear H6.
          inversion H7; subst; clear H7.
          inversion H8; subst; clear H8.
          inversion H9; subst; clear H9.
          repeat constructor;auto.

          revert H3. (**r moves the hypotheses  to the goal *)
          unfold match_elt,fst.
          destruct (Maps.PTree.get _st le1); try congruence.
          unfold snd.
          intro HH ; destruct HH ; split; auto.
          unfold correct_upd_reg.match_res in H0.
          unfold stateM_correct in *.
          tauto.
        }
        reflexivity.
        reflexivity.
        reflexivity.
        reflexivity.
        reflexivity.

        unfold INV; intro H.
        correct_Forall.
        get_invariant _st.
        get_invariant _dst.
        get_invariant _dst64.
        get_invariant _src64.
        destruct c5 as (c5_1 & c5_2).
        unfold val64_correct,stateless in c5_1.
        destruct c5_1 as (EQ & (vl1 & VL)); subst.
        destruct c6 as (c6_1 & c6_2).
        destruct c6_1 as (EQ & (vl2 & VL)); subst.
        exists (v ::v0 :: Vlong (Int64.and vl1 vl2) :: nil). (**r star here *)
        unfold map_opt, exec_expr.
        rewrite p0.
        rewrite p1. rewrite p2. rewrite p3.
        split.
        reflexivity.
        intros.
        simpl.
        intuition.
        unfold stateless,val64_correct.
        split; auto. eexists ; reflexivity.
        intros.

        (**r goal: correct_body p unit (returnM tt) fn (Sreturn None) modifies *)
        eapply correct_body_Sreturn_None.
        unfold match_res, correct_get_opcode_alu64.match_res.
        intros.
        get_invariant _st.
        destruct c3 as (c3 & _); unfold stateM_correct in c3.
        destruct c3 as (_ & c3); assumption.
        reflexivity.
      + reflexivity.
      + intros.
        get_invariant _opcode_alu64.
        unfold exec_expr.
        rewrite p0. f_equal.
        unfold correct_get_opcode_alu64.match_res in c3.
        unfold opcode_alu64_correct in c3.
        (* opcode_alu64_correct should be a mapping between opcodes and int *)
        destruct c3; assumption.
      + compute. intuition congruence.
    - (**r op_BPF_LSH64 *)
      admit.
      (*
      eapply correct_statement_switch with (n:= 96).
      + simpl.
        (**r s1 -> (Ssequence s1 s2) *)
        eapply correct_statement_seq_body_drop.
        intros.
        (**r correct_body p unit (bindM (reg64_to_reg32 c0) ... *)
        eapply correct_statement_seq_body_pure.
        change_app_for_statement.


        eapply correct_statement_if_body_expr.
        destruct (rBPFValues.compl_ne c0 val64_zero) eqn: Hdiv_zero.


        eapply correct_statement_seq_body_unit.
        change_app_for_statement.
        (**r goal: correct_statement p unit (app f a) fn (Scall None (Evar ... *)
        eapply correct_statement_call_none.
        my_reflex.
        my_reflex.
        reflexivity.
        typeclasses eauto.
        unfold correct_upd_reg.match_res. intuition.
        { unfold modifies.
          instantiate (1:= ins_block).
          unfold var_inv_preserve.
          unfold match_temp_env.
          intros.
          instantiate (1 := mrs_block) in H0.
          inversion H1; subst; clear H1.
          inversion H5; subst; clear H5.
          inversion H6; subst; clear H6.
          inversion H7; subst; clear H7.
          inversion H8; subst; clear H8.
          inversion H9; subst; clear H9.
          repeat constructor;auto.

          revert H3. (**r moves the hypotheses  to the goal *)
          unfold match_elt,fst.
          destruct (Maps.PTree.get _st le1); try congruence.
          unfold snd.
          intro HH ; destruct HH ; split; auto.
          unfold correct_upd_reg.match_res in H0.
          unfold stateM_correct in *.
          tauto.
        }
        reflexivity.
        reflexivity.
        reflexivity.
        reflexivity.
        reflexivity.

        unfold INV; intro H.
        correct_Forall.
        get_invariant _st.
        get_invariant _dst.
        get_invariant _dst64.
        get_invariant _src64.
        destruct c5 as (c5_1 & c5_2).
        unfold val64_correct,stateless in c5_1.
        destruct c5_1 as (EQ & (vl1 & VL)); subst.
        destruct c6 as (c6_1 & c6_2).
        destruct c6_1 as (EQ & (vl2 & VL)); subst.
        unfold rBPFValues.val64_divlu, Val.divlu. (**r star here *)
        unfold rBPFValues.compl_ne, val64_zero in Hdiv_zero.
        rewrite Bool.negb_true_iff in Hdiv_zero.
        rewrite Hdiv_zero.
        exists (v ::v0 :: Vlong (Int64.divu vl1 vl2) :: nil). (**r star here *)
        unfold map_opt, exec_expr.
        rewrite p0.
        rewrite p1. rewrite p2. rewrite p3.
        split.
        simpl.
        unfold Cop.sem_div, Cop.sem_binarith;
        simpl.
        Transparent Archi.ptr64.
        unfold Cop.sem_cast; simpl.
        rewrite Hdiv_zero.
        reflexivity.
        intros.
        simpl.
        intuition.
        unfold stateless,val64_correct.
        split; auto. eexists ; reflexivity.
        intros.

        (**r goal: correct_body p unit (returnM tt) fn (Sreturn None) modifies *)
        eapply correct_body_Sreturn_None.
        unfold match_res, correct_get_opcode_alu64.match_res.
        intros.
        get_invariant _st.
        destruct c3 as (c3 & _); unfold stateM_correct in c3.
        destruct c3 as (_ & c3); assumption.
        reflexivity.

        unfold rBPFValues.compl_ne, val64_zero in Hdiv_zero.
        (**r goal: correct_body p unit (upd_flag Flag.BPF_ILLEGAL_DIV) fn ... *)
        eapply correct_statement_seq_body_unit.
        change_app_for_statement.
        (**r goal: correct_statement p unit (app f a) fn (Scall None (Evar ... *)
        eapply correct_statement_call_none.
        my_reflex.
        reflexivity.
        reflexivity.
        typeclasses eauto.
        unfold correct_upd_flag.match_res. intuition.
        { unfold modifies.
          instantiate (1:= ins_block).
          unfold var_inv_preserve.
          unfold match_temp_env.
          intros.
          instantiate (1 := mrs_block) in H0.
          inversion H1; subst; clear H1.
          inversion H5; subst; clear H5.
          inversion H6; subst; clear H6.
          inversion H7; subst; clear H7.
          inversion H8; subst; clear H8.
          inversion H9; subst; clear H9.
          repeat constructor;auto.

          revert H3. (**r moves the hypotheses  to the goal *)
          unfold match_elt,fst.
          destruct (Maps.PTree.get _st le1); try congruence.
          unfold snd.
          intro HH ; destruct HH ; split; auto.
          unfold correct_upd_flag.match_res in H0.
          unfold stateM_correct in *.
          tauto.
        }
        reflexivity.
        reflexivity.
        reflexivity.
        admit.
        reflexivity.

        unfold INV; intro H.
        correct_Forall.
        get_invariant _st.
        get_invariant _dst.
        get_invariant _dst64.
        get_invariant _src64.
        destruct c5 as (c5_1 & c5_2).
        unfold val64_correct,stateless in c5_1.
        destruct c5_1 as (EQ & (vl1 & VL)); subst.
        destruct c6 as (c6_1 & c6_2).
        destruct c6_1 as (EQ & (vl2 & VL)); subst.
        exists (v ::Vint (Int.neg (Int.repr 9)) :: nil). (**r star here *)
        unfold map_opt, exec_expr.
        rewrite p0.
        split.
        simpl.
        reflexivity.
        intros.
        simpl.
        intuition.
        unfold stateless,val64_correct.
        split; auto.
        intros.

        (**r goal: correct_body p unit (returnM tt) fn (Sreturn None) modifies *)
        eapply correct_body_Sreturn_None.
        unfold match_res, correct_get_opcode_alu64.match_res.
        intros.
        get_invariant _st.
        destruct c3 as (c3 & _); unfold stateM_correct in c3.
        destruct c3 as (_ & c3); assumption.
        reflexivity.
        reflexivity.

        intros.
        get_invariant _src64.
        unfold exec_expr.
        rewrite p0. unfold val64_zero, rBPFValues.compl_ne, Int64.zero.
        unfold Cop.sem_binary_operation, Cop.sem_cmp, Cop.sem_binarith, Cop.sem_cast; simpl.
        unfold stateless, val64_correct in c3.
        destruct c3 as ((c3_0 & c3_vl & c3_1) & c3).
        subst.
        reflexivity.

      + reflexivity.
      + intros.
        get_invariant _opcode_alu64.
        unfold exec_expr.
        rewrite p0. f_equal.
        unfold correct_get_opcode_alu64.match_res in c3.
        unfold opcode_alu64_correct in c3.
        (* opcode_alu64_correct should be a mapping between opcodes and int *)
        destruct c3; assumption.
      + compute. intuition congruence. *)
    - (**r op_BPF_RSH64 *)
      admit.
    - (**r op_BPF_NEG64 *)
      eapply correct_statement_switch with (n:= 128).
      + simpl.
        (**r s1 -> (Ssequence s1 s2) *)
        eapply correct_statement_seq_body_drop.
        intros.
        (**r because upd_reg return unit, here we use *_unit? *)
        eapply correct_statement_if_body_expr.
        destruct (c2 =? nat8_0x87)%nat eqn: Hneg_eq.


        eapply correct_statement_seq_body_unit.
        change_app_for_statement.
        (**r goal: correct_statement p unit (app f a) fn (Scall None (Evar ... *)
        eapply correct_statement_call_none.
        my_reflex.
        reflexivity.
        reflexivity.
        typeclasses eauto.
        unfold correct_upd_reg.match_res. intuition.
        { unfold modifies.
          instantiate (1:= ins_block).
          unfold var_inv_preserve.
          unfold match_temp_env.
          intros.
          instantiate (1 := mrs_block) in H0.
          inversion H1; subst; clear H1.
          inversion H5; subst; clear H5.
          inversion H6; subst; clear H6.
          inversion H7; subst; clear H7.
          inversion H8; subst; clear H8.
          inversion H9; subst; clear H9.
          repeat constructor;auto.

          revert H3. (**r moves the hypotheses  to the goal *)
          unfold match_elt,fst.
          destruct (Maps.PTree.get _st le1); try congruence.
          unfold snd.
          intro HH ; destruct HH ; split; auto.
          unfold correct_upd_reg.match_res in H0.
          unfold stateM_correct in *.
          tauto.
        }
        reflexivity.
        reflexivity.
        reflexivity.
        admit. (**r because of Eunop, we could use positve number for bpf_flag *)
        reflexivity.

        unfold INV; intro H.
        correct_Forall.
        get_invariant _st.
        get_invariant _dst.
        get_invariant _dst64.
        get_invariant _src64.
        destruct c5 as (c5_1 & c5_2).
        unfold val64_correct,stateless in c5_1.
        destruct c5_1 as (EQ & (vl1 & VL)); subst.
        destruct c6 as (c6_1 & c6_2).
        destruct c6_1 as (EQ & (vl2 & VL)); subst.
        exists (v :: v0 :: Vlong (Int64.neg vl1) :: nil). (**r star here *)
        unfold map_opt, exec_expr.
        rewrite p0.
        rewrite p1. rewrite p2.
        split.
        unfold Cop.sem_unary_operation; simpl.
        reflexivity.
        intros.
        simpl.
        intuition.
        unfold stateless,val64_correct.
        split; auto. eexists ; reflexivity.
        intros.

        (**r goal: correct_body p unit (returnM tt) fn (Sreturn None) modifies *)
        eapply correct_body_Sreturn_None.
        unfold match_res, correct_get_opcode_alu64.match_res.
        intros.
        get_invariant _st.
        destruct c3 as (c3 & _); unfold stateM_correct in c3.
        destruct c3 as (_ & c3); assumption.
        reflexivity.
        eapply correct_statement_seq_body_unit.
        change_app_for_statement.
        (**r goal: correct_statement p unit (app f a) fn (Scall None (Evar ... *)
        eapply correct_statement_call_none.
        my_reflex.
        reflexivity.
        reflexivity.
        typeclasses eauto.
        unfold correct_upd_flag.match_res. intuition.
        { unfold modifies.
          instantiate (1:= ins_block).
          unfold var_inv_preserve.
          unfold match_temp_env.
          intros.
          instantiate (1 := mrs_block) in H0.
          inversion H1; subst; clear H1.
          inversion H5; subst; clear H5.
          inversion H6; subst; clear H6.
          inversion H7; subst; clear H7.
          inversion H8; subst; clear H8.
          inversion H9; subst; clear H9.
          repeat constructor;auto.

          revert H3. (**r moves the hypotheses  to the goal *)
          unfold match_elt,fst.
          destruct (Maps.PTree.get _st le1); try congruence.
          unfold snd.
          intro HH ; destruct HH ; split; auto.
          unfold correct_upd_flag.match_res in H0.
          unfold stateM_correct in *.
          tauto.
        }
        reflexivity.
        reflexivity.
        reflexivity.
        admit.
        reflexivity.

        unfold INV; intro H.
        correct_Forall.
        get_invariant _st.
        get_invariant _dst.
        get_invariant _dst64.
        get_invariant _src64.
        destruct c5 as (c5_1 & c5_2).
        unfold val64_correct,stateless in c5_1.
        destruct c5_1 as (EQ & (vl1 & VL)); subst.
        destruct c6 as (c6_1 & c6_2).
        destruct c6_1 as (EQ & (vl2 & VL)); subst.
        exists (v ::Vint (Int.neg (Int.repr 1)) :: nil). (**r star here: it should be -1 *)
        unfold map_opt, exec_expr.
        rewrite p0.
        split.
        simpl.
        reflexivity.
        intros.
        simpl.
        intuition.
        unfold stateless,val64_correct.
        split; auto.
        intros.

        (**r goal: correct_body p unit (returnM tt) fn (Sreturn None) modifies *)
        eapply correct_body_Sreturn_None.
        unfold match_res, correct_get_opcode_alu64.match_res.
        intros.
        get_invariant _st.
        destruct c3 as (c3 & _); unfold stateM_correct in c3.
        destruct c3 as (_ & c3); assumption.
        reflexivity.
        reflexivity.

        intros.
        get_invariant _op.
        unfold exec_expr.
        rewrite p0. simpl.
        unfold stateless, opcode_alu64_nat8_correct in c3.
        unfold nat8_0x87.
        destruct c3 as ((Hv_eq & Hland & Hrange) & Hc3).
        rewrite <- Hv_eq.
        destruct (c2 =? 135)%nat eqn: Hc2_eq.
        rewrite Nat.eqb_eq in Hc2_eq.
        subst.
        simpl.
        reflexivity.

        rewrite Nat.eqb_neq in Hc2_eq.
        simpl.
        unfold Cop.sem_cmp, Cop.sem_binarith; simpl.
        assert (Hneq: Int.eq (Int.repr (Z.of_nat c2)) (Int.repr 135) = false). {
          apply Int.eq_false.
          apply nat8_neq_135; auto.
        }
        rewrite Hneq; clear Hneq.
        reflexivity.

      + reflexivity.
      + intros.
        get_invariant _opcode_alu64.
        unfold exec_expr.
        rewrite p0. f_equal.
        unfold correct_get_opcode_alu64.match_res in c3.
        unfold opcode_alu64_correct in c3.
        (* opcode_alu64_correct should be a mapping between opcodes and int *)
        destruct c3; assumption.
      + compute. intuition congruence.
    - (**r op_BPF_MOD64 *)
      eapply correct_statement_switch with (n:= 144).
      + simpl.
        (**r s1 -> (Ssequence s1 s2) *)
        eapply correct_statement_seq_body_drop.
        intros.
        (**r correct_body p unit (if rBPFValues.compl_ne c0 val64_zero then ... *)
        eapply correct_statement_if_body_expr.
        destruct (rBPFValues.compl_ne c0 val64_zero) eqn: Hmod_zero.


        eapply correct_statement_seq_body_unit.
        change_app_for_statement.
        (**r goal: correct_statement p unit (app f a) fn (Scall None (Evar ... *)
        eapply correct_statement_call_none.
        my_reflex.
        reflexivity.
        reflexivity.
        typeclasses eauto.
        unfold correct_upd_reg.match_res. intuition.
        { unfold modifies.
          instantiate (1:= ins_block).
          unfold var_inv_preserve.
          unfold match_temp_env.
          intros.
          instantiate (1 := mrs_block) in H0.
          inversion H1; subst; clear H1.
          inversion H5; subst; clear H5.
          inversion H6; subst; clear H6.
          inversion H7; subst; clear H7.
          inversion H8; subst; clear H8.
          inversion H9; subst; clear H9.
          repeat constructor;auto.

          revert H3. (**r moves the hypotheses  to the goal *)
          unfold match_elt,fst.
          destruct (Maps.PTree.get _st le1); try congruence.
          unfold snd.
          intro HH ; destruct HH ; split; auto.
          unfold correct_upd_reg.match_res in H0.
          unfold stateM_correct in *.
          tauto.
        }
        reflexivity.
        reflexivity.
        reflexivity.
        reflexivity.
        reflexivity.

        unfold INV; intro H.
        correct_Forall.
        get_invariant _st.
        get_invariant _dst.
        get_invariant _dst64.
        get_invariant _src64.
        destruct c5 as (c5_1 & c5_2).
        unfold val64_correct,stateless in c5_1.
        destruct c5_1 as (EQ & (vl1 & VL)); subst.
        destruct c6 as (c6_1 & c6_2).
        destruct c6_1 as (EQ & (vl2 & VL)); subst.
        unfold rBPFValues.val64_modlu, Val.modlu. (**r star here *)
        unfold rBPFValues.compl_ne, val64_zero in Hmod_zero.
        rewrite Bool.negb_true_iff in Hmod_zero.
        rewrite Hmod_zero.
        exists (v ::v0 :: Vlong (Int64.modu vl1 vl2) :: nil). (**r star here *)
        unfold map_opt, exec_expr.
        rewrite p0.
        rewrite p1. rewrite p2. rewrite p3.
        split.
        simpl.
        unfold Cop.sem_mod, Cop.sem_binarith;
        simpl.
        Transparent Archi.ptr64.
        unfold Cop.sem_cast; simpl.
        rewrite Hmod_zero.
        reflexivity.
        intros.
        simpl.
        intuition.
        unfold stateless,val64_correct.
        split; auto. eexists ; reflexivity.
        intros.

        (**r goal: correct_body p unit (returnM tt) fn (Sreturn None) modifies *)
        eapply correct_body_Sreturn_None.
        unfold match_res, correct_get_opcode_alu64.match_res.
        intros.
        get_invariant _st.
        destruct c3 as (c3 & _); unfold stateM_correct in c3.
        destruct c3 as (_ & c3); assumption.
        reflexivity.

        unfold rBPFValues.compl_ne, val64_zero in Hmod_zero.
        (**r goal: correct_body p unit (upd_flag Flag.BPF_ILLEGAL_DIV) fn ... *)
        eapply correct_statement_seq_body_unit.
        change_app_for_statement.
        (**r goal: correct_statement p unit (app f a) fn (Scall None (Evar ... *)
        eapply correct_statement_call_none.
        my_reflex.
        reflexivity.
        reflexivity.
        typeclasses eauto.
        unfold correct_upd_flag.match_res. intuition.
        { unfold modifies.
          instantiate (1:= ins_block).
          unfold var_inv_preserve.
          unfold match_temp_env.
          intros.
          instantiate (1 := mrs_block) in H0.
          inversion H1; subst; clear H1.
          inversion H5; subst; clear H5.
          inversion H6; subst; clear H6.
          inversion H7; subst; clear H7.
          inversion H8; subst; clear H8.
          inversion H9; subst; clear H9.
          repeat constructor;auto.

          revert H3. (**r moves the hypotheses  to the goal *)
          unfold match_elt,fst.
          destruct (Maps.PTree.get _st le1); try congruence.
          unfold snd.
          intro HH ; destruct HH ; split; auto.
          unfold correct_upd_flag.match_res in H0.
          unfold stateM_correct in *.
          tauto.
        }
        reflexivity.
        reflexivity.
        reflexivity.
        admit.
        reflexivity.

        unfold INV; intro H.
        correct_Forall.
        get_invariant _st.
        get_invariant _dst.
        get_invariant _dst64.
        get_invariant _src64.
        destruct c5 as (c5_1 & c5_2).
        unfold val64_correct,stateless in c5_1.
        destruct c5_1 as (EQ & (vl1 & VL)); subst.
        destruct c6 as (c6_1 & c6_2).
        destruct c6_1 as (EQ & (vl2 & VL)); subst.
        exists (v ::Vint (Int.neg (Int.repr 9)) :: nil). (**r star here *)
        unfold map_opt, exec_expr.
        rewrite p0.
        split.
        simpl.
        reflexivity.
        intros.
        simpl.
        intuition.
        unfold stateless,val64_correct.
        split; auto.
        intros.

        (**r goal: correct_body p unit (returnM tt) fn (Sreturn None) modifies *)
        eapply correct_body_Sreturn_None.
        unfold match_res, correct_get_opcode_alu64.match_res.
        intros.
        get_invariant _st.
        destruct c3 as (c3 & _); unfold stateM_correct in c3.
        destruct c3 as (_ & c3); assumption.
        reflexivity.
        reflexivity.

        intros.
        get_invariant _src64.
        unfold exec_expr.
        rewrite p0. unfold val64_zero, rBPFValues.compl_ne, Int64.zero.
        unfold Cop.sem_binary_operation, Cop.sem_cmp, Cop.sem_binarith, Cop.sem_cast; simpl.
        unfold stateless, val64_correct in c3.
        destruct c3 as ((c3_0 & c3_vl & c3_1) & c3).
        subst.
        reflexivity.

      + reflexivity.
      + intros.
        get_invariant _opcode_alu64.
        unfold exec_expr.
        rewrite p0. f_equal.
        unfold correct_get_opcode_alu64.match_res in c3.
        unfold opcode_alu64_correct in c3.
        (* opcode_alu64_correct should be a mapping between opcodes and int *)
        destruct c3; assumption.
      + compute. intuition congruence.
    - (**r op_BPF_XOR64 *)
      eapply correct_statement_switch with (n:= 160).
      + simpl.
        (**r s1 -> (Ssequence s1 s2) *)
        eapply correct_statement_seq_body_drop.
        intros.
        (**r because upd_reg return unit, here we use *_unit? *)
        eapply correct_statement_seq_body_unit.
        change_app_for_statement.
        (**r goal: correct_statement p unit (app f a) fn (Scall None (Evar ... *)
        eapply correct_statement_call_none.
        my_reflex.
        reflexivity.
        reflexivity.
        typeclasses eauto.
        unfold correct_upd_reg.match_res. intuition.
        { unfold modifies.
          instantiate (1:= ins_block).
          unfold var_inv_preserve.
          unfold match_temp_env.
          intros.
          instantiate (1 := mrs_block) in H0.
          inversion H1; subst; clear H1.
          inversion H5; subst; clear H5.
          inversion H6; subst; clear H6.
          inversion H7; subst; clear H7.
          inversion H8; subst; clear H8.
          inversion H9; subst; clear H9.
          repeat constructor;auto.

          revert H3. (**r moves the hypotheses  to the goal *)
          unfold match_elt,fst.
          destruct (Maps.PTree.get _st le1); try congruence.
          unfold snd.
          intro HH ; destruct HH ; split; auto.
          unfold correct_upd_reg.match_res in H0.
          unfold stateM_correct in *.
          tauto.
        }
        reflexivity.
        reflexivity.
        reflexivity.
        reflexivity.
        reflexivity.

        unfold INV; intro H.
        correct_Forall.
        get_invariant _st.
        get_invariant _dst.
        get_invariant _dst64.
        get_invariant _src64.
        destruct c5 as (c5_1 & c5_2).
        unfold val64_correct,stateless in c5_1.
        destruct c5_1 as (EQ & (vl1 & VL)); subst.
        destruct c6 as (c6_1 & c6_2).
        destruct c6_1 as (EQ & (vl2 & VL)); subst.
        exists (v ::v0 :: Vlong (Int64.xor vl1 vl2) :: nil). (**r star here *)
        unfold map_opt, exec_expr.
        rewrite p0.
        rewrite p1. rewrite p2. rewrite p3.
        split.
        reflexivity.
        intros.
        simpl.
        intuition.
        unfold stateless,val64_correct.
        split; auto. eexists ; reflexivity.
        intros.

        (**r goal: correct_body p unit (returnM tt) fn (Sreturn None) modifies *)
        eapply correct_body_Sreturn_None.
        unfold match_res, correct_get_opcode_alu64.match_res.
        intros.
        get_invariant _st.
        destruct c3 as (c3 & _); unfold stateM_correct in c3.
        destruct c3 as (_ & c3); assumption.
        reflexivity.
      + reflexivity.
      + intros.
        get_invariant _opcode_alu64.
        unfold exec_expr.
        rewrite p0. f_equal.
        unfold correct_get_opcode_alu64.match_res in c3.
        unfold opcode_alu64_correct in c3.
        (* opcode_alu64_correct should be a mapping between opcodes and int *)
        destruct c3; assumption.
      + compute. intuition congruence.
    - (**r op_BPF_MOV64 *)
      eapply correct_statement_switch with (n:= 176).
      + simpl.
        (**r s1 -> (Ssequence s1 s2) *)
        eapply correct_statement_seq_body_drop.
        intros.
        (**r because upd_reg return unit, here we use *_unit? *)
        eapply correct_statement_seq_body_unit.
        change_app_for_statement.
        (**r goal: correct_statement p unit (app f a) fn (Scall None (Evar ... *)
        eapply correct_statement_call_none.
        my_reflex.
        reflexivity.
        reflexivity.
        typeclasses eauto.
        unfold correct_upd_reg.match_res. intuition.
        { unfold modifies.
          instantiate (1:= ins_block).
          unfold var_inv_preserve.
          unfold match_temp_env.
          intros.
          instantiate (1 := mrs_block) in H0.
          inversion H1; subst; clear H1.
          inversion H5; subst; clear H5.
          inversion H6; subst; clear H6.
          inversion H7; subst; clear H7.
          inversion H8; subst; clear H8.
          inversion H9; subst; clear H9.
          repeat constructor;auto.

          revert H3. (**r moves the hypotheses  to the goal *)
          unfold match_elt,fst.
          destruct (Maps.PTree.get _st le1); try congruence.
          unfold snd.
          intro HH ; destruct HH ; split; auto.
          unfold correct_upd_reg.match_res in H0.
          unfold stateM_correct in *.
          tauto.
        }
        reflexivity.
        reflexivity.
        reflexivity.
        reflexivity.
        reflexivity.

        unfold INV; intro H.
        correct_Forall.
        get_invariant _st.
        get_invariant _dst.
        get_invariant _dst64.
        get_invariant _src64.
        destruct c5 as (c5_1 & c5_2).
        unfold val64_correct,stateless in c5_1.
        destruct c5_1 as (EQ & (vl1 & VL)); subst.
        destruct c6 as (c6_1 & c6_2).
        destruct c6_1 as (EQ & (vl2 & VL)); subst.
        exists (v ::v0 :: Vlong (vl2) :: nil). (**r star here *)
        unfold map_opt, exec_expr.
        rewrite p0.
        rewrite p1. rewrite p3.
        split.
        reflexivity.
        intros.
        simpl.
        intuition.
        unfold stateless,val64_correct.
        split; auto. eexists ; reflexivity.
        intros.

        (**r goal: correct_body p unit (returnM tt) fn (Sreturn None) modifies *)
        eapply correct_body_Sreturn_None.
        unfold match_res, correct_get_opcode_alu64.match_res.
        intros.
        get_invariant _st.
        destruct c3 as (c3 & _); unfold stateM_correct in c3.
        destruct c3 as (_ & c3); assumption.
        reflexivity.
      + reflexivity.
      + intros.
        get_invariant _opcode_alu64.
        unfold exec_expr.
        rewrite p0. f_equal.
        unfold correct_get_opcode_alu64.match_res in c3.
        unfold opcode_alu64_correct in c3.
        (* opcode_alu64_correct should be a mapping between opcodes and int *)
        destruct c3; assumption.
      + compute. intuition congruence.
    - (**r op_BPF_ARSH64 *)
      admit.
    - (**r op_BPF_ALU64_ILLEGAL_INS *)
      admit.
Admitted.

End Step_opcode_alu64.

Close Scope Z_scope.

Existing Instance correct_function3_step_opcode_alu64.
