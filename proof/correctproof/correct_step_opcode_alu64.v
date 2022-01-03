From bpf.src Require Import DxIntegers DxValues DxOpcode DxMemRegion DxRegs DxState DxMonad DxInstructions.
From Coq Require Import List Lia ZArith.
From compcert Require Import Integers Values Clight Memory.
Import ListNotations.

From bpf.proof Require Import Clightlogic MatchState CorrectRel CommonLemma.

From bpf.clight Require Import interpreter.

From bpf.proof.correctproof Require Import correct_get_opcode_alu64.
(**
Check step_opcode_alu64.
step_opcode_alu64
     : val64_t -> val64_t -> DxRegs.reg -> int8_t -> M unit

*)

Section Step_opcode_alu64.

  (** The program contains our function of interest [fn] *)
  Definition p : Clight.program := prog.

  (* [Args,Res] provides the mapping between the Coq and the C types *)
  (* Definition Args : list CompilableType := [stateCompilableType].*)
  Definition args : list Type := [(val64_t:Type); (val64_t:Type); (reg:Type); (int8_t:Type)].
  Definition res : Type := unit.

  (* [f] is a Coq Monadic function with the right type *)
  Definition f : arrow_type args (M res) := step_opcode_alu64.

  Variable state_block: block. (**r a block storing all rbpf state information? *)

  Definition modifies : list block := [state_block]. (* of the C code *)

  Definition stateM_correct (st:unit) (v: val) (stm:stateM) (m: Memory.Mem.mem) :=
    v = Vptr state_block Ptrofs.zero /\ match_state state_block stm m.

  (* [fn] is the Cligth function which has the same behaviour as [f] *)
  Definition fn: Clight.function := f_step_opcode_alu64.

  (* [match_arg] relates the Coq arguments and the C arguments *)
  Definition match_arg_list : DList.t (fun x => x -> val -> stateM -> Memory.Mem.mem -> Prop) ((unit:Type) ::args) :=
    (DList.DCons stateM_correct
      (DList.DCons (stateless val64_correct)
       (DList.DCons (stateless val64_correct)
          (DList.DCons (stateless reg_correct)
            (DList.DCons (stateless int8_correct)
                    (DList.DNil _)))))).

  (* [match_res] relates the Coq result and the C result *)
  Definition match_res : res -> val -> stateM -> Memory.Mem.mem -> Prop := fun x v st m => True.


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

  Instance correct_function3_step_opcode_alu64 : forall a, correct_function3 p args res f fn modifies false match_arg_list match_res a.
  Proof.
    correct_function_from_body args.
    correct_body.

    unfold f, step_opcode_alu64.
    simpl.
    (** goal: correct_body _ _ (bindM (get_opcode_alu64 _) ... *)
    correct_forward correct_statement_seq_body_nil.

    reflexivity.
    reflexivity.
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

    intros.
    change (match_temp_env INV le st m) in H; unfold INV in H.
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
    destruct x. (**r case discussion on each alu64_instruction *)
    - (**r op_BPF_ADD64 *)
      unfold correct_body.
      intros.
      correct_forward correct_statement_seq_body.
    - (**r op_BPF_SUB64 *)
    - (**r op_BPF_MUL64 *)
    - (**r op_BPF_DIV64 *)
    - (**r op_BPF_OR64 *)
    - (**r op_BPF_AND64 *)
    - (**r op_BPF_LSH64 *)
    - (**r op_BPF_RSH64 *)
    - (**r op_BPF_NEG64 *)
    - (**r op_BPF_MOD64 *)
    - (**r op_BPF_XOR64 *)
    - (**r op_BPF_ARSH64 *)
    - (**r op_BPF_ALU64_ILLEGAL_INS *)
    unfold f, step_opcode_alu64.
    repeat intro.
    match goal with
    | |- match ?X with | _ => _  end =>
      destruct X eqn: Hx; [ idtac | constructor]
    end.
    destruct p0.
    intros.

    get_invariant_more _st.
    get_invariant_more _src64.
    get_invariant_more _dst.
    get_invariant_more _op.
    unfold stateM_correct in H1.
    destruct H1 as (H1_eq & H1_st).
    destruct H1_st.
    unfold stateless, val64_correct in H3.
    destruct H3 as (H3_eq & (H3_vl & H3_c0)).
    unfold stateless, reg_correct in H5.
    unfold stateless, int8_correct in H7.
    subst.

    do 2 eexists; exists Events.E0.

    repeat split; unfold step2.
    -
      forward_star.
      repeat forward_star.
      forward_star.
      repeat forward_star.
      
      forward_star.
      repeat forward_star.
      
      forward_star.
      repeat forward_star.
    - simpl.
      eexists; reflexivity.
    - simpl.
      constructor.
      reflexivity.
  Qed.

End Step_opcode_alu64.

Existing Instance correct_function3_step_opcode_alu64.
