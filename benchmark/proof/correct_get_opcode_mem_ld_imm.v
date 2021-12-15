From bpf.src Require Import DxIntegers DxValues DxOpcode DxMemRegion DxState DxMonad DxInstructions.
From Coq Require Import List Lia.
From compcert Require Import Integers Values Clight Memory.
Import ListNotations.
Require Import ZArith.

From bpf.proof Require Import Clightlogic MatchState CorrectRel CommonLemma.

From bpf.benchmark Require Import clightlogicexample.

(**
unsigned char get_opcode_mem_ld_imm(unsigned char op)
{
  return (unsigned char) (op & 255);
}

Print get_opcode_mem_ld_imm.
get_opcode_mem_ld_imm = 
fun op : int8_t => returnM (DxOpcode.byte_to_opcode_mem_ld_imm op)
     : int8_t -> M DxOpcode.opcode_mem_ld_imm

*)

Section Get_opcode_mem_ld_imm.

  (** The program contains our function of interest [fn] *)
  Definition p : Clight.program := prog.

  (* [Args,Res] provides the mapping between the Coq and the C types *)
  (* Definition Args : list CompilableType := [stateCompilableType].*)
  Definition args : list Type := [(int8_t:Type)].
  Definition res : Type := (opcode_mem_ld_imm:Type).

  (* [f] is a Coq Monadic function with the right type *)
  Definition f : arrow_type args (M res) := get_opcode_mem_ld_imm.

  Variable state_block: block. (**r a block storing all rbpf state information? *)

  (* [fn] is the Cligth function which has the same behaviour as [f] *)
  Definition fn: Clight.function := f_get_opcode_mem_ld_imm.

  (* [match_arg] relates the Coq arguments and the C arguments *)
  Definition match_arg_list : DList.t (fun x => x -> val -> stateM -> Memory.Mem.mem -> Prop) args :=
    (DList.DCons (stateless int8_correct)
                  (DList.DNil _)).

  (* [match_res] relates the Coq result and the C result *)
  Definition match_res : res -> val -> stateM -> Memory.Mem.mem -> Prop := fun x v st m => opcode_mem_ld_imm_correct x v.

  Instance correct_function3_get_opcode_mem_ld_imm : correct_function3 p args res f fn (nil) true match_arg_list match_res.
  Proof.
    correct_function_from_body.
    correct_body.
    (** how to use correct_* *)
    unfold INV.
    unfold f.
    repeat intro.
    get_invariant_more _op.

    unfold stateless, int8_correct in H1.
    subst v.

    (**according to the c function:
unsigned char get_opcode_mem_ld_imm(unsigned char op)
{
  return (unsigned char) (op & 255);
}
      *)
    eexists. exists m, Events.E0.

    repeat split; unfold step2.
    -
      apply Smallstep.plus_star.
      (** TODO: adding Sreturn  more info by Ltac2 *)
      eapply Smallstep.plus_one; eauto.
      eapply step_return_1.
      +
        repeat econstructor; eauto.
        Transparent Archi.ptr64.
        unfold Cop.sem_binary_operation.
        unfold Cop.sem_and; simpl.
        unfold Cop.sem_binarith, Cop.sem_cast, Cop.classify_cast; simpl.
        reflexivity.
        
        reflexivity. 
      + econstructor; eauto.
      + reflexivity.
    - simpl.
      unfold match_res, byte_to_opcode_mem_ld_imm, opcode_mem_ld_imm_correct.
      unfold int8_0xff.
      destruct (match Byte.unsigned (Byte.and c (Byte.repr 255)) with
  | 24%Z => op_BPF_LDDW
  | _ => op_BPF_LDX_IMM_ILLEGAL_INS
  end) eqn: Heq; eexists; reflexivity.
    - simpl.
      constructor.
      simpl.
      apply Int.zero_ext_idem.
      lia.
  Qed.

End Get_opcode_mem_ld_imm.

Existing Instance correct_function3_get_opcode_mem_ld_imm.
