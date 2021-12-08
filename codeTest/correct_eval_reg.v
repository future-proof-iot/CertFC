From dx.tests Require Import DxIntegers DxValues DxMemRegion DxRegs DxState DxMonad DxInstructions.
From Coq Require Import List Lia ZArith.
From compcert Require Import Integers Values Clight Memory.
Import ListNotations.

From bpf.proof Require Import Clightlogic MatchState CorrectRel CommonLemma interpreter.

(**
static unsigned long long eval_reg(struct bpf_state* st, unsigned int i){
    return ( *st).regsmap[i];
}


Definition eval_reg (r: reg) : M val64_t := fun st => Some (eval_reg r st, st).
 *)


Section Eval_reg.

  (** The program contains our function of interest [fn] *)
  Definition p : Clight.program := prog.

  (* [Args,Res] provides the mapping between the Coq and the C types *)
  (* Definition Args : list CompilableType := [stateCompilableType].*)
  Definition args : list Type := [(reg:Type)].
  Definition res : Type := (val64_t:Type).

  (* [f] is a Coq Monadic function with the right type *)
  Definition f : arrow_type args (M res) := DxMonad.eval_reg.

  Variable state_block: block. (**r a block storing all rbpf state information? *)

  (* [fn] is the Cligth function which has the same behaviour as [f] *)
  Definition fn: Clight.function := f_eval_reg.

  Definition modifies : list block := [state_block]. (* of the C code *)

  Definition stateM_correct (st:unit) (v: val) (stm:stateM) (m: Memory.Mem.mem) :=
    v = Vptr state_block Ptrofs.zero /\ match_state state_block stm m.

  (* [match_arg] relates the Coq arguments and the C arguments *)
  Definition match_arg_list : DList.t (fun x => x -> val -> stateM -> Memory.Mem.mem -> Prop) ((unit:Type) ::args) :=
    DList.DCons stateM_correct (DList.DCons reg_correct (DList.DNil _)).

  (* [match_res] relates the Coq result and the C result *)
  Definition match_res : res -> val -> stateM -> Memory.Mem.mem -> Prop := fun x v st m => val64_correct x v.

  Instance correct_function3_eval_reg : correct_function3 p args res f fn modifies false match_arg_list match_res.
  Proof.
    correct_function_from_body.
    correct_body.
    unfold f, INV.
    repeat intro.
    get_invariant_more _st.
    get_invariant_more _i.
    unfold stateM_correct in H1.
    unfold reg_correct in H3.
    destruct H1 as (Hptr & Hmatch).
    subst v v0.
    destruct Hmatch.
    clear minj mpc mflags mperm.
    unfold match_registers in mregs.
    simpl in c.
    specialize (mregs c).
    destruct mregs as (vl & Hreg_load & Hinj).

    (**according to:
         static unsigned long long eval_reg(struct bpf_state* st, unsigned int i)
       1. return value should be v
       2. the memory is same
      *)
    exists (Vlong vl), m, Events.E0.
    repeat split; unfold step2.
    - apply Smallstep.plus_star.
      eapply Smallstep.plus_one; eauto.
      repeat (econstructor; eauto; try (deref_loc_tactic)).

      Transparent Archi.ptr64.

      rewrite Ptrofs.add_zero_l.
      unfold Coqlib.align; simpl.
      unfold Mem.loadv in Hreg_load.
      assert (Heq: Ptrofs.repr (8 * id_of_reg c) = Ptrofs.mul (Ptrofs.repr 8) (Ptrofs.of_intu (Int.repr (id_of_reg c)))). {
        unfold Ptrofs.mul, Ptrofs.of_intu.
        unfold Ptrofs.of_int.
        repeat rewrite Ptrofs.unsigned_repr.
        rewrite Int.unsigned_repr.
        reflexivity.
        rewrite Int_max_unsigned_eq64.
        unfold id_of_reg; destruct c; lia.
        rewrite Ptrofs_max_unsigned_eq64.
        rewrite Int.unsigned_repr.
        unfold id_of_reg; destruct c; lia.
        rewrite Int_max_unsigned_eq64.
        unfold id_of_reg; destruct c; lia.
        rewrite Ptrofs_max_unsigned_eq64.
        lia.
      }
      rewrite Heq in Hreg_load.
      rewrite Hreg_load.
      reflexivity.

      unfold Cop.sem_cast; reflexivity.
    -
      unfold match_res.
      unfold val64_correct.
      unfold DxState.eval_reg.
      symmetry; assumption.
    - unfold DxState.eval_reg; exists vl; symmetry; assumption.
    -
      simpl.
      constructor.
  Qed.
  

End Eval_reg.

Existing Instance correct_function3_eval_reg.
