From dx.tests Require Import DxIntegers DxValues DxMemRegion DxRegs DxState DxMonad DxInstructions.
From Coq Require Import List Lia.
From compcert Require Import Integers Values Clight Memory.
Import ListNotations.
Require Import ZArith.

From bpf.proof Require Import Clightlogic MatchState CommonLemma interpreter.

(**
static unsigned long long eval_reg(struct bpf_state* st, unsigned int i){
  if (i < 11){
    return ( *st).regsmap[i];
  }
  else {
    ( *st).bpf_flag = BPF_ILLEGAL_REGISTER;
    return 0; //if here we update the bpf_flag, we must check bpf_flag after eval_reg
  }
}


Definition eval_reg (r: reg) : M val64_t := fun st => Some (eval_reg r st, st).
 *)

Definition int64_correct (x:int64_t) (v: val) (stm:stateM) (m: Memory.Mem.mem) :=
  Vlong x = v.

Definition reg_correct (r: reg) (v: val) (stm:stateM) (m: Memory.Mem.mem) :=
  match r with
  | R0 => v = Vzero
  | R1 => v = Vone
  | R2 => v = Vint (Int.repr 2)
  | R3 => v = Vint (Int.repr 3)
  | R4 => v = Vint (Int.repr 4)
  | R5 => v = Vint (Int.repr 5)
  | R6 => v = Vint (Int.repr 6)
  | R7 => v = Vint (Int.repr 7)
  | R8 => v = Vint (Int.repr 8)
  | R9 => v = Vint (Int.repr 9)
  | R10 => v = Vint (Int.repr 10)
  end.

Definition val64_correct (x:val64_t) (v: val) (stm:stateM) (m: Memory.Mem.mem) :=
  x = v. (**r /\ exists y, x = Vlong y *)

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
  (* [match_mem] related the Coq monadic state and the C memory *)
  (*Definition match_mem : stateM -> val -> Memory.Mem.mem -> Prop := fun stM v m => match_meminj_state state_block inject_id stM m.*)


  Definition stateM_correct (st:unit) (v: val) (stm:stateM) (m: Memory.Mem.mem) :=
    v = Vptr state_block Ptrofs.zero /\ match_state state_block stm m.

  (* [match_arg] relates the Coq arguments and the C arguments *)
  Definition match_arg_list : DList.t (fun x => x -> val -> stateM -> Memory.Mem.mem -> Prop) ((unit:Type) ::args) :=
    DList.DCons stateM_correct (DList.DCons reg_correct (DList.DNil _)).

  (* [match_res] relates the Coq result and the C result *)
  Definition match_res : res -> val -> stateM -> Memory.Mem.mem -> Prop := fun x v st m => val64_correct x v st m.

  Lemma correct_function3_eval_pc : correct_function3 p args res f fn modifies false match_arg_list match_res.
  Proof.
    eapply correct_function_from_body;
    [ simpl; unfold Coqlib.list_disjoint; simpl; intuition (subst; discriminate) |
      eapply list_no_repet_dec with (eq_dec := Pos.eq_dec); reflexivity |
      simpl; eapply list_no_repet_dec with (eq_dec := Pos.eq_dec); reflexivity |
      reflexivity |
      reflexivity |
      idtac
    ].
    intros.
    unfold args in *.
    car_cdr.
    unfold list_rel_arg.
    simpl.
    unfold correct_body.
    repeat intro. (**r TODO: a ltac named prepare *)
    get_invariant _st.
    get_invariant _i. (**r automatically *)
    destruct c0 as (H_st & Hst_casted).
    destruct c1 as (H_i & Hi_casted).
    unfold stateM_correct in H_st.
    unfold reg_correct in H_i.
    destruct H_st as (Hv_eq & Hst).
    subst v.

    unfold pre in c.
    (** we need to get the value of reg in the memory *)
    destruct Hst; clear minj mpc mflags mperm.
    unfold match_registers in mregs.
    specialize (mregs c).
    destruct mregs as (v & Hreg_load & Hreg_casted).
    unfold Mem.loadv in Hreg_load.
    (** pc \in [ (state_block,0), (state_block,8) ) *)
    (**according to the type of eval_reg:
         static unsigned long long eval_reg(struct bpf_state* st, unsigned int i)
       1. return value should be 
       2. the memory is same
      *)
    exists v, m, Events.E0.

    repeat split; unfold step2.
    - (* goal: Smallstep.star  _ _ (State _ (Ssequence ... *)
      apply Smallstep.plus_star.
      (** TODO: adding Sreturn  more info by Ltac2 *)
      eapply Smallstep.plus_left'; eauto.
      econstructor; eauto.
      econstructor; eauto.
      econstructor; eauto.
      econstructor; eauto.
      (** TODO: we need an invariant to say each register should be [0, 11] *)
      simpl. reflexivity.
      econstructor; eauto.
      simpl.
      do 3 econstructor; eauto.
      econstructor; eauto.
      reflexivity.
      reflexivity.
      reflexivity.
      unfold Coqlib.align; rewrite Ptrofs.add_zero.
      unfold Ptrofs.zero; simpl.
      rewrite Ptrofs.unsigned_repr.
      rewrite <- mpc; reflexivity.
      unfold Ptrofs.max_unsigned, Ptrofs.modulus, Ptrofs.wordsize, Wordsize_Ptrofs.wordsize.
      Transparent Archi.ptr64.
      simpl.
      lia.
      econstructor; eauto.
    - simpl.
      constructor.
  Qed.

End Eval_pc.
