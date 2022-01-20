From bpf.comm Require Import Regs State Monad.
From bpf.src Require Import DxValues.
From Coq Require Import List Lia ZArith.
From compcert Require Import Integers Values Clight Memory.
Import ListNotations.

From bpf.proof Require Import Clightlogic MatchState CorrectRel CommonLemma CommonLib.

From bpf.clight Require Import interpreter.


(**
Check DxMonad.eval_reg.
eval_reg
     : DxRegs.reg -> M val64_t
*)


Section Eval_reg.

  (** The program contains our function of interest [fn] *)
  Definition p : Clight.program := prog.

  (* [Args,Res] provides the mapping between the Coq and the C types *)
  (* Definition Args : list CompilableType := [stateCompilableType].*)
  Definition args : list Type := [(reg:Type)].
  Definition res : Type := (val64_t:Type).

  (* [f] is a Coq Monadic function with the right type *)
  Definition f : arrow_type args (M res) := Monad.eval_reg.

  Variable state_block: block. (**r a block storing all rbpf state information? *)
  Variable mrs_block: block.
  Variable ins_block: block.

  (* [fn] is the Cligth function which has the same behaviour as [f] *)
  Definition fn: Clight.function := f_eval_reg.

  Definition stateM_correct (st:unit) (v: val) (stm:State.state) (m: Memory.Mem.mem) :=
    v = Vptr state_block Ptrofs.zero /\ match_state state_block mrs_block ins_block stm m.

  (* [match_arg] relates the Coq arguments and the C arguments *)
  Definition match_arg_list : DList.t (fun x => x -> val -> State.state -> Memory.Mem.mem -> Prop) ((unit:Type) ::args) :=
    DList.DCons stateM_correct
                (DList.DCons (stateless reg_correct)
                             (DList.DNil _)).

  (* [match_res] relates the Coq result and the C result *)
  Definition match_res : res -> val -> State.state -> Memory.Mem.mem -> Prop := fun x v st m => val64_correct x v.

  Instance correct_function3_eval_reg : forall a, correct_function3 p args res f fn nil false match_arg_list match_res a.
  Proof.
    correct_function_from_body args.
    correct_body.
    unfold f, INV.
    repeat intro.
    get_invariant_more _st.
    get_invariant_more _i.
    unfold stateM_correct in H0.
    unfold stateless, reg_correct in H2.
    destruct H0 as (Hptr & Hmatch).
    subst.
    destruct Hmatch.
    clear munchange mpc mflags mperm.
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
    -
      repeat forward_star.

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
        rewrite Ptrofs_max_unsigned_eq32.
        rewrite Int.unsigned_repr.
        unfold id_of_reg; destruct c; lia.
        rewrite Int_max_unsigned_eq64.
        unfold id_of_reg; destruct c; lia.
        rewrite Ptrofs_max_unsigned_eq32.
        lia.
      }
      rewrite Heq in Hreg_load.
      rewrite Hreg_load.
      reflexivity.

      unfold Cop.sem_cast; reflexivity.
    - 
      unfold State.eval_reg.
      symmetry; assumption.
    - unfold State.eval_reg; exists vl; symmetry; assumption.
    -
      simpl.
      constructor.
  Qed.
  

End Eval_reg.

Existing Instance correct_function3_eval_reg.
