From bpf.comm Require Import Regs State Monad.
From Coq Require Import List Lia ZArith.
From compcert Require Import Integers Values Clight Memory.
Import ListNotations.

From bpf.proof Require Import Clightlogic MatchState CorrectRel CommonLemma CommonLib.

From bpf.clight Require Import interpreter.

Section Eval_reg.
  Context {S: special_blocks}.

  (** The program contains our function of interest [fn] *)
  Definition p : Clight.program := prog.

  (* [Args,Res] provides the mapping between the Coq and the C types *)
  (* Definition Args : list CompilableType := [stateCompilableType].*)
  Definition args : list Type := [(reg:Type)].
  Definition res : Type := (val:Type).

  (* [f] is a Coq Monadic function with the right type *)
  Definition f : arrow_type args (M res) := Monad.eval_reg.

  (* [fn] is the Cligth function which has the same behaviour as [f] *)
  Definition fn: Clight.function := f_eval_reg.

  (* [match_arg] relates the Coq arguments and the C arguments *)
  Definition match_arg_list : DList.t (fun x => x -> Inv) ((unit:Type) ::args) :=
    dcons  (fun _ => StateLess is_state_handle)
(dcons  (fun x => (StateLess (reg_correct x)))
(DList.DNil _)).

  (* [match_res] relates the Coq result and the C result *)
  Definition match_res : res -> Inv := fun x  => StateLess (val64_correct x).

  Instance correct_function_eval_reg : forall a, correct_function p args res f fn ModNothing false match_state match_arg_list match_res a.
  Proof.
    correct_function_from_body args.
    correct_body.
    unfold f, INV.
    repeat intro.
    get_invariant _st.
    get_invariant _i.
    unfold eval_inv, is_state_handle in c0.
    unfold eval_inv, reg_correct in c1.
    subst.
    simpl in c.
    assert (MR : exists vl : int64,
            Mem.loadv AST.Mint64 m
              (Vptr st_blk
                 (Ptrofs.add (Ptrofs.repr 8)
                    (Ptrofs.repr (8 * id_of_reg c)))) =
            Some (Vlong vl) /\ Vlong vl = eval_regmap c (regs_st st)).
    {
      destruct MS.
      unfold match_registers in mregs.
      auto.
    }
    destruct MR as (vl & Hreg_load & Hinj).

    (**according to:
         static unsigned long long eval_reg(struct bpf_state* st, unsigned int i)
       1. return value should be v
       2. the memory is same
      *)
    exists (Vlong vl), m, Events.E0.
    split_and; unfold step2.
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
    - simpl.
      unfold State.eval_reg.
      unfold val64_correct. split ; auto.
      exists vl. auto.
    - constructor.
    - auto.
    - apply unmodifies_effect_refl.
  Qed.
  

End Eval_reg.

Existing Instance correct_function_eval_reg.
