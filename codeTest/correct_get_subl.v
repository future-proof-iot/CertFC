From dx.tests Require Import DxIntegers DxValues DxMemRegion DxState DxMonad DxInstructions.
From Coq Require Import List Lia.
From compcert Require Import Integers Values Clight Memory.
Import ListNotations.
Require Import ZArith.

From bpf.proof Require Import Clightlogic MatchState CommonLemma interpreter.

(**
static unsigned long long get_subl(unsigned long long x1, unsigned long long y1)
{
  return x1 - y1;
}

Definition get_subl (x1 y1: val64_t): M val64_t := returnM (Val.subl x1 y1).

static unsigned long long getMemRegion_block_ptr(struct memory_region *mr0)
{
  return 1LLU;
}

*)

Definition val64_correct (x:val64_t) (v: val) :=
  x = v /\ exists vl, x = Vlong vl.

Section Get_subl.

  (** The program contains our function of interest [fn] *)
  Definition p : Clight.program := prog.

  (* [Args,Res] provides the mapping between the Coq and the C types *)
  (* Definition Args : list CompilableType := [stateCompilableType].*)
  Definition args : list Type := [(val64_t:Type); (val64_t:Type)].
  Definition res : Type := (val64_t:Type).

  (* [f] is a Coq Monadic function with the right type *)
  Definition f : arrow_type args (M res) := get_subl.

  Variable state_block: block. (**r a block storing all rbpf state information? *)

  (* [fn] is the Cligth function which has the same behaviour as [f] *)
  Definition fn: Clight.function := f_get_subl.

  (* [match_arg] relates the Coq arguments and the C arguments *)
  Definition match_arg_list : DList.t (fun x => x -> val -> stateM -> Memory.Mem.mem -> Prop) args :=
    (DList.DCons (stateless val64_correct)
       (DList.DCons (stateless val64_correct)
                    (DList.DNil _))).

  (* [match_res] relates the Coq result and the C result *)
  Definition match_res : res -> val -> stateM -> Memory.Mem.mem -> Prop := fun x v st m => val64_correct x v.

  Lemma correct_function3_eval_pc : correct_function3 p args res f fn (nil) true match_arg_list match_res.
  Proof.
    correct_function_from_body.
    correct_body.
    (** how to use correct_* *)
    unfold INV.
    unfold f.
    repeat intro.
    get_invariant_more _x1.
    get_invariant_more _y1.

    unfold stateless, val64_correct in H1, H3.
    completer.
    subst v v0 c c0.

    (**according to the type of eval_pc:
         static unsigned long long get_subl(unsigned long long x1, unsigned long long y1)
       1. return value should be  x+y
       2. the memory is same
      *)
    exists (Val.subl (Vlong x0) (Vlong x)), m, Events.E0.

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
        unfold Cop.sem_sub, Cop.classify_sub, Ctypes.typeconv; simpl.
        unfold Cop.sem_binarith, Cop.sem_cast, Cop.classify_cast; simpl.
        reflexivity.
      + econstructor; eauto.
      + reflexivity.
    - simpl.
      exists (Int64.sub x0 x); reflexivity.
    - simpl.
      constructor.
  Qed.

End Get_subl.
