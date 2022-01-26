From Coq Require Import List ZArith.
Import ListNotations.
From dx Require Import ResultMonad IR.
From bpf.comm Require Import MemRegion Regs State Monad rBPFAST rBPFValues.
From bpf.monadicmodel Require Import rBPFInterpreter.

From compcert Require Import Coqlib Values Clight Memory Integers.

From bpf.clight Require Import interpreter.

From bpf.proof Require Import MatchState Clightlogic clight_exec CommonLemma CorrectRel.

(*
Check get_mem_region.

get_mem_region
     : nat -> MyMemRegionsType -> M memory_region *)

Section Get_mem_region.

  (** The program contains our function of interest [fn] *)
  Definition p : Clight.program := prog.

  (* [Args,Res] provides the mapping between the Coq and the C types *)
  Definition args : list Type := [(nat:Type); (list memory_region:Type)].
  Definition res : Type := (memory_region:Type).

  (* [f] is a Coq Monadic function with the right type *)
  Definition f : arrow_type args (M res) := get_mem_region.

  Variable state_block: block. (**r a block storing all rbpf state information? *)
  Variable mrs_block: block.
  Variable ins_block: block.

  (* [fn] is the Cligth function which has the same behaviour as [f] *)
  Definition fn: Clight.function := f_get_mem_region.

  Definition stateM_correct (st:unit) (v: val) (stm:State.state) (m: Memory.Mem.mem) :=
    v = Vptr state_block Ptrofs.zero /\ match_state state_block mrs_block ins_block stm m.

  (* [match_arg] relates the Coq arguments and the C arguments *)
  Definition match_arg_list : DList.t (fun x => x -> val -> State.state -> Memory.Mem.mem -> Prop) args :=
      (DList.DCons pc_correct
        (DList.DCons (match_region_list mrs_block)
                (DList.DNil _))).

  (* [match_res] relates the Coq result and the C result *)
  Definition match_res : res -> val -> State.state -> Memory.Mem.mem -> Prop := fun r v st m => List.In r (bpf_mrs st).

  Instance correct_function3_get_mem_region : forall a, correct_function3 p args res f fn (nil) true match_arg_list match_res a.
  Proof.
    correct_function_from_body args.
    correct_body.
    (** how to use correct_* *)
    unfold INV.
    unfold f.
    repeat intro.
    get_invariant _n.
    get_invariant _mrs.

    unfold pc_correct in c1.
    destruct c1 as (Hv_eq & Hrange & Hmax).
    unfold match_region_list in c2.
    destruct c2 as (Hv0_eq & Hmrs_eq & Hmrs_num_eq & Hmatch).
    subst.

    eexists; exists m, Events.E0.
    split.
    {
      repeat forward_star.
    }
    split.
    {
      unfold match_res, match_res, MyMemRegionsIndexnat, Memory_regions.index_nat.
      apply nth_error_In with (n:= c).
      assert (Hlen: (c < List.length (bpf_mrs st))%nat). {
        rewrite Hmrs_num_eq.
        lia.
      }
      apply nth_error_nth' with (d:= default_memory_region) in Hlen.
      rewrite Hlen.
      unfold res.
      rewrite Hlen.
      reflexivity.
    }
    split.
    constructor.
    simpl; split; reflexivity.
Qed.

End Get_mem_region.

Existing Instance correct_function3_get_mem_region.

