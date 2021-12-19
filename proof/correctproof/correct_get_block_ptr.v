From bpf.src Require Import DxIntegers DxValues DxAST DxMemRegion DxState DxMonad DxInstructions.
From dx.Type Require Import Bool.
From dx Require Import IR.
From Coq Require Import List ZArith.
From compcert Require Import Integers Values Clight Memory AST.
From compcert Require Import Coqlib.
Import ListNotations.

From bpf.proof Require Import clight_exec Clightlogic CorrectRel MatchState CommonLemma.

From bpf.clight Require Import interpreter.


(**
Check get_block_ptr.
get_block_ptr
     : memory_region -> M val64_t
*)

Section Get_block_ptr.

  (** The program contains our function of interest [fn] *)
  Definition p : Clight.program := prog.

  (* [Args,Res] provides the mapping between the Coq and the C types *)
  (* Definition Args : list CompilableType := [stateCompilableType].*)
  Definition args : list Type := [(memory_region:Type)].
  Definition res : Type := (valu32_t:Type).

  (* [f] is a Coq Monadic function with the right type *)
  Definition f : arrow_type args (M res) := get_block_ptr.

  Variable state_block: block. (**r a block storing all rbpf state information? *)

  (* [fn] is the Cligth function which has the same behaviour as [f] *)
  Definition fn: Clight.function := f_get_block_ptr.

  (* [match_arg] relates the Coq arguments and the C arguments *)
  Definition match_arg_list : DList.t (fun x => x -> val -> stateM -> Memory.Mem.mem -> Prop) args :=
    (DList.DCons (my_match_region state_block)
       (DList.DNil _)).

  (* [match_res] relates the Coq result and the C result *)
  Definition match_res : res -> val -> stateM -> Memory.Mem.mem -> Prop := fun x v st m => valu32_correct x v.

  Instance correct_function3_get_block_ptr : forall a, correct_function3 p args res f fn (nil) true match_arg_list match_res a.
  Proof.
    intros. unfold args in a.
    car_cdr.
    correct_function_from_body.
    correct_body.
    (** how to use correct_* *)
    unfold INV.
    unfold f.
    repeat intro.
    get_invariant_more _mr.

    unfold match_region in H1.
    destruct H1 as (o & Hptr & Hmatch).
    unfold match_region_at_ofs in Hmatch.
    destruct Hmatch as (_ & _ & _ & (vptr & Hptr_load & Hinj)).
    subst.

    exists (Vint vptr), m, Events.E0.

    repeat split; unfold step2.
    -
      repeat forward_star.
      simpl.
      unfold align, Ctypes.align_attr; simpl.
      unfold Mem.loadv in Hptr_load.
      rewrite Hptr_load; reflexivity.

      simpl.
      Transparent Archi.ptr64.
      reflexivity.
    - assumption.
    - exists vptr; assumption.
    - simpl.
      constructor.
      reflexivity.
  Qed.

End Get_block_ptr.

Existing Instance correct_function3_get_block_ptr.
