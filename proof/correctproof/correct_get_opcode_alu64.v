From bpf.src Require Import DxIntegers DxValues DxOpcode DxMemRegion DxState DxMonad DxInstructions.
From Coq Require Import List Lia ZArith.
From compcert Require Import Integers Values Clight Memory.
Import ListNotations.

From bpf.proof Require Import Clightlogic MatchState CorrectRel CommonLemma.

From bpf.clight Require Import interpreter.


(**
Check get_opcode_alu64.
get_opcode_alu64
     : int8_t -> M DxOpcode.opcode_alu64

*)

Section Get_opcode_alu64.

  (** The program contains our function of interest [fn] *)
  Definition p : Clight.program := prog.

  (* [Args,Res] provides the mapping between the Coq and the C types *)
  (* Definition Args : list CompilableType := [stateCompilableType].*)
  Definition args : list Type := [(int8_t:Type)].
  Definition res : Type := (opcode_alu64:Type).

  (* [f] is a Coq Monadic function with the right type *)
  Definition f : arrow_type args (M res) := get_opcode_alu64.

  Variable state_block: block. (**r a block storing all rbpf state information? *)

  (* [fn] is the Cligth function which has the same behaviour as [f] *)
  Definition fn: Clight.function := f_get_opcode_alu64.

  (* [match_arg] relates the Coq arguments and the C arguments *)
  Definition match_arg_list : DList.t (fun x => x -> val -> stateM -> Memory.Mem.mem -> Prop) args :=
    (DList.DCons (stateless int8_correct)
                (DList.DNil _)).

  (* [match_res] relates the Coq result and the C result *)
  Definition match_res : res -> val -> stateM -> Memory.Mem.mem -> Prop := fun x v st m => opcode_alu64_correct x v.

  Instance correct_function3_get_opcode_alu64 : forall a, correct_function3 p args res f fn nil true match_arg_list match_res a.
  Proof.
    correct_function_from_body args.
    correct_body.
    (** how to use correct_* *)
    unfold INV.
    unfold f.
    repeat intro.
    get_invariant_more _op.

    unfold stateless, int8_correct in H0.
    subst.

    eexists. exists m, Events.E0.

    repeat split; unfold step2.
    -
      repeat forward_star.
    - simpl.
      (**r Search (Int.zero_ext).*)
      rewrite Int.zero_ext_idem;[idtac | lia].
      unfold match_res, opcode_alu64_correct, byte_to_opcode_alu64.
      match goal with
      | |- (match ?X with | _ => _ end) =>
          destruct X; eexists; reflexivity
      end.
    - simpl.
      constructor.
      rewrite Int.zero_ext_idem;[idtac | lia].
      simpl.
      rewrite Int.zero_ext_idem;[idtac | lia].
      reflexivity. (*
    - unfold unmodifies_effect.
      intros.
      destruct modifies.
      reflexivity.
      intros; reflexivity.*)
  Qed.

End Get_opcode_alu64.

Existing Instance correct_function3_get_opcode_alu64.
