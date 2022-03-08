From bpf.comm Require Import MemRegion State Monad.
From bpf.monadicmodel Require Import rBPFInterpreter.
From dx.Type Require Import Bool.
From dx Require Import IR.
From Coq Require Import List ZArith.
From compcert Require Import Integers Values Clight Memory AST.
From compcert Require Import Coqlib.
Import ListNotations.

From bpf.proof Require Import clight_exec Clightlogic CorrectRel MatchState CommonLemma.

From bpf.clight Require Import interpreter.


(**
Check cmp_ptr32_nullM.

cmp_ptr32_nullM
     : val -> M bool

static __attribute__((always_inline)) inline _Bool cmp_ptr32_nullM(struct bpf_state* st, unsigned char* addr){
   return (addr == 0);
}
*)

Section Cmp_ptr32_nullM.

  (** The program contains our function of interest [fn] *)
  Definition p : Clight.program := prog.

  (* [Args,Res] provides the mapping between the Coq and the C types *)
  (* Definition Args : list CompilableType := [stateCompilableType].*)
  Definition args : list Type := [(val:Type)].
  Definition res : Type := (bool:Type).

  (* [f] is a Coq Monadic function with the right type *)
  Definition f : arrow_type args (M res) := cmp_ptr32_nullM.

  Variable state_block: block. (**r a block storing all rbpf state information? *)
  Variable mrs_block: block.
  Variable ins_block: block.

  (* [fn] is the Cligth function which has the same behaviour as [f] *)
  Definition fn: Clight.function := f_cmp_ptr32_nullM.

  (* [match_arg] relates the Coq arguments and the C arguments *)
  Definition match_arg_list : DList.t (fun x => x -> val -> State.state -> Memory.Mem.mem -> Prop) args :=
    DList.DCons (val_ptr_correct state_block mrs_block ins_block)
        (DList.DNil _).

  (* [match_res] relates the Coq result and the C result *)
  Definition match_res : res -> val -> State.state -> Memory.Mem.mem -> Prop := fun x v st m => match_bool x v.

  Instance correct_function3_cmp_ptr32_nullM : forall a, correct_function3 p args res f fn (nil) true match_arg_list match_res a.
  Proof.
    correct_function_from_body args.
    correct_body.
    (** how to use correct_* *)
    unfold INV.
    unfold f, cmp_ptr32_nullM, app.
    repeat intro.
    get_invariant _addr.

    unfold val_ptr_correct in c0.
    destruct c0 as (c0 & Hst).

    unfold rBPFValues.cmp_ptr32_null, State.eval_mem.
    unfold Val.cmpu_bool.
    change Vnullptr with (Vint Int.zero); simpl.

    destruct c eqn: Hc_eq; try constructor.
    - (**r Vint i *)
      intro.
      eexists; exists m, Events.E0.
      split.

      unfold step2; forward_star.
      unfold Cop.sem_binary_operation, typeof; simpl.
      unfold Cop.sem_cmp; simpl.
      unfold Cop.cmp_ptr; simpl.
      unfold option_map; simpl.
      rewrite <- c0.
      unfold Val.cmpu_bool, Int.cmpu, Val.of_bool.
      reflexivity.

      unfold Cop.sem_cast; simpl.
      unfold Vtrue, Vfalse.
      instantiate (1:= (if Int.eq i (Int.repr 0) then Vint Int.one else Vint Int.zero)).
      fold Int.zero.
      destruct (Int.eq i Int.zero).
      rewrite Int_eq_one_zero.
      reflexivity.
      rewrite Int.eq_true.
      reflexivity.

      forward_star.
      unfold match_res, match_bool.
      fold Int.zero.
      destruct (Int.eq i Int.zero).
      split; [reflexivity | ].
      split; [constructor; reflexivity | split; reflexivity].
      split; [reflexivity | ].
      split; [constructor; reflexivity | split; reflexivity].
    - (**r Vptr b i *)
      match goal with
      | |- context[if ?X then _ else _] =>
        destruct X eqn: Heq; try constructor
      end.
      intros.
      eexists; exists m, Events.E0.
      split.

      unfold step2; repeat forward_star.
      unfold Cop.sem_binary_operation, typeof; simpl.
      unfold Cop.sem_cmp, Cop.cmp_ptr; simpl.
      unfold option_map; simpl.
      rewrite <- c0.
      unfold Val.cmpu_bool, Int.cmpu, Val.of_bool; simpl.
      fold Int.zero.
      rewrite Int.eq_true in *.
      rewrite andb_true_l in *.
      unfold Vtrue, Vfalse.

      destruct (Mem.valid_pointer _ _ _) eqn: Hvalid1.

      eapply match_state_implies_valid_pointer in Hvalid1; eauto.
      rewrite Hvalid1.
      rewrite orb_true_l.
      reflexivity.

      rewrite orb_false_l in Heq.
      clear Hvalid1.
      destruct (Mem.valid_pointer _ _ _) eqn: Hvalid1; [| inversion Heq].
      eapply match_state_implies_valid_pointer in Hvalid1; eauto.
      rewrite Hvalid1.
      rewrite orb_true_r.
      reflexivity.
      simpl.
      unfold Cop.sem_cast; simpl.
      rewrite Int.eq_true.
      reflexivity.

      split.
      + unfold match_res, match_bool.
        reflexivity.
      + split; [constructor; reflexivity | split; reflexivity].
  Qed.

End Cmp_ptr32_nullM.

Existing Instance correct_function3_cmp_ptr32_nullM.
