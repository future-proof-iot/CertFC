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

  Definition stateM_correct (st:unit) (v: val) (stm:State.state) (m: Memory.Mem.mem) :=
    v = Vptr state_block Ptrofs.zero /\ match_state state_block mrs_block ins_block stm m.

  (* [match_arg] relates the Coq arguments and the C arguments *)
  Definition match_arg_list : DList.t (fun x => x -> val -> State.state -> Memory.Mem.mem -> Prop) ((unit:Type) ::args) :=
    DList.DCons stateM_correct
      (DList.DCons val_ptr_null_correct
        (DList.DNil _)).

  (* [match_res] relates the Coq result and the C result *)
  Definition match_res : res -> val -> State.state -> Memory.Mem.mem -> Prop := fun x v st m => match_bool x v.

  Instance correct_function3_cmp_ptr32_nullM : forall a, correct_function3 p args res f fn (nil) false match_arg_list match_res a.
  Proof.
    correct_function_from_body args.
    correct_body.
    (** how to use correct_* *)
    unfold INV.
    unfold f, cmp_ptr32_nullM, app.
    repeat intro.
    get_invariant _st.
    get_invariant _addr.

    unfold stateM_correct in c0.
    destruct c0 as (Hv_eq & Hmatch).
    unfold val_ptr_null_correct in c1.
    destruct c1 as (Hv0_eq & Hptr).
    destruct (rBPFValues.cmp_ptr32_null _ _) eqn: Hvalid_ptr.
    - intro.
      destruct Hptr as [Hptr | Hnull].
      + unfold rBPFValues.cmp_ptr32_null in Hvalid_ptr.
        destruct c; try inversion Hvalid_ptr.
        clear Hvalid_ptr.
        destruct Hptr as (b0 & ofs & Hptr).
        subst.
        inversion Hptr.
        clear Hvalid_ptr.

        eexists; exists m, Events.E0.
        split.
        * repeat forward_star.
          unfold Cop.sem_binary_operation, Cop.sem_cmp, Cop.cmp_ptr, Val.cmpu_bool; simpl.
          rewrite <- Hv0_eq.
          fold Int.zero.
          rewrite Int.eq_true in *.
          rewrite andb_true_l in *.
          destruct (Mem.valid_pointer _ _ _) eqn: Hvalid1.
          rewrite orb_true_l in H1; inversion H1.
          subst.
          eapply match_state_implies_valid_pointer in Hvalid1; eauto.
          rewrite Hvalid1.
          rewrite orb_true_l.
          unfold Val.of_bool, Vfalse; simpl.
          reflexivity.
          rewrite orb_false_l in H1.
          clear Hvalid1.
          destruct (Mem.valid_pointer _ _ _) eqn: Hvalid1; [| inversion H1].
          eapply match_state_implies_valid_pointer in Hvalid1; eauto.
          rewrite Hvalid1.
          rewrite orb_true_r.
          unfold Val.of_bool, Vfalse; simpl.
          reflexivity.
          simpl.
          unfold Cop.sem_cast; simpl.
          rewrite Int.eq_true.
          reflexivity.
        * split.
          unfold match_res, match_bool.
          destruct (Int.eq Int.zero Int.zero &&
       (Mem.valid_pointer (State.eval_mem st) b0 (Ptrofs.unsigned i)
        || Mem.valid_pointer (State.eval_mem st) b0 (Ptrofs.unsigned i - 1)));[| inversion H1].
          inversion H1.
          subst.
          reflexivity.
          split; [constructor; reflexivity | split; reflexivity].
      + unfold rBPFValues.cmp_ptr32_null in Hvalid_ptr.
        destruct c; inversion Hvalid_ptr.
        all: unfold Vnullptr in Hnull; simpl in Hnull;
             inversion Hnull;
             unfold Val.cmpu_bool, Vnullptr in Hvalid_ptr; simpl in Hvalid_ptr;
             inversion Hvalid_ptr; subst.
        eexists; exists m, Events.E0.
        split.
        * repeat forward_star.
        * split.
          unfold match_res, match_bool.
          rewrite Int.eq_true.
          reflexivity.
          split; [constructor; reflexivity | split; reflexivity].
    -
      constructor.
  Qed.

End Cmp_ptr32_nullM.

Existing Instance correct_function3_cmp_ptr32_nullM.
