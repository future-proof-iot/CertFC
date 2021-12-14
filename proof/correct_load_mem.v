From dx.tests Require Import DxIntegers DxValues DxMemRegion DxRegs DxState DxMonad DxInstructions.
From Coq Require Import List Lia ZArith.
From compcert Require Import Integers Values Clight Memory AST.
Import ListNotations.

From bpf.proof Require Import Clightlogic MatchState CorrectRel CommonLemma interpreter.

(**
static unsigned long long load_mem(struct bpf_state* st, unsigned int chunk, unsigned long long v){
  switch (chunk) {
    case 1: return (unsigned long long) *(unsigned char * ) (intptr_t)v;
    case 2: return (unsigned long long) *(unsigned short * ) (intptr_t)v;
    case 4: return (unsigned long long) *(unsigned int * ) (intptr_t)v;
    case 8: return (unsigned long long) *(unsigned long long * ) (intptr_t) v;
    default: /*printf ("load:addr = %" PRIu64 "\n", v);*/ /*( *st).bpf_flag = BPF_ILLEGAL_MEM; */ return 0;
  }
}

Definition load_mem (chunk: memory_chunk) (ptr: val64_t): M val64_t := fun st => Some (load_mem chunk ptr st, st).

 *)


Section Load_mem.

  (** The program contains our function of interest [fn] *)
  Definition p : Clight.program := prog.

  (* [Args,Res] provides the mapping between the Coq and the C types *)
  (* Definition Args : list CompilableType := [stateCompilableType].*)
  Definition args : list Type := [(memory_chunk:Type); val64_t].
  Definition res : Type := (val64_t:Type).

  (* [f] is a Coq Monadic function with the right type *)
  Definition f : arrow_type args (M res) := DxMonad.load_mem.

  Variable state_block: block. (**r a block storing all rbpf state information? *)

  (* [fn] is the Cligth function which has the same behaviour as [f] *)
  Definition fn: Clight.function := f_load_mem.

  Definition modifies : list block := [state_block]. (* of the C code *)

  Definition stateM_correct (st:unit) (v: val) (stm:stateM) (m: Memory.Mem.mem) :=
    v = Vptr state_block Ptrofs.zero /\ match_state state_block stm m /\ match_regions (bpf_mrs stm) state_block m.

  (* [match_arg] relates the Coq arguments and the C arguments *)
  Definition match_arg_list : DList.t (fun x => x -> val -> stateM -> Memory.Mem.mem -> Prop) ((unit:Type) ::args) :=
    DList.DCons stateM_correct
                (DList.DCons (stateless match_chunk)
                             (DList.DCons (stateless val64_correct)
                                          (DList.DNil _))).

  (* [match_res] relates the Coq result and the C result *)
  Definition match_res : res -> val -> stateM -> Memory.Mem.mem -> Prop := fun x v st m => val64_correct x v.
Ltac exec_seq_of_labeled_statement :=
  match goal with
  | |- context[seq_of_labeled_statement ?X] =>
      let x := (eval simpl in (seq_of_labeled_statement X)) in
      change (seq_of_labeled_statement X) with x
  end.

  Instance correct_function3_load_mem : correct_function3 p args res f fn modifies false match_arg_list match_res.
  Proof.
    correct_function_from_body.
    correct_body.
    unfold f, INV.
    repeat intro.
    get_invariant_more _st.
    get_invariant_more _chunk.
    get_invariant_more _v.
    unfold stateM_correct in H1.
    unfold stateless, match_chunk in H3.
    unfold stateless, val64_correct in H5.
    destruct H1 as (Hptr & Hmatch).
    destruct H5 as (Hc0_eq & (vl & Hvl_eq)).
    subst v v1 c0.
    
    destruct Hmatch.
    clear mpc mregs mflags mperm.

    (**according to:
         static unsigned long long load_mem(struct bpf_state* st, unsigned int chunk, unsigned long long v)
       1. return value should be Vlong.
       2. the memory is same
     *)
    
    destruct c.
    - exists (Vlong (Int64.repr 0)); subst v0; exists m, Events.E0.
      repeat split.
      eapply Smallstep.star_step; eauto.
      econstructor; eauto.
      econstructor; eauto.
      econstructor.
      eapply Smallstep.star_step; eauto;
      [econstructor;eauto |
        eapply Smallstep.star_step; eauto ; [econstructor; eauto;
                                             econstructor; eauto|]].
      eapply Smallstep.star_refl.
      reflexivity.
      
      simpl.
      rewrite Int.signed_repr.
      eapply Smallstep.star_refl.
      
      
    - 
    repeat split.
    - eapply Smallstep.star_step; eauto.
      econstructor; eauto.
      econstructor; eauto.
      econstructor.
      unfold Int.one.
      reflexivity.

      
      destruct c; subst v0.
      + 
        eapply Smallstep.plus_left'; eauto.
        repeat econstructor; eauto.
        reflexivity.
        eapply Smallstep.plus_left'; eauto.
        econstructor;eauto.
        simpl.
        eapply Smallstep.plus_one; eauto.
        eapply step_return_1.
        exec_seq_of_labeled_statement.



        
        eapply Smallstep.plus_left'; eauto.
        repeat econstructor; eauto.
        eapply Smallstep.plus_one; eauto.
        econstructor; eauto.
      econstructor; eauto.

















      
      forward_plus.
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
  

End Load_mem.

Existing Instance correct_function3_load_mem.
