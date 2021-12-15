From bpf.src Require Import DxIntegers DxValues DxMemRegion DxRegs DxState DxMonad DxInstructions.
From Coq Require Import List Lia ZArith.
From compcert Require Import Integers Values Clight Memory.
Import ListNotations.

From bpf.proof Require Import Clightlogic MatchState CorrectRel CommonLemma.
From bpf.benchmark Require Import clightlogicexample.


(**
static void upd_reg (struct bpf_state* st, unsigned int i, unsigned long long v){
  ( *st).regsmap[i] = v;
}

Definition upd_reg (r: reg) (v: val64_t) : M unit := fun st => Some (tt, upd_reg r v st).
 *)


Section Upd_reg.

  (** The program contains our function of interest [fn] *)
  Definition p : Clight.program := prog.

  (* [Args,Res] provides the mapping between the Coq and the C types *)
  (* Definition Args : list CompilableType := [stateCompilableType].*)
  Definition args : list Type := [(reg:Type);val64_t].
  Definition res : Type := unit.

  (* [f] is a Coq Monadic function with the right type *)
  Definition f : arrow_type args (M res) := DxMonad.upd_reg.

  Variable state_block: block. (**r a block storing all rbpf state information? *)

  (* [fn] is the Cligth function which has the same behaviour as [f] *)
  Definition fn: Clight.function := f_upd_reg.

  Definition modifies : list block := [state_block]. (* of the C code *)

  Definition stateM_correct (st:unit) (v: val) (stm:stateM) (m: Memory.Mem.mem) :=
    v = Vptr state_block Ptrofs.zero /\ match_state state_block stm m.

  (* [match_arg] relates the Coq arguments and the C arguments *)
  Definition match_arg_list : DList.t (fun x => x -> val -> stateM -> Memory.Mem.mem -> Prop) ((unit:Type) ::args) :=
    DList.DCons stateM_correct
      (DList.DCons (stateless reg_correct)
        (DList.DCons (stateless val64_correct)
          (DList.DNil _))).

  (* [match_res] relates the Coq result and the C result *)
  Definition match_res : res -> val -> stateM -> Memory.Mem.mem -> Prop := fun _ _ _ _ => True.

  Instance correct_function3_upd_reg : correct_function3 p args res f fn modifies false match_arg_list match_res.
  Proof.
    correct_function_from_body.
    correct_body.
    repeat intro.
    unfold INV in H.
    get_invariant_more _st.
    get_invariant_more _i.
    get_invariant_more _v.
    unfold stateM_correct in H1.
    unfold stateless, reg_correct in H3.
    unfold stateless, val64_correct in H5.
    destruct H1 as (Hv_eq & Hst).
    destruct H5 as (Hc_eq & (vl & Hvl_eq)).
    subst v0 v v1 c0.

    simpl in c.
    apply (upd_regs_store m _ _ c vl) in Hst as Hstore.
    destruct Hstore as (m1 & Hstore).

    (**according to the type:
         static void upd_reg (struct bpf_state* st, unsigned int i, unsigned long long v)
       1. return value should be Vundef (i.e. void)
       2. the new memory should change the value of reg, i.e. m_reg
      *)
    exists Vundef, m1, Events.E0.

    repeat split; unfold step2.
    - (* goal: Smallstep.star  _ _ (State _ (Ssequence ... *)
      apply Smallstep.plus_star.
      repeat forward_clight.

      rewrite Ptrofs.add_zero_l.
      unfold Coqlib.align; simpl.
      assert (Heq: (8 + 8 * id_of_reg c)%Z = (Ptrofs.unsigned (Ptrofs.add (Ptrofs.repr 8) (Ptrofs.mul (Ptrofs.repr 8) (Ptrofs.of_intu (Int.repr (id_of_reg c))))))). {
        unfold Ptrofs.add, Ptrofs.mul.
        unfold id_of_reg; destruct c; try unfold Ptrofs.of_intu, Ptrofs.of_int; repeat rewrite Ptrofs.unsigned_repr; try rewrite Int.unsigned_repr; try rewrite Int_max_unsigned_eq64; try rewrite Ptrofs_max_unsigned_eq32; try lia.
      }
      rewrite <- Heq.
      rewrite <- Hstore; reflexivity.
      reflexivity.
    - simpl.
      constructor.
    - unfold unmodifies_effect, modifies, In.
      intros.
      destruct (Pos.eq_dec state_block b).
      subst b.
      exfalso.
      apply H1.
      left; reflexivity.
      apply POrderedType.PositiveOrder.neq_sym in n.
      symmetry.
      apply (Mem.load_store_other AST.Mint64 m _ _ _ m1 Hstore chk _ _).
      left; assumption.
Qed.

End Upd_reg.

Existing Instance correct_function3_upd_reg.
