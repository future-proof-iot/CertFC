From bpf.src Require Import DxIntegers DxValues DxMonad DxMemRegion DxRegs DxState DxMonad DxInstructions.
From Coq Require Import List Lia ZArith.
From compcert Require Import Integers Values Clight Memory Memdata.
Import ListNotations.

From bpf.proof Require Import Clightlogic MatchState CorrectRel CommonLemma CommonLib.

From bpf.clight Require Import interpreter.


(**
Check upd_reg.
upd_reg
     : reg -> val64_t -> M unit
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
  Definition match_res : res -> val -> stateM -> Memory.Mem.mem -> Prop := fun _ _ st m => match_state state_block st m.

  Instance correct_function3_upd_reg : forall a, correct_function3 p args res f fn modifies false match_arg_list match_res a.
  Proof.
    correct_function_from_body args.
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
    subst.

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
      repeat forward_star.

      unfold Coqlib.align; simpl.
      rewrite Ptrofs.add_zero_l.
      assert (Heq: (8 + 8 * id_of_reg c)%Z = (Ptrofs.unsigned (Ptrofs.add (Ptrofs.repr 8) (Ptrofs.mul (Ptrofs.repr 8) (Ptrofs.of_intu (Int.repr (id_of_reg c))))))). {
        unfold Ptrofs.add, Ptrofs.mul.
        unfold id_of_reg; destruct c; try unfold Ptrofs.of_intu, Ptrofs.of_int; repeat rewrite Ptrofs.unsigned_repr; try rewrite Int.unsigned_repr; try rewrite Int_max_unsigned_eq64; try rewrite Ptrofs_max_unsigned_eq32; try lia.
      }
      rewrite <- Heq.
      rewrite <- Hstore; reflexivity.
    - intros.
      unfold inject_id in H1; inversion H1; subst.
      clear H1; rewrite Z.add_0_r.
      (**r the memory relation is:
          - Hst: match_state _ st m (between rbpf's st Clight's m)
          - H3: Mem.perm (bpf_m st1) ... (the permission in the rbpf level)
          - goal: Mem.perm m1 ... (the permission in the Clight-level)
        *)
      destruct Hst; clear mpc mflags mregs mrs_num mem_regs mperm.
      apply (upd_reg_preserves_perm c (Vlong vl) _ _ st (bpf_m (DxState.upd_reg c (Vlong vl) st)) m m1 b2 _ ofs _ k0 p3 minj Hstore); [reflexivity | assumption].
    - intros.
      (**r Search Z.divide. *)
      unfold inject_id in H1; inversion H1.
      apply Z.divide_0_r.
    - intros. (**r inject_id is weak, we need inject_id' to say something about state_block *)
      unfold inject_id in H1; inversion H1; clear H1.
      rewrite Z.add_0_r; subst.
      unfold DxState.upd_reg in H3.
      simpl in H3. (** however b2 does not exist in st! and how to say b2 = state_block *)
      exfalso.
      destruct Hst; clear - minvalid H3.
      specialize minvalid with AST.Mint64 ofs Readable.
      destruct minvalid.
      apply H0.
      
      
      admit.
    - intros.
      exfalso.
      apply H1.
      destruct Hst. (**r TODO *) admit. ; clear mpc mflags mregs mrs_num mem_regs mperm.
      (**r we have: It seems `inject_id` is too weak???
        - minj : Mem.inject inject_id (bpf_m st) m
        - H : Mem.store AST.Mint64 (bpf_m st) b 0 (Vlong vl) = (bpf_m (DxState.upd_reg c (Vlong vl) st)).
        - F : inject_id b = Some (b, 0).
        - VF: Val.inject inject_id (Vlong vl) (Vlong vl)
        - we could get `exists n2, store AST.Mint64 m b 0 (Vlong vl) = Some n2
    /\ inject inject_id (bpf_m (DxState.upd_reg c (Vlong vl) st)) n2`.
        - Hstore : Mem.store AST.Mint64 m state_block (8 + 8 * id_of_reg c) (Vlong vl) =
         Some m1
        *)
      apply Mem.valid_block_inject_2 with (f:=inject_id) (m1:= (bpf_m (DxState.upd_reg c (Vlong vl) st))) (b1:= b)(delta:= 0%Z).
      reflexivity.
      unfold Mem.inject.
      

    - intros.
      simpl.
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
