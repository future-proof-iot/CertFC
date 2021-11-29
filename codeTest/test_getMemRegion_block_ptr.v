Require Import ChkPrimitive interpreter.
From dx.tests Require Import DxIntegers DxValues DxMemRegion DxState DxMonad DxInstructions.
From dx Require Import ResultMonad IR.
From Coq Require Import List.
From compcert Require Import Integers Values Clight Memory.
Import ListNotations.
Require Import ZArith.

Definition val64_correct (x: val) (m: Memory.Mem.mem) (v: val) := x = v /\ exists v', Vlong v' = v.

Definition block_ptr_correct (x: memory_region) (m: Memory.Mem.mem) (v: val) :=
  v = block_ptr x /\
  Vlong Int64.one = block_ptr x.

Definition args_block_ptr_correct : DList.t (fun x => coqType x -> Memory.Mem.mem -> val -> Prop) (compilableSymbolArgTypes mem_regionToVal64CompilableSymbolType) :=
  @DList.DCons _  _
     mem_regionCompilableType block_ptr_correct _
     (@DList.DNil CompilableType _).


Section GetMemRegion_block_ptr.

(** The program contains our function of interest [fn] *)
Definition p : Clight.program := prog.

(* [Args,Res] provides the mapping between the Coq and the C types *)
Definition Args : list CompilableType := [mem_regionCompilableType].
Definition Res : CompilableType := val64CompilableType.

(* [f] is a Coq Monadic function with the right type *)
Definition f : encodeCompilableSymbolType (Some M) (MkCompilableSymbolType Args (Some Res)) := getMemRegion_block_ptr.

(* [fn] is the Cligth function which has the same behaviour as [f] *)
Definition fn: Clight.function := f_getMemRegion_block_ptr.

(* [match_mem] related the Coq monadic state and the C memory *)
Definition match_mem : stateM -> genv -> Mem.mem -> Prop :=
  fun stm g m =>
    g = globalenv p /\
      (match Globalenvs.Genv.alloc_globals (genv_genv g) (eval_mem stm) global_definitions with
       | None => True
       | Some m' => m' = m
       end)
.

(* [match_arg] relates the Coq arguments and the C arguments *)
Definition match_arg_list : DList.t (fun x => coqType x -> Memory.Mem.mem -> val -> Prop) Args :=
  args_block_ptr_correct.

(* [match_res] relates the Coq result and the C result *)
Definition match_res : coqType Res -> Memory.Mem.mem -> val -> Prop := val64_correct.

(** How to tell compcert this relation *) (*
Axiom id_assum: __1004 = IdentDef.mem_region_id.*)

Lemma correct_function_block_ptr : correct_function p Args Res f fn match_mem match_arg_list match_res.
Proof.
  constructor.
  - unfold Args; intro; car_cdr; simpl;
    (** Here, the goal is readable *)
    intros.
    (** Here, we know that v = Val.addl (fst c) (fst c0) and m' = m and the trace is empty*)
    (* We need to do it early or we have problems with existentials *)
    destruct c as (v,v'); unfold block_ptr_correct in *; simpl in H; intuition subst; clear H2; rewrite <- H3.
    simpl; do 3 eexists; repeat split;
    (* We need to run the program. Some automation is probably possible *)
    unfold step2.
    apply Smallstep.plus_star;
    eapply Smallstep.plus_left'; eauto.
    econstructor; eauto;
    (* We build the initial environment *)
    econstructor; eauto.
    + eapply list_no_repet_dec with (eq_dec := Pos.eq_dec); reflexivity.
    + simpl; eapply list_no_repet_dec with (eq_dec := Pos.eq_dec); reflexivity.
    + simpl; unfold Coqlib.list_disjoint; simpl; intuition congruence.
    + repeat econstructor; eauto.
    + reflexivity.
    + eapply Smallstep.plus_one;
      econstructor; eauto.
      * econstructor; eauto.
      * Transparent Archi.ptr64.
        simpl; rewrite <- H3; reflexivity.
      * compute; destruct v; simpl in *; eauto.
    + unfold match_mem in H0; destruct H0; assumption.
    + eauto.
Qed.

End GetMemRegion_block_ptr.