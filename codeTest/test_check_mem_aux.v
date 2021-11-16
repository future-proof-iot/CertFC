Require Import ChkPrimitive RelCorrect interpreter.
From dx Require Import ResultMonad IR.
From dx.tests Require Import DxIntegers DxValues DxAST DxMemRegion DxState DxMonad DxInstructions.
From compcert Require Import Values Clight Memory.
From Coq Require Import List ZArith.
Import ListNotations.

Require Import test_is_well_chunk_bool.

Section Check_mem_aux.

(** The program contains our function of interest [fn] *)
Definition p : Clight.program := prog.

(* [Args,Res] provides the mapping between the Coq and the C types *)
Definition Args : list CompilableType := [mem_regionCompilableType; val64CompilableType; memoryChunkCompilableType].
Definition Res : CompilableType := val64CompilableType.

(* [f] is a Coq Monadic function with the right type *)
Definition f : encodeCompilableSymbolType (Some M) (MkCompilableSymbolType Args (Some Res)) := check_mem_aux.

(* [fn] is the Cligth function which has the same behaviour as [f] *)
Definition fn: Clight.function := f_check_mem_aux.

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
  args_check_mem_aux_correct.

(* [match_res] relates the Coq result and the C result *)
Definition match_res : coqType Res -> Memory.Mem.mem -> val -> Prop := valptr_correct.

(** How to tell compcert this relation *) (*
Axiom id_assum: __1004 = IdentDef.mem_region_id.*)

Lemma correct_function_check_mem_aux_correct : correct_function p Args Res f fn match_mem match_arg_list match_res.
Proof.
  constructor.
  unfold Args; intro; car_cdr; simpl;
    (** Here, the goal is readable *)
    intros.
    destruct c as (v,v').
    unfold mem_region_correct, val64_correct, is_well_chunk_correct in H;
    intuition subst; clear H7;
    destruct H5 as [b [ofs [vaddr [vsize [Hptr [Hmptr [Haddr [Hmaddr Hsize]]]]]]]];
    destruct H6 as [v0 H6]; subst;
    rewrite <- H6 in H3. simpl in *; rewrite H3; simpl.
    destruct (fst c1) eqn: Hc1 in H1; subst;
    simpl in *; rewrite Hc1; simpl.
    do 3 eexists; repeat split; unfold step2.
    apply Smallstep.plus_star;
    eapply Smallstep.plus_left'; eauto.
    do 2 econstructor; eauto.
    + eapply list_no_repet_dec with (eq_dec := Pos.eq_dec); reflexivity.
    + simpl; eapply list_no_repet_dec with (eq_dec := Pos.eq_dec); reflexivity.
    + simpl; unfold Coqlib.list_disjoint; simpl; intuition congruence.
    + repeat econstructor; eauto.
    + reflexivity.
    + rewrite H1, Hptr; rewrite <- H6. eapply Smallstep.plus_left'; eauto; repeat econstructor; eauto. Print Maps.PTree.get.
      simpl.

    destruct c as (v,v'); unfold block_size_correct in *; simpl in H; intuition subst; clear H2; destruct H1 ; subst.
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
        simpl; rewrite <- H1; reflexivity.
      * compute; destruct v; simpl in *; eauto.
    + unfold match_mem in H0; destruct H0; assumption.
    + eauto.
Qed.

End Check_mem_aux.