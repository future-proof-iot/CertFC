Require Import ChkPrimitive RelCorrect generated.
From dx.tests Require Import DxIntegers DxValues DxMemRegion DxState DxMonad DxInstructions.
From dx Require Import ResultMonad IR.
From Coq Require Import List.
From compcert Require Import Values Clight Memory.
Import ListNotations.
Require Import ZArith.



Section GetMemRegion_start_addr.

(** The program contains our function of interest [fn] *)
Definition p : Clight.program := prog.

(* [Args,Res] provides the mapping between the Coq and the C types *)
Definition Args : list CompilableType := [mem_regionCompilableType].
Definition Res : CompilableType := val64CompilableType.

(* [f] is a Coq Monadic function with the right type *)
Definition f : encodeCompilableSymbolType (Some M) (MkCompilableSymbolType Args (Some Res)) := getMemRegion_start_addr.

(* [fn] is the Cligth function which has the same behaviour as [f] *)
Definition fn: Clight.function := f_getMemRegion_start_addr.

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
  args_start_addr_correct.

(* [match_res] relates the Coq result and the C result *)
Definition match_res : coqType Res -> Memory.Mem.mem -> val -> Prop := val64_correct.

(** How to tell compcert this relation *) (*
Axiom id_assum: __1004 = IdentDef.mem_region_id.*)

Lemma correct_function_start_addr : correct_function p Args Res f fn match_mem match_arg_list match_res.
Proof.
  constructor. (*
  - reflexivity.
  - reflexivity.
  - unfold Args.
    simpl.
    unfold mem_region_type.
    unfold Clightdefs.tptr.
    rewrite id_assum.
    reflexivity.
  - reflexivity.*)
  - unfold Args.
    intro.
    car_cdr.
    simpl.
    (** Here, the goal is readable *)
    intros.
    (** Here, we know that v = Val.addl (fst c) (fst c0) and m' = m and the trace is empty*)
    (* We need to do it early or we have problems with existentials *)
    destruct c as (v,v').
    unfold start_addr_correct in *.
    simpl in H.
    intuition subst. clear H2. destruct H1 ; subst. destruct H as [ofs [vaddr [H [H1 H2]]]].
    simpl.
    do 3 eexists.
    repeat split.
    (* We need to run the program. Some automation is probably possible *)
    unfold step2.
    apply Smallstep.plus_star.
    eapply Smallstep.plus_left';eauto.
    econstructor ; eauto.
    (* We build the initial environment *)
    econstructor;eauto.
    +
      eapply list_no_repet_dec with (eq_dec := Pos.eq_dec).
      reflexivity.
    + simpl.
      eapply list_no_repet_dec with (eq_dec := Pos.eq_dec).
      reflexivity.
    + simpl.
      unfold Coqlib.list_disjoint.
      simpl; intuition congruence.
    + repeat econstructor; eauto.
    + reflexivity.
    + eapply Smallstep.plus_one.
      econstructor; eauto.
      * econstructor;eauto.
        econstructor;eauto.
        econstructor;eauto.
        econstructor;eauto.
        econstructor;eauto.
        rewrite H; reflexivity; simpl.
        apply deref_loc_copy; simpl; reflexivity.
        reflexivity.
        reflexivity.
        reflexivity.
        simpl; econstructor;eauto.
        simpl; reflexivity.
        Transparent Archi.align_int64.
        unfold Archi.align_int64; unfold Coqlib.align; simpl.
        rewrite Integers.Ptrofs.add_zero.
        rewrite H1; reflexivity.
      * simpl; rewrite <- H2.
        Transparent Archi.ptr64.
        reflexivity.
      * compute; destruct v; simpl in *.
        eauto.
    + unfold match_mem in H0.
      destruct H0; assumption.
    + eauto.
Qed.

End GetMemRegion_start_addr.