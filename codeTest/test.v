Require Import ChkPrimitive RelCorrect generated.
From dx.tests Require Import DxIntegers DxValues DxState DxMonad DxInstructions.
From dx Require Import ResultMonad IR.
From Coq Require Import List.
From compcert Require Import Values Clight Memory.
Import ListNotations.
Require Import ZArith.


(** The program contains our function of interest [fn] *)
Definition p : Clight.program := prog.

(* [Args,Res] provides the mapping between the Coq and the C types *)
Definition Args : list CompilableType := [val64CompilableType; val64CompilableType].
Definition Res : CompilableType := val64CompilableType.

(* [f] is a Coq Monadic function with the right type *)
Definition f : encodeCompilableSymbolType (Some M) (MkCompilableSymbolType Args (Some Res)) := get_addl.

(* [fn] is the Cligth function which has the same behaviour as [f] *)
Definition fn: Clight.function := f_get_addl.

(* [match_mem] related the Coq monadic state and the C memory *)
Definition match_mem : stateM -> genv -> Memory.Mem.mem -> Prop :=
  fun stm g m =>
    g = globalenv p /\
      (match Globalenvs.Genv.alloc_globals (genv_genv g) (eval_mem stm) global_definitions with
       | None => True
       | Some m' => m' = m
       end).

(* [match_arg] relates the Coq arguments and the C arguments *)
Definition match_arg_list : DList.t (fun x => coqType x -> Memory.Mem.mem -> val -> Prop) Args :=
  args_binary_val64_correct.

(* [match_res] relates the Coq result and the C result *)
Definition match_res : coqType Res -> Memory.Mem.mem -> val -> Prop := val64_correct.

Lemma correct_function_addl : correct_function p Args Res f fn match_mem match_arg_list match_res.
Proof.
  constructor. (*
  - reflexivity.
  - reflexivity.
  - reflexivity.
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
    destruct c0 as (c0,c0').
    unfold val64_correct in *.
    simpl in H.
    intuition subst. destruct H3 ; subst.
    destruct H5 ; subst.
    simpl.
    eexists. eexists. eexists.
    repeat split.
    (* We need to run the program. Some automation is probably possible *)
    unfold step1.
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
      simpl. intuition congruence.
    + repeat econstructor; eauto.
    + reflexivity.
    +  eapply Smallstep.plus_one.
      econstructor; eauto.
       (* We evaluate the expresssions *)
      econstructor;eauto.
      econstructor;eauto.
      reflexivity.
      econstructor;eauto.
      reflexivity.
      Transparent Archi.ptr64.
      reflexivity.
      reflexivity.
      reflexivity.
    + unfold match_mem in H0. destruct H0 as [H0 H1]. assumption.
    + eexists;reflexivity.
Qed.
