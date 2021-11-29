Require Import ChkPrimitive interpreter.
From dx.tests Require Import DxIntegers DxValues DxAST DxState DxMonad DxInstructions.
From dx.Type Require Import Bool.
From dx Require Import IR.
From Coq Require Import List.
From compcert Require Import Integers Values Clight Memory AST.
Import ListNotations.
Require Import ZArith.

Definition bool_correct (x:bool) (m: Memory.Mem.mem) (v: val) :=
  if x then
   v = Vtrue 
  else
   v = Vfalse.

Definition is_well_chunk_correct (x: memory_chunk) (m: Memory.Mem.mem) (b: val) :=
  match x with
  | Mint8unsigned => b = Vint (Int.one)
  | Mint16unsigned => b = Vint (Int.repr 2)
  | Mint32  => b = Vint (Int.repr 4)
  | Mint64 => b = Vint (Int.repr 8)
  | _ => b = Vint (Int.repr 0)
  end.

Definition args_is_well_chunk_correct : DList.t (fun x => coqType x -> Memory.Mem.mem -> val -> Prop) (compilableSymbolArgTypes memoryChunkToboolSymbolType) :=
  @DList.DCons _  _
     memoryChunkCompilableType is_well_chunk_correct _
     (@DList.DNil CompilableType _).

Section Is_well_chunk_bool.

(** The program contains our function of interest [fn] *)
Definition p : Clight.program := prog.

(* [Args,Res] provides the mapping between the Coq and the C types *)
Definition Args : list CompilableType := [memoryChunkCompilableType].
Definition Res : CompilableType := boolCompilableType.

(* [f] is a Coq Monadic function with the right type *)
Definition f : encodeCompilableSymbolType (Some M) (MkCompilableSymbolType Args (Some Res)) := is_well_chunk_bool.

(* [fn] is the Cligth function which has the same behaviour as [f] *)
Definition fn: Clight.function := f_is_well_chunk_bool.

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
  args_is_well_chunk_correct.

(* [match_res] relates the Coq result and the C result *)
Definition match_res : coqType Res -> Memory.Mem.mem -> val -> Prop := bool_correct.

(** How to tell compcert this relation *) (*
Axiom id_assum: __1004 = IdentDef.mem_region_id.*)

Lemma correct_function_is_well_chunk_bool : correct_function p Args Res f fn match_mem match_arg_list match_res.
Proof.
  constructor.
  - unfold Args; intro; car_cdr; simpl;
    (** Here, the goal is readable *)
    intros.
    (** Here, we know that v = Val.addl (fst c) (fst c0) and m' = m and the trace is empty*)
    (* We need to do it early or we have problems with existentials *)
    destruct c as (v,v'); unfold is_well_chunk_correct in *; simpl in H; intuition subst; clear H2;
    destruct v; subst; simpl; do 3 eexists; repeat split; unfold step2;
    try (apply Smallstep.plus_star; eapply Smallstep.plus_left'; eauto;
      do 2 econstructor; eauto;
      [ eapply list_no_repet_dec with (eq_dec := Pos.eq_dec); reflexivity |
       simpl; eapply list_no_repet_dec with (eq_dec := Pos.eq_dec); reflexivity |
       simpl; unfold Coqlib.list_disjoint; simpl; intuition congruence |
       repeat econstructor; eauto |
       reflexivity |
       repeat econstructor; eauto |
       reflexivity |
       repeat econstructor; eauto |
       repeat econstructor; eauto]);
    try (unfold match_mem in H0; destruct H0; assumption).
Qed.

End Is_well_chunk_bool.