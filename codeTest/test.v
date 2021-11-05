Require Import generated.
From dx.tests Require Import ChkPrimitive DxIntegers DxValues DxMonad DxInstructions.
From dx Require Import ResultMonad IR.
From Coq Require Import List.
From compcert Require Import Values Clight Memory.
Import ListNotations.

Definition val64_correct (x v:val) := x = v /\ exists v', Vlong v' = v.

Definition args_binary_val64_correct : DList.t (fun x => coqType x -> val -> Prop) (compilableSymbolArgTypes val64Toval64Toval64SymbolType) :=
  @DList.DCons _ _ val64CompilableType val64_correct _
               (@DList.DCons _  _
                             val64CompilableType val64_correct _
                             (@DList.DNil CompilableType _)).

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
  fun stm g m => True.

(* [match_arg] relates the Coq arguments and the C arguments *)
Definition match_arg_list : DList.t (fun x => coqType x -> val -> Prop) Args := 
  args_binary_val64_correct.

(* [match_res] relates the Coq result and the C result *)
Definition match_res : coqType Res -> val -> Prop := val64_correct.

Lemma correct_function_addl : correct_function p Args Res f fn match_mem match_arg_list match_res.
Proof.
  constructor.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - intros.
    destruct la.

Qed.

