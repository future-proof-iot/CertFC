From dx.tests Require Import DxIntegers DxValues DxMemRegion DxState DxMonad DxInstructions.
From Coq Require Import List.
From compcert Require Import Integers Values Clight Memory.
Import ListNotations.
Require Import ZArith.

Require Import Clightlogic MatchState CommonLemma interpreter.

(**
static void upd_pc(struct bpf_state* st, unsigned long long pc) {
  ( *st).state_pc = pc;
  return ;
}
Definition upd_pc (p: int64_t): M unit := fun st => Some (tt, upd_pc p st).
*)

Definition int64_correct (x:int64_t) (v: val) (m: Memory.Mem.mem) :=
  Vlong x = v.


Section Upd_pc.

  (** The program contains our function of interest [fn] *)
  Definition p : Clight.program := prog.

  (* [Args,Res] provides the mapping between the Coq and the C types *)
  (* Definition Args : list CompilableType := [stateCompilableType].*)
  Definition args : list Type := [(int64_t:Type)].
  Definition res : Type := unit.

  (* [f] is a Coq Monadic function with the right type *)
  Definition f : arrow_type args (M res) := DxMonad.upd_pc.

  Variable state_block: block. (**r a block storing all rbpf state information? *)

  (* [fn] is the Cligth function which has the same behaviour as [f] *)
  Definition fn: Clight.function := f_upd_pc.

  Definition modifies : list block := [state_block]. (* of the C code *)
  (* [match_mem] related the Coq monadic state and the C memory *)
  Definition match_mem : stateM -> val -> Memory.Mem.mem -> Prop := fun stM v m => match_meminj_state state_block inject_id stM m.

  (* [match_arg] relates the Coq arguments and the C arguments *)
  Definition match_arg_list : DList.t (fun x => x -> val -> Memory.Mem.mem -> Prop) args := DList.DCons int64_correct (DList.DNil _).

  (* [match_res] relates the Coq result and the C result *)
  Definition match_res : res -> val -> Memory.Mem.mem -> Prop := fun _ _ _ => True.

  Lemma correct_function3_upd_pc : correct_function3 p args res f fn modifies match_mem match_arg_list match_res.
  Proof.
    apply correct_function_from_body.
    - simpl; unfold Coqlib.list_disjoint. simpl; intuition (subst; discriminate).
    - eapply list_no_repet_dec with (eq_dec := Pos.eq_dec); reflexivity.
    - simpl; eapply list_no_repet_dec with (eq_dec := Pos.eq_dec); reflexivity.
    - reflexivity.
    - simpl. admit.
    - intros.
      unfold args in *.
      car_cdr.
      unfold app, list_rel_arg.
      simpl.
      unfold correct_body.
      repeat intro.
      unfold pre in *.
      do 3 eexists.
      ...
      repeat intro.
     reflexivity. repeat econstructor; eauto.
  - reflexivity.
  -
  Qed.

End Upd_pc.
