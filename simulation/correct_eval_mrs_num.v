(**************************************************************************)
(*  This file is part of CertrBPF,                                        *)
(*  a formally verified rBPF verifier + interpreter + JIT in Coq.         *)
(*                                                                        *)
(*  Copyright (C) 2022 Inria                                              *)
(*                                                                        *)
(*  This program is free software; you can redistribute it and/or modify  *)
(*  it under the terms of the GNU General Public License as published by  *)
(*  the Free Software Foundation; either version 2 of the License, or     *)
(*  (at your option) any later version.                                   *)
(*                                                                        *)
(*  This program is distributed in the hope that it will be useful,       *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the         *)
(*  GNU General Public License for more details.                          *)
(*                                                                        *)
(**************************************************************************)

From bpf.comm Require Import MemRegion State Monad rBPFMonadOp.
From Coq Require Import List Lia.
From compcert Require Import Integers Values Clight Memory.
Import ListNotations.
Require Import ZArith.

From bpf.clightlogic Require Import Clightlogic CorrectRel CommonLemma.

From bpf.clight Require Import interpreter.

From bpf.simulation Require Import MatchState InterpreterRel.


(**
static __attribute__((always_inline)) inline unsigned int eval_mrs_num(struct bpf_state* st){
  return ( *st).mrs_num;
}

Print eval_mrs_num.
eval_mrs_num = fun st : State.state => Some (eval_mem_num st, st)
     : M nat

*)

Section Eval_mrs_num.
  Context {S : special_blocks}.

  (** The program contains our function of interest [fn] *)
  Definition p : Clight.program := prog.

  (* [Args,Res] provides the mapping between the Coq and the C types *)
  Definition args : list Type := [].
  Definition res : Type := (nat:Type).

  (* [f] is a Coq Monadic function with the right type *)
  Definition f : arrow_type args (M State.state res) := eval_mrs_num.

  (* [fn] is the Cligth function which has the same behaviour as [f] *)
  Definition fn: Clight.function := f_eval_mrs_num.

  (* [match_arg] relates the Coq arguments and the C arguments *)
  Definition match_arg_list : DList.t (fun x => x -> Inv _) ((unit:Type) ::args) :=
    (dcons (fun _ => StateLess _ is_state_handle)
                (DList.DNil _)).

  (* [match_res] relates the Coq result and the C result *)
  Definition match_res : res -> Inv State.state := fun re => StateFull _ (fun v st m => nat_correct re v /\ re = (mrs_num st)).

  Instance correct_function_eval_mrs_num : forall a, correct_function _ p args res f fn ModNothing false match_state match_arg_list match_res a.
  Proof.
    correct_function_from_body args.
    correct_body.
    (** how to use correct_* *)
    unfold INV.
    unfold f.
    repeat intro.
    get_invariant _st.
    unfold eval_inv, is_state_handle in c.
    subst.

    assert (Hst' := MS).
    destruct Hst'. clear - MS p0 mmrs_num mem_regs.

    eexists. exists m, Events.E0.

    split_and.
    {
      repeat forward_star.
      rewrite Ptrofs.add_zero_l.
      unfold Coqlib.align; simpl. change (832 / 8)%Z with 104%Z.

      destruct mmrs_num as (mmrs_num & _).
      unfold Mem.loadv in mmrs_num.
      rewrite mmrs_num.
      reflexivity.
      reflexivity.
    }
    split.
    {
      unfold match_res, nat_correct, eval_mem_num.
      split.
      reflexivity.
      unfold match_regions in mem_regs.
      destruct mem_regs as (_ & Hlen & Hrange & _).
      rewrite Hlen in Hrange.
      change Int.max_unsigned with Ptrofs.max_unsigned.
      lia.
    }
    unfold eval_mem_num. reflexivity.
    constructor. reflexivity.
    auto.
    apply unmodifies_effect_refl.
  Qed.

End Eval_mrs_num.

Existing Instance correct_function_eval_mrs_num.
