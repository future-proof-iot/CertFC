Require Import ChkPrimitive RelCorrect interpreter.
From dx Require Import ResultMonad IR.
From dx.tests Require Import DxIntegers DxValues DxAST DxMemRegion DxState DxMonad DxInstructions.
From compcert Require Import Values Clight Memory Integers.
From Coq Require Import List ZArith.
Import ListNotations.

Require Import test_is_well_chunk_bool test_getMemRegion_block_ptr.

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

Ltac simpl_eq H :=
  repeat unfold eq_rect_r,eq_rect,eq_sym,eq_ind_r,eq_ind in H.

Ltac simpl_eq_goal :=
repeat unfold eq_rect_r,eq_rect,eq_sym,eq_ind_r,eq_ind.

Ltac nameK K :=
  match goal with
  | |-context[
          (Callstate _ _ ?k _)] =>

      set (K:= k)
  end.

Lemma bool_correct_Vint : forall r m v,
    bool_correct r m v <-> v = Vint (if r then Int.one else Int.zero).
Proof.
  unfold bool_correct. intros.
  destruct r;reflexivity.
Qed.

Lemma Int_eq_one_zero :
  Int.eq Int.one Int.zero = false.
Proof.
  reflexivity.
Qed.

Lemma memoryChunk_vint:
  forall (c : (fun x : CompilableType => coqType x * val) memoryChunkCompilableType),
     match fst c with
     | AST.Mint8unsigned => snd c = Vint Int.one
     | AST.Mint16unsigned => snd c = Vint (Int.repr 2)
     | AST.Mint32 => snd c = Vint (Int.repr 4)
     | AST.Mint64 => snd c = Vint (Int.repr 8)
     | _ => snd c = Vint (Int.repr 0)
     end -> exists x, snd c = Vint x.
Proof.
  intros; destruct (fst c) in H; rewrite H; eexists; reflexivity.
Qed.

Lemma correct_function_check_mem_aux_correct : correct_function p Args Res f fn match_mem match_arg_list match_res.
Proof.
  constructor.
  unfold Args. intro. car_cdr. simpl.
    (** Here, the goal is readable *)
  intros.
  simpl_eq_goal.

  unfold mem_region_correct, val64_correct, is_well_chunk_correct in H.
  destruct H; subst.
  assert (Hchunk: exists x, snd c1 = Vint x). admit. (*apply memoryChunk_vint.*)
  destruct Hchunk as [x Hchunk]; simpl in Hchunk.

  destruct H as (Hsndc & Hptrc & b & ofs & vaddr & vsize & Hptr & Hmaddr & Haddr & Hmsize & Hsize). (**r I just destruct here, and must automation is done *)

  destruct (f _ _ _ _) eqn: Hf.
  destruct p0.
  do 3 eexists.
  repeat split; unfold step2.
  apply Smallstep.plus_star;
  eapply Smallstep.plus_left'; eauto.
  do 2 econstructor; eauto.
  + eapply list_no_repet_dec with (eq_dec := Pos.eq_dec); reflexivity.
  + simpl; eapply list_no_repet_dec with (eq_dec := Pos.eq_dec); reflexivity.
  + simpl; unfold Coqlib.list_disjoint; simpl; intuition (subst; discriminate).
  + repeat econstructor; eauto.
  + reflexivity.
  + eapply Smallstep.plus_left'; eauto.
      repeat econstructor; eauto. (** call is_well_chunk_bool *)
      eapply Smallstep.plus_left'; eauto.
      repeat econstructor; eauto.
      eapply Smallstep.plus_left'; eauto.
      econstructor; eauto.
      simpl; reflexivity.
      econstructor.
      eapply eval_Evar_global. (**r we must tell coq to evaluate the goal with this inductive constructor otherwise coq will use another one *)
      reflexivity.
      reflexivity.
      simpl.
      eapply deref_loc_reference. (**r coq doesn't know which constructor is correct *)
      simpl; reflexivity.
      econstructor; eauto.
      econstructor; eauto.
      reflexivity.
      simpl.
      rewrite Hchunk.
      reflexivity.
      econstructor; eauto.
      econstructor; eauto.
      reflexivity.
      unfold f, check_mem_aux in Hf.
      match goal with
      | W : @bindM _ _ ?F1 ?F2 _ = _ |- _ =>
          unfold bindM at 1 in W;
          unfold runM in W;
          let X := fresh "F1" in
          let v := fresh "r" in
          let st' := fresh "st" in
          destruct F1 as [(v,st')|] eqn:X ; try congruence
      end.
  + unfold match_mem in H0; destruct H0.
    assert (Heq_st: st = s). {
      unfold f, check_mem_aux in Hf.
      unfold bindM, returnM, runM in Hf.
      destruct (is_well_chunk_bool _ _) in Hf; try (inversion Hf).
      destruct p0 in Hf.
      destruct b0 in Hf.
      destruct (getMemRegion_block_ptr _ _) in Hf; try (inversion Hf).
      destruct p0 in Hf.
      destruct (getMemRegion_start_addr _ _) in Hf; try (inversion Hf).
      destruct p0 in Hf.
      destruct (getMemRegion_block_size _ _) in Hf; try (inversion Hf).
      destruct p0 in Hf.
      destruct (get_subl _ _ _) in Hf; try (inversion Hf).
      destruct p0 in Hf.
      destruct (get_addl _ _ _) in Hf; try (inversion Hf).
      destruct p0 in Hf.
      destruct (complu_le val64_zero v2 && complu_lt v3 v1)%bool in Hf.
      apply st in Hf.
      destruct (complu_le v2 (memory_chunk_to_val64_upbound (fst c1)) && compl_eq val64_zero (val64_modlu v2 (memory_chunk_to_val64 (fst c1))))%bool in Hf.
      destruct (complu_le v2 (memory_chunk_to_val64_upbound (fst c1)) &&
        compl_eq val64_zero (val64_modlu v2 (memory_chunk_to_val64 (fst c1))))%bool in Hf.
      simpl in Hf.
      destruct p0 in Hf.
      d
    }

 assumption.
      destruct correct_function_is_well_chunk_bool.
      nameK K.
      specialize (fn_eval_ok (DList.DCons  c1  (DList.DNil _))).
      cbv zeta in fn_eval_ok.
      specialize (fn_eval_ok K st m).
      change (                 ChkPrimitive.app
                   (eq_rect_r (fun T : Type => T) test_is_well_chunk_bool.f
                      (arrow_type_encode' test_is_well_chunk_bool.Args
                         test_is_well_chunk_bool.Res M))
                   (DList.MapT (fun x : CompilableType => coqType x)
                      (fun (x : CompilableType) (v : coqType x * val) =>
                       fst v)
                      (DList.DCons c1
                         (DList.DNil
                            (fun x : CompilableType => coqType x * val)))) st
             ) with (test_is_well_chunk_bool.f (fst c1) st) in fn_eval_ok.
      unfold test_is_well_chunk_bool.f in *.
      unfold memoryChunkCompilableType,coqType in fn_eval_ok.
      rewrite F1 in fn_eval_ok.
      unfold test_is_well_chunk_bool.match_arg_list in *.
      unfold args_is_well_chunk_correct in *.
      repeat unfold DList.Forall2, DList.car
        in fn_eval_ok.
      intuition.
      destruct H8 as (v1 & m1 & t & (STEP &P1 &P2)).
      repeat unfold DList.list in STEP.
      eapply Smallstep.star_plus_trans.
      rewrite Hchunk in *.
      eapply STEP.
      (* Done - we need to continue *)
      eapply Smallstep.plus_left'; eauto.
      repeat econstructor; eauto.
      eapply Smallstep.plus_left'; eauto.
      repeat econstructor; eauto.
      eapply Smallstep.plus_left'; eauto.
      repeat econstructor; eauto.
      (* Use property of return *)
      unfold test_is_well_chunk_bool.match_res in P2.
      rewrite bool_correct_Vint in P2.
      subst.
      reflexivity.
      eapply Smallstep.plus_left'; eauto.
      repeat econstructor; eauto.
      eapply Smallstep.plus_left'; eauto.
      repeat econstructor; eauto.
      destruct r.
      (* Conditional *)
      rewrite Int_eq_one_zero.
      rewrite Int_eq_one_zero.
      unfold negb.
      (* Sequence *)
      eapply Smallstep.plus_left'; eauto.
      repeat econstructor; eauto.
      eapply Smallstep.plus_left'; eauto.
      repeat econstructor; eauto.
      (* Another call ... *)
      eapply Smallstep.plus_left'; eauto.
      econstructor; eauto.
      reflexivity.
      econstructor; eauto.
      eapply eval_Evar_global. (**r coq doesn't apply this one *)
      reflexivity.
      simpl; reflexivity.
      simpl.
      eapply deref_loc_reference. simpl; reflexivity.
      econstructor; eauto.
      econstructor; eauto.
      reflexivity.
      rewrite H2 in *.
      simpl.
      
      rewrite Hptr in *.
      unfold Cop.sem_cast, Cop.classify_cast.
      simpl.
      econstructor.
      reflexivity.
      econstructor; eauto.
      econstructor; eauto.
      reflexivity.
      
      
      destruct correct_function_block_ptr.
      nameK K.

Qed.

End Check_mem_aux.
