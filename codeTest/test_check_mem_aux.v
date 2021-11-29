Require Import ChkPrimitive interpreter.
From dx Require Import ResultMonad IR.
From dx.tests Require Import DxIntegers DxValues DxAST DxMemRegion DxState DxMonad DxInstructions.
From compcert Require Import Values Clight Memory Integers Events.
From Coq Require Import List ZArith.
Import ListNotations.

Require Import test_is_well_chunk_bool test_getMemRegion_block_ptr.

Definition val64_correct (x: val) (m: Memory.Mem.mem) (v: val) := x = v /\ exists v', Vlong v' = v.

Definition valptr_correct (x:val) (m: Memory.Mem.mem) (v: val) :=
  x = v /\
  ((x = val64_zero)\/ (exists b ofs, x = Vptr b ofs)).

Definition mem_region_correct (x: memory_region) (m: Memory.Mem.mem) (v: val) :=
  v = block_ptr x /\
  (exists b ofs vaddr vsize, (v = Vptr b ofs) /\
   (Mem.loadv AST.Mint64 m (Vptr b ofs) = Some (start_addr x)) /\
    Vlong vaddr = start_addr x /\
   (Mem.loadv AST.Mint64 m (Vptr b (Integers.Ptrofs.add ofs (Integers.Ptrofs.repr 8))) = Some (block_size x)) /\
    Vlong vsize = block_size x).

Definition memoryRegionToval64TomemoryChunkToval64SymbolType :=
  MkCompilableSymbolType [mem_regionCompilableType; val64CompilableType; memoryChunkCompilableType] (Some val64CompilableType).

(* TODO: could we just give `Definition f_name: DList.t ... (compilableSymbolArgTypes _) := [mem_region_correct; val64_correct; is_well_chunk_correct]`*)
Definition args_check_mem_aux_correct : DList.t (fun x => coqType x -> Memory.Mem.mem -> val -> Prop) (compilableSymbolArgTypes memoryRegionToval64TomemoryChunkToval64SymbolType) :=
  @DList.DCons _  _
    mem_regionCompilableType mem_region_correct _
    (@DList.DCons _  _
      val64CompilableType val64_correct _
    (@DList.DCons _  _
      memoryChunkCompilableType is_well_chunk_correct _
        (@DList.DNil CompilableType _))).

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
(*
Ltac forward_seq :=
  match goal with
  | |- Smallstep.plus _ _ (State _ (Ssequence _ _) _ _ _ _) _ _ =>
      eapply Smallstep.plus_left'; eauto; [eapply step_seq | idtac]
  end.

Ltac forward_call_one_arg :=
  match goal with
  | |- Smallstep.plus _ _ (State _ (Scall _ _ _) _ _ _ _) _ _ =>
      eapply Smallstep.plus_left'; eauto; [eapply step_call; [reflexivity | eapply eval_Elvalue;[eapply eval_Evar_global; reflexivity | eapply deref_loc_reference; reflexivity] | eapply eval_Econs; [eapply eval_Etempvar; reflexivity | reflexivity | eapply eval_Enil] | econstructor; eauto | reflexivity] | idtac]
  end.

Ltac forward_returnstate :=
  match goal with
  | |- Smallstep.plus _ _ (Returnstate _ _ _) _ _ =>
      eapply Smallstep.plus_left'; eauto; [eapply step_returnstate | idtac]
  end.

Ltac forward_skip_seq :=
  match goal with
  | |- Smallstep.plus _ _ (State _ Sskip (Kseq _ _) _ _ _) _ _ =>
      eapply Smallstep.plus_left'; eauto; [eapply step_skip_seq | idtac]
  end.

Ltac forward_if :=
  match goal with
  | |- Smallstep.plus _ _ (State _ (Sifthenelse _ _ _) _ _ _ _) _ _ =>
  eapply Smallstep.plus_left'; eauto; [eapply step_ifthenelse; [eapply eval_Etempvar; rewrite Maps.PTree.gss; reflexivity | reflexivity] | idtac]
  end.*)

Ltac forward :=
 match goal with
  (** forward_seq *)
  | |- Smallstep.plus _ _ (State _ (Ssequence _ _) _ _ _ _) _ _ =>
      eapply Smallstep.plus_left'; eauto; [eapply step_seq | idtac]
  (** forward_call_one_arg *)
  | |- Smallstep.plus _ _ (State _ (Scall _ _ _) _ _ _ _) _ _ =>
      eapply Smallstep.plus_left'; eauto;
      [eapply step_call;
        [reflexivity |                                (** goal: classify_fun *)
         eapply eval_Elvalue;                         (** goal: eval_expr *)
          [eapply eval_Evar_global; reflexivity |     (** eval_lvalue *)
           eapply deref_loc_reference; reflexivity] | (** goal: deref_loc *)
         eapply eval_Econs;                           (** goal: eval_exprlist *)
          [eapply eval_Etempvar; reflexivity |        (** goal: eval_expr *)
           reflexivity |                              (** goal: Cop.sem_cast *)
           eapply eval_Enil] |                        (** goal: eval_exprlist *)
         econstructor; eauto |                        (** goal: Globalenvs.Genv.find_funct *)
         reflexivity] |                               (** goal: type_of_fundef *)
       idtac]
  (** forward_returnstate *)
  | |- Smallstep.plus _ _ (Returnstate _ _ _) _ _ =>
      eapply Smallstep.plus_left'; eauto; [eapply step_returnstate | idtac]
  (** forward_skip_seq *)
  | |- Smallstep.plus _ _ (State _ Sskip (Kseq _ _) _ _ _) _ _ =>
      eapply Smallstep.plus_left'; eauto; [eapply step_skip_seq | idtac]
  (** forward_if *)
  | |- Smallstep.plus _ _ (State _ (Sifthenelse _ _ _) _ _ _ _) _ _ =>
    eapply Smallstep.plus_left'; eauto;
    [eapply step_ifthenelse;
      [eapply eval_Etempvar; rewrite Maps.PTree.gss; reflexivity |
       reflexivity] |
     idtac]
  (** forward_return_some *)
  | |- Smallstep.plus _ _ (State _ (Sreturn _) _ _ _ _) _ _ =>
    eapply Smallstep.plus_left'; eauto;
      [eapply step_return_1;
        [eapply eval_Econst_long |
         reflexivity |
         reflexivity] | idtac]
  end.

Ltac dx_bindM :=
  match goal with
  | W : @bindM _ _ ?F1 ?F2 _ = _ |- _ =>
      unfold bindM at 1 in W;
      unfold runM in W;
      let X := fresh "F0" in
      let v := fresh "r" in
      let st' := fresh "st" in
      destruct F1 as [(v,st')|] eqn:X ; try congruence
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

Lemma Int_eq_zero_zero :
  Int.eq Int.zero Int.zero = true.
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
  destruct H1 as ((Heq_c0 & (v' & Hc0_vlong)) & Hfst_c1 & Htrue); clear Htrue.
  assert (Hchunk: exists x, snd c1 = Vint x). apply (memoryChunk_vint c1 Hfst_c1).
  destruct Hchunk as [x Hchunk]; simpl in Hchunk.

  destruct H as (Hsndc & b & ofs & vaddr & vsize & Hptr & Hmaddr & Haddr & Hmsize & Hsize).

  destruct (f _ _ _ _) eqn: Hf.
  destruct p0.
  do 3 eexists.
  repeat split; unfold step2.
  apply Smallstep.plus_star;
  eapply Smallstep.plus_left'; eauto.
  do 2 econstructor; eauto.
  - eapply list_no_repet_dec with (eq_dec := Pos.eq_dec); reflexivity.
  - simpl; eapply list_no_repet_dec with (eq_dec := Pos.eq_dec); reflexivity.
  - simpl; unfold Coqlib.list_disjoint; simpl; intuition (subst; discriminate).
  - repeat econstructor; eauto.
  - reflexivity.
  - (** goal: Smallstep.plus _ _ (Ssequence (Ssequence (Scall ... *)
    rewrite Hchunk, Hptr.
    rewrite <- Hc0_vlong.
    eapply Smallstep.plus_left'; eauto.
    eapply step_seq.
    (** goal: Smallstep.plus _ _ (State _ (Ssequence (Scall _ Evar _is_well_chunk_bool ...)))*)
    forward.
    (** goal: Smallstep.plus _ _ (State _ (Scall _ Evar _is_well_chunk_bool ...))*)
    forward.

    (** goal: Smallstep.plus _ _ (Callstate (Ctypes.Internal f_is_well_chunk_bool) ...) *)
    unfold f in Hf.
    unfold check_mem_aux in Hf.
    dx_bindM.
    (** proving is_well_chunk_bool preserves state: st = st0 *)
    destruct correct_function_is_well_chunk_bool. (**r apply `f_is_well_chunk_bool` *)
    nameK K0.
    specialize (fn_eval_ok (DList.DCons  c1  (DList.DNil _))).
    cbv zeta in fn_eval_ok.
    specialize (fn_eval_ok K0 st m).
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
    rewrite F0 in fn_eval_ok.
    unfold test_is_well_chunk_bool.match_arg_list in *.
    unfold args_is_well_chunk_correct in *.
    repeat unfold DList.Forall2, DList.car in fn_eval_ok.
    intuition.
    destruct H1 as (v1 & m1 & t & (STEP &P1 &P2)).
    repeat unfold DList.list in STEP.
    eapply Smallstep.star_plus_trans.
    (** goal: star ge s1 t1 s2 *)
    rewrite Hchunk in *.
    eapply STEP.
    (* Done - we need to continue *)

    (* we need to solve the memory relation now *)
    unfold match_mem in H0.
    destruct H0 as (_ & H0).
    destruct (Globalenvs.Genv.alloc_globals (globalenv p) 
                                            (eval_mem s) global_definitions) in H0; subst.
    clear m0.
    unfold test_is_well_chunk_bool.p, test_is_well_chunk_bool.fn in STEP.
    
    assert (Hmem_eq: m = m1). {
      rewrite Hchunk in STEP.
      simpl in STEP.
    }
    
    (** goal: plus ge s2 t2 s3 *)
    (** goal: Smallstep.plus _ _ (Returnstate v1 (call_cont K) m1) _ (Returnstate c2 (call_cont k) ?m')*)
    forward.
    (** goal: Smallstep.plus _ _ (State _ Sskip (Kseq (Sset _well_chunk _) (Kseq (Sifthenelse ... *)
    forward.
    (** goal: Smallstep.plus _ _ (State (Sset _well_chunk _) (Kseq (Sifthenelse ... *)
    eapply Smallstep.plus_left'; eauto.
    (** goal: step _ _ (State _ (Sset _well_chunk _ (Kseq ... *)
    repeat econstructor; eauto.
    (** goal: Cop.sem_cast *)
    (* Use property of return *)
    unfold test_is_well_chunk_bool.match_res in P2.
    rewrite bool_correct_Vint in P2.
    subst.
    reflexivity.
    (** goal: Smallstep.plus _ _ (State _ Sskip (Kseq (Sifthenelse ... *)
    forward.
    (** goal: Smallstep.plus _ _ (State _ (Sifthenelse _ (Ssequence (Ssequence (Scall ... *)
    forward.
    (** goal: Smallstep.plus _ _ (State _ (if negb (Int.eq (if Int.eq (if r then Int.one else Int.zero) ... *)
    destruct (@fst AST.memory_chunk val c1); simpl in F0; unfold returnM in F0; inversion F0; subst; unfold returnM in Hf; inversion Hf; subst; repeat dx_bindM.
    + (* fst c1 = Mint8signed *)
      do 2 (rewrite Int_eq_zero_zero).
      unfold negb.
      (** goal: Smallstep.plus _ _ (State _ (Sreturn  Some ... *)
      eapply Smallstep.plus_one; eauto.
      eapply step_return_1.
      eapply eval_Econst_long.
      reflexivity.
      simpl.
      (** goal: Some m1 = Some ?m' *)
  
     
      unfold test_is_well_chunk_bool.match_mem in P1.
      destruct P1 as (Henv & P1).
      unfold test_is_well_chunk_bool.p in *.
      rewrite Henv in P1.
      unfold Globalenvs.Genv.alloc_globals in P1.
      simpl in P1.
      reflexivity.
      forward.
      eapply Smallstep.plus_left'; eauto.
(*
step (globalenv p) (function_entry2 (globalenv p))
  (Returnstate (Vlong (Int64.repr 0)) (call_cont k) m1)
  ?Goal14@{st:=s; c2:=val64_zero; s:=s; r:=false; st0:=s} 
  ?s2
*)
      repeat econstructor; eauto.
      repeat econstructor; eauto.
      repeat econstructor; eauto.
      .
      .
      .
      .
      repeat econstructor; eauto.
    destruct r; .
    + (* Conditional: r:=true *)
      rewrite Int_eq_one_zero;
      rewrite Int_eq_one_zero;
      unfold negb.
      (** goal: Smallstep.plus _ _ (State _ (Ssequence (Ssequence (Scall ... *)
      do 2 forward_seq.
      (** goal: Smallstep.plus _ _ (State _ (Scall _ (Evar _getMemRegion_block_ptr ... *)
      (* Another call ... *)
      forward_call_one_arg.
      (** goal: Smallstep.plus _ _ (Callstate (Ctypes.Internal f_getMemRegion_block_ptr) ...) *)
      destruct correct_function_block_ptr. (**r apply `f_block_ptr` *)
      nameK K1.
      specialize (fn_eval_ok (DList.DCons  c  (DList.DNil _))).
      cbv zeta in fn_eval_ok.
      specialize (fn_eval_ok K1 st m).

      change (ChkPrimitive.app
                 (eq_rect_r (fun T : Type => T)
                    test_getMemRegion_block_ptr.f
                    (arrow_type_encode'
                       test_getMemRegion_block_ptr.Args
                       test_getMemRegion_block_ptr.Res M))
                 (DList.MapT
                    (fun x : CompilableType => coqType x)
                    (fun (x : CompilableType)
                       (v : coqType x * val) => 
                     fst v)
                    (DList.DCons c
                       (DList.DNil
                          (fun x : CompilableType =>
                           coqType x * val)))) st
         ) with (test_getMemRegion_block_ptr.f (fst c) st) in fn_eval_ok.
    unfold test_getMemRegion_block_ptr.f in *.
    unfold mem_regionCompilableType, coqType in fn_eval_ok.
    rewrite F1 in fn_eval_ok.
    unfold test_is_well_chunk_bool.match_arg_list in *.
    unfold args_is_well_chunk_correct in *.
    repeat unfold DList.Forall2, DList.car in fn_eval_ok.
    intuition.
    destruct H1 as (v1 & m1 & t & (STEP &P1 &P2)).
    repeat unfold DList.list in STEP.
    eapply Smallstep.star_plus_trans.
    (** goal: star ge s1 t1 s2 *)
    rewrite Hchunk in *.
    eapply STEP.
    (* Done - we need to continue *)


      * (* Conditional: r:= false *)
(*       * (** goal: t = t1 ** t2 *)
 *)
  + unfold match_mem in H0; destruct H0.
    assert (Heq_st: st = s). {
      unfold f, check_mem_aux, is_well_chunk_bool, bindM, returnM, runM in Hf.
      unfold coqType', compilableSymbolResType, coqType, Res, val64CompilableType, val64_t, stateM in Hf.
      unfold getMemRegion_block_ptr, getMemRegion_start_addr, getMemRegion_block_size, get_subl, get_addl, memory_chunk_to_val64, complu_le, complu_lt, memory_chunk_to_val64_upbound, compl_eq, returnM in Hf.
      unfold val64_zero, val64_modlu in Hf;
      destruct (@fst AST.memory_chunk val c1) in Hf; try congruence;
      match goal with
      | W: (if ?b0 then if ?b1 then _ else _ else _) _ = _ |- _ =>
          destruct b0; destruct b1; try congruence
      end.
      }
      rewrite Heq_st in y; eapply y.
  + (**res *)
    simpl in c2.
    unfold f, check_mem_aux, is_well_chunk_bool, bindM, runM, returnM in Hf.
    unfold coqType', compilableSymbolResType, coqType, Res, val64CompilableType, val64_t, stateM in Hf.
    unfold getMemRegion_block_ptr, getMemRegion_start_addr, getMemRegion_block_size, get_subl, get_addl, memory_chunk_to_val64, complu_le, complu_lt, memory_chunk_to_val64_upbound, compl_eq, returnM in Hf.
    unfold val64_zero, val64_modlu in Hf;
    destruct (@fst AST.memory_chunk val c1) in Hf; try congruence.
    match goal with
    | W: (if ?b0 then if ?b1 then _ else _ else _) _ = _ |- _ =>
        destruct b0; destruct b1; try congruence
    end.
    destruct (@fst AST.memory_chunk val c1) eqn: Hfst_eq in Hf; congruence.
  + unfold f, check_mem_aux, is_well_chunk_bool, bindM, runM, returnM in Hf.
    unfold coqType', compilableSymbolResType, coqType, Res, val64CompilableType, val64_t, stateM in Hf.
    destruct (@fst AST.memory_chunk val c1) eqn: Hfst_eq in Hf; congruence.
  Unshelve.
  apply Events.E0.
Qed.

Definition ft := 0%nat.
Definition fs := 1%nat.

End Check_mem_aux.
