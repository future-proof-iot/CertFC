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

Lemma correct_function_check_mem_aux_correct_aux:
  forall
(c : (fun x : CompilableType => coqType x * val) mem_regionCompilableType)
(c0 : (fun x : CompilableType => coqType x * val) val64CompilableType)
(c1 : (fun x : CompilableType => coqType x * val) memoryChunkCompilableType)
(k : cont)
(st : stateM)
(m : mem)
(Hsndc : snd c = block_ptr (fst c))
(Hptrc : Vlong Int64.one = block_ptr (fst c))
(b : block)
(ofs : ptrofs)
(vaddr vsize : int64)
(Hptr : snd c = Vptr b ofs)
(Hmaddr : Mem.loadv AST.Mint64 m (Vptr b ofs) = Some (start_addr (fst c)))
(Haddr : Vlong vaddr = start_addr (fst c))
(Hmsize : Mem.loadv AST.Mint64 m (Vptr b (Ptrofs.add ofs (Ptrofs.repr 8))) =
         Some (block_size (fst c)))
(Hsize : Vlong vsize = block_size (fst c))
(Heq_c0 : fst c0 = snd c0)
(v' : int64)
(Hc0_vlong : Vlong v' = snd c0)
(Hfst_c1 : match fst c1 with
          | AST.Mint8unsigned => snd c1 = Vint Int.one
          | AST.Mint16unsigned => snd c1 = Vint (Int.repr 2)
          | AST.Mint32 => snd c1 = Vint (Int.repr 4)
          | AST.Mint64 => snd c1 = Vint (Int.repr 8)
          | _ => snd c1 = Vint (Int.repr 0)
          end)
(H0 : match_mem st (globalenv p) m)
(x : int)
(Hchunk : snd c1 = Vint x)
(c2 : coqType'
       (compilableSymbolResType
          {| compilableSymbolArgTypes := Args; compilableSymbolResType := Some Res |}))
(s : DxState.state)
(Hf : f (fst c) (fst c0) (fst c1) st = Some (c2, s)),
  (*exists t2,*)
Smallstep.plus (fun ge : genv => step ge (function_entry2 ge))
  (globalenv p)
  (State fn (fn_body fn) k empty_env
     (Maps.PTree.set _chunk1 (snd c1)
        (Maps.PTree.set _addr0 (snd c0)
           (Maps.PTree.set _mr3 (snd c) (create_undef_temps (fn_temps fn))))) m) 
  Events.E0 (Returnstate c2 (call_cont k) m).
Proof.
  intros.
  (*exists Events.E0.*)
  eapply Smallstep.plus_left' with (t1:= Events.E0) (t2:= Events.E0); eauto.
  repeat econstructor; eauto. (** call is_well_chunk_bool *)
  eapply Smallstep.plus_left' with (t1:= Events.E0) (t2:= Events.E0); eauto.
  repeat econstructor; eauto.
  eapply Smallstep.plus_left' with (t1:= Events.E0) (t2:= Events.E0); eauto.
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
  unfold coqType, memoryChunkCompilableType in Hchunk.
  (* Set Printing All. *)
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

  destruct H as (Hsndc & Hptrc & b & ofs & vaddr & vsize & Hptr & Hmaddr & Haddr & Hmsize & Hsize). (**r I just destruct here, and must automation is done *)

  destruct (f _ _ _ _) eqn: Hf.
  destruct p0.
  eexists. exists m, Events.E0.
  (*do 3 eexists.*)
  repeat split; unfold step2.
  apply Smallstep.plus_star;
  eapply Smallstep.plus_left'; eauto.
  do 2 econstructor; eauto.
  + eapply list_no_repet_dec with (eq_dec := Pos.eq_dec); reflexivity.
  + simpl; eapply list_no_repet_dec with (eq_dec := Pos.eq_dec); reflexivity.
  + simpl; unfold Coqlib.list_disjoint; simpl; intuition (subst; discriminate).
  + repeat econstructor; eauto.
  + reflexivity.
  + apply correct_function_check_mem_aux_correct_aux with (b:=b) (st := st) (ofs:=ofs) (vaddr:=vaddr) (vsize:=vsize)(v':=v') (x:=x) (s:=s); assumption. (*eapply Smallstep.plus_left'; eauto.
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
    end.*)
  + repeat (rewrite Events.E0_left). eauto.
  + unfold match_mem in H0; destruct H0.
    assert (Heq_st: st = s). {
      unfold f, check_mem_aux, is_well_chunk_bool, bindM, returnM, runM in Hf.
      unfold coqType', compilableSymbolResType, coqType, Res, val64CompilableType, val64_t, stateM in Hf.
      destruct (@fst AST.memory_chunk val c1) eqn: Hfst_eq in Hf; congruence.
      }
      rewrite Heq_st in H0; assumption.
  + (**res *)
    simpl in c2.
    unfold f, check_mem_aux, is_well_chunk_bool, bindM, runM, returnM in Hf.
    unfold coqType', compilableSymbolResType, coqType, Res, val64CompilableType, val64_t, stateM in Hf.
    destruct (@fst AST.memory_chunk val c1) eqn: Hfst_eq in Hf; congruence.
  + unfold f, check_mem_aux, is_well_chunk_bool, bindM, runM, returnM in Hf.
    unfold coqType', compilableSymbolResType, coqType, Res, val64CompilableType, val64_t, stateM in Hf.
    destruct (@fst AST.memory_chunk val c1) eqn: Hfst_eq in Hf; congruence.
Qed.

Definition ft := 0%nat.
Definition fs := 1%nat.

End Check_mem_aux.
