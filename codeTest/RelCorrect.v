From compcert Require Import Integers Values AST Clight Memory.
From dx.tests Require Import DxIntegers DxValues DxAST DxMemRegion.
From dx.Type Require Import Bool.
From dx Require Import ResultMonad IR.
From Coq Require Import ZArith List.
Import ListNotations.
Require Import ChkPrimitive.

Definition val64_correct (x: val) (m: Memory.Mem.mem) (v: val) := x = v /\ exists v', Vlong v' = v.

Definition args_binary_val64_correct : DList.t (fun x => coqType x -> Memory.Mem.mem -> val -> Prop) (compilableSymbolArgTypes val64Toval64Toval64SymbolType) :=
  @DList.DCons _ _ val64CompilableType val64_correct _
               (@DList.DCons _  _
                             val64CompilableType val64_correct _
                             (@DList.DNil CompilableType _)).


Definition block_ptr_correct (x: memory_region) (m: Memory.Mem.mem) (v: val) :=
  v = block_ptr x /\
  Vlong Int64.one = block_ptr x.

Definition args_block_ptr_correct : DList.t (fun x => coqType x -> Memory.Mem.mem -> val -> Prop) (compilableSymbolArgTypes mem_regionToVal64CompilableSymbolType) :=
  @DList.DCons _  _
     mem_regionCompilableType block_ptr_correct _
     (@DList.DNil CompilableType _).

Definition start_addr_correct (x: memory_region) (m: Memory.Mem.mem) (v: val) :=
  exists b ofs vaddr, (v = Vptr b ofs) /\
  (Mem.loadv AST.Mint64 m (Vptr b ofs) = Some (start_addr x)) /\
  Vlong vaddr = start_addr x.

Definition args_start_addr_correct : DList.t (fun x => coqType x -> Memory.Mem.mem -> val -> Prop) (compilableSymbolArgTypes mem_regionToVal64CompilableSymbolType) :=
  @DList.DCons _  _
     mem_regionCompilableType start_addr_correct _
     (@DList.DNil CompilableType _).

Definition block_size_correct (x: memory_region) (m: Memory.Mem.mem) (v: val) :=
  exists b ofs vsize, (v = Vptr b ofs) /\
  (Mem.loadv AST.Mint64 m (Vptr b (Integers.Ptrofs.add ofs (Integers.Ptrofs.repr 8))) = Some (block_size x)) /\
  Vlong vsize = block_size x.

Definition args_block_size_correct : DList.t (fun x => coqType x -> Memory.Mem.mem -> val -> Prop) (compilableSymbolArgTypes mem_regionToVal64CompilableSymbolType) :=
  @DList.DCons _  _
     mem_regionCompilableType block_size_correct _
     (@DList.DNil CompilableType _).

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

(** Here *)
Definition args_is_well_chunk_correct : DList.t (fun x => coqType x -> Memory.Mem.mem -> bool -> Prop) (compilableSymbolArgTypes memoryChunkToboolSymbolType) :=
  @DList.DCons _  _
     memoryChunkCompilableType is_well_chunk_correct _
     (@DList.DNil CompilableType _).

Lemma list_no_repet_dec : forall {A:Type} eq_dec (l:list A) H,
    Coqlib.list_norepet_dec eq_dec l = left H ->
    Coqlib.list_norepet l.
Proof.
  intros.
  auto.
Qed.

Lemma exists_pair : forall {A B: Type} (x: A * B) a b,
    (fst x , snd x) = (a,b) ->
    x = (a,b).
Proof.
  destruct x; simpl ; auto.
Qed.

Lemma store_ok_if_valid :
      forall m1 chunk b ofs v
             (V : Mem.valid_access m1 chunk b ofs Writable),
        Mem.store chunk m1 b ofs v =
          Some (proj1_sig (Mem.valid_access_store m1 chunk b ofs v V)).
Proof.
  intros.
  destruct (Mem.valid_access_store m1 chunk b ofs v V).
  simpl. auto.
Qed.