From Coq Require Import List ZArith.
Import ListNotations.

From compcert.cfrontend Require Csyntax Ctypes Cop.
From compcert.common Require Import Values.
From compcert.lib Require Integers.

From dx Require Import ResultMonad IR.
From dx.Type Require Import Nat.

Require Import IdentDef CoqIntegers DxIntegers DxValues.

Record memory_region : Type := mkmr{
  block_ptr  : val64_t;
  start_addr : val64_t;
  block_size : val64_t;
}.

Record memory_regions : Type := mkmrs{
  bpf_ctx: memory_region;
  bpf_stk: memory_region;
  content: memory_region;
}.

Definition default_memory_region := {|
  block_ptr  := val64_zero;
  start_addr := val64_zero;
  block_size := val64_zero;
|}.

Definition default_memory_regions := {|
  bpf_ctx := default_memory_region;
  bpf_stk := default_memory_region;
  content := default_memory_region;
|}.

(******************** Dx Related *******************)

Definition mem_region_type: Ctypes.type := Ctypes.Tstruct mem_region_id Ctypes.noattr.

Definition mem_region_def: Ctypes.composite_definition := 
  Ctypes.Composite mem_region_id Ctypes.Struct [(start_addr_id, C_U64); (size_id, C_U32)] Ctypes.noattr.

Definition mem_regions_type: Ctypes.type := Ctypes.Tstruct mem_regions_id Ctypes.noattr.

Definition mem_regions_def: Ctypes.composite_definition := 
  Ctypes.Composite mem_regions_id Ctypes.Struct [(bpf_ctx_id, mem_region_type); (bpf_stk_id, mem_region_type); (content_id, mem_region_type)] Ctypes.noattr.

Definition mem_regionCompilableType := MkCompilableType memory_region mem_region_type.
Definition mem_regionsCompilableType := MkCompilableType memory_regions mem_regions_type.

(** Type for mem_region -> val64_t *)
Definition mem_regionToVal64CompilableSymbolType :=
  MkCompilableSymbolType [mem_regionCompilableType] (Some val64CompilableType).

Definition Const_block_ptr := 
  MkPrimitive mem_regionToVal64CompilableSymbolType 
              block_ptr
              (fun es => match es with
                         | [e1] => Ok (C_U64_one)
                         | _   => Err PrimitiveEncodingFailed
                         end).

Definition Const_start_addr := 
  MkPrimitive mem_regionToVal64CompilableSymbolType 
              start_addr
              (fun es => match es with
                         | [e1] => Ok (Csyntax.Efield e1 start_addr_id C_U64)
                         | _   => Err PrimitiveEncodingFailed
                         end).

Definition Const_block_size := 
  MkPrimitive mem_regionToVal64CompilableSymbolType 
              block_size
              (fun es => match es with
                         | [e1] => Ok (Csyntax.Efield e1 size_id C_U64)
                         | _   => Err PrimitiveEncodingFailed
                         end).

(** Type for mem_regions -> mem_region *)
Definition mem_regionTomem_regionsCompilableSymbolType :=
  MkCompilableSymbolType [mem_regionsCompilableType] (Some mem_regionCompilableType).

Definition Const_bpf_ctx := 
  MkPrimitive mem_regionTomem_regionsCompilableSymbolType 
              bpf_ctx
              (fun es => match es with
                         | [e1] => Ok (Csyntax.Efield e1 bpf_ctx_id mem_region_type)
                         | _   => Err PrimitiveEncodingFailed
                         end).

Definition Const_bpf_stk := 
  MkPrimitive mem_regionTomem_regionsCompilableSymbolType 
              bpf_stk
              (fun es => match es with
                         | [e1] => Ok (Csyntax.Efield e1 bpf_stk_id mem_region_type)
                         | _   => Err PrimitiveEncodingFailed
                         end).

Definition Const_content := 
  MkPrimitive mem_regionTomem_regionsCompilableSymbolType 
              content
              (fun es => match es with
                         | [e1] => Ok (Csyntax.Efield e1 content_id mem_region_type)
                         | _   => Err PrimitiveEncodingFailed
                         end).


Module Exports.
  Definition mem_regionCompilableType := mem_regionCompilableType.
  Definition mem_regionsCompilableType:= mem_regionsCompilableType.
  Definition Const_block_ptr          := Const_block_ptr.
  Definition Const_start_addr         := Const_start_addr.
  Definition Const_block_size         := Const_block_size.
  Definition Const_bpf_ctx            := Const_bpf_ctx.
  Definition Const_bpf_stk            := Const_bpf_stk.
  Definition Const_content            := Const_content.
End Exports.
