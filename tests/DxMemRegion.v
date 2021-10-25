From Coq Require Import List ZArith.
Import ListNotations.

From compcert.cfrontend Require Csyntax Ctypes Cop.
From compcert.common Require Import Values.
From compcert.lib Require Integers.

From dx Require Import ResultMonad IR.
From dx.Type Require Import Nat.

Require Import IdentDef CoqIntegers DxIntegers DxValues.

Definition mem_region_type: Ctypes.type := Ctypes.Tstruct mem_region_id Ctypes.noattr.

Definition mem_region_def: Ctypes.composite_definition := 
  Ctypes.Composite state_id Ctypes.Struct [(start_addr, C_U64); (size, C_U32)] Ctypes.noattr.

Record memory_region : Type := mkmr{
  ptr       : val64_t;
  start_addr: val64_t;
  size      : val64_t;
}.

Definition mem_regionCompilableType := MkCompilableType memory_region mem_region_type.

Definition default_memory_region := {|
  ptr        := Vzero;
  start_addr := Vzero;
  size       := Vzero;
|}.

Module MemRegions.

  Definition t := list memory_region.
  Definition index (l: t) (idx: nat): memory_region := 
    List.nth idx l default_memory_region.

End MemRegions.

Definition MemRegionsType := MemRegions.t.
Definition MemRegionsIndex := MemRegions.index.

(** "Mapping relations from Coq to C":
  Coq:                  -> C:
  l:list memory_region  -> mem_region_type *l
  index l idx           -> *(l+idx)
 *)

Definition get_index (x idx: Csyntax.expr): Csyntax.expr :=
  Csyntax.Eindex x idx mem_region_type.

(** Coq2C: l:list memory_region  -> mem_region_type *l *)
Definition MemRegionsCompilableType :=
  MkCompilableType MemRegionsType (Ctypes.Tpointer mem_region_type Ctypes.noattr).

(** Type for MemRegions.t -> nat -> mem_region_type *)
Definition MemRegionsTonatTomem_regionCompilableSymbolType :=
  MkCompilableSymbolType [MemRegionsCompilableType; natCompilableType] (Some mem_regionCompilableType).

(** Coq2C: get l idx -> *(l+idx) *)
Definition MemRegionsIndexPrimitive := 
  MkPrimitive MemRegionsTonatTomem_regionCompilableSymbolType 
              MemRegionsIndex
              (fun es => match es with
                         | [e1; e2] => Ok (get_index e1 e2)
                         | _   => Err PrimitiveEncodingFailed
                         end).

Module Exports.
  Definition mem_regionCompilableType := mem_regionCompilableType.
  Definition MemRegionsCompilableType := MemRegionsCompilableType.
  Definition MemRegionsIndexPrimitive := MemRegionsIndexPrimitive.
End Exports.
