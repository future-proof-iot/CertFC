From Coq Require Import List ZArith.
Import ListNotations.

From compcert.cfrontend Require Csyntax Ctypes Cop.
From compcert Require Import Integers Values Memtype.

From dx Require Import ResultMonad IR IRtoC.
From dx.Type Require Import Nat.

From bpf.comm Require Import MemRegion.
From bpf.src Require Import IdentDef CoqIntegers DxIntegers DxValues DxMemType.
(*
Record memory_region : Type := mkmr{
  start_addr : valptr8_t;
  block_size : valu32_t;   (**r should those be val32_t? *)
  block_perm : permission; (**r let's say it should be u32 *)
  block_ptr  : valptr8_t;
}.

Definition default_memory_region := {|
  start_addr := valptr_null;
  block_size := val32_zero;
  block_perm := Nonempty;
  block_ptr  := valptr_null;
|}.

Module Memory_regions.

  Definition t := list memory_region.
  Definition index_nat (l: t) (idx: nat): memory_region := 
    List.nth idx l (default_memory_region).

End Memory_regions.

Definition MyMemRegionsType := Memory_regions.t.
Definition MyMemRegionsIndexnat := Memory_regions.index_nat.

Definition default_memory_regions: MyMemRegionsType :=  [].
*)
Fixpoint MyMemRegionsAdd (mr: memory_region) (l: MyMemRegionsType) :=
  match l with
  | [] => [mr]
  | hd :: tl => hd :: MyMemRegionsAdd mr tl
  end.


(******************** Dx Related *******************)

Definition mem_region_type: Ctypes.type := Ctypes.Tpointer (Ctypes.Tstruct mem_region_id Ctypes.noattr) Ctypes.noattr.

Definition mem_region_def: Ctypes.composite_definition := 
  Ctypes.Composite mem_region_id Ctypes.Struct [(start_addr_id, C_U32); (size_id, C_U32); (perm_id, C_U32); (block_ptr_id, C_U8_pointer)] Ctypes.noattr.

Definition mem_regionCompilableType := MkCompilableType memory_region mem_region_type.

(** Type for mem_region -> valptr8_t *)

Definition mem_regionToValU8PTRCompilableSymbolType :=
  MkCompilableSymbolType [mem_regionCompilableType] (Some valptr8CompilableType).

Definition Const_block_ptr := 
  MkPrimitive mem_regionToValU8PTRCompilableSymbolType 
              block_ptr
              (fun es => match es with
                         | [e1] => Ok (Csyntax.Efield (Csyntax.Ederef e1 mem_region_type) block_ptr_id C_U8_pointer)
                         | _   => Err PrimitiveEncodingFailed
                         end).

(** Type for mem_region -> valu32_t *)

Definition mem_regionToValU32CompilableSymbolType :=
  MkCompilableSymbolType [mem_regionCompilableType] (Some valU32CompilableType).

Definition mem_regionTopermCompilableSymbolType :=
  MkCompilableSymbolType [mem_regionCompilableType] (Some permissionCompilableType).


Definition Const_start_addr := 
  MkPrimitive mem_regionToValU32CompilableSymbolType 
              start_addr
              (fun es => match es with
                         | [e1] => Ok (Csyntax.Efield (Csyntax.Ederef e1 mem_region_type) start_addr_id C_U32)
                         | _   => Err PrimitiveEncodingFailed
                         end).

Definition Const_block_size := 
  MkPrimitive mem_regionToValU32CompilableSymbolType 
              block_size
              (fun es => match es with
                         | [e1] => Ok (Csyntax.Efield (Csyntax.Ederef e1 mem_region_type) size_id C_U32)
                         | _   => Err PrimitiveEncodingFailed
                         end).

Definition Const_block_perm := 
  MkPrimitive mem_regionTopermCompilableSymbolType 
              block_perm
              (fun es => match es with
                         | [e1] => Ok (Csyntax.Efield (Csyntax.Ederef e1 mem_region_type) perm_id C_U32)
                         | _   => Err PrimitiveEncodingFailed
                         end).

(** "Mapping relations from Coq to C":
  Coq:                  -> C:
  l:list memory_region  -> mem_region_type *l
  get l idx             -> *(l+idx)
 *)

Definition get_index (x idx: Csyntax.expr): Csyntax.expr :=
  (*Csyntax.Eindex x idx mem_region_type.*)
  Csyntax.Ebinop Cop.Oadd x idx (Ctypes.Tpointer mem_region_type Ctypes.noattr).

(** Coq2C: l:list memory_region  -> memory_region *l *)
Definition MyMemRegionsCompilableType :=
  MkCompilableType MyMemRegionsType mem_region_type.

(** Type for MyMemRegions.t -> nat -> memory_region *)
Definition MyMemRegionsToNatToMemRegionCompilableSymbolType :=
  MkCompilableSymbolType [MyMemRegionsCompilableType; natCompilableType] (Some mem_regionCompilableType).

(** Coq2C: get l idx -> *(l+idx) *)
Definition myListIndexNatPrimitive := 
  MkPrimitive MyMemRegionsToNatToMemRegionCompilableSymbolType 
              MyMemRegionsIndexnat
              (fun es => match es with
                         | [e1; e2] => Ok (get_index e1 e2)
                         | _   => Err PrimitiveEncodingFailed
                         end).

Module Exports.
  Definition mem_regionCompilableType   := mem_regionCompilableType.
  Definition Const_block_ptr            := Const_block_ptr.
  Definition Const_start_addr           := Const_start_addr.
  Definition Const_block_size           := Const_block_size.
  Definition Const_block_perm           := Const_block_perm.
  Definition MyMemRegionsCompilableType := MyMemRegionsCompilableType.
  Definition myListIndexNatPrimitive    := myListIndexNatPrimitive.
End Exports.
