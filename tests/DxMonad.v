From compcert Require Import AST Memory.
Require Import DxIntegers DxValues DxRegs DxFlag DxMemRegion DxState.


Definition stateM := state. (*This one must be int_64 defined in DxIntegers *)


Definition M (A: Type) := stateM -> option (A * state).

Definition runM {A: Type} (x: M A) (st: stateM) := x st.
Definition returnM {A: Type} (a: A) : M A := fun st => Some (a, st).
Definition emptyM {A: Type} : M A := fun st => None.
Definition bindM {A B: Type} (x: M A) (f: A -> M B) : M B :=
  fun st =>
    match runM x st with
    | None => None
    | Some (x', st') => runM (f x') st'
    end.

Definition eval_pc: M sint32_t := fun st => Some (eval_pc st, st).
Definition upd_pc (p: sint32_t): M unit := fun st => Some (tt, upd_pc p st).
Definition upd_pc_incr: M unit := fun st => Some (tt, upd_pc_incr st).

Definition eval_flag: M bpf_flag := fun st => Some (eval_flag st, st).
Definition upd_flag (f:bpf_flag) : M unit := fun st => Some (tt, upd_flag f st).

Definition eval_mem_num: M nat := fun st => Some (eval_mem_num st, st).

Definition eval_reg (r: reg) : M val64_t := fun st => Some (eval_reg r st, st).
Definition upd_reg (r: reg) (v: val64_t) : M unit := fun st => Some (tt, upd_reg r v st).

Definition eval_mem_regions : M MyMemRegionsType := fun st => Some (eval_mem_regions st, st).

(*
Definition bpf_add_mem_region (mr: memory_region) : M unit := fun st => Some (tt, add_mem_region mr st).

Definition bpf_add_region_ctx (mr: memory_region) : M unit := fun st => Some (tt, add_mem_region_ctx mr st).*)

Definition load_mem (chunk: memory_chunk) (ptr: valu32_t): M val64_t := fun st => Some (load_mem chunk ptr st, st).

Definition store_mem_imm (chunk: memory_chunk) (ptr: valu32_t) (v: vals32_t) : M unit := fun st => Some (tt, store_mem_imm chunk ptr v st).

Definition store_mem_reg (chunk: memory_chunk) (ptr: valu32_t) (v: val64_t) : M unit := fun st => Some (tt, store_mem_reg chunk ptr v st).

Declare Scope monad_scope.
Notation "'do' x <- a ; b" :=
  (bindM a (fun x => b))
    (at level 200, x name, a at level 100, b at level 200)
  : monad_scope.
