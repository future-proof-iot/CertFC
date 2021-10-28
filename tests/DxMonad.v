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

Definition eval_pc: M int64_t := fun st => Some (eval_pc_tot st, st).
Definition upd_pc (p: int64_t): M unit := fun st => Some (tt, upd_pc_tot p st).
Definition upd_pc_incr: M unit := fun st => Some (tt, upd_pc_incr_tot st).

Definition eval_reg (r: reg) : M val64_t := fun st => Some (eval_reg_tot r st, st).
Definition upd_reg (r: reg) (v: val64_t) : M unit := fun st => Some (tt, upd_reg_tot r v st).
Definition eval_flag : M bpf_flag := fun st => Some (eval_flag_tot st, st).
Definition upd_flag (f:bpf_flag) : M unit := fun st => Some (tt, upd_flag_tot f st).
Definition eval_mem_regions : M memory_regions := fun st => Some (snd st, st).
Definition upd_mem_regions (mrs: memory_regions) : M unit := fun st => Some (tt, upd_mem_regions_tot mrs st).

(*Definition eval_reg_mem (chunk: memory_chunk) (r: reg) : M val64_t := fun st => Some (eval_reg_tot r st, st).
Definition upd_reg_mem (chunk: memory_chunk) (r: reg) (v: val64_t) : M unit := fun st => Some (tt, upd_reg_tot r v st).*)


Definition load_mem_tot (chunk: memory_chunk) (ptr: val64_t) (st: state) :=
  match Mem.loadv chunk (fst (fst (fst st))) ptr with
  | Some res => res
  | None => val64_zero
  end.

Definition store_mem_imm_tot (chunk: memory_chunk) (ptr: val64_t) (v: vals32_t) (st: state) :=
  match Mem.storev chunk (fst (fst (fst st))) ptr v with
  | Some m => m
  | None => init_mem
  end.

Definition store_mem_reg_tot (chunk: memory_chunk) (ptr v: val64_t) (st: state) :=
  match Mem.storev chunk (fst (fst (fst st))) ptr v with
  | Some m => m
  | None => init_mem
  end.

Definition load_mem (chunk: memory_chunk) (ptr: val64_t): M val64_t := fun st => Some (load_mem_tot chunk ptr st, st).

Definition store_mem_imm (chunk: memory_chunk) (ptr: val64_t) (v: vals32_t) : M unit := fun st => Some (tt, ((store_mem_imm_tot chunk ptr v st), snd (fst (fst st)), snd (fst st), snd st)).

Definition store_mem_reg (chunk: memory_chunk) (ptr v: val64_t) : M unit := fun st => Some (tt, ((store_mem_reg_tot chunk ptr v st), snd (fst (fst st)), snd (fst st), snd st)).

Declare Scope monad_scope.
Notation "'do' x <- a ; b" :=
  (bindM a (fun x => b))
    (at level 200, x name, a at level 100, b at level 200)
  : monad_scope.
