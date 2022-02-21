From compcert Require Import AST Integers Values Memory.

From bpf.comm Require Import Regs Flag rBPFValues MemRegion State.

Definition M (A: Type) := state -> option (A * state).

Definition returnM {A: Type} (a: A) : M A := fun st => Some (a, st).
Definition returnS: M state := fun st => Some (st, st).
Definition errorM {A: Type} : M A := fun st => None.
Definition bindM {A B: Type} (x: M A) (f: A -> M B) : M B :=
  fun st =>
    match x st with
    | None => None
    | Some (x', st') => (f x') st'
    end.

Definition eval_pc: M int := fun st => Some (eval_pc st, st).
Definition upd_pc (p: int): M unit := fun st => Some (tt, upd_pc p st).
Definition upd_pc_incr: M unit := fun st => Some (tt, upd_pc_incr st).

Definition eval_flag: M bpf_flag := fun st => Some (eval_flag st, st).
Definition upd_flag (f:bpf_flag) : M unit := fun st => Some (tt, upd_flag f st).

Definition eval_mrs_num: M nat := fun st => Some (eval_mem_num st, st).

Definition eval_reg (r: reg) : M val := fun st => Some (eval_reg r st, st).
Definition upd_reg (r: reg) (v: val) : M unit := fun st =>
  match v with
  | Vlong _ => Some (tt, upd_reg r v st)
  | _ => None
  end.

Definition eval_mrs_regions : M MyMemRegionsType := fun st => Some (eval_mem_regions st, st).

Definition eval_mem_regions: M MyMemRegionsType := fun st => Some (eval_mem_regions st, st).

Definition eval_mem : M Mem.mem := fun st => Some (eval_mem st, st).


Definition load_mem (chunk: memory_chunk) (ptr: val): M val := fun st => Some (load_mem chunk ptr st, st).

Definition store_mem_imm (chunk: memory_chunk) (ptr: val) (v: val) : M unit := fun st => 
  match store_mem_imm chunk ptr v st with
  | Some res => Some (tt, res)
  | None => None
  end.

Definition store_mem_reg (chunk: memory_chunk) (ptr: val) (v: val) : M unit := fun st => 
  match store_mem_reg chunk ptr v st with
  | Some res => Some (tt, res)
  | None => None
  end.

Definition eval_ins_len : M int := fun st => Some (eval_ins_len st, st).
Definition eval_ins (idx: int) : M int64 := fun st => Some (eval_ins idx st, st).

Definition cmp_ptr32_nullM (v: val): M bool := fun st =>
  match cmp_ptr32_null (State.eval_mem st) v with
  | Some res => Some (res, st)
  | None     => None
  end.

Declare Scope monad_scope.
Notation "'do' x <- a ; b" :=
  (bindM a (fun x => b))
    (at level 200, x name, a at level 100, b at level 200)
  : monad_scope.

(* Given the immediate of the call, it returns a function pointer *)

(* Let assume there is a bpf context pointer in the memory. For the time being, your interpreter does not use it.
   Let keep it that way -- at least for the moment. *)
Axiom _bpf_get_call : val -> M val. (**r here is Vint -> Vptr *)
Axiom exec_function : val -> M val. (**r Vptr -> Vint *)
Axiom lemma_bpf_get_call :
  forall i st1,
    exists ptr,
      _bpf_get_call (Vint i) st1 = Some (ptr, st1) /\
      (ptr = Vnullptr \/ (exists b ofs, ptr = Vptr b ofs)).
Axiom lemma_exec_function0 :
  forall b ofs st1,
      exists v st2, exec_function (Vptr b ofs) st1 = Some (Vint v, st2) /\ cmp_ptr32_null (State.eval_mem st1) (Vptr b ofs) = Some false.
(*
Axiom lemma_exec_function1 :
  forall st1, exec_function Vnullptr st1 = None. *)
(*
Axiom lemma_exec_function: forall (st:state) (i: int) (m:mem),
      exec_function st (_bpf_get_call i) Vnullptr = NormalState (upd_pc (pc st) st) m.
*)
