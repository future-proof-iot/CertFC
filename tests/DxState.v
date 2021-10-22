From compcert Require Import Memory Integers.

Require Import DxIntegers DxRegs DxFlag DxValues.

(******************** no-monadic function: *_tot *******************)

Definition ErrUnd: Type := ErrorUndef.

Definition eval_pc_tot (st: state): int64_t := pc_loc (snd st).

Definition upd_pc_tot (p: int64_t) (st:state): state := 
  let m  := fst st in
  let rs := snd st in
  let next_rs := {| pc_loc := Int64.add p Int64.one; regs_st := regs_st rs; |} in
    (m, next_rs).

Definition eval_reg_tot (r: reg) (st:state): val64_t :=
  eval_regmap r (regs_st (snd st)).

Definition upd_reg_tot (r:reg) (v:val64_t) (st:state): state :=
  let m  := fst st in
  let rs := snd st in
  let next_rs := {| pc_loc := Int64.add (pc_loc rs) Int64.one; regs_st := upd_regmap r v (regs_st rs); |} in
    (m, next_rs).

(******************** dx related *******************)




(*
Definition default_mem: mem := Mem.empty.

Definition default_state: state := 
  (default_mem, {| pc := 0; regs := init_regmap;|}).

Definition upd_errorundef_tot (eu: ErrorUndef) (st: state): state := default_state.

Definition eval_mem_tot (st: state): mem := fst st.*)

(******************** Monad Definition & monadic function *******************)

Definition MrBPF (Res: Type) := state -> (state * Res) + ErrUnd.

Definition returnM {A: Type} (a: A) : MrBPF A := fun b => inl (b, a).

Definition bindM {A B: Type} (ma: MrBPF A) (f: A -> MrBPF B) : MrBPF B :=
  fun b => 
     match ma b with
     | inl s => (f (snd s)) (fst s)
     | inr e => inr e
     end.

Definition default_MrBPF : MrBPF state := returnM init_state.

Declare Scope monad_scope.
Notation "'do' x <- a ; b" :=
  (bindM a (fun x => b))
    (at level 200, x name, a at level 100, b at level 200)
  : monad_scope.

Open Scope monad_scope.

Definition eval_pc (st: state): MrBPF int64_t := returnM (eval_pc_tot st).

Definition upd_pc (p: int64_t) (st: state): MrBPF state := returnM (upd_pc_tot p st).

Definition eval_reg (r: reg) (st: state): MrBPF val64_t :=  returnM (eval_reg_tot r st).

Definition upd_reg (r: reg) (v: val64_t) (st: state): MrBPF state := returnM (upd_reg_tot r v st).

(*
Definition upd_errorundef (eu: ErrorUndef) (st: state): MrBPF state := returnM (upd_errorundef_tot eu st).

Definition eval_mem (st: state): MrBPF mem := returnM (eval_mem_tot st).*)

Close Scope monad_scope.