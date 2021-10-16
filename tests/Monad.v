From Coq Require Import List.
Import ListNotations.
From compcert Require Import Coqlib Integers Values Memory Maps Memdata.
From dx.tests Require Import Int16 Asm.

Record regs_state: Type := make_rst{
  pc    : nat;
  regs  : regmap;
}.

(** C: 
struct regs_state {
  unsigned int pc;
  unsigned long long regs[11];
}
 *)

Inductive ErrorUndef :=
  | ErrorL: bpf_flag -> ErrorUndef
  | UndefR: bpf_flag -> ErrorUndef.

Record M (ErrUnd State Res: Type) := mkM{
  run : State -> (State * Res) + ErrUnd;
}.

Definition State: Type := mem * regs_state.
Definition ErrUnd: Type := ErrorUndef.

Definition MrBPF: Type -> Type := M ErrUnd State.

Definition returnM {A: Type} (a: A) : MrBPF A :=
  {| run := fun b => inl (b, a) |}.

Definition bindM {A B: Type} (ma: MrBPF A) (f: A -> MrBPF B) : MrBPF B :=
  {| run := fun b => 
         match (run _ _ A ma) b with
         | inl s => run _ _ B (f (snd s)) (fst s)
         | inr e => inr e
         end
    |}.

Definition default_MrBPF : MrBPF unit :=
  {| run := fun s: State =>
       inl (s, tt)
   |}.

Declare Scope monad_scope.
Notation "'do' x <- a ; b" :=
  (bindM a (fun x => b))
    (at level 200, x name, a at level 100, b at level 200)
  : monad_scope.

Open Scope monad_scope.

Definition eval_pc: MrBPF nat :=
  {| run := fun st: State => inl (st, pc (snd st)) |}.

Definition upd_pc' (p:nat) (st:State): State := 
  let m  := fst st in
  let rs := snd st in
  let next_rs := {| pc := Nat.add p 1; regs := regs rs; |} in
    (m, next_rs)
.

Definition upd_pc (p: nat): MrBPF unit :=
  {| run := fun st: State =>
       let new_st := upd_pc' p st in
         inl (new_st, tt)
   |}.

Definition eval_reg (r: reg) : MrBPF val := 
  {| run := fun st:State =>
       let ret:val := eval_regmap r (regs (snd st)) in
         inl (st, ret)
   |}.

Definition upd_reg' (r:reg) (v:val) (st:State): State :=
  let m  := fst st in
  let rs := snd st in
  let next_rs := {| pc := Nat.add (pc rs) 1; regs := upd_regmap r v (regs rs); |} in
    (m, next_rs)
.

Definition upd_reg (r: reg) (v: val) : MrBPF unit :=
  {| run := fun st: State =>
       let new_st := upd_reg' r v st in
       inl (new_st, tt)
   |}.

Definition upd_errorundef (eu: ErrorUndef) : MrBPF unit :=
  {| run := fun st: State => inr eu |}.

Definition eval_mem: MrBPF mem :=
  {| run := fun st:State => inl (st, (fst st)) |}.

Close Scope monad_scope.

(**
Definition memory_region : Type := val * (int64 * nat).

Record memory_regions : Type := mkmr{
  ctx    : memory_region;
  stk    : memory_region;
  content: memory_region;
}.

Definition init_mem: mem := Mem.empty.

Definition init_State: State := 
  (init_mem, {| pc := 0; regs := init_regmap;|})
.
*)